package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Clause.vars
import leo.datastructures._
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Have, Refine, Rewrite}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Obj
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{Pi, Prf}
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewModularEncoding.AssumeStep.{encAssumeStep, extractVarNames}
import leo.modules.output.LPoutput.NewModularEncoding.EqualityProofSteps
import leo.modules.output.LPoutput.NewModularEncoding.ProofTermUtil.{proofName, proofTermAsTacticArg}

import scala.collection.mutable

object RewritingBasedRuleEncoding {

  ////////////////////////////////////////////////////////////////
  ////////// Utilities shared by rewriting-based rules
  ////////////////////////////////////////////////////////////////

  object Util {

    /**
      * Encoded preliminaries of one RewriteSimp step.
      */
    final case class EncRewriteCtx(encChild: lpClauseInst,
                                   encParent: lpClauseInst,
                                   encRewriteRules: Seq[lpClauseInst],
                                   sharedVarMap: Map[Int, String],
                                   childVarMap: Map[Int, String],
                                   parentNameLpEnc: LpTerm[Level.Obj],
                                   rewriteRuleNamesLpEnc: Seq[LpTerm[Level.Obj]])

    final case class RewriteRuleUse(rewriteRuleParentId: Long,
                                    rewriteRule: Clause,
                                    origTermSubst: Subst,
                                    origTypeSubst: Subst)

    final case class PreparedRewriteRuleUse(rewriteRuleParentId: Long,
                                            originalRule: Clause,
                                            shiftedRule: Clause,
                                            instantiatedRule: Clause,
                                            termSubst: Seq[UniTermSubst])

    /**
      * Encode the child, main parent, and rewrite-rule parents in one pass.
      *
      * The returned context contains both the encoded clauses and the proof
      * names that will later be used to refine with the parent proofs.
      */
    def initRewriteRuleCtxt(childCl: Clause,
                            parentCl: Clause,
                            rewriteRuleCls: Seq[Clause],
                            parentNameLpEnc0: Name,
                            rewriteRuleNameLpEnc0: Seq[Name]): EncRewriteCtx = {
      require(rewriteRuleCls.length == rewriteRuleNameLpEnc0.length,
        "Each rewrite-rule clause must have a corresponding Lambdapi proof name")

      val allClauses = Seq(childCl, parentCl) ++ rewriteRuleCls
      val (sharedVarMap, encClauses) = lpClauseInst.apply_to_set(allClauses)

      val encChild = encClauses.head
      val encParent = encClauses(1)
      val encRewriteRules = encClauses.drop(2)
      val childVarMap = sharedVarMap.view.filterKeys(vars(childCl).distinct).toMap

      EncRewriteCtx(
        encChild,
        encParent,
        encRewriteRules,
        sharedVarMap,
        childVarMap,
        proofName(parentNameLpEnc0),
        rewriteRuleNameLpEnc0.map(proofName)
      )
    }

    /**
      * Normalize rewrite-use information from `FurtherInfo`.
      */
    def initRewriteRuleUses(addInfoRw: Seq[AddInfoRewrite],
                            rewriteRuleParents: Seq[ClauseProxy]): Seq[RewriteRuleUse] = {
      if (addInfoRw.nonEmpty) {
        addInfoRw.map(info => RewriteRuleUse(info.rewriteRuleParentId, info.rewriteRule, info.origTermSubst, info.origTypeSubst))
      } else {
        rewriteRuleParents.map(parent => RewriteRuleUse(parent.id, parent.cl, Subst.id, Subst.id))
      }
    }

    /**
      * Reconstruct one rewrite-rule instance in the same variable space used by
      * Leo's matcher. Non-ground rewrite rules are shifted past the variables of
      * the rewritten clause before matching; the recorded substitution is
      * indexed over that shifted rule.
      */
    def prepareRewriteRuleUse(use: RewriteRuleUse,
                              rewrittenParent: Clause): Either[String, PreparedRewriteRuleUse] = {
      if (use.rewriteRule.typeVars.nonEmpty || use.origTypeSubst != Subst.id) {
        Left("RW: Polymorphic rewrite-rule instantiation not encoded")
      } else {
        val termOffset = Clause.maxImplicitlyBound(rewrittenParent)
        val shiftedRule = use.rewriteRule.substitute(Subst.shift(termOffset))
        val instantiatedRule = shiftedRule.substitute(use.origTermSubst, use.origTypeSubst)
        val currentVarIndices = rewrittenParent.implicitlyBound.map(_._1).toSet
        val residualRuleVars = instantiatedRule.implicitlyBound.map(_._1).filterNot(currentVarIndices)

        if (residualRuleVars.nonEmpty) {
          Left(s"RW: Rewrite-rule substitution leaves variables outside the rewritten parent context: ${residualRuleVars.mkString(", ")}")
        } else {
          SubstitutionEncoding.trackTermSubstitution(
            use.origTermSubst,
            use.origTypeSubst,
            shiftedRule.implicitlyBound
          ).map(termSubst => PreparedRewriteRuleUse(use.rewriteRuleParentId, use.rewriteRule, shiftedRule, instantiatedRule, termSubst))
        }
      }
    }

  }
}

////////////////////////////////////////////////////////////////
////////// Encoding for Leo's RewriteSimp rule
////////////////////////////////////////////////////////////////

object RewriteSimpEncoding {

  import RewritingBasedRuleEncoding.Util._

  // Define reasons for proofs being non-encodable
  private val MissingRewriteSubstitutionReason = "RW: Non-ground rewrite rule has no recorded instantiation"
  private val LiteralTransformationReason = "RW: Literal simplification or transformation not encoded"
  private val RewriteUnderBinderReason = "RW: Rewrite under binder required"

  final case class RewriteSimpCtx(rewriteUses: Seq[RewriteRuleUse],
                                  parentModuloRw: Option[Clause])

  /**
    * Mutable proof-construction state for one RewriteSimp step.
    *
    * `allSteps` contains goal-transforming script steps in the order in which
    * Lambdapi should execute them. Rewrite-rule setup haves are kept separately
    * because they only provide local proof names; literal-shape rewrites must
    * run before the actual rewrite tactics use those names.
    */
  final case class RewriteState(allSteps: Vector[LpProofScript],
                                rewriteRuleSetupSteps: Vector[LpProofScript],
                                rewriteApplicationSteps: Vector[LpProofScript],
                                rewrittenLits: Vector[lpLiteralInst],
                                notEncodedReasons: mutable.LinkedHashSet[String],
                                transformationsRwCounter: Int,
                                eqFlipCounter: Int,
                                rewriteInstantiationCounter: Int) {
    def markNotEncoded(reason: String): RewriteState = {
      notEncodedReasons += reason
      this
    }
    def allTransformationsEncoded: Boolean = notEncodedReasons.isEmpty
  }

  def initRewriteSimpCtxt(child: ClauseProxy,
                          rewriteRuleParents: Seq[ClauseProxy],
                          parentModuloRw: Option[Clause]): RewriteSimpCtx = {
    RewriteSimpCtx(
      initRewriteRuleUses(child.furtherInfo.addInfoRw, rewriteRuleParents),
      parentModuloRw
    )
  }


  /**
    * Orchestrator for the migrated encoding of Leo-III's `RewriteSimp` rule.
    *
    * The produced modular proof script has the following shape:
    *
    * 1. Abstract over the variables of the child clause.
    *
    * 2. Account for literal-shape mismatches between the child and the
    *    simulated rewritten parent. These are transformations such as moving
    *    between a formula literal and a Boolean equality literal, or flipping
    *    the sides of an equality literal. They are currently emitted as:
    *
    *      have TransformLiteral_N : π (oldLiteral = newLiteral) { ... };
    *      rewrite .[focused literal pattern] TransformLiteral_N;
    *
    * 3. For each rewrite-rule parent used by Leo-III, introduce a local proof
    *    term for the equality that Lambdapi should use for rewriting:
    *
    *    - If the rewrite-rule parent is a non-equational single literal, prove
    *      its Boolean equality form, either `⊤ = P` or `⊥ = P`, using the
    *      corresponding simplification theorem.
    *
    *    - If the rewrite-rule parent is an equational single literal, prove
    *      the reverse equality once using equality symmetry.
    *
    *    - Instantiate non-ground rewrite-rule parents with the substitution
    *      recorded by Leo, then refine the local equality proof with that
    *      instantiated rule proof.
    *
    * 4. Replay every focused rewrite in the parent clause using the local proof
    *    terms from step 3.
    *
    * 5. If literal simplifications from `addInfoSimp` were applied, defer to the
    *    migrated encoding of `Simp`. This is not implemented in this module yet,
    *    so such cases are currently reported as unsupported.
    *
    * 6. Refine the final goal with the parent proof, instantiated with the
    *    variables abstracted in step 1.
    */
  def encRewrite(cl: ClauseProxy,
                 parents: Seq[ClauseProxy],
                 addInfoSimp: Seq[(Seq[Int], Int)],
                 parentModuloRw: Option[Clause],
                 parentNameLpEnc: Seq[Name],
                 sig: LpSig): EncodeResult = {
    Out.lp_debug_info("Encoding instance of rewrite simplification")
    assert(parents.length == parentNameLpEnc.length)

    // Extract the main parent and the rewrite-rule parents. The first parent is
    // the clause to be rewritten; all remaining parents justify the rewrite
    // equalities used by the step.
    val parent = parents.head
    val rewriteRules = parents.tail
    val sourceBeforeParent = parentNameLpEnc.head
    val sourcesBeforeEq = parentNameLpEnc.tail

    val rwCtx = initRewriteSimpCtxt(cl, rewriteRules, parentModuloRw)

    if (cl.furtherInfo.addInfoRw.isEmpty && rewriteRules.exists(rule => rule.cl.implicitlyBound.nonEmpty)) {
      return NotEncodable(MissingRewriteSubstitutionReason)
    }

    val preparedRewriteUses = rwCtx.rewriteUses.map { use =>
      prepareRewriteRuleUse(use, parent.cl) match {
        case Left(reason) => return NotEncodable(reason)
        case Right(prepared) => prepared
      }
    }

    val rewriteRuleSourcesByParentId = rewriteRules.zip(sourcesBeforeEq).map {
      case (ruleParent, sourceName) => ruleParent.id -> sourceName
    }.toMap
    val rewriteRuleSourceNames = preparedRewriteUses.map { use =>
      rewriteRuleSourcesByParentId.get(use.rewriteRuleParentId) match {
        case Some(sourceName) => sourceName
        case None => return NotEncodable(s"RW: Recorded rewrite parent ${use.rewriteRuleParentId} is absent from the proof annotation")
      }
    }

    // Encode the instantiated rewrite uses, child, and main parent with one
    // shared variable map. PatternBuilder deliberately performs exact matching,
    // so it must receive the concrete instances used by Leo.
    val ctxt = initRewriteRuleCtxt(cl.cl, parent.cl, preparedRewriteUses.map(_.instantiatedRule), sourceBeforeParent, rewriteRuleSourceNames)
    val EncRewriteCtx(encChild, encParent, encRewriteRules, sharedVarMap, _, parentNameLpEnc0, rewriteRuleNamesLpEnc) = ctxt

    Out.lp_debug_info(s"Encoding application or RW-rule on ${sourceBeforeParent.value}")
    Out.lp_debug_info(s"Found ${rwCtx.rewriteUses.length} recorded rewrite rule use(s)")

    val initialReasons = mutable.LinkedHashSet.empty[String]
    val childVarNames = extractVarNames(encChild)
    val initialAssumeSteps = encAssumeStep(childVarNames).toVector
    val disappearingParentVars = parent.cl.implicitlyBound.filterNot(cl.cl.implicitlyBound.contains)
    var state = RewriteState(initialAssumeSteps, Vector.empty, Vector.empty, encParent.lits.toVector, initialReasons, 0, 0, 0)

    // Literal simplifications tracked via AddInfoSimp are not migrated yet.
    state = encodeSimplificationTransformations(addInfoSimp, state)

    // First inspect every rewrite rule and collect:
    //   - local have-steps proving the equality actually used for rewriting;
    //   - rewrite tactics for every found occurrence;
    //   - the parent literals after those rewrites have been simulated.
    preparedRewriteUses.zip(rewriteRuleNamesLpEnc).zip(encRewriteRules).foreach {
      case ((rewriteUse, rewriteRuleName), encRewriteRule) =>
        state = encodeOneRewriteRuleApplication(rewriteUse, encRewriteRule, rewriteRuleName, parent.cl.implicitlyBound, sharedVarMap, state)
    }

    // If the simulated rewritten parent differs from the child only by literal
    // shape, transform the current goal to the intermediate shape that the
    // rewrite tactics will then solve. This deliberately precedes the collected
    // rewrite-rule setup and rewrite-application steps in the final script.
    state =
      if (state.allTransformationsEncoded) transformRemainingLiterals(encChild.lits, state)
      else state

    // Finish the proof script in backward order:
    //   child goal
    //   -> optional literal-shape transformations
    //   -> rewrite-rule haves
    //   -> rewrite applications
    //   -> instantiated parent proof.
    val rewriteBodySteps = state.allSteps.drop(initialAssumeSteps.length) ++ state.rewriteRuleSetupSteps ++ state.rewriteApplicationSteps
    val parentRefine = refineWithInstantiatedProof(
      parentNameLpEnc0,
      parent.cl.implicitlyBound,
      parent.cl.implicitlyBound,
      sharedVarMap
    )
    val completedRewriteBody = rewriteBodySteps :+ parentRefine

    val finalSteps = if (disappearingParentVars.isEmpty) {
      initialAssumeSteps ++ completedRewriteBody
    } else {
      // Replay the rewrite under the variables that disappear from the child,
      // then instantiate that local proof with witnesses. This keeps each such
      // variable consistent across the rewrite-rule instance and main parent.
      val localProofName = Name("RewriteWithParentVars")
      val disappearingBinders = disappearingParentVars.map { case (index, ty) =>
        Lifting.OlVarM(var2Lp(index, ty, sharedVarMap))
      }
      val localProofSteps = encAssumeStep(disappearingBinders.map(_.name)) ++ completedRewriteBody
      val localProof = Have(localProofName, Pi(disappearingBinders, Prf(encChild.term)), localProofSteps.map(Left(_)))
      val instantiatedLocalProof = refineWithInstantiatedProof(
        proofName(localProofName),
        disappearingParentVars,
        Seq.empty,
        sharedVarMap
      )
      initialAssumeSteps ++ Vector(localProof, instantiatedLocalProof)
    }

    if (state.allTransformationsEncoded) Encoded(finalSteps)
    else NotEncodable(state.notEncodedReasons.mkString("; "))
  }

  ////////////////////////////////////////////////////////////////
  ////////// Rewrite-rule setup
  ////////////////////////////////////////////////////////////////

  /**
    * Prepare and apply one rewrite-rule parent.
    *
    * Leo records the rule in the orientation used by proof search. Lambdapi's
    * rewrite tactic needs a positive equality in the direction used to transform
    * the current goal, so non-equational rewrite clauses are first turned into
    * Boolean equalities and positive equalities are flipped.
    *
    * todo: rather than flipping, just use "rewrite left"
    */
  private def encodeOneRewriteRuleApplication(rewriteUse: PreparedRewriteRuleUse,
                                              encRewriteRule: lpClauseInst,
                                              sourceBeforeEq: LpTerm[Level.Obj],
                                              currentVars: Seq[(Int, Type)],
                                              sharedVarMap: Map[Int, String],
                                              state0: RewriteState): RewriteState = {
    val rewriteEqClause = rewriteUse.instantiatedRule
    assert(rewriteEqClause.lits.length == 1, s"trying to encode RW rule application with RW clause of length ${rewriteEqClause.lits.length}")

    val rewriteEq = rewriteEqClause.lits.head
    val rwLhs = term2LP(rewriteEq.left, sharedVarMap)
    val rwRhs0 = term2LP(rewriteEq.right, sharedVarMap)
    val rwType = type2LP(rewriteEq.right.ty)
    val rwPol = rewriteEq.polarity

    val (state1, instantiatedSource) = provideInstantiatedRewriteRuleProof(
      rewriteUse,
      encRewriteRule,
      sourceBeforeEq,
      currentVars,
      sharedVarMap,
      state0
    )

    Out.lp_debug_info(s"Rewriting with ${instantiatedSource}")
    val (state2, transformedSource, rwRhs) = provideRewriteEqualityProof(rewriteEq, rwLhs, rwRhs0, rwType, rwPol, instantiatedSource, state1)
    rewriteFocusedGoal(rwLhs, rwRhs, transformedSource, state2)
  }

  /** Prove the concrete rewrite-rule instance recorded by Leo. */
  private def provideInstantiatedRewriteRuleProof(rewriteUse: PreparedRewriteRuleUse,
                                                  encRewriteRule: lpClauseInst,
                                                  sourceBeforeEq: LpTerm[Level.Obj],
                                                  currentVars: Seq[(Int, Type)],
                                                  sharedVarMap: Map[Int, String],
                                                  state0: RewriteState): (RewriteState, LpTerm[Level.Obj]) = {
    if (rewriteUse.termSubst.isEmpty) {
      (state0, sourceBeforeEq)
    } else {
      val stepName = Name(s"RewriteInstantiation_${state0.rewriteInstantiationCounter}")
      val instantiatedSource = SubstitutionEncoding.instantiateProofTerm(
        rewriteUse.shiftedRule.implicitlyBound,
        currentVars,
        rewriteUse.termSubst,
        sharedVarMap,
        sourceBeforeEq
      )
      val haveInstance = LpProofScript.Have(
        stepName,
        Prf(encRewriteRule.term),
        Seq(Left(Refine(Obj(instantiatedSource))))
      )

      (
        state0.copy(
          rewriteRuleSetupSteps = state0.rewriteRuleSetupSteps :+ haveInstance,
          rewriteInstantiationCounter = state0.rewriteInstantiationCounter + 1
        ),
        proofName(stepName)
      )
    }
  }

  /** Return the proof term and RHS that should be used by the rewrite tactic. */
  private def provideRewriteEqualityProof(rewriteEq: Literal,
                                          rwLhs: LpTerm[Level.Obj],
                                          rwRhs0: LpTerm[Level.Obj],
                                          rwType: OlMonoType,
                                          rwPol: Boolean,
                                          sourceBeforeEq: LpTerm[Level.Obj],
                                          state0: RewriteState): (RewriteState, LpTerm[Level.Obj], LpTerm[Level.Obj]) = {
    if (!rewriteEq.equational) {
      recordPropLiteralRewriteEquality(rwLhs, rwPol, sourceBeforeEq, state0)
    } else if (rewriteEq.polarity) {
      recordFlippedRewriteEquality(rwLhs, rwRhs0, rwType, sourceBeforeEq, state0)
    } else {
      throw new Exception("Error while attempting to encode rewrite step in LP: Rewrite rule is equational but not positive")
    }
  }

  /**
    * Add the shared subproof that turns a non-equational rewrite-rule parent
    * into the Boolean equality used by the later rewrite tactic.
    */
  private def recordPropLiteralRewriteEquality(rwLhs: LpTerm[Level.Obj],
                                               rwPol: Boolean,
                                               sourceBeforeEq: LpTerm[Level.Obj],
                                               state0: RewriteState): (RewriteState, LpTerm[Level.Obj], LpTerm[Level.Obj]) = {
    val transformationStepName = Name(s"TransformToEqLits_${state0.transformationsRwCounter}")
    val equalityProof = EqualityProofSteps.provePropLiteralAsBooleanEquality(transformationStepName, rwLhs, rwPol, sourceBeforeEq)

    Out.lp_debug_info("Transforming rewrite rule to equality...")
    (
      state0.copy(
        rewriteRuleSetupSteps = state0.rewriteRuleSetupSteps :+ equalityProof.step,
        transformationsRwCounter = state0.transformationsRwCounter + 1
      ),
      equalityProof.proofTerm,
      equalityProof.rhs
    )
  }

  /**
    * Add the shared subproof that flips an equational rewrite-rule parent and
    * records the local proof name used by the later rewrite tactic.
    */
  private def recordFlippedRewriteEquality(rwLhs: LpTerm[Level.Obj],
                                           rwRhs: LpTerm[Level.Obj],
                                           rwType: OlMonoType,
                                           sourceBeforeEq: LpTerm[Level.Obj],
                                           state0: RewriteState): (RewriteState, LpTerm[Level.Obj], LpTerm[Level.Obj]) = {
    val transformationStepName = Name(s"flip_equality_${state0.eqFlipCounter}")
    val equalityProof = EqualityProofSteps.proveFlippedEquality(transformationStepName, rwLhs, rwRhs, rwType, sourceBeforeEq)
    Out.lp_debug_info(s"transforming rewrite clause to ${LogicConst.Eq(rwType, rwRhs, rwLhs)}")

    (
      state0.copy(
        rewriteRuleSetupSteps = state0.rewriteRuleSetupSteps :+ equalityProof.step,
        eqFlipCounter = state0.eqFlipCounter + 1
      ),
      equalityProof.proofTerm,
      equalityProof.rhs
    )
  }

  ////////////////////////////////////////////////////////////////
  ////////// Rewrite occurrence search and replay
  ////////////////////////////////////////////////////////////////

  /**
    * Simulate applying one rewrite equality to every literal of the parent.
    *
    * For each found occurrence, this updates `rewrittenLits` and records the
    * corresponding Lambdapi rewrite tactic.
    * Occurrences below binders are currently treated as unsupported.
    */
  private def rewriteFocusedGoal(rwLhs: LpTerm[Level.Obj],
                                 rwRhs: LpTerm[Level.Obj],
                                 sourceBeforeEq: LpTerm[Level.Obj],
                                 state0: RewriteState): RewriteState = {
    val clauseLen = state0.rewrittenLits.length
    var state = state0
    state0.rewrittenLits.zipWithIndex.foreach {
      case (encLit, litCount) =>
        val (patternTerm, rewrittenLitTerm, counter, rwUnderBinder) = PatternBuilder.findRWTerm(Map(rwLhs -> rwRhs), encLit.term)
        if (rwUnderBinder) {
          Out.lp_debug_info(s"Rewriting tactic cannot be used on literal of the parent clause since term is under binder")
          state = state.markNotEncoded(RewriteUnderBinderReason)
        } else if (counter != 0) {
          val rewrittenLit = encLit.copy(term = rewrittenLitTerm)
          state = state.copy(rewrittenLits = state.rewrittenLits.updated(litCount, rewrittenLit))
          Out.lp_debug_info(s"Trying to apply rewrite rule to literal $litCount of the parent clause")
          val rewritePattern = PatternBuilder.generateClausePattern(litCount, clauseLen, patternTerm)
          state = state.copy(
            rewriteApplicationSteps = state.rewriteApplicationSteps :+
              Rewrite(Some(rewritePattern), proofTermAsTacticArg(sourceBeforeEq))
          )
        }
    }
    state
  }

  ////////////////////////////////////////////////////////////////
  ////////// Literal-shape transformations
  ////////////////////////////////////////////////////////////////

  /**
    * Add transformations for mismatches between the child literal and the
    * simulated rewritten parent literal.
    *
    * These transformations are not the actual term rewrites. They only account
    * for changes such as moving between a proposition and a Boolean equality
    * literal, so that the subsequent rewrite tactics apply to the right
    * intermediate goal.
    */
  private def transformRemainingLiterals(encChildLits: Seq[lpLiteralInst],
                                         state0: RewriteState): RewriteState = {
    var state = state0
    EqualityProofSteps.literalMismatches(encChildLits, state0.rewrittenLits).foreach { mismatch =>
      Out.lp_debug_info(s"rewritten Literal: ${mismatch.intermediateLit}, corresponding literal in child clause: ${mismatch.targetLit}")
      val transformStepName = Name(s"TransformLiteral_${state.transformationsRwCounter}")
      val additionalSteps = EqualityProofSteps.transformLiteralWithTactic(
        transformStepName,
        mismatch.targetLit,
        mismatch.intermediateLit,
        mismatch.clauseAfterTransformation,
        mismatch.litIdx
      )
      state = state.copy(
        allSteps = state.allSteps ++ additionalSteps,
        transformationsRwCounter = state.transformationsRwCounter + 1
      )
    }
    state
  }

  ////////////////////////////////////////////////////////////////
  ////////// Unsupported simplification tracking and final refinement
  ////////////////////////////////////////////////////////////////

  /** Keep the old behavior for AddInfoSimp until Simp is migrated to the new structures. */
  private def encodeSimplificationTransformations(addInfoSimp: Seq[(Seq[Int], Int)],
                                                  state0: RewriteState): RewriteState = {
    if (addInfoSimp.nonEmpty) {
      Out.lp_debug_info("Simplification steps not yet encoded")
      state0.markNotEncoded(LiteralTransformationReason)
    } else state0
  }

  /** Close the current subgoal with a proof instantiated in the variables available at that point. */
  private def refineWithInstantiatedProof(sourceProof: LpTerm[Level.Obj],
                                          quantifiedVars: Seq[(Int, Type)],
                                          availableVars: Seq[(Int, Type)],
                                          sharedVarMap: Map[Int, String]): Refine = {
    val instantiatedParent = SubstitutionEncoding.instantiateProofTerm(
      quantifiedVars,
      availableVars,
      Seq.empty,
      sharedVarMap,
      sourceProof
    )
    Refine(Obj(instantiatedParent))
  }
}
