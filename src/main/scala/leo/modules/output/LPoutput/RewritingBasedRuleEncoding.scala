package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Clause.vars
import leo.datastructures._
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.ImplicitTransformationUtil.{reconstructBeforeLiteralNormalisation, verifySubstitutionLiteralNormalisazion}
import leo.modules.output.LPoutput.LpLibs.ND.Terms.topIntro
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Have, Refine, Repeat, Rewrite, Simplify, Try}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Obj
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{Pi, Prf}
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewModularEncoding.AssumeStep.{encAssumeStep, extractVarNames}
import leo.modules.output.LPoutput.NewModularEncoding.EqualityProofSteps
import leo.modules.output.LPoutput.NewModularEncoding.ProofTermUtil.{applyProofToVars, proofName, proofTermAsTacticArg}

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
                                   encBlockResults: Seq[lpClauseInst],
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
                                            termSubst: Seq[UniTermSubst],
                                            residualRuleVars: Seq[Int])

    /**
      * Encode the child, main parent, block results, and any concrete fallback
      * rewrite-rule instances in one pass.
      *
      * The returned context contains both the encoded clauses and the proof
      * names that will later be used to refine with the parent proofs.
      */
    def initRewriteRuleCtxt(childCl: Clause,
                            parentCl: Clause,
                            blockResultCls: Seq[Clause],
                            rewriteRuleCls: Seq[Clause],
                            parentNameLpEnc0: Name,
                            rewriteRuleNameLpEnc0: Seq[Name]): EncRewriteCtx = {
      require(rewriteRuleCls.length == rewriteRuleNameLpEnc0.length,
        "Each rewrite-rule clause must have a corresponding Lambdapi proof name")

      val allClauses = Seq(childCl, parentCl) ++ blockResultCls ++ rewriteRuleCls
      val (sharedVarMap, encClauses) = lpClauseInst.apply_to_set(allClauses)

      val encChild = encClauses.head
      val encParent = encClauses(1)
      val encBlockResults = encClauses.slice(2, 2 + blockResultCls.length)
      val encRewriteRules = encClauses.drop(2 + blockResultCls.length)
      val childVarMap = sharedVarMap.view.filterKeys(vars(childCl).distinct).toMap

      EncRewriteCtx(
        encChild,
        encParent,
        encBlockResults,
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
      * Move quantified rewrite-rule variables beyond every variable index used
      * by the enclosing RewriteSimp proof.
      */
    def shiftRewriteRulesPast(rewriteRules: Seq[Clause],
                              enclosingClauses: Seq[Clause]): Seq[Clause] = {
      val termOffset = enclosingClauses.foldLeft(0) { case (currentMax, clause) =>
        math.max(currentMax, Clause.maxImplicitlyBound(clause))
      }
      rewriteRules.map(_.substitute(Subst.shift(termOffset)))
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
        val shiftedRule = shiftRewriteRulesPast(Seq(use.rewriteRule), Seq(rewrittenParent)).head
        val instantiatedRule = shiftedRule.substitute(use.origTermSubst, use.origTypeSubst)
        val currentVarIndices = rewrittenParent.implicitlyBound.map(_._1).toSet
        val residualRuleVars = instantiatedRule.implicitlyBound.map(_._1).filterNot(currentVarIndices)

        SubstitutionEncoding.trackTermSubstitution(
          use.origTermSubst,
          use.origTypeSubst,
          shiftedRule.implicitlyBound
        ).map(termSubst => PreparedRewriteRuleUse(use.rewriteRuleParentId, use.rewriteRule, shiftedRule, instantiatedRule, termSubst, residualRuleVars))
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
  private val LiteralReconstructionReason = "RW: Could not reconstruct literal normalization"

  final case class RewriteSimpCtx(rewriteUses: Seq[RewriteRuleUse])

  /**
    * Mutable proof-construction state for one RewriteSimp step.
    *
    * Literal-normalization steps and rewrite-rule setup haves are kept
    * separately because normalization changes the outer goal, while the rule
    * haves are used inside the forward rewrite implication.
    */
  final case class RewriteState(literalTransformationSteps: Vector[LpProofScript],
                                rewriteRuleSetupSteps: Vector[LpProofScript],
                                forwardRewriteRules: Vector[Vector[LpTerm[Level.Obj]]],
                                notEncodedReasons: mutable.LinkedHashSet[String],
                                transformationsRwCounter: Int,
                                rewriteInstantiationCounter: Int) {
    def markNotEncoded(reason: String): RewriteState = {
      notEncodedReasons += reason
      this
    }
    def allTransformationsEncoded: Boolean = notEncodedReasons.isEmpty
  }

  def initRewriteSimpCtxt(child: ClauseProxy,
                          rewriteRuleParents: Seq[ClauseProxy]): RewriteSimpCtx = {
    RewriteSimpCtx(initRewriteRuleUses(child.furtherInfo.addInfoRw, rewriteRuleParents))
  }


  /**
    * Orchestrator for the migrated encoding of Leo-III's `RewriteSimp` rule.
    *
    * The produced modular proof script has the following shape:
    *
    * 1. Abstract over the variables of the child clause.
    *
    * 2. Replay the exact equality flips and Boolean literal normalizations
    *    recorded by `Literal.mkOrdered`, backwards on the child goal. This
    *    exposes the clause immediately after term rewriting and before literal
    *    normalization.
    *
    * 3. For each uninterrupted block of one rewrite-rule parent, prepare the
    *    equality proofs that Lambdapi should use for rewriting:
    *
    *    - If the rewrite-rule parent is a non-equational single literal, prove
    *      its forward Boolean equality form, either `P = ⊤` or `P = ⊥`, using
    *      the corresponding simplification theorem.
    *
    *    - If the rewrite-rule parent is an equational single literal, use its
    *      original quantified proof directly, since Leo also rewrites
    *      left-to-right.
    *
    *    - For non-ground rules, also derive the corresponding function
    *      equality. The pointwise proof handles concrete applications and the
    *      lifted proof handles eta-contracted function occurrences.
    *
    * 4. Prove one local implication for each block, from its recorded input
    *    clause to its recorded raw result clause. Apply the block's rule proofs
    *    with `repeat rewrite`, leaving occurrence discovery (including beneath
    *    binders) to Lambdapi, and compose the implications in Leo's order.
    *
    * 5. If literal simplifications from `addInfoSimp` were applied, defer to the
    *    migrated encoding of `Simp`. This is not implemented in this module yet,
    *    so such cases are currently reported as unsupported.
    *
    * 6. Apply the composed local implications to the instantiated parent proof.
    */
  def encRewrite(cl: ClauseProxy,
                 parents: Seq[ClauseProxy],
                 addInfoSimp: Seq[(Seq[Int], Int)],
                 _parentModuloRw: Option[Clause],
                 parentNameLpEnc: Seq[Name],
                 _sig: LpSig): EncodeResult = {
    Out.lp_debug_info("Encoding instance of rewrite simplification")
    assert(parents.length == parentNameLpEnc.length)

    // Extract the main parent and the rewrite-rule parents. The first parent is
    // the clause to be rewritten; all remaining parents justify the rewrite
    // equalities used by the step.
    val parent = parents.head
    val rewriteRules = parents.tail
    val sourceBeforeParent = parentNameLpEnc.head
    val sourcesBeforeEq = parentNameLpEnc.tail

    val rwCtx = initRewriteSimpCtxt(cl, rewriteRules)

    if (cl.furtherInfo.addInfoRw.isEmpty && rewriteRules.exists(rule => rule.cl.implicitlyBound.nonEmpty)) {
      return NotEncodable(MissingRewriteSubstitutionReason)
    }

    val groupedRewriteUses = rwCtx.rewriteUses.foldLeft(Vector.empty[Vector[RewriteRuleUse]]) {
      case (groups, rewriteUse) if groups.lastOption.exists(_.head.rewriteRuleParentId == rewriteUse.rewriteRuleParentId) =>
        groups.updated(groups.length - 1, groups.last :+ rewriteUse)
      case (groups, rewriteUse) =>
        groups :+ Vector(rewriteUse)
    }
    val blockResults = cl.furtherInfo.addInfoRwBlockResults
    if (blockResults.length != groupedRewriteUses.length) {
      return NotEncodable(s"RW: Recorded ${groupedRewriteUses.length} rewrite-rule block(s), but found ${blockResults.length} intermediate result clause(s)")
    }

    val rewriteRuleSourcesByParentId = rewriteRules.zip(sourcesBeforeEq).map {
      case (ruleParent, sourceName) => ruleParent.id -> sourceName
    }.toMap
    val rewriteRuleSourceNames = groupedRewriteUses.map { uses =>
      rewriteRuleSourcesByParentId.get(uses.head.rewriteRuleParentId) match {
        case Some(sourceName) => sourceName
        case None => return NotEncodable(s"RW: Recorded rewrite parent ${uses.head.rewriteRuleParentId} is absent from the proof annotation")
      }
    }

    // Keep the original rewrite rules quantified.  The concrete substitutions
    // recorded in AddInfoRewrite remain available to the instantiation helpers
    // above as a fallback, but exhaustive block proofs do not need them.
    if (groupedRewriteUses.exists(_.head.rewriteRule.typeVars.nonEmpty)) {
      return NotEncodable("RW: Polymorphic quantified rewrite rules are not encoded")
    }
    val enclosingClauses = Seq(cl.cl, parent.cl) ++ blockResults
    val shiftedRewriteRules = shiftRewriteRulesPast(
      groupedRewriteUses.map(_.head.rewriteRule),
      enclosingClauses
    )
    val ctxt = initRewriteRuleCtxt(
      cl.cl,
      parent.cl,
      blockResults,
      shiftedRewriteRules,
      sourceBeforeParent,
      rewriteRuleSourceNames
    )
    val EncRewriteCtx(
      encChild,
      encParent,
      encBlockResults,
      encRewriteRules,
      sharedVarMap,
      _,
      parentNameLpEnc0,
      rewriteRuleNamesLpEnc
    ) = ctxt

    Out.lp_debug_info(s"Encoding application or RW-rule on ${sourceBeforeParent.value}")
    Out.lp_debug_info(s"Found ${rwCtx.rewriteUses.length} recorded rewrite rule use(s) in ${groupedRewriteUses.length} block(s)")

    val initialReasons = mutable.LinkedHashSet.empty[String]
    val childVarNames = extractVarNames(encChild)
    val initialAssumeSteps = encAssumeStep(childVarNames).toVector
    val disappearingParentVars = parent.cl.implicitlyBound.filterNot(cl.cl.implicitlyBound.contains)
    var state = RewriteState(Vector.empty, Vector.empty, Vector.empty, initialReasons, 0, 0)

    // Literal simplifications tracked via AddInfoSimp are not migrated yet.
    state = encodeSimplificationTransformations(addInfoSimp, state)

    val literalTransformations = cl.furtherInfo.addInfoRwLiteralTransformation
    val beforeLiteralNormalisation = reconstructBeforeLiteralNormalisation(encChild.lits, literalTransformations) match {
      case Left(reason) =>
        state = state.markNotEncoded(s"$LiteralReconstructionReason: $reason")
        encChild.lits.toVector
      case Right(lits) => lits
    }
    state = state.copy(
      literalTransformationSteps = verifySubstitutionLiteralNormalisazion(
        literalTransformations,
        encChild.lits.map(_.polarity),
        encChild.lits.length
      ).toVector
    )

    // Prepare one quantified equality proof per uninterrupted rule block.
    // Concrete instantiation support is intentionally retained in this module
    // so it can be restored as a fallback without changing the recorded trace.
    groupedRewriteUses.zip(encRewriteRules).zip(rewriteRuleNamesLpEnc).foreach {
      case ((rewriteUses, encRewriteRule), rewriteRuleName) =>
        val rewriteUse = rewriteUses.head
        val rewriteEq = rewriteUse.rewriteRule.lits.head
        val (nextState, forwardEqualities) = provideQuantifiedRewriteEqualityProof(
          rewriteEq,
          encRewriteRule,
          rewriteRuleName,
          state
        )
        state = nextState.copy(forwardRewriteRules = nextState.forwardRewriteRules :+ forwardEqualities)
    }

    val rewriteConclusion = nAry.disjunction(beforeLiteralNormalisation.map(_.term))
    if (encBlockResults.lastOption.forall(_.term != rewriteConclusion)) {
      return NotEncodable("RW: Last recorded rewrite block does not produce the clause before literal normalization")
    }
    val blockStarts = encParent +: encBlockResults.dropRight(1)
    val rewriteApplications = blockStarts.zip(encBlockResults).zip(state.forwardRewriteRules).zipWithIndex.map {
      case (((beforeBlock, afterBlock), rules), blockIndex) =>
        val rewriteApplicationSteps = rules.map { rule =>
          Repeat(Rewrite(None, proofTermAsTacticArg(rule)))
        } ++ Vector(
          Try(Simplify(onlyBeta = true)),
          Rewrite(None, LpTerm.Const[Level.Meta](SymRef.LP(QName.local("⇒_idem")))),
          Refine(topIntro[Level.Meta])
        )
        Have(
          Name(s"rwApp_$blockIndex"),
          Prf(LogicConst.Imp(beforeBlock.term, afterBlock.term)),
          rewriteApplicationSteps.map(Left(_))
        )
    }
    val instantiatedParent = instantiateProof(
      parentNameLpEnc0,
      parent.cl.implicitlyBound,
      parent.cl.implicitlyBound,
      sharedVarMap
    )
    val rewrittenParentProof = rewriteApplications.indices.foldLeft(instantiatedParent) { case (proof, blockIndex) =>
      LpTerm.App(
        proofName(Name(s"rwApp_$blockIndex")),
        Seq(Arg.Explicit(proof))
      )
    }
    val applyRewrite = Refine(Obj(rewrittenParentProof))
    val completedRewriteBody = state.literalTransformationSteps ++
      state.rewriteRuleSetupSteps ++ rewriteApplications ++ Vector(applyRewrite)

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
      val instantiatedLocalProof = Refine(Obj(instantiateProof(
        proofName(localProofName),
        disappearingParentVars,
        Seq.empty,
        sharedVarMap
      )))
      initialAssumeSteps ++ Vector(localProof, instantiatedLocalProof)
    }

    if (state.allTransformationsEncoded) Encoded(finalSteps)
    else NotEncodable(state.notEncodedReasons.mkString("; "))
  }

  ////////////////////////////////////////////////////////////////
  ////////// Rewrite-rule setup
  ////////////////////////////////////////////////////////////////

  /**
    * Prepare one rewrite-rule parent for the forward implication.
    *
    * Non-equational parents are converted to `P = ⊤` or `P = ⊥`.
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
    if (rewriteUse.residualRuleVars.nonEmpty) {
      Out.lp_debug_info(s"Using the quantified rewrite parent for a rewrite below ${rewriteUse.residualRuleVars.length} binder(s)")
      val (state1, forwardEqualities) = provideQuantifiedRewriteEqualityProof(
        rewriteEq,
        encRewriteRule,
        sourceBeforeEq,
        state0
      )
      return state1.copy(forwardRewriteRules = state1.forwardRewriteRules :+ forwardEqualities)
    }

    val (state1, instantiatedSource) = provideInstantiatedRewriteRuleProof(
      rewriteUse,
      encRewriteRule,
      sourceBeforeEq,
      currentVars,
      sharedVarMap,
      state0
    )

    Out.lp_debug_info(s"Rewriting with ${instantiatedSource}")
    val (state2, forwardEquality) = provideForwardRewriteEqualityProof(
      rewriteEq,
      term2LP(rewriteEq.left, sharedVarMap),
      instantiatedSource,
      state1
    )
    state2.copy(forwardRewriteRules = state2.forwardRewriteRules :+ Vector(forwardEquality))
  }

  /** Keep the original rule quantified and let Lambdapi match its variables. */
  private def provideQuantifiedRewriteEqualityProof(rewriteEq: Literal,
                                                     encRewriteRule: lpClauseInst,
                                                     sourceBeforeEq: LpTerm[Level.Obj],
                                                     state0: RewriteState): (RewriteState, Vector[LpTerm[Level.Obj]]) = {
    val (state1, pointwiseEquality, lhs, rhs, resultType) = if (rewriteEq.equational) {
      if (!rewriteEq.polarity) {
        throw new Exception("Error while attempting to encode rewrite step in LP: Rewrite rule is equational but not positive")
      }
      encRewriteRule.lits.head.term match {
        case LogicConst.Eq(eqType, encLhs, encRhs) => (state0, sourceBeforeEq, encLhs, encRhs, eqType)
        case _ => throw new Exception("Error while attempting to encode a quantified equational rewrite rule")
      }
    } else {
      val encodedLiteral = encRewriteRule.lits.head
      val encodedLhs = if (rewriteEq.polarity) encodedLiteral.term else encodedLiteral.term match {
        case LogicConst.Not(body) => body
        case _ => throw new Exception("Error while attempting to encode a negative propositional rewrite rule")
      }
      val binderNames = extractVarNames(encRewriteRule)
      val appliedSource = applyProofToVars(sourceBeforeEq, binderNames)
      val transformationStepName = Name(s"TransformToEqLits_${state0.transformationsRwCounter}")
      val equalityProof = EqualityProofSteps.provePropLiteralAsForwardBooleanEquality(
        transformationStepName,
        encodedLhs,
        rewriteEq.polarity,
        appliedSource,
        encRewriteRule.metaVars,
        binderNames
      )
      (
        state0.copy(
          rewriteRuleSetupSteps = state0.rewriteRuleSetupSteps :+ equalityProof.step,
          transformationsRwCounter = state0.transformationsRwCounter + 1
        ),
        equalityProof.proofTerm,
        encodedLhs,
        if (rewriteEq.polarity) LogicConst.Top else LogicConst.Bot,
        HolBaseTypes.O
      )
    }

    if (encRewriteRule.vars.isEmpty) {
      (state1, Vector(pointwiseEquality))
    } else {
      val (state2, liftedEquality) = recordLiftedRewriteEquality(
        encRewriteRule,
        lhs,
        rhs,
        resultType,
        pointwiseEquality,
        state1
      )
      (state2, Vector(pointwiseEquality, liftedEquality))
    }
  }

  /**
    * Lift a pointwise rewrite equality to an equality between lambda terms.
    * This is what allows Lambdapi's ordinary rewrite tactic to replace both
    * applications below binders and eta-contracted occurrences of a function.
    */
  private def recordLiftedRewriteEquality(encRewriteRule: lpClauseInst,
                                          lhs: LpTerm[Level.Obj],
                                          rhs: LpTerm[Level.Obj],
                                          resultType: OlMonoType,
                                          pointwiseEquality: LpTerm[Level.Obj],
                                          state0: RewriteState): (RewriteState, LpTerm[Level.Obj]) = {
    val binders = encRewriteRule.vars.map {
      case Left(termVar) => termVar
      case Right(_) => throw new Exception("Error in Lambdapi Encoding: Polymorphic rewrite rules are not encoded")
    }
    if (binders.isEmpty) return (state0, pointwiseEquality)

    val binderNames = binders.map(_.name)
    val appliedPointwiseProof = applyProofToVars(pointwiseEquality, binderNames)
    val funExt = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("funExt")))

    def liftEquality(remaining: Seq[LpTerm.Var[Level.Obj]]): LpTerm[Level.Obj] = remaining match {
      case Seq() => appliedPointwiseProof
      case binder +: tail =>
        val lhsFunction = lpTermBuilder.lam(remaining, lhs)
        val rhsFunction = lpTermBuilder.lam(remaining, rhs)
        val pointwiseProof = LpTerm.Lam[Level.Obj](binder.name -> binder.ty, liftEquality(tail))
        LpTerm.App(
          funExt,
          Seq(
            Arg.ImplicitTypeArg(lpTermBuilder.olTy(binder)),
            Arg.ImplicitTypeArg(lpTermBuilder.funTy(tail, resultType)),
            Arg.Explicit(lhsFunction),
            Arg.Explicit(rhsFunction),
            Arg.Explicit(pointwiseProof)
          )
        )
    }

    val liftedName = Name(s"LiftedRewrite_${state0.transformationsRwCounter}")
    val lambdaLhs = lpTermBuilder.lam(binders, lhs)
    val lambdaRhs = lpTermBuilder.lam(binders, rhs)
    val liftedLhs = lhs match {
      case LpTerm.App(head, args)
        if args == binders.map(binder => Arg.Explicit[Level.Obj](binder)) => head
      case _ => lambdaLhs
    }
    val liftedEquality = LogicConst.Eq(
      lpTermBuilder.funTy(binders, resultType),
      liftedLhs,
      lambdaRhs
    )
    val liftedStep = Have(
      liftedName,
      Prf(liftedEquality),
      Seq(Left(Refine(Obj(liftEquality(binders)))))
    )
    (
      state0.copy(
        rewriteRuleSetupSteps = state0.rewriteRuleSetupSteps :+ liftedStep,
        transformationsRwCounter = state0.transformationsRwCounter + 1
      ),
      proofName(liftedName)
    )
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

  /** Return the equality proof used by the forward rewrite tactic. */
  private def provideForwardRewriteEqualityProof(rewriteEq: Literal,
                                                  rwLhs: LpTerm[Level.Obj],
                                                  sourceBeforeEq: LpTerm[Level.Obj],
                                                  state0: RewriteState): (RewriteState, LpTerm[Level.Obj]) = {
    if (!rewriteEq.equational) {
      recordPropLiteralRewriteEquality(rwLhs, rewriteEq.polarity, sourceBeforeEq, state0)
    } else if (rewriteEq.polarity) {
      (state0, sourceBeforeEq)
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
                                               state0: RewriteState): (RewriteState, LpTerm[Level.Obj]) = {
    val transformationStepName = Name(s"TransformToEqLits_${state0.transformationsRwCounter}")
    val equalityProof = EqualityProofSteps.provePropLiteralAsForwardBooleanEquality(transformationStepName, rwLhs, rwPol, sourceBeforeEq)

    Out.lp_debug_info("Transforming rewrite rule to equality...")
    (
      state0.copy(
        rewriteRuleSetupSteps = state0.rewriteRuleSetupSteps :+ equalityProof.step,
        transformationsRwCounter = state0.transformationsRwCounter + 1
      ),
      equalityProof.proofTerm
    )
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

  /** Instantiate a proof in the variables available at the current proof point. */
  private def instantiateProof(sourceProof: LpTerm[Level.Obj],
                               quantifiedVars: Seq[(Int, Type)],
                               availableVars: Seq[(Int, Type)],
                               sharedVarMap: Map[Int, String]): LpTerm[Level.Obj] = {
    SubstitutionEncoding.instantiateProofTerm(
      quantifiedVars,
      availableVars,
      Seq.empty,
      sharedVarMap,
      sourceProof
    )
  }
}
