package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures._
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.ImplicitTransformationUtil.verifySubstitutionLiteralNormalisazion
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Assume, Have, Refine, Rewrite, RewritePattern, Side, Simplify, Try}
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
                                   parentNameLpEnc: LpTerm[Level.Obj],
                                   rewriteRuleNamesLpEnc: Seq[LpTerm[Level.Obj]])

    final case class RewriteRuleUse(rewriteRuleParentId: Long,
                                    rewriteRule: Clause,
                                    origTermSubst: Subst,
                                    origTypeSubst: Subst,
                                    occurrence: Option[RewriteOccurrence])

    final case class PreparedRewriteRuleUse(rewriteRuleParentId: Long,
                                            shiftedRule: Clause,
                                            instantiatedRule: Clause,
                                            termSubst: Seq[UniTermSubst],
                                            residualRuleVars: Seq[(Int, Type)],
                                            binderDependentVars: Seq[(Int, Type)],
                                            occurrence: RewriteOccurrence)

    /**
      * Encode the child, main parent, block results, and concrete rewrite-rule
      * instances in one pass.
      *
      * The returned context contains both the encoded clauses and the proof
      * names that will later be used to refine with the parent proofs.
      */
    def initRewriteRuleCtxt(childCl: Clause,
                            parentCl: Clause,
                            blockResultCls: Seq[RawClause],
                            rewriteRuleCls: Seq[Clause],
                            parentNameLpEnc0: Name,
                            rewriteRuleNameLpEnc0: Seq[Name]): EncRewriteCtx = {
      require(rewriteRuleCls.length == rewriteRuleNameLpEnc0.length,
        "Each rewrite-rule clause must have a corresponding Lambdapi proof name")

      val allClauses = Seq(childCl, parentCl) ++ rewriteRuleCls
      val rawClauseVars = blockResultCls.flatMap(_.implicitlyBound)
      // Keep the child in its usual form; the parent and instantiated rewrite
      // rules must retain the structure used by the recorded rewrite positions.
      val (sharedVarMap, encClauses) = lpClauseInst.apply_to_set(
        allClauses, rawClauseVars, suppressReductionAt = (1 until allClauses.length).toSet
      )

      val encChild = encClauses.head
      val encParent = encClauses(1)
      val encBlockResults = blockResultCls.map { blockResult =>
        RawClauseEncoding.clause2Lp(blockResult, sharedVarMap, suppressReduction = true)
      }
      val encRewriteRules = encClauses.drop(2)

      EncRewriteCtx(
        encChild,
        encParent,
        encBlockResults,
        encRewriteRules,
        sharedVarMap,
        proofName(parentNameLpEnc0),
        rewriteRuleNameLpEnc0.map(proofName)
      )
    }

    /**
      * Normalize rewrite-use information from `FurtherInfo`.
      */
    def initRewriteRuleUses(addInfoRw: Seq[AddInfoRewrite]): Seq[RewriteRuleUse] =
      addInfoRw.map(info => RewriteRuleUse(info.rewriteRuleParentId, info.rewriteRule, info.origTermSubst, info.origTypeSubst, info.occurrence))

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
      * Reconstruct the part of a rewrite-rule instance available outside the
      * recorded occurrence's binders. Leo shifts a non-ground rule past the
      * parent variables and then lifts it again by the binder depth for matching.
      * Substitutions mentioning local binder variables remain quantified so
      * Lambdapi can infer them at the focused rewrite site.
      */
    def prepareRewriteRuleUse(use: RewriteRuleUse, rewrittenParent: Clause): Either[String, PreparedRewriteRuleUse] = {
      use.occurrence match {
        case None => Left("RW: Rewrite occurrence position not recorded")
        case Some(_) if use.rewriteRule.typeVars.nonEmpty || use.origTypeSubst != Subst.id =>
          Left("RW: Polymorphic rewrite-rule instantiation not encoded")
        case Some(occurrence) =>
          val shiftedRule = shiftRewriteRulesPast(Seq(use.rewriteRule), Seq(rewrittenParent)).head
          // Leo lifts the matching template once more for every enclosing
          // object binder. Its recorded substitution therefore has indices in
          // that local space, whereas the rule proof is quantified outside it.
          val binderDepth = occurrence.position.seq.count(_ == -1)
          val termMap = Map.newBuilder[Int, Term]
          val boundMap = Map.newBuilder[Int, Int]
          val binderDependent = Vector.newBuilder[(Int, Type)]
          shiftedRule.implicitlyBound.foreach { case variable @ (index, _) =>
            use.origTermSubst.substBndIdx(index + binderDepth) match {
              case BoundFront(target) if target <= binderDepth =>
                binderDependent += variable
              case BoundFront(target) if target - binderDepth != index =>
                boundMap += index -> (target - binderDepth)
              case TermFront(term) if term.fv.exists(_._1 <= binderDepth) =>
                binderDependent += variable
              case TermFront(term) =>
                termMap += index -> term.lift(-binderDepth)
              case TypeFront(_) =>
                return Left(s"RW: Type entry in term substitution for variable $index")
              case _ => ()
            }
          }
          val outerSubst = Subst.fromMaps(termMap.result(), boundMap.result())
          val instantiatedRule = shiftedRule.substitute(outerSubst, use.origTypeSubst)
          val currentVarIndices = rewrittenParent.implicitlyBound.map(_._1).toSet
          val residualRuleVars = instantiatedRule.implicitlyBound.filterNot { case (index, _) =>
            currentVarIndices.contains(index)
          }

          SubstitutionEncoding.trackTermSubstitution(
            outerSubst,
            use.origTypeSubst,
            shiftedRule.implicitlyBound
          ).map(termSubst => PreparedRewriteRuleUse(
            use.rewriteRuleParentId,
            shiftedRule,
            instantiatedRule,
            termSubst,
            residualRuleVars,
            binderDependent.result(),
            occurrence
          ))
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
  private val MissingRewriteMetadataReason = "RW: Rewrite application metadata not recorded"
  private val LiteralTransformationReason = "RW: Literal simplification or transformation not encoded"

  final case class FocusedRewrite(pattern: RewritePattern,
                                  proof: LpTerm[Level.Obj])

  /**
    * Mutable proof-construction state for one RewriteSimp step.
    *
    * Literal-normalization steps and rewrite-rule setup haves are kept
    * separately because normalization changes the outer goal, while the rule
    * haves are used inside the forward rewrite implication.
    */
  final case class RewriteState(literalTransformationSteps: Vector[LpProofScript],
                                rewriteRuleSetupSteps: Vector[LpProofScript],
                                forwardRewriteRules: Vector[Vector[FocusedRewrite]],
                                notEncodedReasons: mutable.LinkedHashSet[String],
                                transformationsRwCounter: Int,
                                rewriteInstantiationCounter: Int) {
    def markNotEncoded(reason: String): RewriteState = {
      notEncodedReasons += reason
      this
    }
    def allTransformationsEncoded: Boolean = notEncodedReasons.isEmpty
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
    *    - Instantiate variables whose substitutions are available outside the
    *      selected binders. Leave binder-dependent variables quantified for
    *      Lambdapi's rewrite tactic to infer at the selected occurrence.
    *
    *    - If variables remain after instantiation and the recorded occurrence
    *      requires it, derive the corresponding function equality. The
    *      occurrence determines whether the pointwise or lifted proof is used.
    *
    * 4. Prove one local implication from the parent to the final recorded raw
    *    result clause. Replay every recorded occurrence with a focused rewrite
    *    in Leo's order, across all recorded blocks.
    *
    * 5. If literal simplifications from `addInfoSimp` were applied, defer to the
    *    migrated encoding of `Simp`. This is not implemented in this module yet,
    *    so such cases are currently reported as unsupported.
    *
    * 6. Apply the local implication to the instantiated parent proof.
    */
  def encRewrite(cl: ClauseProxy,
                 parents: Seq[ClauseProxy],
                 addInfoSimp: Seq[(Seq[Int], Int)],
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

    if (cl.furtherInfo.addInfoRw.isEmpty) {
      return NotEncodable(MissingRewriteMetadataReason)
    }
    val rewriteUses = initRewriteRuleUses(cl.furtherInfo.addInfoRw)
    val groupedRewriteUses = rewriteUses.foldLeft(Vector.empty[Vector[RewriteRuleUse]]) {
      case (groups, rewriteUse) if groups.lastOption.exists(_.head.rewriteRuleParentId == rewriteUse.rewriteRuleParentId) =>
        groups.updated(groups.length - 1, groups.last :+ rewriteUse)
      case (groups, rewriteUse) =>
        groups :+ Vector(rewriteUse)
    }
    val blockResults = cl.furtherInfo.addInfoRwBlockResults
    if (blockResults.length != groupedRewriteUses.length) {
      return NotEncodable(s"RW: Recorded ${groupedRewriteUses.length} rewrite-rule block(s), but found ${blockResults.length} intermediate result clause(s)")
    }

    val groupedPreparedRewriteUses = groupedRewriteUses.map { rewriteUses =>
      rewriteUses.map { use =>
        prepareRewriteRuleUse(use, parent.cl) match {
          case Left(reason) => return NotEncodable(reason)
          case Right(prepared) => prepared
        }
      }
    }
    val preparedRewriteUses = groupedPreparedRewriteUses.flatten

    val rewriteRuleSourcesByParentId = rewriteRules.zip(sourcesBeforeEq).map {
      case (ruleParent, sourceName) => ruleParent.id -> sourceName
    }.toMap
    val rewriteRuleSourceNames = preparedRewriteUses.map { use =>
      rewriteRuleSourcesByParentId.get(use.rewriteRuleParentId) match {
        case Some(sourceName) => sourceName
        case None => return NotEncodable(s"RW: Recorded rewrite parent ${use.rewriteRuleParentId} is absent from the proof annotation")
      }
    }

    // Encode every recorded instance, rather than one bare quantified rule per
    // block. A block may use the same parent with several different matches.
    val ctxt = initRewriteRuleCtxt(
      cl.cl,
      parent.cl,
      blockResults,
      preparedRewriteUses.map(_.instantiatedRule),
      sourceBeforeParent,
      rewriteRuleSourceNames
    )
    val EncRewriteCtx(
      encChild,
      encParent,
      encBlockResults,
      encRewriteRules,
      sharedVarMap,
      parentNameLpEnc0,
      rewriteRuleNamesLpEnc
    ) = ctxt

    Out.lp_debug_info(s"Encoding application or RW-rule on ${sourceBeforeParent.value}")
    Out.lp_debug_info(s"Found ${rewriteUses.length} recorded rewrite rule use(s) in ${groupedRewriteUses.length} block(s)")

    val initialReasons = mutable.LinkedHashSet.empty[String]
    val childVarNames = extractVarNames(encChild)
    val initialAssumeSteps = encAssumeStep(childVarNames).toVector
    val disappearingParentVars = parent.cl.implicitlyBound.filterNot(cl.cl.implicitlyBound.contains)
    var state = RewriteState(Vector.empty, Vector.empty, Vector.empty, initialReasons, 0, 0)

    // Literal simplifications tracked via AddInfoSimp are not migrated yet.
    state = encodeSimplificationTransformations(addInfoSimp, state)

    val literalTransformations = cl.furtherInfo.addInfoRwLiteralTransformation
    state = state.copy(
      literalTransformationSteps = verifySubstitutionLiteralNormalisazion(
        literalTransformations,
        encChild.lits.map(_.polarity),
        encChild.lits.length
      ).toVector
    )

    // Preserve Leo's uninterrupted rule blocks, but prepare concrete rewrite
    // evidence for each recorded application inside the block.
    val encodedRewriteRules = encRewriteRules.iterator
    val rewriteRuleProofs = rewriteRuleNamesLpEnc.iterator
    groupedPreparedRewriteUses.foreach { rewriteUses =>
      var blockFocusedRewrites = Vector.empty[FocusedRewrite]
      rewriteUses.foreach { rewriteUse =>
        val encodedApplication = encodeOneRewriteRuleApplication(
          rewriteUse,
          encodedRewriteRules.next(),
          rewriteRuleProofs.next(),
          parent.cl,
          parent.cl.implicitlyBound,
          sharedVarMap,
          state
        )
        encodedApplication match {
          case Left(reason) => return NotEncodable(reason)
          case Right((nextState, focusedRewrite)) =>
            state = nextState
            blockFocusedRewrites = blockFocusedRewrites :+ focusedRewrite
        }
      }
      state = state.copy(forwardRewriteRules = state.forwardRewriteRules :+ blockFocusedRewrites)
    }

    // TODO: Compare the final uncontracted block result with the reconstructed
    // child before literal normalization modulo beta/eta conversion.
    // For this experiment, retain the recorded blocks but emit one implication
    // with all rewrite applications in their original order.
    val rewriteApplicationSteps = state.forwardRewriteRules.flatten.map { rule =>
      Rewrite(Some(rule.pattern), proofTermAsTacticArg(rule.proof))
    } ++ Vector(
      Try(Simplify(onlyBeta = true)),
      Assume(Seq(Name("etaEq"))),
      Refine(LpTerm.Var[Level.Meta](Name("etaEq"), None))
    )
    val rewriteApplication = Have(
      Name("rwApp_0"),
      Prf(LogicConst.Imp(encParent.term, encBlockResults.last.term)),
      rewriteApplicationSteps.map(Left(_))
    )
    val instantiatedParent = instantiateProof(
      parentNameLpEnc0,
      parent.cl.implicitlyBound,
      parent.cl.implicitlyBound,
      sharedVarMap
    )
    val rewrittenParentProof = LpTerm.App(
      proofName(Name("rwApp_0")),
      Seq(Arg.Explicit(instantiatedParent))
    )
    val applyRewrite = Refine(Obj(rewrittenParentProof))
    val completedRewriteBody = state.literalTransformationSteps ++
      state.rewriteRuleSetupSteps ++ Vector(rewriteApplication, applyRewrite)

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
                                              rewrittenParent: Clause,
                                              currentVars: Seq[(Int, Type)],
                                              sharedVarMap: Map[Int, String],
                                              state0: RewriteState): Either[String, (RewriteState, FocusedRewrite)] = {
    val rewriteEqClause = rewriteUse.instantiatedRule
    assert(rewriteEqClause.lits.length == 1, s"trying to encode RW rule application with RW clause of length ${rewriteEqClause.lits.length}")

    val patternContext = PatternBuilder.prepareClausePositionPattern(rewrittenParent, rewriteUse.occurrence) match {
      case Left(reason) => return Left(reason)
      case Right(context) => context
    }
    val rewriteEq = rewriteEqClause.lits.head
    val residualBinders = rewriteUse.residualRuleVars.map { case (index, ty) =>
      var2Lp(index, ty, sharedVarMap)
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
    val (state2, pointwiseEquality, lhs, rhs, resultType) = provideForwardRewriteEqualityProof(
      rewriteEq,
      encRewriteRule,
      instantiatedSource,
      residualBinders,
      state1
    )

    val pointwise = RewriteEquality(pointwiseEquality, lhs, rhs)
    val liftedShape = if (residualBinders.isEmpty) None else Some(
      makeLiftedRewriteShape(residualBinders, lhs, rhs, resultType)
    )

    val selectedForm = if (rewriteUse.binderDependentVars.nonEmpty) {
      // Those variables cannot be instantiated outside the enclosing lambda.
      // Keep them quantified and let Lambdapi match them at the focused site.
      if (rewriteEq.left.ty != rewriteUse.occurrence.redex.ty) {
        Left("RW: Quantified rewrite site has a different type from the rule")
      } else {
        val hole = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("x")))
        Right(SelectedRewriteForm(useLifted = false, targetPattern = RewritePattern(hole, hole)))
      }
    } else {
      selectRewriteForm(rewriteUse.occurrence, pointwise, liftedShape, sharedVarMap)
    }

    selectedForm.flatMap {
      case SelectedRewriteForm(useLifted, targetPattern) =>
        val (state3, selectedProof) = if (useLifted) {
          val (nextState, liftedProof) = recordLiftedRewriteEquality(
            residualBinders,
            lhs,
            rhs,
            pointwiseEquality,
            liftedShape.get,
            state2
          )
          (nextState, liftedProof)
        } else (state2, pointwise.proof)

        val clausePattern = patternContext.plug(targetPattern)
        val implicationPattern = PatternBuilder.embedPatternInBinaryConnective(
          clausePattern,
          Side.Left,
          LogicConst.Imp.apply
        )
        Right((state3, FocusedRewrite(implicationPattern, selectedProof)))
    }
  }

  private final case class RewriteEquality(proof: LpTerm[Level.Obj],
                                           lhs: LpTerm[Level.Obj],
                                           rhs: LpTerm[Level.Obj])

  private final case class LiftedRewriteShape(lhs: LpTerm[Level.Obj],
                                              rhs: LpTerm[Level.Obj],
                                              equalityType: OlMonoType,
                                              pointwiseResultType: OlMonoType)

  private final case class SelectedRewriteForm(useLifted: Boolean,
                                               targetPattern: RewritePattern)

  /** Decide which equality proves the recorded rewrite and where it must focus. */
  private def selectRewriteForm(occurrence: RewriteOccurrence,
                                pointwise: RewriteEquality,
                                lifted: Option[LiftedRewriteShape],
                                sharedVarMap: Map[Int, String]): Either[String, SelectedRewriteForm] = {
    val encodedRedex = term2LP(occurrence.redex, sharedVarMap, suppressReduction = true)
    val encodedContractum = term2LP(occurrence.contractum, sharedVarMap, suppressReduction = true)
    val patternHole = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("x")))
    val rootPattern = RewritePattern(patternHole, patternHole)

    if (pointwise.lhs == encodedRedex && pointwise.rhs == encodedContractum) {
      Right(SelectedRewriteForm(useLifted = false, rootPattern))
    } else lifted match {
      case Some(liftedShape)
        if liftedShape.lhs == encodedRedex && liftedShape.rhs == encodedContractum =>
        Right(SelectedRewriteForm(useLifted = true, rootPattern))
      case Some(liftedShape) =>
        encodedRedex match {
          case LpTerm.App(head, args)
            if head == liftedShape.lhs && lpTermBuilder.betaApply(liftedShape.rhs, args) == encodedContractum =>
            PatternBuilder.leoPosition2LpPattern(
              occurrence.redex,
              Position.root.headPos,
              patternHole
            ).map { applicationPattern =>
              SelectedRewriteForm(
                useLifted = true,
                RewritePattern(applicationPattern.pattern, patternHole)
              )
            }
          case _ =>
            Left("RW: Neither the pointwise nor lifted equality matches the recorded rewrite occurrence")
        }
      case None =>
        Left("RW: Pointwise equality does not match the recorded rewrite occurrence")
    }
  }

  /** Construct the equality terms produced by lifting a pointwise equality. */
  private def makeLiftedRewriteShape(binders: Seq[LpTerm.Var[Level.Obj]],
                                     lhs: LpTerm[Level.Obj],
                                     rhs: LpTerm[Level.Obj],
                                     resultType: OlMonoType): LiftedRewriteShape = {
    val lambdaLhs = lpTermBuilder.lam(binders, lhs)
    val lambdaRhs = lpTermBuilder.lam(binders, rhs)
    val liftedLhs = lhs match {
      case LpTerm.App(head, args)
        if args == binders.map(binder => Arg.Explicit[Level.Obj](binder)) => head
      case _ => lambdaLhs
    }
    LiftedRewriteShape(
      liftedLhs,
      lambdaRhs,
      lpTermBuilder.funTy(binders, resultType),
      resultType
    )
  }

  /**
    * Lift a pointwise rewrite equality to an equality between lambda terms.
    * This is what allows Lambdapi's ordinary rewrite tactic to replace both
    * applications below binders and eta-contracted occurrences of a function.
    */
  private def recordLiftedRewriteEquality(binders: Seq[LpTerm.Var[Level.Obj]],
                                          lhs: LpTerm[Level.Obj],
                                          rhs: LpTerm[Level.Obj],
                                          pointwiseEquality: LpTerm[Level.Obj],
                                          liftedShape: LiftedRewriteShape,
                                          state0: RewriteState): (RewriteState, LpTerm[Level.Obj]) = {
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
            Arg.ImplicitTypeArg(lpTermBuilder.funTy(tail, liftedShape.pointwiseResultType)),
            Arg.Explicit(lhsFunction),
            Arg.Explicit(rhsFunction),
            Arg.Explicit(pointwiseProof)
          )
        )
    }

    val liftedName = Name(s"LiftedRewrite_${state0.transformationsRwCounter}")
    val liftedEquality = LogicConst.Eq(
      liftedShape.equalityType,
      liftedShape.lhs,
      liftedShape.rhs
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

  /** Give every recorded rewrite use a proof with the unreduced rule encoding. */
  private def provideInstantiatedRewriteRuleProof(rewriteUse: PreparedRewriteRuleUse,
                                                  encRewriteRule: lpClauseInst,
                                                  sourceBeforeEq: LpTerm[Level.Obj],
                                                  currentVars: Seq[(Int, Type)],
                                                  sharedVarMap: Map[Int, String],
                                                  state0: RewriteState): (RewriteState, LpTerm[Level.Obj]) = {
    val stepName = Name(s"RewriteInstantiation_${state0.rewriteInstantiationCounter}")
    val availableVars = (currentVars ++ rewriteUse.residualRuleVars).distinct
    val instantiatedSource = SubstitutionEncoding.instantiateProofTerm(
      rewriteUse.shiftedRule.implicitlyBound,
      availableVars,
      rewriteUse.termSubst,
      sharedVarMap,
      sourceBeforeEq
    )
    val residualBinders = rewriteUse.residualRuleVars.map { case (index, ty) =>
      var2Lp(index, ty, sharedVarMap)
    }
    val residualMetaBinders = residualBinders.map(Lifting.OlVarM(_))
    val haveInstance = LpProofScript.Have(
      stepName,
      if (residualMetaBinders.isEmpty) Prf(encRewriteRule.term)
      else Pi(residualMetaBinders, Prf(encRewriteRule.term)),
      encAssumeStep(residualBinders.map(_.name)).map(Left(_)) ++
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

  /** Return the equality proof used by the forward rewrite tactic. */
  private def provideForwardRewriteEqualityProof(rewriteEq: Literal,
                                                  encRewriteRule: lpClauseInst,
                                                  sourceBeforeEq: LpTerm[Level.Obj],
                                                  residualBinders: Seq[LpTerm.Var[Level.Obj]],
                                                  state0: RewriteState): (RewriteState, LpTerm[Level.Obj], LpTerm[Level.Obj], LpTerm[Level.Obj], OlMonoType) = {
    if (!rewriteEq.equational) {
      val encodedLiteral = encRewriteRule.lits.head
      val rwLhs = if (rewriteEq.polarity) encodedLiteral.term else encodedLiteral.term match {
        case LogicConst.Not(body) => body
        case _ => throw new Exception("Error while attempting to encode a negative propositional rewrite rule")
      }
      val (state1, pointwiseEquality) = recordPropLiteralRewriteEquality(
        rwLhs,
        rewriteEq.polarity,
        sourceBeforeEq,
        residualBinders,
        state0
      )
      (
        state1,
        pointwiseEquality,
        rwLhs,
        if (rewriteEq.polarity) LogicConst.Top else LogicConst.Bot,
        HolBaseTypes.O
      )
    } else if (rewriteEq.polarity) {
      encRewriteRule.lits.head.term match {
        case LogicConst.Eq(eqType, lhs, rhs) => (state0, sourceBeforeEq, lhs, rhs, eqType)
        case _ => throw new Exception("Error while attempting to encode an instantiated equational rewrite rule")
      }
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
                                               residualBinders: Seq[LpTerm.Var[Level.Obj]],
                                               state0: RewriteState): (RewriteState, LpTerm[Level.Obj]) = {
    val transformationStepName = Name(s"TransformToEqLits_${state0.transformationsRwCounter}")
    val binderNames = residualBinders.map(_.name)
    val appliedSource = applyProofToVars(sourceBeforeEq, binderNames)
    val equalityProof = EqualityProofSteps.provePropLiteralAsForwardBooleanEquality(
      transformationStepName,
      rwLhs,
      rwPol,
      appliedSource,
      residualBinders.map(Lifting.OlVarM(_)),
      binderNames
    )

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
