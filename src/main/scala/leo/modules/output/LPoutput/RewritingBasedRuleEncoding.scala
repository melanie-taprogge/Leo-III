package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures._
import leo.datastructures.Term.:::>
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
                                   encFinalResult: lpClauseInst,
                                   encRewriteRules: Seq[lpClauseInst],
                                   sharedVarMap: Map[Int, String],
                                   parentNameLpEnc: LpTerm[Level.Obj],
                                   rewriteRuleNamesLpEnc: Seq[LpTerm[Level.Obj]])

    final case class InstantiatedRewriteRuleUse(rewriteRuleParentId: Long,
                                                shiftedRule: Clause,
                                                instantiatedRule: RawClause,
                                                termSubst: Seq[UniTermSubst],
                                                binderDependentVars: Seq[(Int, Type)],
                                                occurrence: RewriteOccurrence,
                                                binderDepth: Int)

    final case class PreparedRewriteRuleUse(rewriteRuleParentId: Long,
                                            shiftedRule: Clause,
                                            instantiatedRule: RawClause,
                                            termSubst: Seq[UniTermSubst],
                                            residualRuleVars: Seq[(Int, Type)],
                                            binderDependentVars: Seq[(Int, Type)],
                                            occurrence: RewriteOccurrence)

    /**
      * Encode the child, main parent, final raw result, and concrete rewrite-rule
      * instances in one pass.
      *
      * The returned context contains both the encoded clauses and the proof
      * names that will later be used to refine with the parent proofs.
      */
    def initRewriteRuleCtxt(childCl: Clause,
                            parentCl: Clause,
                            finalResultCl: RawClause,
                            rewriteRuleCls: Seq[RawClause],
                            parentNameLpEnc0: Name,
                            rewriteRuleNameLpEnc0: Seq[Name]): EncRewriteCtx = {
      require(rewriteRuleCls.length == rewriteRuleNameLpEnc0.length,
        "Each rewrite-rule clause must have a corresponding Lambdapi proof name")

      val allClauses = Seq(childCl, parentCl)
      val rawClauseVars = (Seq(finalResultCl) ++ rewriteRuleCls).flatMap(_.implicitlyBound)
      // Keep the child in its usual form; the parent and instantiated rewrite
      // rules must retain the structure used by the recorded rewrite positions.
      val (sharedVarMap, encClauses) = lpClauseInst.apply_to_set(allClauses, rawClauseVars, suppressReductionAt = Set(1))

      val encChild = encClauses.head
      val encParent = encClauses(1)
      val encFinalResult = RawClauseEncoding.clause2Lp(finalResultCl, sharedVarMap, suppressReduction = true)
      val encRewriteRules = rewriteRuleCls.map { rewriteRule =>
        RawClauseEncoding.clause2Lp(rewriteRule, sharedVarMap, suppressReduction = true)
      }

      EncRewriteCtx(encChild, encParent, encFinalResult, encRewriteRules, sharedVarMap, proofName(parentNameLpEnc0), rewriteRuleNameLpEnc0.map(proofName)
      )
    }

    /**
      * Reconstruct the part of a rewrite-rule instance available outside the
      * recorded occurrence's binders. Leo shifts a non-ground rule past the
      * parent variables and then lifts it again by the binder depth for matching.
      * Substitutions mentioning local binder variables remain quantified so
      * Lambdapi can infer them at the focused rewrite site.
      */
    def instantiateRewriteRuleUse(use: AddInfoRewrite, rewrittenParent: Clause): Either[String, InstantiatedRewriteRuleUse] = {
      use.occurrence match {
        case None => Left("RW: Rewrite occurrence position not recorded")
        case Some(_) if use.rewriteRule.typeVars.nonEmpty || use.origTypeSubst != Subst.id => Left("RW: Polymorphic rewrite-rule instantiation not encoded")
        case Some(occurrence) =>
          val shiftedRule = shiftPast(Seq(use.rewriteRule), Seq(rewrittenParent)).head
          // Leo lifts the matching template once more for every enclosing object binder. We need to likewise lift our indices
          // to match the recorded substitutions
          val binderDepth = occurrence.position.seq.count(_ == -1)
          val termMap = Map.newBuilder[Int, Term] // var to substituted term
          val boundMap = Map.newBuilder[Int, Int] // var to substituted var
          val binderDependent = Vector.newBuilder[(Int, Type)]
          // Test if each of the substitutions recorded by Leo-III depends on variables that are only available under local binders
          shiftedRule.implicitlyBound.foreach { case variable @ (index, _) =>
            use.origTermSubst.substBndIdx(index + binderDepth) match {
              case BoundFront(target) if target <= binderDepth =>
                binderDependent += variable
              case BoundFront(target) if target - binderDepth != index =>
                boundMap += index -> (target - binderDepth)
              case TermFront(term) if term.fv.exists(_._1 <= binderDepth) =>
                // Lambdapi rewrite tactic is currently unable to match terms requiring instantiation with lambda terms
                term.etaContract match {
                  case _ :::> _ =>
                    return Left(s"RW: Binder-dependent substitution for rewrite-rule requires an explicit lambda instance")
                  case _ => ()
                }
                binderDependent += variable
              case TermFront(term) =>
                termMap += index -> term.lift(-binderDepth)
              case TypeFront(_) =>
                return Left(s"RW: Type entry in term substitution for variable $index")
              case _ => ()
            }
          }
          // extract the term substitution to apply
          val outerSubst = Subst.fromMaps(termMap.result(), boundMap.result())
          // apply the substitution to the individual sides of the rewrite clause (to prevent literal normalisation)
          val instantiatedRule = RawClause(shiftedRule.lits.map { lit =>
            val left = lit.left.substitute(outerSubst, use.origTypeSubst)
            if (lit.equational) {
              RawEqLiteral(left, lit.right.substitute(outerSubst, use.origTypeSubst), lit.polarity)
            } else RawNonEqLiteral(left, lit.polarity)
          })
          SubstitutionEncoding.trackTermSubstitution(outerSubst, use.origTypeSubst, shiftedRule.implicitlyBound
          ).map(termSubst => InstantiatedRewriteRuleUse(use.rewriteRuleParentId, shiftedRule, instantiatedRule, termSubst, binderDependent.result(), occurrence, binderDepth))
      }
    }

    /** Align the instantiated rule with the exact recorded redex when eta conversion permits it. */
    def alignRewriteRuleUseToRedex(use: InstantiatedRewriteRuleUse, rewrittenParent: Clause): PreparedRewriteRuleUse = {
      val alignedRule = if (use.binderDepth == 0) {RawClause(use.instantiatedRule.lits.map {
          case RawEqLiteral(left, right, polarity) if left != use.occurrence.redex && left.etaContract == use.occurrence.redex.etaContract =>
            RawEqLiteral(use.occurrence.redex, right, polarity)
          case RawNonEqLiteral(term, polarity) if term != use.occurrence.redex && term.etaContract == use.occurrence.redex.etaContract =>
            RawNonEqLiteral(use.occurrence.redex, polarity)
          case lit => lit
        })
      } else use.instantiatedRule
      // Alignment can change the variables in the rule, so collect residual variables only after choosing its final form.
      val currentVarIndices = rewrittenParent.implicitlyBound.map(_._1).toSet
      val residualRuleVars = alignedRule.implicitlyBound.filterNot { case (index, _) =>
        currentVarIndices.contains(index)
      }
      PreparedRewriteRuleUse(use.rewriteRuleParentId, use.shiftedRule, alignedRule, use.termSubst, residualRuleVars, use.binderDependentVars, use.occurrence
      )
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
    * The recorded literal-normalization steps are the
    * necessary transformation applied to the child to be proved.
    * Rewrite-rule setup are the transformations that are applied
    * to prepare the parents used as rewrite-clauses.
    */
  final case class RewriteState(literalTransformationSteps: Vector[LpProofScript],
                                rewriteRuleSetupSteps: Vector[LpProofScript],
                                forwardRewriteRules: Vector[FocusedRewrite],
                                notEncodedReasons: mutable.LinkedHashSet[String],
                                transformationsRwCounter: Int,
                                rewriteRuleProofCounter: Int) {
    def markNotEncoded(reason: String): RewriteState = {
      notEncodedReasons += reason
      this
    }
    def allTransformationsEncoded: Boolean = notEncodedReasons.isEmpty
  }

  /**
    * Orchestrator for the encoding of Leo-III's `RewriteSimp` rule.
    *
    * The local rewrite implication uses the main parent and the recorded raw
    * result without beta/eta reduction, preserving the term structure to which
    * Leo's rewrite positions refer. Each rule instance is encoded in the same
    * form. The child goal keeps its usual encoding; Lambdapi closes the gap
    * between it and the raw result by conversion after literal normalization.
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
    * 3. For each recorded rewrite-rule application, prepare the equality proof
    *    that Lambdapi should use for rewriting:
    *
    *    - Instantiate variables whose substitutions are available outside the
    *      selected binders. Leave binder-dependent variables quantified for
    *      Lambdapi's rewrite tactic to infer at the selected occurrence.
    *
    *    - When the rule as used by Leo-III in matching (not normalized)
    *      differs from its parent proof, introduce an explicit proof
    *      of the required unreduced rule form, retaining any eta expansions present
    *      in Leo's terms. Reuse the parent proof when the forms coincide.
    *
    *    - If the rewrite-rule parent is a non-equational single literal, prove
    *      its forward Boolean equality form, either `P = ⊤` or `P = ⊥`, using
    *      the corresponding simplification theorem.
    *
    * 4. Prove one local implication from the unreduced parent to the unreduced
    *    final raw result. Replay every recorded occurrence with a focused
    *    rewrite in Leo's order, then close modulo beta/eta conversion.
    *
    * 5. Apply the local implication to the instantiated parent proof. If some
    *    parent variables disappear from the child, first prove the child under
    *    those variables and then instantiate that local proof with witnesses.
    */
  def encRewrite(cl: ClauseProxy, parents: Seq[ClauseProxy], addInfoSimp: Seq[(Seq[Int], Int)], parentNameLpEnc: Seq[Name], _sig: LpSig): EncodeResult = {
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
    val rewriteUses = cl.furtherInfo.addInfoRw
    val finalRawResult = cl.furtherInfo.addInfoRwFinalResult match {
      case Some(result) => result
      case None => return NotEncodable("RW: Final raw result clause not recorded")
    }

    val preparedRewriteUses = rewriteUses.map { use =>
      val instantiated = instantiateRewriteRuleUse(use, parent.cl) match {
        case Left(reason) => return NotEncodable(reason)
        case Right(rule) => rule
      }
      alignRewriteRuleUseToRedex(instantiated, parent.cl)
    }

    // associate the prepared rewrite rules with the names of their proofs in the script‚
    val rewriteRuleSourcesByParentId = rewriteRules.zip(sourcesBeforeEq).map {
      case (ruleParent, sourceName) => ruleParent.id -> sourceName
    }.toMap
    val rewriteRuleSourceNames = preparedRewriteUses.map { use =>
      rewriteRuleSourcesByParentId.get(use.rewriteRuleParentId) match {
        case Some(sourceName) => sourceName
        case None => return NotEncodable(s"RW: Recorded rewrite parent ${use.rewriteRuleParentId} is absent from the proof annotation")
      }
    }

    // Encode every recorded instance of rewriting. The same parent may be used with several different matches.
    val ctxt = initRewriteRuleCtxt(cl.cl, parent.cl, finalRawResult, preparedRewriteUses.map(_.instantiatedRule), sourceBeforeParent, rewriteRuleSourceNames)
    val EncRewriteCtx(encChild, encParent, encFinalResult, encRewriteRules, sharedVarMap, parentNameLpEnc0, rewriteRuleNamesLpEnc) = ctxt

    Out.lp_debug_info(s"Encoding application or RW-rule on ${sourceBeforeParent.value}")
    Out.lp_debug_info(s"Found ${rewriteUses.length} recorded rewrite rule use(s)")

    val initialReasons = mutable.LinkedHashSet.empty[String]
    val childVarNames = extractVarNames(encChild)
    val initialAssumeSteps = encAssumeStep(childVarNames).toVector
    val disappearingParentVars = parent.cl.implicitlyBound.filterNot(cl.cl.implicitlyBound.contains)
    var state = RewriteState(Vector.empty, Vector.empty, Vector.empty, initialReasons, 0, 0)

    val literalTransformations = cl.furtherInfo.addInfoRwLiteralTransformation
    state = state.copy(literalTransformationSteps = verifySubstitutionLiteralNormalisazion(literalTransformations, encChild.lits.map(_.polarity), encChild.lits.length).toVector)

    // Prepare concrete rewrite evidence for each recorded application.
    val encodedRewriteRules = encRewriteRules.iterator
    val rewriteRuleProofs = rewriteRuleNamesLpEnc.iterator
    preparedRewriteUses.foreach { rewriteUse =>
      // Apply any necessary transformations in dedicated substeps
      val encodedApplication = encodeOneRewriteRuleApplication(rewriteUse, encodedRewriteRules.next(), rewriteRuleProofs.next(), parent.cl, parent.cl.implicitlyBound, sharedVarMap, state)
      encodedApplication match {
        case Left(reason) => return NotEncodable(reason)
        case Right((nextState, focusedRewrite)) =>
          state = nextState.copy(forwardRewriteRules = nextState.forwardRewriteRules :+ focusedRewrite)
      }
    }

    // construct the implication proving the rewrite applications
    // Build a List of all necessary steps of the proof:
    val rewriteApplicationSteps = state.forwardRewriteRules.map { rule =>
      // apply each of the targeted rewrites
      Rewrite(Some(rule.pattern), proofTermAsTacticArg(rule.proof))
      // close the proof by beta-reducing and proving the implication via assume and refine
    } ++ Vector(
      Try(Simplify(onlyBeta = true)), Assume(Seq(Name("etaEq"))), Refine(LpTerm.Var[Level.Meta](Name("etaEq"), None))
    )
    // Construct the actual implication proof
    val rewrittenParentProofName = Name("rwApp_0")
    val rewriteApplication = Have(rewrittenParentProofName, Prf(LogicConst.Imp(encParent.term, encFinalResult.term)), rewriteApplicationSteps.map(Left(_)))

    // Instantiate the parent and apply the final refinement step
    val instantiatedParent = instantiateProof(parentNameLpEnc0, parent.cl.implicitlyBound, parent.cl.implicitlyBound, sharedVarMap)
    val rewrittenParentProof = LpTerm.App(proofName(rewrittenParentProofName), Seq(Arg.Explicit(instantiatedParent)))
    val applyRewrite = Refine(Obj(rewrittenParentProof))

    // construct the overall proof
    val completedRewriteBody = state.literalTransformationSteps ++ state.rewriteRuleSetupSteps ++ Vector(rewriteApplication, applyRewrite)

    val finalSteps = if (disappearingParentVars.isEmpty) {
      initialAssumeSteps ++ completedRewriteBody
    } else {
      // Replay the rewrite under the variables that disappear from the child,
      // then instantiate that local proof with witnesses. This keeps each such
      // variable consistent across the rewrite-rule instance and main parent.
      // TODO: The local proof may be avoidable by substituting the same witness
      // for each disappearing variable throughout the rule proofs, rewrite
      // patterns, implication, and parent application. Validate this for
      // occurrences whose recorded redex contains a disappearing variable.
      val localProofName = Name("RewriteWithParentVars")
      val disappearingBinders = disappearingParentVars.map { case (index, ty) =>
        Lifting.OlVarM(var2Lp(index, ty, sharedVarMap))
      }
      val localProofSteps = encAssumeStep(disappearingBinders.map(_.name)) ++ completedRewriteBody
      val localProof = Have(localProofName, Pi(disappearingBinders, Prf(encChild.term)), localProofSteps.map(Left(_)))
      val instantiatedLocalProof = Refine(Obj(instantiateProof(proofName(localProofName), disappearingParentVars, Seq.empty, sharedVarMap)))
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

    val rewriteEq = rewriteEqClause.lits.head
    val residualBinders = rewriteUse.residualRuleVars.map { case (index, ty) =>
      var2Lp(index, ty, sharedVarMap)
    }
    // If necessary, provide a substp that applies existing substitutions and proves the non-normalized shape of the used rewrite-clause
    val (state1, instantiatedSource) = provideInstantiatedRewriteRuleProof(rewriteUse, encRewriteRule, sourceBeforeEq, currentVars, sharedVarMap, state0)

    Out.lp_debug_info(s"Rewriting with ${instantiatedSource}")
    // If necessary, prove transformation from non-equational to equational form and construct the precise shape of the used rule
    val (state2, pointwiseEquality, lhs, rhs) = provideForwardRewriteEqualityProof(rewriteEq, encRewriteRule, instantiatedSource, residualBinders, state1)
    val pointwise = RewriteEquality(pointwiseEquality, lhs, rhs)

    // construct the pattern of the application of the rewrite-clause
    // Check if the rewrite Equality has the expected shape
    // If this holds, construct a pattern only contianing the variable to be matched as the target
    val targetPattern = if (rewriteUse.binderDependentVars.nonEmpty) {
      // binderDependentVars cannot be instantiated outside the enclosing lambda. Keep them quantified and let Lambdapi match them at the focused site.
      if (rewriteEq.terms.head.ty != rewriteUse.occurrence.redex.ty) {
        Left("RW: Quantified rewrite site has a different type from the rule")
      } else {
        val hole = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("x")))
        Right(RewritePattern(hole, hole))
      }
    } else {
      selectPointwiseRewritePattern(rewriteUse.occurrence, pointwise, sharedVarMap)
    }

    // prepare the pattern context at applied position
    val patternContext = PatternBuilder.prepareClausePositionPattern(rewrittenParent, rewriteUse.occurrence) match {
      case Left(reason) => return Left(reason)
      case Right(context) => context
    }
    // insert target pattern and embed in clause pattern
    targetPattern.map { pattern =>
      val clausePattern = patternContext.plug(pattern)
      val implicationPattern = PatternBuilder.embedPatternInBinaryConnective(clausePattern, Side.Left, LogicConst.Imp.apply)
      (state2, FocusedRewrite(implicationPattern, pointwise.proof))
    }
  }

  private final case class RewriteEquality(proof: LpTerm[Level.Obj],
                                           lhs: LpTerm[Level.Obj],
                                           rhs: LpTerm[Level.Obj])

  /** Ensure that the pointwise equality matches the exact recorded rewrite occurrence. */
  private def selectPointwiseRewritePattern(occurrence: RewriteOccurrence,
                                            pointwise: RewriteEquality,
                                            sharedVarMap: Map[Int, String]): Either[String, RewritePattern] = {
    val encodedRedex = term2LP(occurrence.redex, sharedVarMap, suppressReduction = true)
    val encodedContractum = term2LP(occurrence.contractum, sharedVarMap, suppressReduction = true)
    val patternHole = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("x")))

    if (pointwise.lhs == encodedRedex && pointwise.rhs == encodedContractum) {
      Right(RewritePattern(patternHole, patternHole))
    } else {
      Left("RW: Pointwise equality does not match the recorded rewrite occurrence")
    }
  }

  /** If necessary, prove the concrete form needed for rewriting by applying any existing substitutions and
    * making the non-normalized shape of the used rewrite-clause explicit.
    * Returns one shared substep.
    * */
  private def provideInstantiatedRewriteRuleProof(rewriteUse: PreparedRewriteRuleUse,
                                                  encRewriteRule: lpClauseInst,
                                                  sourceBeforeEq: LpTerm[Level.Obj],
                                                  currentVars: Seq[(Int, Type)],
                                                  sharedVarMap: Map[Int, String],
                                                  state0: RewriteState): (RewriteState, LpTerm[Level.Obj]) = {
    // If no substitution was applied and the normally printed source rule already -> use its proof directly.
    val unchangedRule = rewriteUse.termSubst.isEmpty && // no substitution needs to be applied
      rewriteUse.shiftedRule.implicitlyBound.forall { case (index, _) => sharedVarMap.contains(index) } && // Condition under which we may encode the step with the sharedVarMap
      RawClauseEncoding.clause2Lp(RawClause(rewriteUse.shiftedRule), sharedVarMap).asMl == encRewriteRule.asMl // The encoded rules are the same (this is not the case if we need eta expansion)
    if (unchangedRule) return (state0, sourceBeforeEq)

    // Otherwise, prove the required form
    val stepPrefix = if (rewriteUse.termSubst.nonEmpty) "RewriteInstantiation" else "RewriteRuleForm"
    val stepName = Name(s"${stepPrefix}_${state0.rewriteRuleProofCounter}")
    val availableVars = (currentVars ++ rewriteUse.residualRuleVars).distinct
    // Apply substitution if it exists
    val instantiatedSource = SubstitutionEncoding.instantiateProofTerm(rewriteUse.shiftedRule.implicitlyBound, availableVars, rewriteUse.termSubst, sharedVarMap, sourceBeforeEq)
    val residualBinders = rewriteUse.residualRuleVars.map { case (index, ty) =>
      var2Lp(index, ty, sharedVarMap)
    }
    val residualMetaBinders = residualBinders.map(Lifting.OlVarM(_))
    // construct substep for proving the needed form of the child.
    // Note that encRewriteRule is the exact rule used by Leo prior to normalising, this step therefore also proves eta equivalence to the original proof step.
    val haveInstance = LpProofScript.Have(stepName,
      if (residualMetaBinders.isEmpty) Prf(encRewriteRule.term)
      else Pi(residualMetaBinders, Prf(encRewriteRule.term)),
      encAssumeStep(residualBinders.map(_.name)).map(Left(_)) ++ Seq(Left(Refine(Obj(instantiatedSource)))))

    (state0.copy(rewriteRuleSetupSteps = state0.rewriteRuleSetupSteps :+ haveInstance, rewriteRuleProofCounter = state0.rewriteRuleProofCounter + 1), proofName(stepName))
  }

  /** If the rewrite-clause is not already equational, transform to equational shape.
    * Returns the final shape of the used rule, and adds the transformation substep to the current state if necessary.
    * */
  private def provideForwardRewriteEqualityProof(rewriteEq: RawLiteral,
                                                  encRewriteRule: lpClauseInst,
                                                  sourceBeforeEq: LpTerm[Level.Obj],
                                                  residualBinders: Seq[LpTerm.Var[Level.Obj]],
                                                  state0: RewriteState): (RewriteState, LpTerm[Level.Obj], LpTerm[Level.Obj], LpTerm[Level.Obj]) = {
    rewriteEq match {
      case RawNonEqLiteral(_, polarity) =>
        // If the used rewrite-clause is not equational but a negative non-equational literal, extract the body
        val encodedLiteral = encRewriteRule.lits.head
        val rwLhs = if (polarity) encodedLiteral.term else encodedLiteral.term match {
          case LogicConst.Not(body) => body
          case _ => throw new Exception("Error while attempting to encode a negative propositional rewrite rule")
        }
        // construct the equality used by the actual rewrite tactic
        val (state1, pointwiseEquality) = recordPropLiteralRewriteEquality(rwLhs, polarity, sourceBeforeEq, residualBinders, state0)
        (state1, pointwiseEquality, rwLhs,
          if (polarity) LogicConst.Top else LogicConst.Bot
        )
      case RawEqLiteral(_, _, true) =>
        // Clause is already a unit clause with an equational literal, no transformation needed
        encRewriteRule.lits.head.term match {
          case LogicConst.Eq(_, lhs, rhs) => (state0, sourceBeforeEq, lhs, rhs)
          case _ => throw new Exception("Error while attempting to encode an instantiated equational rewrite rule")
        }
      case RawEqLiteral(_, _, false) =>
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
    val equalityProof = EqualityProofSteps.provePropLiteralAsForwardBooleanEquality(transformationStepName, rwLhs, rwPol, appliedSource, residualBinders.map(Lifting.OlVarM(_)), binderNames)

    Out.lp_debug_info("Transforming rewrite rule to equality...")
    (state0.copy(
        rewriteRuleSetupSteps = state0.rewriteRuleSetupSteps :+ equalityProof.step,
        transformationsRwCounter = state0.transformationsRwCounter + 1
      ),
      equalityProof.proofTerm
    )
  }

  ////////////////////////////////////////////////////////////////
  ////////// Final refinement
  ////////////////////////////////////////////////////////////////

  /** Instantiate a proof in the variables available at the current proof point. */
  private def instantiateProof(sourceProof: LpTerm[Level.Obj],
                               quantifiedVars: Seq[(Int, Type)],
                               availableVars: Seq[(Int, Type)],
                               sharedVarMap: Map[Int, String]): LpTerm[Level.Obj] = {
    SubstitutionEncoding.instantiateProofTerm(quantifiedVars, availableVars, Seq.empty, sharedVarMap, sourceProof
    )
  }
}
