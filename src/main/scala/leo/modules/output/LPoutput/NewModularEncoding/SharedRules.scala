package leo.modules.output.LPoutput.NewModularEncoding

import leo.Out
import leo.modules.output.LPoutput.LpLibs.EqRules.AsTerms.eqImp
import leo.modules.output.LPoutput.LpLibs.EqRules.AsTerms.{lpSimp_eqBot, lpSimp_eqTop}
import leo.modules.output.LPoutput.LpLibs.LeoTactics.EvalApp.removeBot
import leo.modules.output.LPoutput.LpLibs.MetaTheorems.Inst.deleteBots
import leo.modules.output.LPoutput.LpLibs.ND.Terms.eqSym
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Assume, Eval, Have, Refine, Rewrite, Side, Simplify, Try}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Obj}
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{Pi, Prf}
import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig.depTyConStr


object AssumeStep {
  def extractVarNames(encChild: lpClauseInst): Seq[Name] = {
    encChild.vars.map {
      case Left(olVar) => olVar.name
      case Right(_) => throw new Exception(s"Error in Lambdapi Encoding: Encountered unexpected TyVar, Poymorphism not yet encoded")
    }
  }

  def encAssumeStep(varNames: Seq[Name]): (Seq[LpProofScript]) = {
    if (varNames.nonEmpty) {
      (Seq(Assume(varNames)))
    } else (Seq.empty)
  }
}

object ProofTermUtil {
  /** Reference a proof-local Lambdapi name as an object-level proof term. */
  def proofName(name: Name): LpTerm[Level.Obj] =
    Const(SymRef.LP(QName.local(name.value)))

  /**
    * Use an object-level proof term as an argument to a proof-script tactic.
    *
    * Plain constants can be represented directly at the meta level, which
    * prints clean tactic calls such as `rewrite ... step42`. Compound proof
    * terms are wrapped in `Obj` so the meta-level tactic argument still prints
    * as the underlying object-level proof expression.
    */
  def proofTermAsTacticArg(term: LpTerm[Level.Obj]): LpTerm[Level.Meta] = term match {
    case Const(sym) => Const[Level.Meta](sym)
    case _ => Obj(term)
  }

  /** Apply a parent proof to the variables introduced for the current proof step. */
  def applyProofToVars(proof: LpTerm[Level.Obj], varNames: Seq[Name]): LpTerm[Level.Obj] = {
    if (varNames.isEmpty) proof
    else LpTerm.App(proof, varNames.map(varName => Arg.Explicit[Level.Obj](LpTerm.Var(varName, None))))
  }
}

object EqualityProofSteps {
  final case class RewriteRuleEqualityProof(step: Have,
                                            proofTerm: LpTerm[Level.Obj],
                                            rhs: LpTerm[Level.Obj])

  final case class LiteralMismatch(targetLit: lpLiteralInst,
                                   intermediateLit: lpLiteralInst,
                                   clauseAfterTransformation: Seq[lpLiteralInst],
                                   litIdx: Int)

  private val NormalizeEqLitTactic: LpTerm[Level.Meta] =
    Const[Level.Meta](SymRef.LP(QName.local("normalizeEqLit")))

  private def closeEqTactic(ty: OlMonoType): LpTerm[Level.Meta] =
    LpTerm.App[Level.Meta](
      Const[Level.Meta](SymRef.LP(QName.local("closeEq"))),
      Seq(Arg.ExplicitTypeArg[Level.Meta](ty))
    )

  /**
    * Prove the Boolean equality form of a non-equational rewrite-rule parent.
    *
    * A positive proposition `P` becomes `P = ⊤`; a negative proposition becomes
    * `P = ⊥`. This is the same forward orientation used by Leo's rewrite table.
    */
  def provePropLiteralAsForwardBooleanEquality(stepName: Name,
                                               litTerm: LpTerm[Level.Obj],
                                               polarity: Boolean,
                                               sourceProof: LpTerm[Level.Obj],
                                               binders: Seq[LpTerm.Var[Level.Meta]] = Seq.empty,
                                               binderNames: Seq[Name] = Seq.empty): RewriteRuleEqualityProof = {
    val transformedRewriteEq =
      if (polarity) LogicConst.Eq(HolBaseTypes.O, litTerm, LogicConst.Top)
      else LogicConst.Eq(HolBaseTypes.O, litTerm, LogicConst.Bot)
    val rewriteRule =
      if (polarity) lpSimp_eqTop[Level.Meta]
      else lpSimp_eqBot[Level.Meta]
    val rwRhs =
      if (polarity) LogicConst.Top
      else LogicConst.Bot

    val haveTransformStep = Have(
      stepName,
      if (binders.isEmpty) Prf(transformedRewriteEq) else Pi(binders, Prf(transformedRewriteEq)),
      AssumeStep.encAssumeStep(binderNames).map(Left(_)) ++ Seq(
        Left(Rewrite(None, rewriteRule)),
        Left(Refine(Obj(sourceProof)))
      )
    )

    RewriteRuleEqualityProof(haveTransformStep, ProofTermUtil.proofName(stepName), rwRhs)
  }

  /**
    * Prove the reverse of an equational rewrite-rule parent using equality
    * symmetry. The returned RHS is the original right-hand side of the
    * unflipped equality, i.e. the target used by the later rewrite simulation.
    */
  def proveFlippedEquality(stepName: Name,
                           lhs: LpTerm[Level.Obj],
                           rhs: LpTerm[Level.Obj],
                           eqType: OlMonoType,
                           sourceProof: LpTerm[Level.Obj]): RewriteRuleEqualityProof = {
    val transformedRewriteEq = LogicConst.Eq(eqType, rhs, lhs)
    val haveTransformStep = Have(
      stepName,
      Prf(transformedRewriteEq),
      Seq(
        Left(Rewrite(None, eqSym[Level.Meta])),
        Left(Refine(Obj(sourceProof)))
      )
    )

    RewriteRuleEqualityProof(haveTransformStep, ProofTermUtil.proofName(stepName), rhs)
  }

  /**
    * Compute the literal positions where a target clause differs from the
    * intermediate clause shape expected by subsequent proof steps.
    *
    * The function is pure: it simulates the sequence of focused literal
    * transformations and returns the information needed to construct the actual
    * proof-script commands elsewhere.
    */
  def literalMismatches(targetLits: Seq[lpLiteralInst],
                        intermediateLits: Seq[lpLiteralInst]): Vector[LiteralMismatch] = {
    require(targetLits.length == intermediateLits.length,
      s"Cannot compare literal transformations for clauses of different length: ${targetLits.length} and ${intermediateLits.length}")

    var currentGoalLits = targetLits.toVector
    val result = Vector.newBuilder[LiteralMismatch]

    intermediateLits.zipWithIndex.foreach {
      case (intermediateLit, litIdx) =>
        val currentTargetLit = currentGoalLits(litIdx)
        if (currentTargetLit != intermediateLit) {
          val clauseAfterTransformation = currentGoalLits.updated(litIdx, intermediateLit)
          result += LiteralMismatch(currentTargetLit, intermediateLit, clauseAfterTransformation, litIdx)
          currentGoalLits = clauseAfterTransformation
        }
    }

    result.result()
  }

  /**
    * Emit a generic literal transformation via a focused rewrite.
    *
    * The local `have` is proved by a user-defined Lambdapi tactic that
    * normalizes both literals to a common normal form and compares them. The
    * resulting equality proof is then used to rewrite exactly the selected
    * literal position in the current clause goal.
    */
  def transformLiteralWithTactic(stepName: Name,
                                 targetLit: lpLiteralInst,
                                 intermediateLit: lpLiteralInst,
                                 clauseAfterTransformation: Seq[lpLiteralInst],
                                 litIdx: Int): Seq[LpProofScript] = {
    val patternVar = Const[Level.Obj](SymRef.LP(QName.local("x")))
    val rewritePattern = PatternBuilder.generateClausePattern(litIdx, clauseAfterTransformation.length, patternVar, patternVar)
    val closeEqType = targetLit.equalitySideType.orElse(intermediateLit.equalitySideType).getOrElse(HolBaseTypes.O)

    Seq(
      Have(
        stepName,
        Prf(LogicConst.Eq(HolBaseTypes.O, targetLit.term, intermediateLit.term)),
        Seq(
          Left(Eval(NormalizeEqLitTactic)),
          Left(Try(Simplify(Seq(Name(depTyConStr))))),
          Left(Eval(closeEqTactic(closeEqType)))
        )
      ),
      Rewrite(Some(rewritePattern), ProofTermUtil.proofTermAsTacticArg(ProofTermUtil.proofName(stepName)))
    )
  }
}

object InstMetaTheorems {
  /**
    * Construct a substep that removes trivially false Literals
    *
    * @param nameHaveRemoveStep The intended name of the term defiend by the LP-have Tactic
    * @param encSubstParent     A sequence of encoded literals representing the parent of the step
    * @param encChildLits       A sequence of encoded literals representing the clause to be proved
    * @param deletePositions    A sequence with indices indicating which of the literal of the parent are to be removed
    *                           It is left to the user to ensure that they are indeed trivially false
    * @return a LP have tactic proving the removal of the literals in a substep
    */
  def constructRemoveStep(nameHaveRemoveStep: Name, encSubstParent: Seq[lpLiteralInst], encChildLits: Seq[lpLiteralInst], deletePositions: Seq[Int]) = {
    // todo: change encoding s.t. we only need encoded parent and do the deletion automatically
    val impToProve = Prf(LogicConst.Eq(HolBaseTypes.O, nAry.disjunction(encSubstParent.map(_.term)), nAry.disjunction(encChildLits.map(_.term))))
    val proofScript: Seq[LpProofScript] = deletePositions.map(posInSubs => {
      Out.lp_debug_info(s"orig pos is ${posInSubs}")
      val patternLitInfo = PatternBuilder.PatternInfo(posInSubs, None, polarity = true)
      val pattern = PatternBuilder.generateClausePattern(Seq(patternLitInfo), encSubstParent.length)
      val embeddedPattern = PatternBuilder.embedPatternInEq(pattern, Side.Left)
      removeBot(embeddedPattern)
    })
    // todo: probably replace this with a test on an encoded clause?
    val finalStep =
      Refine(deleteBots(encChildLits, deletePositions.sorted))
    Have(nameHaveRemoveStep, impToProve, (proofScript :+ finalStep).map(step => Left(step)))
  }

  @inline def applyRemoveStep(nameHaveRemoveStep: Name, maybeSubstStepName: LpTerm[Level.Obj]) = LpTerm.App(eqImp, Seq(Arg.Explicit[Level.Obj](Const(SymRef.LP(QName.local(nameHaveRemoveStep.value)))), Arg.Explicit[Level.Obj](maybeSubstStepName)))

}
