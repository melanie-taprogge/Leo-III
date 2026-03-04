package leo.modules.output.LPoutput.NewModularEncoding

import leo.Out
import leo.modules.output.LPoutput.LpLibs.EqRules.AsTerms.eqImp
import leo.modules.output.LPoutput.LpLibs.LeoTactics.EvalApp.removeBot
import leo.modules.output.LPoutput.LpLibs.MetaTheorems.Inst.deleteBots
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Assume, Have, Refine, Side}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Const
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.Prf
import leo.modules.output.LPoutput.NewLpDatastructures._


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
