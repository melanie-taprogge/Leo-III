package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures._

/**
  * Representations of the simplification rules
  *
  * @author Melanie Taprogge
  */

object CNFEncoding {

  val allBoolRulesTermName = lpConstantTerm("boolIds")

  val onlyBoolRulesTermName = lpConstantTerm("onlyBoolIds")

  val allBoolRuleApplicationStep = lpEval(allBoolRulesTermName)

  val fullCnfTacName = lpConstantTerm("cnfTac")

  val cnfTacQuantifiers = lpConstantTerm("stepwise_quants")

  val cnfTacSkolem = lpConstantTerm("stepwise_skolem")

  def cnfTac(varsListName: Option[lpConstantTerm],skDefsLis: Option[lpList]) = {

    lpEval(lpFunctionApp(fullCnfTacName,Seq(varsListName.getOrElse(lpListLast),skDefsLis.getOrElse(lpListLast))))
}

  abstract class clausificationProcedures extends lpUserTactic {
    def name: lpConstantTerm
    override def pretty(implicit prefix: PrettyConfig): String = name.pretty
  }

  case object lpSkolemizeExists extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("skolemProzess_∃")
  }

  case object lpSkolemizeUniv extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("skolemProzess_∀")
  }

  case object lpSkolemProcess extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("skolemProzess")
  }

  case object lpMoveUniv extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("move_∀_out")
  }

  case object lpMoveExists extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("move_¬∃_out")
  }

  case object singleStepQuant extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("singleStepQuant")
  }




}
