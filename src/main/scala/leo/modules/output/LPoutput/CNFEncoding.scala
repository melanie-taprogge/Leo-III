package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._

/**
  * Representations of the simplification rules
  *
  * @author Melanie Taprogge
  */

//todo: encode proofs properly

object CNFEncoding {

  val allBoolRulesTermName = lpConstantTerm("boolIds")

  val onlyBoolRulesTermName = lpConstantTerm("onlyBoolIds")

  val allBoolRuleApplicationStep = lpEval(allBoolRulesTermName)

  val fullCnfTacName = lpConstantTerm("cnfTac")

  val cnfTacQuantifiers = lpConstantTerm("stepwise_quants")

  def cnfTac(varsListName: Option[lpConstantTerm],skDefsListName: Option[lpConstantTerm]) = {

    /*
    val instTac: lpTerm= (varsListName, skDefsListName) match {
      case (Some(vars), Some(sks)) => lpFunctionApp(fullCnfTacName,Seq(vars,sks))
      case (Some(vars), None) =>
      case (None, Some(sks)) =>
      case (None,None) => allBoolRulesTermName
    }
     */
    lpEval(lpFunctionApp(fullCnfTacName,Seq(varsListName.getOrElse(lpListLast),skDefsListName.getOrElse(lpListLast))))
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

  case object lpMoveUniv extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("move_∀_out2")
  }

  case object lpMoveExists extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("move_¬∃_out2")
  }

  case object singleStepQuant extends clausificationProcedures {
    override def name: lpConstantTerm = lpConstantTerm("singleStepQuant")
  }




}
