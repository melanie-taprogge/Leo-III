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

  val allBoolRuleApplicationStep = lpEval(allBoolRulesTermName)

  val fullCnfTacName = lpConstantTerm("cnfTac")
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


}
