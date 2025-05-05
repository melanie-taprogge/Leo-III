package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._

/**
  * Representations of the simplification rules
  *
  * @author Melanie Taprogge
  */

//todo: encode proofs properly

object CNFEncoding {

  val allBoolRulesTermName = lpConstantTerm("allCNFids_app")

  val allBoolRuleApplicationStep = lpEval(allBoolRulesTermName)


}
