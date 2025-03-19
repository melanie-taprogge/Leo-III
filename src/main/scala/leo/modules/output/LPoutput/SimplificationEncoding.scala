package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._

/**
  * Representations of the simplification rules
  *
  * @author Melanie Taprogge
  */

//todo: encode proofs properly

object SimplificationEncoding {

  val allSimpRulesTermName = lpConstantTerm("applyAllSimplifications")

  val allSimpRuleApplicationStep = lpEval(allSimpRulesTermName)

  val implicitArguments = false

  // map of names to the simplification rules and a boolean decoding weather or not we need type instanciation
  val SimpNeedsTyping:  Map[simplificationRules,Boolean] =
    Map(lpSimp_or_idem -> false,
        lpSimp_eq_idem -> true,
        lpSimp_negEq_idem -> true,
        lpSimp_negTop -> false,
        )

  // map the names of the simplification rules to the names of the functions encoding them and a boolean indicating weather or not they need to be instanciated
  val SimpRuleMap: Map[Int,(simplificationRules,Boolean)] =
    Map(1 -> (lpSimp_or_idem, SimpNeedsTyping(lpSimp_or_idem)),
        31 -> (lpSimp_eq_idem, SimpNeedsTyping(lpSimp_eq_idem)),
        37 -> (lpSimp_negEq_idem, SimpNeedsTyping(lpSimp_negEq_idem)),
        24 -> (lpSimp_negTop, SimpNeedsTyping(lpSimp_negTop)),
        26 -> (lpSimp_negTop, SimpNeedsTyping(lpSimp_negTop)))

  abstract class simplificationRules extends lpStatement{
    def name: lpConstantTerm
  }

  case object lpSimp_or_idem extends simplificationRules {
    // (π (x = (x ∨ x)))
   override def name: lpConstantTerm = lpConstantTerm("∨_idem")
    override def pretty: String = name.pretty
  }

  case object lpSimp_orF extends simplificationRules {
    // π ((x ∨ ⊥) = x)
    override def name: lpConstantTerm = lpConstantTerm("∨⊥")
    override def pretty: String = name.pretty
  }

  case object lpSimp_eq_idem extends simplificationRules {
    // (T : Set) (x : τ T): (π (⊤ = (x = x)))
    override def name: lpConstantTerm = lpConstantTerm("eq_idem")
    override def pretty: String = name.pretty
  }

  case object lpSimp_negEq_idem extends simplificationRules {
    // (T : Set) (x : τ T): (π (⊥ = (¬ (x = x))))
    override def name: lpConstantTerm = lpConstantTerm("¬eq_idem")
    override def pretty: String = name.pretty
  }

  case object lpSimp_negTop extends simplificationRules {
    // (π (⊥ = (¬ ⊤)))
    override def name: lpConstantTerm = lpConstantTerm("¬⊤")
    override def pretty: String = name.pretty
  }

  case object lpSimp_dne extends simplificationRules {
    // x: (π (x = (¬ ¬ x)))
    override def name: lpConstantTerm = lpConstantTerm("¬¬ₑ_eq")
    override def pretty: String = name.pretty
    def instanciate(a: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(a))
    }
  }

}
