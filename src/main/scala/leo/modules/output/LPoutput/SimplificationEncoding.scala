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

  // Idempotence and Contradiction for ∧ and ∨

  // 6
  /** Rule (x : τ T): π ((x ∨ x) = x) */
  case object lpSimp_or_idem extends simplificationRules {
   override def name: lpConstantTerm = lpConstantTerm("∨_idem")
    override def pretty: String = name.pretty
  }

  // Disjunction/Conjunction with ⊤ / ⊥

  // 14
  /** Rule (x : τ T): π ((x ∨ ⊥) = x) */
  case object lpSimp_orBot extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("∨⊥")
    override def pretty: String = name.pretty
  }

  // Negation of ⊤ and ⊥

  // 18
  /** Rule π (¬ ⊤ = ⊥) */
  case object lpSimp_negTop extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("¬⊤")
    override def pretty: String = name.pretty
  }

  //Equalities

  // 20
  /** Rule (T : Set) (x : τ T): (π ((x = x) = ⊤)) */
  case object lpSimp_eq_idem extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("=_idem")
    override def pretty: String = name.pretty
  }

  // 21
  /** Rule (T : Set) (x : τ T): π (¬ (x = x) = ⊥) */
  case object lpSimp_negEq_idem extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("¬=_idem")
    override def pretty: String = name.pretty
  }

  // 22
  /** Rule (x : τ o): π ((x = ⊤) = x) */
  case object lpSimp_eqTop extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("=⊤")
    override def pretty: String = name.pretty
  }

  // 23
  /** Rule (x : τ o): π ((⊤ = x) = x) */
  case object lpSimp_topEq extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("⊤=")
    override def pretty: String = name.pretty
  }

  // 24
  /** Rule (x : τ o): π (¬(x = ⊤) = ¬ x) */
  case object lpSimp_negEqTop extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("¬=⊤")
    override def pretty: String = name.pretty
  }

  // 26
  /** Rule (x : τ o): π ((x = ⊥) = ¬ x) */
  case object lpSimp_eqBot extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("=⊥")
    override def pretty: String = name.pretty
  }

  // 27
  /** Rule (x : τ o): π ((⊥ = x) = ¬ x) */
  case object lpSimp_botEq extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("⊥=")
    override def pretty: String = name.pretty
  }

  // 28
  /** Rule (x : τ o): π (¬ (x = ⊥) = x) */
  case object lpSimp_negEqBot extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("¬=⊥")
    override def pretty: String = name.pretty
  }

  //Equalities with negations

  // 30
  /** Rule (x : τ o): π ((¬ x = ⊤) = ¬ x) */
  case object lpSimp_notEqTop extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("neg=⊤")
    override def pretty: String = name.pretty
  }

  // 32
  /** Rule (x : τ o): π (¬(¬ x = ⊤) = x) */
  case object lpSimp_negNotEqTop extends simplificationRules {
    override def name: lpConstantTerm = lpConstantTerm("¬neg=⊤")
    override def pretty: String = name.pretty
  }

  // 36
  /** Rule (x : τ o):π (¬(¬ x = ⊥) = ¬ x) */
  case object lpSimp_negNotEqBot extends simplificationRules {
    // π (¬(¬ x = ⊥) = ¬ x)
    override def name: lpConstantTerm = lpConstantTerm("¬neg=⊥")
    override def pretty: String = name.pretty
  }

  // Simplifications reflecting Classical Principles

  // 52
  case object lpSimp_dne extends simplificationRules {
    // x: (π (x = (¬ ¬ x)))
    override def name: lpConstantTerm = lpConstantTerm("¬¬ₑ_eq")
    override def pretty: String = name.pretty
    def instanciate(a: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(a))
    }
  }

}
