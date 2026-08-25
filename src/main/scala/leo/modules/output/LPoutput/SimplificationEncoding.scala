package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures._

/**
  * Representations of the simplification rules
  *
  * @author Melanie Taprogge
  */

//todo: encode proofs properly

object SimplificationEncoding {

  val allSimpRulesTermName = lpConstantTerm("applyAllSimplifications")
  val allSimpRulesWithArithmeticTermName = lpConstantTerm("applyAllSimplificationsWithArithmatic")

  val allSimpRuleApplicationStep = lpEval(allSimpRulesTermName)
  val allSimpWithArithmeticRuleApplicationStep = lpEval(allSimpRulesWithArithmeticTermName)
  
  
  // Idempotence and Contradiction for ∧ and ∨

  // 6
  /** Rule (x : τ T): π ((x ∨ x) = x) */
  case object lpSimp_or_idem extends lpNameRef {
   override def name: lpConstantTerm = lpConstantTerm("∨_idem")
  }

  // Disjunction/Conjunction with ⊤ / ⊥

  // 14
  /** Rule (x : τ T): π ((x ∨ ⊥) = x) */
  case object lpSimp_orBot extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("∨⊥")
  }

  /** Rule (x : τ T): π ((⊥ ∨ x) = x) */
  case object lpSimp_botOr extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("⊥∨")
  }

  // Negation of ⊤ and ⊥

  // 18
  /** Rule π (¬ ⊤ = ⊥) */
  case object lpSimp_negTop extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("¬⊤")
  }

  //Equalities

  // 20
  /** Rule (T : Set) (x : τ T): (π ((x = x) = ⊤)) */
  case object lpSimp_eq_idem extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("=_idem")
    def instanciate(ty: lpOlType, term: Option[lpOlTerm]): lpFunctionApp = {
      val args = if (term.isDefined) Seq(ty, term.get) else Seq(ty)
      lpFunctionApp(name, args)
    }
  }

  // 21
  /** Rule (T : Set) (x : τ T): π (¬ (x = x) = ⊥) */
  case object lpSimp_negEq_idem extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("¬=_idem")

    def instanciate(ty: lpOlType, term: Option[lpOlTerm]):lpFunctionApp ={
      val args = if (term.isDefined) Seq(ty, term.get) else Seq(ty)
      lpFunctionApp(name, args)}
  }

  // 22
  /** Rule (x : τ o): π ((x = ⊤) = x) */
  case object lpSimp_eqTop extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("=⊤")
    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop), x0, lpOlTop)
  }

  // 23
  /** Rule (x : τ o): π ((⊤ = x) = x) */
  case object lpSimp_topEq extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("⊤=")
  }

  // 24
  /** Rule (x : τ o): π (¬(x = ⊤) = ¬ x) */
  case object lpSimp_negEqTop extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("¬=⊤")

    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop)), x0, lpOlTop)

  }

  // 26
  /** Rule (x : τ o): π ((x = ⊥) = ¬ x) */
  case object lpSimp_eqBot extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("=⊥")
    
  }

  // 27
  /** Rule (x : τ o): π ((⊥ = x) = ¬ x) */
  case object lpSimp_botEq extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("⊥=")
    
  }

  // 28
  /** Rule (x : τ o): π (¬ (x = ⊥) = x) */
  case object lpSimp_negEqBot extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("¬=⊥")
    
  }

  //Equalities with negations

  // 30
  /** Rule (x : τ o): π ((¬ x = ⊤) = ¬ x) */
  case object lpSimp_notEqTop extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("neg=⊤")

    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop), lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)

  }

  // 32
  /** Rule (x : τ o): π (¬(¬ x = ⊤) = x) */
  case object lpSimp_negNotEqTop extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm("¬neg=⊤")

    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)), lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)
  }

  // 36
  /** Rule (x : τ o):π (¬(¬ x = ⊥) = ¬ x) */
  case object lpSimp_negNotEqBot extends lpNameRef {
    // π (¬(¬ x = ⊥) = ¬ x)
    override def name: lpConstantTerm = lpConstantTerm("¬neg=⊥")
    
  }

  // Simplifications reflecting Classical Principles

  // 52
  case object lpSimp_dne extends lpNameRef {
    // x: (π (x = (¬ ¬ x)))
    override def name: lpConstantTerm = lpConstantTerm("¬¬ₑ_eq")
    
    def instanciate(a: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(a))
    }
  }
}
