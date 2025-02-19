package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._

/**
  * Representations of the simplification rules
  *
  * @author Melanie Taprogge
  */

//todo: encode proofs properly

object SimplificationEncoding {

  val implicitArguments = false

  // map of names to the simplification rules and a boolean decoding weather or not we need type instanciation
  val SimpNeedsTyping:  Map[simplificationRules,Boolean] =
    Map(Simp1_eq -> false,
        Simp9_eq -> true,
        Simp10_eq -> true,
        Simp16_eq -> false,
        )

  // map the names of the simplification rules to the names of the functions encoding them and a boolean indicating weather or not they need to be instanciated
  val SimpRuleMap: Map[Int,(simplificationRules,Boolean)] =
    Map(1 -> (Simp1_eq, SimpNeedsTyping(Simp1_eq)),
        31 -> (Simp9_eq, SimpNeedsTyping(Simp9_eq)),
        37 -> (Simp10_eq, SimpNeedsTyping(Simp10_eq)),
        24 -> (Simp16_eq, SimpNeedsTyping(Simp16_eq)),
        26 -> (Simp16_eq, SimpNeedsTyping(Simp16_eq)))

  abstract class simplificationRules extends lpStatement{
    def name: lpConstantTerm

    def ty: lpMlType

    def proof: lpProofScript

    def dec: lpDeclaration
  }

  case object Simp1_eq extends simplificationRules {
    // (π (x = (x ∨ x)))

    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("Simp1_eq")

    override def ty: lpMlType = lpMlDependType(Seq(lpUntypedVar(x1)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUntypedBinaryConnectiveTerm(lpOr,x1,x1),x1).prf)

    override def proof: lpProofScript = {
      lpProofScript(Seq(lpProofScriptStringProof("assume x;\n    refine propExt x (x ∨ x) _ _ \n        {assume h2;\n        refine ∨ᵢ₁ h2}\n        {assume h1;\n        refine ∨ₑ h1 _ _\n            {assume h2;\n            refine h2}\n            {assume h2;\n            refine h2}}")))
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${x1.pretty}]")))
      else Seq(lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp1_eq.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp1_eq.name, arguments, Some(ty), proof).pretty
  }

  case object Simp7_eq extends simplificationRules {

    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("simp7_eq")

    // π (x = (x ∨ ⊥))
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x1,lpOlUntypedBinaryConnectiveTerm(lpOr,x1,lpOlBot)).prf

    override def proof: lpProofScript = {
      lpProofScript(Seq(lpProofScriptStringProof("assume x;\n    refine propExt x (x ∨ ⊥) _ _ \n        {assume h1;\n        refine ∨ᵢ₁ h1}\n        {assume h1;\n        refine ∨ₑ h1 _ _\n            {assume h2;\n            refine h2}\n            {assume h2;\n            refine ⊥ₑ h2}}")))
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${x1.pretty}]")))
      else Seq(lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp7_eq.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp7_eq.name, arguments, Some(ty), proof).pretty
  }

  case object Simp9_eq extends simplificationRules {

    val T =lpOlUserDefinedType("T")
    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("Simp9_eq")

    // (T : Set) (x : τ T): (π ( ⊤ = (x = x)))
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlTypedBinaryConnectiveTerm(lpEq,T,x1,x1),lpOlTop).prf

    override def proof: lpProofScript = {
      lpProofScript(Seq(lpProofScriptStringProof("assume T x;\n    refine propExt ⊤ (x = x) _ _ \n        {assume h1;\n        refine eq_refl x}\n        {assume h1;\n        refine ⊤ᵢ}")))
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${T.pretty}${x1.pretty}]")))
      else Seq(lpUntypedVar(T),lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp9_eq.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp9_eq.name, arguments, Some(ty), proof).pretty
  }

  case object Simp10_eq extends simplificationRules {

    val T = lpOlUserDefinedType("T")
    val x1 = lpOlTypedTermVar(lpOlConstantTerm("x"),T)

    override def name: lpConstantTerm = lpConstantTerm("simp10_eq")

    // (T : Set) (x : τ T): (π (⊥ = (¬ (x = x))))
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlBot, lpOlTypedBinaryConnectiveTerm(lpInEq, T, x1.name, x1.name)).prf

    override def proof: lpProofScript = {
      lpProofScript(Seq(lpProofScriptStringProof("assume T x;\n    refine propExt ⊥ (¬ (x = x)) _ _ \n        {assume h1;\n        refine ⊥ₑ h1}\n        {assume h1;\n        have H1: π (x = x) → π ⊥\n            {assume h2;\n            refine h1 h2};\n        refine H1 (eq_refl [T] x)}")))
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${T.pretty}${x1.pretty}]")))
      else Seq(lpUntypedVar(T),lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp10_eq.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp10_eq.name, arguments, Some(ty), proof).pretty
  }

  case object Simp16_eq extends simplificationRules {

    override def name: lpConstantTerm = lpConstantTerm("simp16_eq")

    // (π (⊥ = (¬ ⊤)))
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype, lpOlBot, lpOlUnaryConnectiveTerm(lpNot,lpOlTop)).prf

    override def proof: lpProofScript = {
      lpProofScript(Seq(lpProofScriptStringProof("refine propExt ⊥ (¬ ⊤) _ _ \n        {assume h1;\n        refine ⊥ₑ h1}\n        {assume h1;\n        refine h1 ⊤ᵢ}")))
    }

    override def dec: lpDeclaration = lpDeclaration(Simp16_eq.name,Seq.empty,ty)

    override def pretty: String = lpDefinition(Simp16_eq.name, Seq.empty, Some(ty), proof).pretty
  }

  case object Simp17_eq extends simplificationRules {

    val x = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("simp17_eq")

    // x: (π (x = (¬ ¬ x)))
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, x, lpOlUnaryConnectiveTerm(lpNot,lpOlUnaryConnectiveTerm(lpNot,x))).prf

    override def proof: lpProofScript = {
      lpProofScript(Seq(lpProofScriptStringProof("assume x;\n    refine propExt x (¬ ¬ x) _ _ \n        {assume h1 h2;\n        refine h2 h1}\n        {assume h1;\n        refine dne x h1}")))
    }

    override def dec: lpDeclaration = lpDeclaration(Simp17_eq.name, Seq(x), ty)

    override def pretty: String = lpDefinition(Simp17_eq.name, Seq(x), Some(ty), proof).pretty

    def instanciate(a: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(a))
    }
  }

}
