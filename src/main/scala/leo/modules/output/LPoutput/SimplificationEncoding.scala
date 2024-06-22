package leo.modules.output.LPoutput

import leo.datastructures.Literal.{asTerm, vars}
import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.LPoutput.Encodings._
import leo.datastructures.{Clause, ClauseProxy, Literal, Signature, Term}
import leo.modules.HOLSignature._
import leo.modules.calculus.BoolExt
import leo.modules.output.intToName
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.Transformations._

object SimplificationEncoding {

  val implicitArguments = false

  // map of names to the simplification rules and a boolean decoding weather or not we need type instanciation
  val SimpNeedsTyping:  Map[simplificationRules,Boolean] =
    Map(Simp1_eq -> false,
        Simp9_eq -> true,
        Simp10_eq -> true,
        Simp16_eq -> false,
        )

  val SimpRuleMap: Map[String,(simplificationRules,Boolean)] =
    Map("Simp1" -> (Simp1_eq, SimpNeedsTyping(Simp1_eq)),
        "Simp9" -> (Simp9_eq, SimpNeedsTyping(Simp9_eq)),
        "Simp10" -> (Simp10_eq, SimpNeedsTyping(Simp10_eq)),
        "Simp16" -> (Simp16_eq, SimpNeedsTyping(Simp16_eq)))

  abstract class simplificationRules extends lpStatement{
    def name: lpConstantTerm

    def ty: lpMlType

    def proof: lpTerm

    def dec: lpDeclaration
  }

  case object Simp1 extends simplificationRules{

    val x1 = lpOlConstantTerm("x")
    val h1 = lpOlConstantTerm("h")
    val h2 = lpOlConstantTerm("H")

    override def name: lpConstantTerm = lpConstantTerm("Simp1")

    // Prf (x ∨ x) → Prf x
    override def ty: lpMlType = lpMlFunctionType(Seq(lpOlUntypedBinaryConnectiveTerm(lpOr,x1,x1).prf,x1.prf))

    // λ (x : Prop) (h : Prf (x ∨ x)), h x (λ H, H) (λ H, H);
    override def proof: lpTerm = {
      lpLambdaTerm(Seq(lpUntypedVar(x1),lpTypedVar(h1,lpOlUntypedBinaryConnectiveTerm(lpOr,x1,x1).prf)),lpFunctionApp(h1,Seq(x1,lpLambdaTerm(Seq(lpUntypedVar(h2)),lpUntypedVar(h2)),lpLambdaTerm(Seq(lpUntypedVar(h2)),lpUntypedVar(h2)))))
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${x1.pretty}]")))
      else Seq(lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp1.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp1.name,arguments,ty,proof).pretty
  }

  case object Simp1_eq extends simplificationRules {

    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("Simp1_eq")

    // Prf (eq [↑ o] (x ∨ x) x)
    override def ty: lpMlType = lpMlDependType(Seq(lpUntypedVar(x1)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUntypedBinaryConnectiveTerm(lpOr,x1,x1),x1).prf)

    override def proof: lpTerm = {
      throw new Exception("proofs for simplificationRules not encoded yet")
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${x1.pretty}]")))
      else Seq(lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp1_eq.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp1_eq.name, arguments, ty, proof).pretty
  }

  case object Simp7_eq extends simplificationRules {

    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("Simp7_eq")

    // Prf(eq [↑ o] (x ∨ ⊥) x)
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x1,lpOlUntypedBinaryConnectiveTerm(lpOr,x1,lpOlBot)).prf

    override def proof: lpTerm = {
      throw new Exception("proofs for simplificationRules not encoded yet")
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${x1.pretty}]")))
      else Seq(lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp7_eq.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp7_eq.name, arguments, ty, proof).pretty
  }

  case object Simp9_eq extends simplificationRules {

    val T =lpOlUserDefinedType("T")
    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("Simp9_eq")

    // Simp9_eq [T] x : Prf (eq [↑ o] (eq [T] x x) ⊤)
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlTypedBinaryConnectiveTerm(lpEq,T,x1,x1),lpOlTop).prf

    override def proof: lpTerm = {
      throw new Exception("proofs for simplificationRules not encoded yet")
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${T.pretty}${x1.pretty}]")))
      else Seq(lpUntypedVar(T),lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp9_eq.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp9_eq.name, arguments, ty, proof).pretty
  }

  case object Simp10_eq extends simplificationRules {

    val T = lpOlUserDefinedType("T")
    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("Simp10_eq")

    // Simp10_eq [T] x : Prf (inEq [↑ o] (inEq [T] x x) ⊥)
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlBot, lpOlTypedBinaryConnectiveTerm(lpInEq, T, x1, x1)).prf

    override def proof: lpTerm = {
      throw new Exception("proofs for simplificationRules not encoded yet")
    }

    val arguments: Seq[lpVariable] =
      if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${T.pretty}${x1.pretty}]")))
      else Seq(lpUntypedVar(T),lpUntypedVar(x1))

    override def dec: lpDeclaration = lpDeclaration(Simp10_eq.name,arguments,ty)

    override def pretty: String = lpDefinition(Simp10_eq.name, arguments, ty, proof).pretty
  }

  case object Simp16_eq extends simplificationRules {

    override def name: lpConstantTerm = lpConstantTerm("Simp16_eq")

    // Simp16_eq : Prf (eq [↑ o] (¬ ⊤) ⊥)
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype, lpOlBot, lpOlUnaryConnectiveTerm(lpNot,lpOlTop)).prf

    override def proof: lpTerm = {
      throw new Exception("proofs for simplificationRules not encoded yet")
    }

    override def dec: lpDeclaration = lpDeclaration(Simp16_eq.name,Seq.empty,ty)

    override def pretty: String = lpDefinition(Simp16_eq.name, Seq.empty, ty, proof).pretty
  }

}
