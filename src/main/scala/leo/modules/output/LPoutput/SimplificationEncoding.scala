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
  val SimpRuleMap: Map[String,(simplificationRules,Boolean)] =
    Map("Simp1" -> (Simp1_eq, false),
        "Simp9" -> (Simp9_eq, true),
        "Simp16" -> (Simp16_eq, false))

  abstract class simplificationRules extends lpStatement{
    def name: lpConstantTerm

    def ty: lpMlType

    def proof: lpTerm
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

    override def pretty: String = {

      val arguments: Seq[lpVariable] =
        if(implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${x1.pretty}]")))
        else Seq(lpUntypedVar(x1))

      lpDefinition(Simp1.name,arguments,ty,proof).pretty
    }
  }

  case object Simp1_eq extends simplificationRules {

    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("Simp1_eq")

    // Prf (eq [↑ o] (x ∨ x) x)
    override def ty: lpMlType = lpMlDependType(Seq(lpUntypedVar(x1)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUntypedBinaryConnectiveTerm(lpOr,x1,x1),x1).prf)

    override def proof: lpTerm = {
      throw new Exception("proofs for simplificationRules not encoded yet")
    }

    override def pretty: String = {

      val arguments: Seq[lpVariable] =
        if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${x1.pretty}]")))
        else Seq(lpUntypedVar(x1))

      lpDefinition(Simp1.name, arguments, ty, proof).pretty
    }
  }

  case object Simp9_eq extends simplificationRules {

    val T =lpOlUserDefinedType("T")
    val x1 = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("Simp9_eq")

    // Simp9_eq [T] x : Prf (eq [↑ o] (eq [T] x x) ⊤)
    override def ty: lpMlType = lpMlDependType(Seq(lpUntypedVar(lpConstantTerm(T.pretty)),lpUntypedVar(x1)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlTypedBinaryConnectiveTerm(lpEq,T,x1,x1),lpOlTop).prf)

    override def proof: lpTerm = {
      throw new Exception("proofs for simplificationRules not encoded yet")
    }

    override def pretty: String = {

      val arguments: Seq[lpVariable] =
        if (implicitArguments) Seq(lpUntypedVar(lpConstantTerm(s"[${T.pretty}${x1.pretty}]")))
        else Seq(lpUntypedVar(x1))

      lpDefinition(Simp1.name, arguments, ty, proof).pretty
    }
  }

  case object Simp16_eq extends simplificationRules {

    override def name: lpConstantTerm = lpConstantTerm("Simp16_eq")

    // Simp16_eq : Prf (eq [↑ o] (¬ ⊤) ⊥)
    override def ty: lpMlType = throw new Exception("proofs for simplificationRules not encoded yet")

    override def proof: lpTerm = {
      throw new Exception("proofs for simplificationRules not encoded yet")
    }

    override def pretty: String = {
      lpDefinition(Simp1.name, Seq.empty, ty, proof).pretty
    }
  }

}
