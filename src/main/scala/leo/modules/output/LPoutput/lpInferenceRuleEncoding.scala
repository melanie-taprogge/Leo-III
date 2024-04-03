package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.LPSignature.{HOLtop, Prf, lpPropExt, oType,lpEm}
import leo.modules.output.LPoutput.calculusEncoding.{nameBottom, nameHypothesis, nameX, nameType}
import leo.modules.output.LPoutput.lpDatastructures._

object lpInferenceRuleEncoding {

  abstract class inferenceRules extends lpDefinedRules

  case class funextPosEq_rev(n: Int = 1) extends inferenceRules {

    if (n > 1) throw new Exception(s"error encoding eqFactoring: trying to instanciate rule for more than one arg not encoded yet")
    override def name: String = s"funextPos$n"

    // [T S] f g x : Prf(= (= [S] (f x) (g x)) (= [T ⤳ S] f g))
    val T = lpOlUserDefinedPolyType("T")
    val S = lpOlUserDefinedPolyType("S")
    val f = lpOlConstantTerm("f")
    val g = lpOlConstantTerm("g")
    val x = lpOlConstantTerm("x") //todo i need n x here
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTypedBinaryConnectiveTerm(lpEq,S,lpOlFunctionApp(f,Seq(x)),lpOlFunctionApp(g,Seq(x))),lpOlTypedBinaryConnectiveTerm(lpEq,lpOlFunctionType(Seq(T,S)),f,g)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet") //todo: generate depending on number of args
    override def dec: lpDeclaration = lpDeclaration(lpConstantTerm(name), Seq(f,g,x), ty, Seq(T,S))

    override def pretty: String = lpDefinition(lpConstantTerm(name), Seq(f,g,x), ty, proof, Seq(T,S)).pretty

    def instanciate(TS0:Option[(lpOlPolyType,lpOlPolyType)],f:lpOlTerm,g:lpOlTerm,x:Seq[lpOlTerm]):lpFunctionApp ={
      val ImpArgs = TS0 match {
        case Some((t,s)) => Seq(t,s)
        case None => Seq.empty
      }
      lpFunctionApp(lpConstantTerm(name),Seq(f,g)++x,ImpArgs)
    }
  }

  case object polaritySwitchEqLit extends inferenceRules {

    override def name: String = s"polaritySwitchEqLit"

    // a b : Prf(= [o] (= [o] a b) (= [o] (¬ a) (¬ b)))
    val a = lpOlConstantTerm("a")
    val b = lpOlConstantTerm("b")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, a,b), lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUnaryConnectiveTerm(lpNot,a),lpOlUnaryConnectiveTerm(lpNot,b))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet") //todo: generate depending on number of args

    override def dec: lpDeclaration = lpDeclaration(lpConstantTerm(name), Seq(a,b), ty)

    override def pretty: String = lpDefinition(lpConstantTerm(name), Seq(a,b), ty, proof).pretty

    def instanciate(a: lpOlTerm, b: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(lpConstantTerm(name), Seq(a,b))
    }
  }

  case object polaritySwitchNonEqLit extends inferenceRules {

    override def name: String = s"polaritySwitchNonEqLit"

    // a : Prf(= a (¬ ¬ a))
    val a = lpOlConstantTerm("a")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, a, lpOlUnaryConnectiveTerm(lpNot,lpOlUnaryConnectiveTerm(lpNot,a))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet") //todo: generate depending on number of args

    override def dec: lpDeclaration = lpDeclaration(lpConstantTerm(name), Seq(a), ty)

    override def pretty: String = lpDefinition(lpConstantTerm(name), Seq(a), ty, proof).pretty

    def instanciate(a: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(lpConstantTerm(name), Seq(a))
    }
  }

}
