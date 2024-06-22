package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.LPSignature.{HOLtop, Prf, lpPropExt, oType,lpEm}
import leo.modules.output.LPoutput.calculusEncoding.{nameBottom, nameHypothesis, nameX, nameType}
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.lpUseful._

object lpInferenceRuleEncoding {

  abstract class inferenceRules extends lpDefinedRules{

    def usedBasicRules: Set[lpStatement] = Set.empty

  }


  case class eqFactoring_script(polarity: Boolean) extends inferenceRules {

    // pos: [T] x y z v : Prf((eq [T] x y) ∨ (eq [T] z v)) → Prf((eq [T] x y) ∨ ¬ (eq [T] x z) ∨ ¬ (eq [T] y v))
    // neg: [T] x y z v : Prf(¬ (eq [T] x y) ∨ ¬ (eq [T] z v)) → Prf(¬ (eq [T] x y) ∨ ¬ (eq [T] x z) ∨ ¬ (eq [T] y v))
    override def name: lpConstantTerm = {
      val pol = if (polarity) "Pos" else "Neg"
      lpConstantTerm(s"eqFact$pol")
    }

    //def res(T0, x0, y0, z0, v0):lpOlTerm = {}

    val T = lpOlUserDefinedPolyType("T")
    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")
    val z = lpOlConstantTerm("z")
    val v = lpOlConstantTerm("v")

    override def ty: lpMlType = {
      if (polarity) {
        lpMlFunctionType(Seq(lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlTypedBinaryConnectiveTerm(lpEq,T,x,y),lpOlTypedBinaryConnectiveTerm(lpEq,T,z,v)).prf, lpOlUntypedBinaryConnectiveTerm_multi(lpOr,Seq(lpOlTypedBinaryConnectiveTerm(lpEq,T,x,y),lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,T,x,z)),lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,T,y,v)))).prf))
      } else {
        lpMlFunctionType(Seq(lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,T,x,y)),lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,T,z,v))).prf, lpOlUntypedBinaryConnectiveTerm_multi(lpOr,Seq(lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,T,x,y)),lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,T,x,z)),lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,T,y,v)))).prf))
      }
    }

    override def proof: lpProofScript = throw new Exception("proof for eqFactoring not encoded yet") //todo: generate depending on number of args

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x, y, z, v), ty, Seq(T))

    override def pretty: String = lpDefinition(name, Seq(x, y, z, v), ty, proof, Seq(T)).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, z0: lpOlTerm, v0: lpOlTerm, T0: lpOlPolyType): lpFunctionApp = {
      lpFunctionApp(name, Seq(x0, y0, z0, v0), Seq(T0))
    }

    def result(x0: lpOlTerm, y0: lpOlTerm, z0: lpOlTerm, v0: lpOlTerm, T0: lpOlPolyType): Seq[lpOlTerm] = {
      if (polarity) { //todo: mane both these terms and the rhs of the rule depend on one defined version
        Seq(lpOlTypedBinaryConnectiveTerm(lpEq, T0, x0, y0), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, x0, z0)), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, v0)))
      } else {
        Seq(lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, x0, y0)), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, x0, z0)), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, v0)))
      }
    }

  }


  case class funextPosEq_rev(n: Int = 1) extends inferenceRules {

    override val proofIsDefined = true

    if (n > 1) throw new Exception(s"error encoding funcExt: trying to instanciate rule for more than one arg not encoded yet")
    override def name: lpConstantTerm = lpConstantTerm(s"funextPos$n")

    // [T S] f g x : Prf(= (= [S] (f x) (g x)) (= [T ⤳ S] f g))
    val T = lpOlUserDefinedMonoType("T")
    val S = lpOlUserDefinedMonoType("S")
    val f = lpOlConstantTerm("f")
    val g = lpOlConstantTerm("g")
    val x = lpOlConstantTerm("x") //todo i need n x here
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTypedBinaryConnectiveTerm(lpEq,S,lpOlFunctionApp(f,Seq(x)),lpOlFunctionApp(g,Seq(x))),lpOlTypedBinaryConnectiveTerm(lpEq,lpOlFunctionType(Seq(T,S)),f,g)).prf

    // todo: encode properly and generate variably
    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("this is statically encoded, change that...\n    assume T S f g x;\n\n    have H1: Prf(= [S] (f x) (g x)) → Prf(= [(T ⤳ S)] f g)\n        {refine (funExt [T] [S] f g) x};\n\n    have H2: Prf((= [(T ⤳ S)] f g)) → Prf(= [S] (f x) (g x))\n        {assume h;\n        refine =def [(T ⤳ S)] f g h (λ y, = [S] (y x) (g x)) (=ref [S] (g x))};\n\n    refine (propExt (= [S] (f x) (g x)) (= [(T ⤳ S)] f g)) H1 H2;\n"))) //todo: generate depending on number of args

    override def usedBasicRules: Set[lpStatement] = Set(eqRef(),eqDef())

    override def dec: lpDeclaration = lpDeclaration(name, Seq(f,g,x), ty, Seq(T,S))

    override def pretty: String = lpDefinition(name, Seq(f,g,x), ty, proof, Seq(T,S)).pretty

    def instanciate(TS0:Option[(lpOlPolyType,lpOlPolyType)],f:lpOlTerm,g:lpOlTerm,x:Seq[lpOlTerm]):lpFunctionApp ={
      val ImpArgs = TS0 match {
        case Some((t,s)) => Seq(t,s)
        case None => Seq.empty
      }
      lpFunctionApp(name,Seq(f,g)++x,ImpArgs)
    }
  }

  /*
  case class funextPosEq_proofTerm(n: Int = 1, parameters0:(Int,Int,Int,Int)) extends inferenceRules {

    if (n > 1) throw new Exception(s"error encoding eqFactoring: trying to instanciate rule for more than one arg not encoded yet")

    var parameters = parameters0

    override def name: lpConstantTerm = lpConstantTerm(s"funextPos${n}_proofTerm")

    /*
    // [T S] f g x : Prf(= (= [S] (f x) (g x)) (= [T ⤳ S] f g))
    val T = lpOlUserDefinedPolyType("T")
    val S = lpOlUserDefinedPolyType("S")
    val f = lpOlConstantTerm("f")
    val g = lpOlConstantTerm("g")
    val x = lpOlConstantTerm("x") //todo i need n x here
     */
    val x1 = nameX(1)
    val x2 = nameX(2)
    val x3 = nameX(3)
    val x4 = nameX(4)
    val x5 = nameX(5)
    val h1 = nameHypothesis(1)
    val T1 = nameType(1)
    val T2 = nameType(2)

    // λ T S f g (h1 : Prf (eq [↑ (T ⤳ S)] f g)) a (p : Els (↑ S) → Prop), h1 (λ x, p (x a))
    // Prf(eq [↑ (T ⤳ S)] f g) → Π a , Prf(eq [↑ S] (f a) (g a))
    override def ty: lpMlType = lpMlDependType(Seq(lpUntypedVar(T1),lpUntypedVar(T2),lpUntypedVar(x3),lpUntypedVar(x4)))
      //lpLambdaTerm(Seq(lpUntypedVar(T1),lpUntypedVar(T2),lpUntypedVar(x3),lpUntypedVar(x4),lpTypedVar(h1,lpOlTypedBinaryConnectiveTerm(lpEq,lpOlFunctionType(Seq(T1,T2)),x3,x4).prf),lpUntypedVar(x1),lpTypedVar(x2,T2)),lpOlFunctionApp(lpOlConstantTerm(h1.name),Seq(lpLambdaTerm(Seq(lpUntypedVar(x5)),lpOlFunctionApp(x2,Seq(lpFunctionApp(x5,Seq(x1))))))))

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet") //todo: generate depending on number of args

    override def dec: lpDeclaration = lpDeclaration(name, Seq(f, g, x), ty, Seq(T, S))

    override def pretty: String = lpDefinition(name, Seq(f, g, x), ty, proof, Seq(T, S)).pretty

    def instanciate(TS0: Option[(lpOlPolyType, lpOlPolyType)], f: lpOlTerm, g: lpOlTerm, x: Seq[lpOlTerm]): lpFunctionApp = {
      val ImpArgs = TS0 match {
        case Some((t, s)) => Seq(t, s)
        case None => Seq.empty
      }
      lpFunctionApp(name, Seq(f, g) ++ x, ImpArgs)
    }
  }
*/

  case class boolExt(lhsNeg: Boolean, polarity: Boolean) extends inferenceRules {

    // transform an equality literal of form a=b to either (¬ a ∨ b) or (a ∨ ¬ b)
    // lhs encodes weather we want the negation on the lhs (¬ a ∨ b) or not, then we return the version for the rhs (a ∨ ¬ b)

    override val proofIsDefined = true

    override def name: lpConstantTerm = {
      val pol = if (polarity) "P" else "N"
      val category = {
        if (polarity & lhsNeg) "L"
        else if (polarity & !lhsNeg) "R"
        else if (!polarity & lhsNeg) "P"
        else "N"
      }
      lpConstantTerm(s"boolExt$pol$category")
    }

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")

    override def ty: lpMlType = {
      if (polarity & lhsNeg){
        // a b : Prf(eq [↑ o] a b) → Prf((¬ a) ∨  b)
        lpMlFunctionType(Seq(lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x,y).prf,lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlUnaryConnectiveTerm(lpNot,x),y).prf))
      }else if (polarity & !lhsNeg){
        // a b : Prf(eq [↑ o] a b) → Prf(a ∨ (¬ b))
        lpMlFunctionType(Seq(lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x,y).prf,lpOlUntypedBinaryConnectiveTerm(lpOr,x,lpOlUnaryConnectiveTerm(lpNot,y)).prf))
      }else if (!polarity & lhsNeg){
        // x y: Prf(¬(= [o] x y)) → Prf(x ∨ y)
        lpMlFunctionType(Seq(lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x,y)).prf,lpOlUntypedBinaryConnectiveTerm(lpOr,x,y).prf))
      }else{
        // x y: Prf(¬(= [o] x y)) → Prf(¬ x ∨ ¬ y)
        lpMlFunctionType(Seq(lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x,y)).prf,lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlUnaryConnectiveTerm(lpNot,x),lpOlUnaryConnectiveTerm(lpNot,y)).prf))
      }
    }

    override def proof: lpProofScript = {
      if (polarity & !lhsNeg) {
        lpProofScript(Seq(lpProofScriptCommentLine("this is not properly encoded yet, change that\n    assume x y h;\n    refine =def [o] x y h (λ z, z ∨ ¬ y) (em y);")))
      } else if (polarity & lhsNeg) {
        // a b : Prf(eq [↑ o] a b) → Prf(a ∨ (¬ b))
        lpProofScript(Seq(lpProofScriptCommentLine("this is not properly encoded yet, change that\n    assume x y h1;\n    have em_sym: Prf(¬ y ∨ y)\n        {refine ∨E y (¬ y) (¬ y ∨ y) _ _ (em y)\n            {assume h2;\n            refine ∨Ir (¬ y) y h2}\n            {assume h2;\n            refine ∨Il (¬ y) y h2}};\n    refine =def [o] x y h1 (λ z, ¬ z ∨ y) em_sym;")))
      } else if (!polarity & lhsNeg) {
        // x y: Prf(¬(= [o] x y)) → Prf(x ∨ y)
        lpProofScript(Seq(lpProofScriptCommentLine("this is not properly encoded yet, change that\n    assume x y h1;\n   \n    refine ∨E x (¬ x) (x ∨ y) _ _ (em x)\n        {assume h2;\n        refine ∨Il x y h2}\n        {assume h2;\n        have yPrf: Prf y\n            {have notNotYprf: Prf (¬ y) → Prf ⊥\n                {assume h3;\n                have xImpY: Prf x → Prf y\n                    {assume h4;\n                    refine ⊥I y (¬E x h4 h2)};\n                have yImpX: Prf y → Prf x\n                    {assume h4;\n                    refine ⊥I x (¬E y h4 h3)};\n                refine (λ u, ¬E (= [o] x y) u h1) (propExt x y xImpY yImpX)};\n            refine npp (y) (¬I (¬ y) notNotYprf)};\n        refine ∨Ir x y yPrf};")))
      } else {
        // x y: Prf(¬(= [o] x y)) → Prf(¬ x ∨ ¬ y)
        lpProofScript(Seq(lpProofScriptCommentLine("this is not properly encoded yet, change that\n    assume x y h1;\n   \n    refine ∨E x (¬ x) (¬ x ∨ ¬ y) _ _ (em x)\n        {assume h2;\n        have notNotYprf: Prf (y) → Prf ⊥\n            {assume h3;\n            have xImpY: Prf(x) → Prf(y)\n                {assume h4;\n                refine h3};\n            have yImpX: Prf(y) → Prf(x)\n                {assume h4;\n                refine h2};\n            refine (λ u, ¬E (= [o] x y) u h1) (propExt x y xImpY yImpX)};\n        refine ∨Ir (¬ x) (¬ y) (¬I y notNotYprf)}\n        {assume h2;\n        refine ∨Il (¬ x) (¬ y) h2}")))
      }
    }

    override def usedBasicRules: Set[lpStatement] = {
      if (polarity & !lhsNeg) {
        Set(eqDef(),lpEm)
      } else if (polarity & lhsNeg) {
        Set(eqDef(),lpEm, orE(),orIr(),orIl())
      } else if (!polarity & lhsNeg) {
        Set(lpEm, orE(),orIr(),orIl())
      } else {
        Set(lpEm, orE(),orIr(),orIl())
      }
    }
    override def dec: lpDeclaration = lpDeclaration(name, Seq(x,y), ty)

    override def pretty: String = lpDefinition(name, Seq(x,y), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(x0,y0))
    }
  }

  case object polaritySwitchEqLit extends inferenceRules {

    override def name: lpConstantTerm = lpConstantTerm(s"polaritySwitchEqLit")

    // a b : Prf(= [o] (= [o] a b) (= [o] (¬ a) (¬ b)))
    val a = lpOlConstantTerm("a")
    val b = lpOlConstantTerm("b")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, a,b), lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUnaryConnectiveTerm(lpNot,a),lpOlUnaryConnectiveTerm(lpNot,b))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet") //todo: generate depending on number of args

    override def dec: lpDeclaration = lpDeclaration(name, Seq(a,b), ty)

    override def pretty: String = lpDefinition(name, Seq(a,b), ty, proof).pretty

    def instanciate(a: lpOlTerm, b: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(a,b))
    }
  }

  case object polaritySwitchNonEqLit extends inferenceRules {

    override def name: lpConstantTerm = lpConstantTerm(s"polaritySwitchNonEqLit")

    // a : Prf(= a (¬ ¬ a))
    val a = lpOlConstantTerm("a")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, a, lpOlUnaryConnectiveTerm(lpNot,lpOlUnaryConnectiveTerm(lpNot,a))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet") //todo: generate depending on number of args

    override def dec: lpDeclaration = lpDeclaration(name, Seq(a), ty)

    override def pretty: String = lpDefinition(name, Seq(a), ty, proof).pretty

    def instanciate(a: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(a))
    }
  }

}
