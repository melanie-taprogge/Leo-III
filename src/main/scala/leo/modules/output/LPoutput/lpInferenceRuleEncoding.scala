package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.NaturalDeductionRules._

/** Definitions of the Inferences rules of the calculus EP
  *
  * @author Melanie Taprogge
  */

// todo: encode proofs properly

object lpInferenceRuleEncoding {

  abstract class inferenceRules extends lpDefinedRules{

    def usedBasicRules: Set[lpStatement] = Set.empty

  }

  ////////////////////////////////////////////////////////////////
  ////////// Primary Inference Rules
  ////////////////////////////////////////////////////////////////

  case class eqFactoring_script(polarity: Boolean) extends inferenceRules {
    // pos: [T] x y z v : Prf((eq [T] x y) ∨ (eq [T] z v)) → Prf((eq [T] x y) ∨ ¬ (eq [T] x z) ∨ ¬ (eq [T] y v))
    // neg: [T] x y z v : Prf(¬ (eq [T] x y) ∨ ¬ (eq [T] z v)) → Prf(¬ (eq [T] x y) ∨ ¬ (eq [T] x z) ∨ ¬ (eq [T] y v))

    override def name: lpConstantTerm = {
      val pol = if (polarity) "_p" else "_n"
      lpConstantTerm(s"EqFact$pol")
    }

    val T = lpOlUserDefinedPolyType("T")
    val x = lpOlTypedVar(lpOlConstantTerm("x"),T)
    val y = lpOlTypedVar(lpOlConstantTerm("y"),T)
    val z = lpOlTypedVar(lpOlConstantTerm("z"),T)
    val v = lpOlTypedVar(lpOlConstantTerm("v"),T)

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


  ////////////////////////////////////////////////////////////////
  ////////// Extensionality
  ////////////////////////////////////////////////////////////////

  case class funExtPosEq_rev() extends inferenceRules {
    // [T S] f g x : Prf(= (= [S] (f x) (g x)) (= [T ⤳ S] f g))

    override val proofIsDefined = true

    override def name: lpConstantTerm = lpConstantTerm(s"PFE")

    val T = lpOlUserDefinedMonoType("T")
    val S = lpOlUserDefinedMonoType("S")
    val f = lpOlTypedVar(lpOlConstantTerm("f"),lpOlFunctionType(Seq(S,T)))
    val g = lpOlTypedVar(lpOlConstantTerm("g"),lpOlFunctionType(Seq(S,T)))
    val x = lpOlTypedVar(lpOlConstantTerm("x"),S)

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTypedBinaryConnectiveTerm(lpEq,S,lpOlFunctionApp(f,Seq(x)),lpOlFunctionApp(g,Seq(x))),lpOlTypedBinaryConnectiveTerm(lpEq,lpOlFunctionType(Seq(T,S)),f,g)).prf

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptStringProof("assume T S f g x;\n\n    have H1: Prf((f x) = (g x)) → Prf(f = g)\n        {refine (funExt [S] [T] f g) x};\n\n    have H2: Prf((f = g)) → Prf((f x) = (g x))\n        {assume h;\n        refine =def [(S ⤳ T)] f g h (λ y,(y x) = (g x)) (=ref [T] (g x))};\n\n    refine (propExt ((f x) = (g x)) (f = g)) H1 H2;"))) //todo: generate depending on number of args

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


  case class boolExt(lhsNeg: Boolean, polarity: Boolean) extends inferenceRules {
    // lhsNeg encodes weather we want the negation on the lhs

    override val proofIsDefined = true

    override def name: lpConstantTerm = {
      val pol = if (polarity) "P" else "N"
      val category = {
        if (polarity & lhsNeg) "_l"
        else if (polarity & !lhsNeg) "_r"
        else if (!polarity & lhsNeg) "_p"
        else "_n"
      }
      lpConstantTerm(s"${pol}BE$category")
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
        lpProofScript(Seq(lpProofScriptStringProof("assume x y h;\n    refine =def [o] x y h (λ z, z ∨ ¬ y) (em y);")))
      } else if (polarity & lhsNeg) {
        // a b : Prf(eq [↑ o] a b) → Prf(a ∨ (¬ b))
        lpProofScript(Seq(lpProofScriptStringProof("assume x y h1;\n    have em_sym: Prf(¬ y ∨ y)\n        {refine ∨E y (¬ y) (¬ y ∨ y) _ _ (em y)\n            {assume h2;\n            refine ∨Ir (¬ y) y h2}\n            {assume h2;\n            refine ∨Il (¬ y) y h2}};\n    refine =def [o] x y h1 (λ z, ¬ z ∨ y) em_sym;")))
      } else if (!polarity & lhsNeg) {
        // x y: Prf(¬(= [o] x y)) → Prf(x ∨ y)
        lpProofScript(Seq(lpProofScriptStringProof("assume x y h1;\n   \n    refine ∨E x (¬ x) (x ∨ y) _ _ (em x)\n        {assume h2;\n        refine ∨Il x y h2}\n        {assume h2;\n        have yPrf: Prf y\n            {have notNotYprf: Prf (¬ y) → Prf ⊥\n                {assume h3;\n                have xImpY: Prf x → Prf y\n                    {assume h4;\n                    refine ⊥I y (¬E x h4 h2)};\n                have yImpX: Prf y → Prf x\n                    {assume h4;\n                    refine ⊥I x (¬E y h4 h3)};\n                refine (λ u, ¬E (= [o] x y) u h1) (propExt x y xImpY yImpX)};\n            refine npp (y) (¬I (¬ y) notNotYprf)};\n        refine ∨Ir x y yPrf};")))
      } else {
        // x y: Prf(¬(= [o] x y)) → Prf(¬ x ∨ ¬ y)
        lpProofScript(Seq(lpProofScriptStringProof("assume x y h1;\n   \n    refine ∨E x (¬ x) (¬ x ∨ ¬ y) _ _ (em x)\n        {assume h2;\n        have notNotYprf: Prf (y) → Prf ⊥\n            {assume h3;\n            have xImpY: Prf(x) → Prf(y)\n                {assume h4;\n                refine h3};\n            have yImpX: Prf(y) → Prf(x)\n                {assume h4;\n                refine h2};\n            refine (λ u, ¬E (= [o] x y) u h1) (propExt x y xImpY yImpX)};\n        refine ∨Ir (¬ x) (¬ y) (¬I y notNotYprf)}\n        {assume h2;\n        refine ∨Il (¬ x) (¬ y) h2}")))
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


  ////////////////////////////////////////////////////////////////
  ////////// Additional Leo-III Inferences
  ////////////////////////////////////////////////////////////////

  case object polaritySwitchEqLit extends inferenceRules {
    // a b : Prf(= [o] (= [o] a b) (= [o] (¬ a) (¬ b)))

    override def name: lpConstantTerm = lpConstantTerm(s"polaritySwitchEqLit")

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


}
