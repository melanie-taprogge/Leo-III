package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.LPoutput.lpDatastructures._
//import leo.modules.output.LPoutput.NaturalDeductionRules._

/** Definitions of the Inferences rules of the calculus EP
  *
  * @author Melanie Taprogge
  */

// todo: encode proofs properly

object lpInferenceRuleEncoding {

  abstract class inferenceRules extends lpDefinedRules{

    // def usedBasicRules: Set[lpStatement] = Set.empty

  }

  ////////////////////////////////////////////////////////////////
  ////////// Primary Inference Rules
  ////////////////////////////////////////////////////////////////

  case class eqFactoring_script(polarity: Boolean) extends inferenceRules {
    // pos: [T : Set] (x y z v : τ T): ((π ((x = y) ∨ (z = v))) → (π ((x = y) ∨ (¬ (x = z)) ∨ (¬ (y = v)))))
    // neg: [T] x y z v: ((π ((¬ (x = y)) ∨ (¬ (z = v)))) → (π ((¬ (x = y)) ∨ (¬ (x = z)) ∨ (¬ (y = v)))))

    override val proofIsDefined = true

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

    override def proof: lpProofScript = {
      if (polarity) {
        lpProofScript(Seq(lpProofScriptStringProof("assume T x y z v h1;\n    refine (∨ₑ (em (x = y)) _ _ ) \n                {assume h2;\n                type ∨ᵢ₁ [x = y] [¬ (x = z)] h2;\n                refine (∨ᵢ₁ h2)}\n                {assume h3;\n                refine ∨ₑ (em (x = z)) _ _ \n                    {assume h4;\n                    refine ∨ₑ (em (y = v)) _ _ \n                        {assume h5;\n                        have H1: π (z = v)\n                            {refine ∨ₑ h1 _ _\n                                {assume h6;\n                                refine ⊥ₑ (h3 h6)}\n                                {assume h7;\n                                refine h7}};\n                        have H2: π(x = v)\n                            {refine ind_eq h4 (λ a, (a = v)) H1};\n                        have H3: π(v = y)\n                            {refine ind_eq h5 (λ a, (v = a)) (eq_refl [T] v)};\n                        have H4: π(x = y)\n                            {refine ind_eq H2 (λ a, (a = y)) H3};\n                        refine ⊥ₑ (h3 H4)}\n                        {assume h8;\n                        refine ∨ᵢ₂ (∨ᵢ₂ h8)}}\n                    {assume h9;\n                    refine ∨ᵢ₂ (∨ᵢ₁ h9)}}")))
      } else {
        lpProofScript(Seq(lpProofScriptStringProof("assume T x y z v h1;\n    refine (∨ₑ (em (x = y)) _ _ )\n                {assume h3;\n                refine (∨ₑ (em (x = z)) _ _ ) \n                    {assume h4;\n                    refine (∨ₑ (em (y = v)) _ _ )\n                        {assume h5;\n                        have H1: π(z = x)\n                            {refine ind_eq h4 (λ a, (z = a)) (eq_refl [T] z)};\n                        have H2: π(z = y)\n                            {refine ind_eq H1 (λ a, (a = y)) h3};\n                        have H3: π( ¬ (z = v))\n                            {refine ∨ₑ h1 _ _\n                                {assume h6;\n                                refine ⊥ₑ (h6 h3)}\n                                {assume h6;\n                                refine h6}};\n                        have H4: π(z = v)\n                            {refine ind_eq  H2 (λ a, (a = v)) h5};\n                        refine ⊥ₑ (H3 H4)}\n                        {assume h6;\n                        refine ∨ᵢ₂ (∨ᵢ₂ h6)}}\n                    {assume h4;\n                    refine ∨ᵢ₂ (∨ᵢ₁  h4)}}\n                {assume h3;\n                refine ∨ᵢ₁ h3}")))
      }
    }

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
    // [T] [S] (f : (τ (S × T))) (g : (τ (S × T))) (x : (τ S)): ((π (f = g)) → (π ((f x) = (g x))))

    override val proofIsDefined = true

    override def name: lpConstantTerm = lpConstantTerm(s"PFE")

    val T = lpOlUserDefinedMonoType("T")
    val S = lpOlUserDefinedMonoType("S")
    val f = lpOlTypedVar(lpOlConstantTerm("f"),lpOlFunctionType(Seq(S,T)))
    val g = lpOlTypedVar(lpOlConstantTerm("g"),lpOlFunctionType(Seq(S,T)))
    val x = lpOlTypedVar(lpOlConstantTerm("x"),S)

    override def ty: lpMlType = lpMlFunctionType(Seq(lpOlTypedBinaryConnectiveTerm(lpEq,lpOlFunctionType(Seq(T,S)),f,g).prf,lpOlTypedBinaryConnectiveTerm(lpEq,S,lpOlFunctionApp(f,Seq(x)),lpOlFunctionApp(g,Seq(x))).prf))

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptStringProof("assume T S f g x h;\n    refine ind_eq h (λ y, (y x) = (g x)) (eq_refl [T] (g x))"))) //todo: generate depending on number of args

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
        // x y: π(x = y) → π((¬ x) ∨ y)
        lpMlFunctionType(Seq(lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x,y).prf,lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlUnaryConnectiveTerm(lpNot,x),y).prf))
      }else if (polarity & !lhsNeg){
        // x y: π(x = y) → π(x ∨ (¬ y))
        lpMlFunctionType(Seq(lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x,y).prf,lpOlUntypedBinaryConnectiveTerm(lpOr,x,lpOlUnaryConnectiveTerm(lpNot,y)).prf))
      }else if (!polarity & lhsNeg){
        // x y: π(¬(x = y)) → π(x ∨ y)
        lpMlFunctionType(Seq(lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x,y)).prf,lpOlUntypedBinaryConnectiveTerm(lpOr,x,y).prf))
      }else{
        // x y: π(¬(x = y)) → π(¬ x ∨ ¬ y)
        lpMlFunctionType(Seq(lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x,y)).prf,lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlUnaryConnectiveTerm(lpNot,x),lpOlUnaryConnectiveTerm(lpNot,y)).prf))
      }
    }

    override def proof: lpProofScript = {
      if (polarity & !lhsNeg) {
        lpProofScript(Seq(lpProofScriptStringProof("assume x y h;\n    refine ind_eq h (λ z, z ∨ ¬ y) (em y);")))
      } else if (polarity & lhsNeg) {
        lpProofScript(Seq(lpProofScriptStringProof("assume x y h;\n    have em_sym: π(¬ y ∨ y)\n        {refine ∨ₑ(em y)  _ _ \n            {assume h2;\n            refine ∨ᵢ₂ h2}\n            {assume h2;\n            refine ∨ᵢ₁ h2}};\n    refine ind_eq h (λ z, ¬ z ∨ y) em_sym;")))
      } else if (!polarity & lhsNeg) {
        lpProofScript(Seq(lpProofScriptStringProof("assume x y h1;\n    refine ∨ₑ (em x) _ _\n        {assume h2;\n        refine ∨ᵢ₁ h2}\n        {assume h2;\n        have H1: π y\n            {have H2: π (¬ y) → π ⊥\n                {assume h3;\n                have H3: π x → π y\n                    {assume h4;\n                    refine ⊥ₑ (h2 h4)};\n                have H4: π y → π x\n                    {assume h4;\n                    refine ⊥ₑ (h3 h4)};\n                refine h1 (propExt x y H3 H4)};\n            refine npp (y) H2};\n        refine ∨ᵢ₂ H1};")))
      } else {
        lpProofScript(Seq(lpProofScriptStringProof("assume x y h1;\n    refine ∨ₑ (em x) _ _\n        {assume h2;\n        have H1: π (y) → π ⊥\n            {assume h3;\n            have H2: π(x) → π(y)\n                {assume h4;\n                refine h3};\n            have H3: π(y) → π(x)\n                {assume h4;\n                refine h2};\n            refine h1 (propExt x y H2 H3)};\n        refine ∨ᵢ₂ H1}\n        {assume h2;\n        refine ∨ᵢ₁ h2}")))
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
    // in non eq case, we use simp 17, for equational case this is encoded
    // todo: update to standard library
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
