package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._

object LPSignature {

  abstract class lpAxioms extends lpTerm{
    def name: lpConstantTerm
    def ty: lpMlType
  }

  case object lpEm extends lpAxioms{
    //  Π x: Prop, Prf (x ∨ ¬ x)
    override def name: lpConstantTerm = lpConstantTerm("em")
    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"),lpOtype.lift2Meta)),lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlConstantTerm("x"),lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm("x"))).prf)
    override def pretty: String = lpDeclaration(lpEm.name,Seq.empty,lpEm.ty).pretty
  }

  abstract class lpTheorems extends lpTerm {
    def name: lpConstantTerm
    override def pretty: String = name.pretty
  }

  object lpTheorems {
    case object eqImp extends lpTheorems {
      override def name: lpConstantTerm = lpConstantTerm("=⇒")
    }
  }

  case object lpDne extends lpAxioms {
    // symbol dne x : π(¬ ¬ x) → π x
    // todo: add proof encoding
    override def name: lpConstantTerm = lpConstantTerm("¬¬ₑ")

    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"), lpOtype.lift2Meta)),lpMlFunctionType(Seq(lpOlUnaryConnectiveTerm(lpNot,lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm("x"))).prf,lpOlConstantTerm("x").prf)))

    override def pretty: String = lpDeclaration(lpDne.name, Seq.empty, lpDne.ty).pretty
  }

  case object lpPropExt extends lpAxioms {
    override def name: lpConstantTerm = lpConstantTerm("propExt")

    // Π x: Els (↑ o), Π y: Els (↑ o), (Prf x → Prf y) → (Prf y → Prf x) → Prf (eq x y)
    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"), lpOtype.lift2Meta),lpTypedVar(lpConstantTerm("y"), lpOtype.lift2Meta)), lpMlFunctionType(Seq(lpMlFunctionType(Seq(lpOlConstantTerm("x").prf,lpOlConstantTerm("y").prf)),lpMlFunctionType(Seq(lpOlConstantTerm("y").prf,lpOlConstantTerm("x").prf)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlConstantTerm("x"),lpOlConstantTerm("y")).prf)))

    override def pretty: String = lpDeclaration(lpPropExt.name, Seq.empty, lpPropExt.ty).pretty
  }

  val cnfLib: String = "require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt Stdlib.PropExt Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Epsilon Leo-III-lambdapi-lib.EPrules Leo-III-lambdapi-lib.SimpTactic Leo-III-lambdapi-lib.MetaTheorems;\n\n/******************************************************************************\n *  Classical Quantifier De Morgan\n ******************************************************************************/\n\n opaque symbol ¬∀=∃¬ (t : Set) (p : τ (t ⤳ o)) : //lemma6\n π (¬(∀ p) = (`∃ (x : τ t), ¬ (p x)))≔\nbegin\n assume t p;\n refine propExt (¬ (∀ p)) (`∃ x, ¬ (p x)) _ _\n {assume h;\n     refine ∨ₑ (em (`∃ x, ¬ p x)) _ _\n     {assume he; refine he}\n     {assume hne;\n         have forall_p : Π x : τ t, π (p x)\n             {assume a; refine ¬¬ₑ (p a) (λ hp, hne (∃ᵢ [t] [λ y, ¬ p y] a hp))};\n         refine ⊥ₑ (h (λ a, forall_p a))}}\n {assume h h2;\n     refine ∃ₑ [t] [λ y, ¬ p y] h (λ a hna, hna (h2 a))}\nend;\n\nopaque symbol ¬∃=∀¬ (t : Set) (p : τ (t ⤳ o)) : // lemma7\n π (¬(∃ p) = (`∀ (x : τ t), ¬ p x))≔     \nbegin\n assume t p;\n refine propExt (¬ (∃ p)) (`∀ x, ¬ p x) _ _\n {assume h a ha; refine h (∃ᵢ [t] [p] a ha)}\n {assume h1 h2; refine ∃ₑ [t] [p] h2 (λ a ha, (h1 a) ha)}\nend;\n\n/******************************************************************************\n*  Skolemisazion\n******************************************************************************/\n\nopaque symbol εᵢ_rev :  Π [a: Set], Π p: (τ a → Prop),  π (p (ε p)) → π (∃ p)≔\nbegin\n assume a p h;\n refine ∃ᵢ [a] [p] (ε p) h\nend;\n\nopaque symbol ∃_skolem (a: Set) (p: τ a → Prop) :  \n π ((∃ p) = (p (ε p)))≔\nbegin\n assume a p;\n refine propExt (∃ p) (p (ε p)) (εᵢ [a] p) (εᵢ_rev [a] p)\nend;\n\nopaque symbol ∀_skolem (a: Set) (p: τ a → Prop) :  \n π (¬ (∀ p) = ¬ (p (ε (λ x, ¬ (p x)))))≔\nbegin\n assume a p;\n rewrite ¬∀=∃¬;\n refine  propExt (`∃ x, ¬ (p x)) (¬ (p (ε (λ x, ¬ (p x))))) _ _\n     {assume h; refine ind_eq (eq_sym (∃_skolem a (λ x, ¬ (p x)))) (λ x, x) h}\n     {assume h; refine ind_eq (∃_skolem a (λ x, ¬ (p x))) (λ x, x) h}\nend;\n\n\n/******************************************************************************\n *  Quantifier Distributivity\n ******************************************************************************/\n\n opaque symbol ∀∧_dist_r t a (p : τ(t ⤳ o)): π ((a ∧ ∀ p) = (`∀ x, a ∧ p x))≔\n begin\n     assume t a p;\n     refine propExt (a ∧ ∀ p) (∀(λ x, a ∧ p x)) _ _\n         {assume h x;\n         refine ∧ᵢ (∧ₑ₁ h) ((∧ₑ₂ h) x)}\n         {assume h;\n         refine ∨ₑ (em (∀ p)) _ _\n             {assume h1;\n             refine ∧ᵢ (∧ₑ₁ (h (el t))) h1}\n             {assume h1;\n             have H0: π (¬ (p (ε (λ x, ¬ (p x)))))\n                 {refine =⇒ (∀_skolem t p) h1};\n             have H1: π (p (ε (λ x, ¬ (p x))))\n                 {refine ∧ₑ₂ (h (ε (λ x, ¬ (p x))))};\n             refine ⊥ₑ (H0 H1)}}\n end;\n \n opaque symbol ∀∧_dist_l t a (p : τ(t ⤳ o)): π ((∀ p ∧ a) = (`∀ x,p x ∧ a))≔\n begin\n     assume t a p;\n     refine propExt (∀ p ∧ a) (`∀ x, p x ∧ a) _ _\n         {assume h0 x;\n         rewrite ∧_com;\n         refine (=⇒ ((∀∧_dist_r t a p)) (=⇒ (∧_com (∀ p) a) h0)) x\n         }\n         {assume h0;\n         rewrite ∧_com;\n         have H0: π (`∀ x, a ∧ p x)\n             {assume x;\n             rewrite ∧_com;\n             refine h0 x};\n         refine =⇒ (eq_sym (∀∧_dist_r t a p)) H0\n         };\n end;\n \n opaque symbol ∀∨_dist_r t a (p : τ(t ⤳ o)): π ((a ∨ ∀ p) = (`∀ x, a ∨ p x))≔\n begin\n     assume t a p;\n     refine propExt (a ∨ ∀ p) (∀(λ x, a ∨ p x)) _ _\n         {assume h x;\n         refine ∨ₑ h _ _\n             {assume h0;\n             refine ∨ᵢ₁ h0}\n             {assume h0;\n             refine ∨ᵢ₂ (h0 x)}}\n         {assume h;\n         refine ∨ₑ (em (∀ p)) _ _\n             {assume h1;\n             refine ∨ᵢ₂ h1}\n             {assume h1;\n             have H0: π (¬ (p (ε (λ x, ¬ (p x)))))\n                 {refine =⇒ (∀_skolem t p) h1};\n             refine ∨ₑ (h (ε (λ x, ¬ (p x)))) _ _\n                 {assume h0;\n                 refine ∨ᵢ₁ h0}\n                 {assume h0;\n                 refine ⊥ₑ (H0 h0)}}}\n end;\n \n opaque symbol ∀∨_dist_l t a (p : τ(t ⤳ o)): π ((∀ p ∨ a) = (`∀ x,p x ∨ a))≔\n begin\n     assume t a p;\n     refine propExt (∀ p ∨ a) (`∀ x,p x ∨ a) _ _\n         {assume h0 x;\n         rewrite ∨_com;\n         refine (=⇒ ((∀∨_dist_r t a p)) (=⇒ (∨_com (∀ p) a) h0)) x}\n         {assume h0;\n         rewrite ∨_com;\n         have H0: π (`∀ x, a ∨ p x)\n             {assume x;\n             rewrite ∨_com;\n             refine h0 x};\n         refine =⇒ (eq_sym (∀∨_dist_r t a p)) H0};\n end;\n \n opaque symbol ∀_ext [t: Set] p q : π(`∀ (x : τ t), p x = q x) → π ((`∀ (x: τ t), p x) = (`∀ (x: τ t), q x))≔\n begin\n     assume t p q h;\n     refine propExt (`∀ (x: τ t), p x) (`∀ (x: τ t), q x) _ _\n         {assume h1 x;\n         refine =⇒ (h x) (h1 x)}\n         {assume h1 x;\n         refine =⇒ (eq_sym (h x)) (h1 x)}\n end;"

}
