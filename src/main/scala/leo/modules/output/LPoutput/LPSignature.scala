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

  case object lpPropExt extends lpAxioms {
    override def name: lpConstantTerm = lpConstantTerm("propExt")

    // Π x: Els (↑ o), Π y: Els (↑ o), (Prf x → Prf y) → (Prf y → Prf x) → Prf (eq x y)
    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"), lpOtype.lift2Meta),lpTypedVar(lpConstantTerm("y"), lpOtype.lift2Meta)), lpMlFunctionType(Seq(lpMlFunctionType(Seq(lpOlConstantTerm("x").prf,lpOlConstantTerm("y").prf)),lpMlFunctionType(Seq(lpOlConstantTerm("y").prf,lpOlConstantTerm("x").prf)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlConstantTerm("x"),lpOlConstantTerm("y")).prf)))

    override def pretty: String = lpDeclaration(lpPropExt.name, Seq.empty, lpPropExt.ty).pretty
  }

  // todo: properly encode this using the datastructures
  val ExTTenc = "require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq;\n\n// some basic notions\nsymbol o : Set;\nsymbol ι : Set;\nrule τ o ↪ Prop;\nrule τ ($s × $t) ↪ τ $s → τ $t;\n\nsymbol propExt x y : (π x → π y) → (π y → π x) → π (x = y);\nsymbol funExt [T S] (f g : (τ (T × S))) : π(∀(λ x, (f x) = (g x))) → π(f = g);\n\nsymbol em x : π((x ∨ ¬ x));\n\nopaque symbol npp x : π(¬ ¬ x) → π x ≔\nbegin\n    assume x h1;\n    refine ∨ₑ (em x) _ _\n        {assume h2;\n        refine h2}\n        {assume h2;\n        refine ⊥ₑ (h1 h2)}\nend;"

  val RwRenc = "///////////////////////////////////////////////////////////////////////////////////////\n////////////////////////////// REWRITE RULES OF THE THEORY ////////////////////////////\n///////////////////////////////////////////////////////////////////////////////////////\n\nrule Prf ⊤ ↪ Π r, Prf r → Prf r;\n\nrule Prf ⊥ ↪ Π r, Prf r;\n\nrule Prf (¬ $p) ↪ Prf $p → Π r, Prf r;\n\nrule Prf ($p ∧ $q) ↪ Π r, (Prf $p → Prf $q → Prf r) → Prf r;\n\nrule Prf ($p ∨ $q) ↪ Π r, (Prf $p → Prf r) → (Prf $q → Prf r) → Prf r;\n\nrule Prf ($x ⇒ $y) ↪ Prf $x → Prf $y;\n\nrule Prf (∀ $p) ↪ Π x, Prf ($p x);\n\nrule Prf (∃ $p) ↪ Π r, (Π x, Prf ($p x) → Prf r) → Prf r;\n\nrule Prf ($x = $y) ↪  Π p , (Prf(p $x) → Prf(p $y));"


}
