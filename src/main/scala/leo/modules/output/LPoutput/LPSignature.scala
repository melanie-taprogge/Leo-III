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
  val ExTTenc = "// Definition of the logic and the assumed axioms\n\n///////////////////////////////////////////////////////////////////////////////////////\n////////////////////////////// ExTT AS A LAMBDAPI THEORY //////////////////////////////\n///////////////////////////////////////////////////////////////////////////////////////\n\n// System U definitions and declarations\n\nconstant symbol Prop : TYPE;\n\nsymbol Prf : Prop → TYPE;\n\nconstant symbol ⊤ : Prop;\n\nconstant symbol ⊥ : Prop;\n\nconstant symbol MonoSet : TYPE;\n\ninjective symbol El : MonoSet → TYPE;\n\nconstant symbol ι : MonoSet;\n\nconstant symbol o : MonoSet;\n\nrule El o ↪ Prop;\n\nconstant symbol ¬ : Prop → Prop; notation ¬ prefix 50;\n\nconstant symbol ∧ : Prop → Prop → Prop; notation ∧ infix right 30;\n\nconstant symbol ∨ : Prop → Prop → Prop; notation ∨ infix right 20;\n\nconstant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 10;\n\nconstant symbol ∀ [a : MonoSet] : (El a → Prop) → Prop; notation ∀ quantifier;\n\nconstant symbol ∃ [a : MonoSet] : (El a → Prop) → Prop; notation ∃ quantifier;\n\nconstant symbol ⤳ : MonoSet → MonoSet → MonoSet; notation ⤳ infix right 10;\n\nrule El ($x ⤳ $y) ↪ El $x → El $y;\n\n\n// Additional definitions and declarations\n\nsymbol em x : Prf((x ∨ ¬ x));\n\nsymbol = [T: MonoSet] : El T → El T → Prop; notation = infix right 40;\n\nsymbol propExt x y : (Prf x → Prf y) → (Prf y → Prf x) → Prf (x = y);\n\nsymbol funExt [T S] (f g : (El(T ⤳ S))) x : Prf((f x) = (g x)) → Prf(f = g);\n\n\n// Linking symbols to builtins (for the use of equality tactics)\n\nbuiltin \"P\"     ≔ Prf;\n\nbuiltin \"T\"     ≔ El;\n\nbuiltin \"eq\"    ≔ =;"

  val RwRenc = "///////////////////////////////////////////////////////////////////////////////////////\n////////////////////////////// REWRITE RULES OF THE THEORY ////////////////////////////\n///////////////////////////////////////////////////////////////////////////////////////\n\nrule Prf ⊤ ↪ Π r, Prf r → Prf r;\n\nrule Prf ⊥ ↪ Π r, Prf r;\n\nrule Prf (¬ $p) ↪ Prf $p → Π r, Prf r;\n\nrule Prf ($p ∧ $q) ↪ Π r, (Prf $p → Prf $q → Prf r) → Prf r;\n\nrule Prf ($p ∨ $q) ↪ Π r, (Prf $p → Prf r) → (Prf $q → Prf r) → Prf r;\n\nrule Prf ($x ⇒ $y) ↪ Prf $x → Prf $y;\n\nrule Prf (∀ $p) ↪ Π x, Prf ($p x);\n\nrule Prf (∃ $p) ↪ Π r, (Π x, Prf ($p x) → Prf r) → Prf r;\n\nrule Prf ($x = $y) ↪  Π p , (Prf(p $x) → Prf(p $y));"


}
