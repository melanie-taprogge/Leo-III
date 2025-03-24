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
}
