package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._

object LPSignature {

  // define the elements of the logic definition we will need to encode the problem

  val Prf: String = "Prf"
  val lor: String = "∨"
  val land: String = "∧"
  val HOLimpl: String = "⇒"
  val uparrow: String = "↑"
  val Els: String = "Els"
  val Scheme: String = "Scheme"
  val HOLtop: String = "⊤"
  val HOLbot: String = "⊥"
  val Prop: String = "Prop"
  val lnot: String = "¬"                      //
  val equ: String = "eq"
  val inEqu: String = "inEq"
  val oType: String = "o"
  val iType: String = "ι"
  val HOLarrow: String = "⤳"
  val variableIdentifier: String = "$"
  val ruleArrow: String = "↪"
  val metaType: String = "TYPE"
  val typeOfTptptTypes: String = "Set"
  val rightarrow: String = "→"
  val LPlambda: String = "λ"
  val Pi: String = "Π"
  val objectExists: String = "∃"
  val objectForAll: String = "∀"
  val colonEq: String = "≔"

  // axioms
  val npp_name: String = "npp"
  val npp_ax: String = s"symbol $npp_name : $Pi x: $Els($uparrow $oType), $Prf ($lnot ($lnot x)) $rightarrow $Prf x;"
  val propExt_name: String = "propExt"
  abstract class lpAxioms extends lpTerm{
    def name: lpConstantTerm
    def ty: lpMlType
  }
  case object lpNpp extends lpAxioms{
    override def name: lpConstantTerm = lpConstantTerm("npp")
    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"),lpOtype.lift2Meta)),lpMlFunctionType(Seq(lpOlUnaryConnectiveTerm(lpNot,lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm("x"))).prf,lpOlConstantTerm("x").prf)))
    override def pretty: String = lpDeclaration(lpNpp.name,Seq.empty,lpNpp.ty).pretty
  }

  case object lpEm extends lpAxioms{
    override def name: lpConstantTerm = lpConstantTerm("em")
    //  Π x: Prop, Prf (x ∨ ¬ x)
    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"),lpOtype.lift2Meta)),lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlConstantTerm("x"),lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm("x"))).prf)
    override def pretty: String = lpDeclaration(lpEm.name,Seq.empty,lpEm.ty).pretty
  }

  case object lpPropExt extends lpAxioms {
    override def name: lpConstantTerm = lpConstantTerm("propExt")

    //                                                                                                                Π x: Els (↑ o), Π y: Els (↑ o), (Prf x → Prf y) → (Prf y → Prf x) → Prf (eq x y)
    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"), lpOtype.lift2Meta),lpTypedVar(lpConstantTerm("y"), lpOtype.lift2Meta)), lpMlFunctionType(Seq(lpMlFunctionType(Seq(lpOlConstantTerm("x").prf,lpOlConstantTerm("y").prf)),lpMlFunctionType(Seq(lpOlConstantTerm("y").prf,lpOlConstantTerm("x").prf)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlConstantTerm("x"),lpOlConstantTerm("y")).prf)))

    override def pretty: String = lpDeclaration(lpPropExt.name, Seq.empty, lpPropExt.ty).pretty
  }




}
