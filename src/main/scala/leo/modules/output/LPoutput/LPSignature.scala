package leo.modules.output.LPoutput

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

  val tptpDefinedTypeMap: Map[String, String] = Map(
    "$o" -> oType,
    "$i" -> iType)

  val tptpDefinedSymbolMap: Map[String, String] = Map(
    "$false" -> HOLbot,
    "$true" -> HOLtop)


}
