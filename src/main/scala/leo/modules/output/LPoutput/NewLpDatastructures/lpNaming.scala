package leo.modules.output.LPoutput.NewLpDatastructures

import leo.modules.output.LPoutput
import leo.modules.output.LPoutput.LpLibs.ND

//////////////////////////////////////////
// Utility for determining weather a name is not safe to use
// - Defines the Strings used in the standard library
// - Defines a list of all Lambdapi Keywords
// - Defines a RegEx for all forbidden Strings
//////////////////////////////////////////

/** Stirngs used in the Lambdapi Standard Library to represent object-logics*/
object lpEncSig {
  // ** Propositions as types
  val prfStr = "π"
  val elStr = "τ"
  // ** Standard Library Types
  val oTyStr = "o"
  val iTyStr = "ι"
  val tyConStr = "⤳"
  // ** Standard Library Propositional Constants
  val topStr = "⊤"
  val botStr = "⊥"
  val negStr = "¬"
  val andStr = "∧"
  val orStr = "∨"
  val impStr = "⇒"
  val eqStr = "="
  // ** Standard Library Binders
  val forAllStr = "∀"
  val exStr = "∃"
  val choiceStr = "ε"

  // ** Symbols encoded by new constants
  val tptpIntStr = "tptp_int"
  val tptpRationalStr = "tptp_rat"
  val tptpRealStr = "tptp_real"

  val tptpLessStr = "tptp_less"
  val tptpLessEqStr = "tptp_lesseq"
  val tptpGreaterStr = "tptp_greater"
  val tptpGreaterEqStr = "tptp_greatereq"
  val tptpUnaryMinusStr = "tptp_uminus"
  val tptpSumStr = "tptp_sum"
  val tptpDifferenceStr = "tptp_difference"
  val tptpProductStr = "tptp_product"
  val tptpQuotientStr = "tptp_quotient"

  val tptpArithmeticAscii: Seq[String] = Seq(
    tptpIntStr, tptpRationalStr, tptpRealStr,
    tptpLessStr, tptpLessEqStr, tptpGreaterStr, tptpGreaterEqStr,
    tptpUnaryMinusStr, tptpSumStr, tptpDifferenceStr, tptpProductStr, tptpQuotientStr
  )

  val allAscii: Seq[String] = Seq(oTyStr, eqStr) ++ tptpArithmeticAscii
}


/** All of the strings used as keywords etc. in Lambdapi */
object lpSysStrings {

  // todo: just like the logic names, define these as meta-values and call on them from printing
  private val lpKeywords = Set(
    "require", "open", "symbol", "notation", "builtin", "opaque",
    "rule", "off", "unif_rule", "coerce_rule", "inductive", "proof",
    "assume", "apply", "refine", "simplify", "rewrite", "have",
    "print", "proofterm", "assert", "assertnot", "compute",
    "constant", "injective", "commutative", "associative",
    "in", "notation", "reflexivity", "admit", "right", "left",
    "induction", "focus", "generalize", "orelse", "remove",
    "repeat", "set", "solve", "symmetry", "try", "why3", "with",
    "abort", "admitted", "fail", "search", "type", "as", "begin",
    "debug", "end", "flag", "infix", "off", "on", "postfix",
    "prefix", "private", "protected", "prover", "prover_timeout",
    "quantifier", "sequential", "TYPE"
  )

  /** All of the strings that may not be used as symbol names in the encoded problem and proof */
  val reserve: Set[String] = lpKeywords ++ lpEncSig.allAscii ++ ND.Names.allAscii ++ LPoutput.lpKeywords //todo: the latter is only necessary for compatibility with old DS, delete once fully migrated

  /** Regular expression matching all symbols that syntactically are not allowed in Lambdapi */
  val lpAllowedRegEx = """^[^\t\r\n :,;`(){}\[\]".@$|?/]+$"""
  // todo: also make sure the symbols do not include any occurrences of the pre-and postfixes used in LP to encode the forbidden names
}


//////////////////////////////////////////
// Utility for generating names
//////////////////////////////////////////

/** Generate uniform names for classes of Lambdapi symbols */
object nameGeneration {
  /** Generate Lambdapi names for encoded integers */
  @inline def nameInt(n:BigInt) : String = s"int_$n"

  /** Generate Lambdapi names for encoded rational numbers */
  def nameRational(n0: BigInt, n1: BigInt): String = s"rat_${n0}_$n1"

  /** Generate Lambdapi names for encoded real numbers */
  def nameReal(n0: BigInt, n1: BigInt , n2: BigInt): String = s"real_${n0}_${n1}_$n2"
}



