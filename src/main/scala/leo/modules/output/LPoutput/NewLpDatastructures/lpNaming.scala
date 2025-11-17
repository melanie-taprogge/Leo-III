package leo.modules.output.LPoutput.NewLpDatastructures

import leo.modules.output.LPoutput

object Prefixes {
  val sigPrefix = Some(Prefix(Name("S")))
  val formulaeFilePrefix = Some(Prefix(Name("F")))
}

object lpEncSig {
  val prfStr = "π"
  val elStr = "τ"
  val oTyStr = "o"
  val iTyStr = "ι"
  val tyConStr = "⤳"
  val topStr = "⊤"
  val botStr = "⊥"
  val negStr = "¬"
  val andStr = "∧"
  val orStr = "∨"
  val impStr = "⇒"
  val eqStr = "="
  val forAllStr = "∀"
  val exStr = "∃"
  val witnessStr = "el"
  val choiceStr = "ε"

  val allAscii = Seq(oTyStr, witnessStr)
}

object tptpRepSig {
  val tptpIntStr = "tptp_int"

  val allAscii = Seq(tptpIntStr)
}

object lpSysStrings {

  val lpKeywords = Set(
    "require", "open", "symbol", "notation", "builtin", "opaque",
    "rule", "unif_rule", "coerce_rule", "inductive", "proof",
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

  val reserve = lpKeywords ++ lpEncSig.allAscii ++ tptpRepSig.allAscii ++ LPoutput.lpKeywords //todo: the latter is only necessary for compatibility with old DS, delete once fully migrated

  val lpAllowedRegEx = """^[^\t\r\n :,;`(){}\[\]".@$|?/]+$"""
}
/*
object tptpNames {
  val tptpDefinedSymbolMap: Map[String, String] = Map(
    "$false" -> lpEncSig.topStr,
    "$true" -> lpEncSig.botStr)
}


  private def termId2Qn(i : Int, sig: Signature):QName = {
    val origName: String = sig(i).name
    // skolem symbols are always local
    val prfx = if (isPropSet(Signature.PropSkolemConstant, sig(i).flag)) None else sigPrefix
    val symbol = tptpDefinedSymbolMap.getOrElse(origName, NameAllocator.safe(origName,sig))
    QName(prfx,Name(symbol))
  }

  private def tyId2Qn(i: Int, sig: Signature): QName = {
    val origName: String = sig(i).name
    val symbol = tptpDefinedSymbolMap.getOrElse(origName, lpEscapeName(origName, sig))
    QName(sigPrefix, Name(symbol))
  }

   */



