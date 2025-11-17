package leo.modules.output.LPoutput.NewLpDatastructures

import leo.datastructures.{Signature, isPropSet}
import leo.datastructures.Signature.Key
import leo.modules.HOLSignature
import leo.modules.HOLSignature._
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
import leo.modules.output.LPoutput.NewLpDatastructures.tptpRepSig.tptpIntStr

/*
val leoBaseTy = Map[Signature.Key,](
  oKey -> OlType.O,
  iKey -> OlType.I)

 */

object tptpConstMappings {

  val leoBaseTy = Map[Signature.Key,QName](
    HOLSignature.oKey -> QName.local(oTyStr),
    HOLSignature.iKey -> QName.local(iTyStr),
    HOLSignature.intKey -> QName.in(Prefixes.sigPrefix.get,tptpIntStr))


  val leoTopBot = Map[Signature.Key, QName](LitTrue.key -> QName.local(topStr),
    HOLSignature.LitFalse.key -> QName.local(botStr))

  val leoTypedConnectives = Map[Signature.Key, QName](
    HOLSignature.===.key -> QName.local(eqStr)
  )

  val leoBinders = Map[Signature.Key, QName](
    HOLSignature.Forall.key -> QName.local(forAllStr),
    HOLSignature.Exists.key -> QName.local(exStr)
  )

  val leoUntypedConnectives = Map[Signature.Key, QName](
    HOLSignature.|||.key -> QName.local(orStr),
    HOLSignature.&.key -> QName.local(andStr),
    HOLSignature.Impl.key -> QName.local(impStr),
    HOLSignature.Not.key -> QName.local(negStr),
    HOLSignature.Impl.key -> QName.local(impStr)
  )//todo: also include the special cases and then build lambda terms for them?

  val leoDefinedConstants = Seq(!===.key)

  val LeoConstants: Map[Signature.Key, QName] = leoTopBot ++ leoTypedConnectives ++ leoUntypedConnectives ++ leoBinders

}
final case class LpSig(
                        orig: Signature,
                        termNames: Map[Key, QName],
                        typeNames: Map[Key, QName],
                        reserved: Set[String]
                      )

object LpSigBuilder {

  private def escapeIfNeeded(raw: String): String =
    if (raw.matches(lpSysStrings.lpAllowedRegEx)) raw
    else s"{|$raw|}"

  private def avails(base0: String, reserved: collection.mutable.Set[String]): String = {
    val base = escapeIfNeeded(base0)
    if (!reserved(base)) { base }
    else {
      val fresh = freshIfNeeded(base0, reserved)
      val safeFresh = escapeIfNeeded(fresh)
      safeFresh
    }
  }

  /*
  private def freshIfNeeded(name: String, taken: collection.mutable.Set[String]): String = {
    if (!taken.contains(name)) name
    else {
      var i = 1
      var newName = s"${name}_$i"
      while (taken.contains(newName)) {
        i += 1
        newName = s"${name}_$i"
      }
      newName
    }
  }
   */
  // use this for compatibility reasons for now but the commented version above would be nicer...
  private def freshIfNeeded(name: String, taken: collection.mutable.Set[String]): String = {
    if (!taken.contains(name)) name
    else {
      val newName = s"${name}_"
      freshIfNeeded(newName, taken)
    }
  }

  /** Build an LP-safe signature mirror. */
  def build(orig: Signature): LpSig = {
    // Start with LP-reserved names (keywords + all library glyph spellings)
    val res = collection.mutable.Set.empty[String]
    res ++= lpSysStrings.reserve // union of keywords + glyph names (unicode+ascii)

    // Produce term names
    val termNames: Map[Signature.Key, QName] = {
      orig.allConstants.map { k =>
        val meta = orig.meta(k)
        if (tptpConstMappings.LeoConstants.keySet.contains(meta.key)) {
          k -> tptpConstMappings.LeoConstants(meta.key)
        }
        else {
            val raw = meta.name
            val safe = avails(raw, res)
            // Skolems are always local
            val qn = if (isPropSet(Signature.PropSkolemConstant, meta.flag))
              QName(None, Name(safe))
            else
              QName(Prefixes.sigPrefix, Name(safe))
            (k -> qn)
          }
      }.toMap
    }

    // Produce type names (type constructors / base types)
    val typeNames: Map[Signature.Key, QName] = {
      orig.typeConstructors.map { k =>
        val meta = orig.meta(k)
        if (tptpConstMappings.leoBaseTy.keySet.contains(meta.key))
          {k -> tptpConstMappings.leoBaseTy(meta.key)}
        else{
          val raw = meta.name
          val safe = avails(raw, res)
          val qn = QName(Prefixes.sigPrefix, Name(safe))
          (k -> qn)
        }
      }.toMap
    }

    LpSig(orig, termNames, typeNames, res.toSet)
  }
}

