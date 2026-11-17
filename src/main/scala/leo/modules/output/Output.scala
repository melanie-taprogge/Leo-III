package leo.modules.output

import leo.datastructures.Signature

/**
  * Trait for wrapping strings. Might be handy if the computation of the strings
  * are somewhat involved/complex and you just want to compute them if they are
  * indeed needed.
  *
  * @author Alexander Steen <a.steen@fu-berlin.de>
  * @since 07.11.14
  */
trait Output extends Function0[String] {
  /** Signature references carried by a proof annotation. */
  def referencedSymbols: Set[Signature.Key] = Set.empty
}
trait Output_track extends Function0[(String,Any)]{}


