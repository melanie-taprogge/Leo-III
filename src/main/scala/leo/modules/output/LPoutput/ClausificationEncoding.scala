package leo.modules.output.LPoutput

import leo.datastructures.ClauseProxy
import leo.modules.output.LPoutput.EncodeResult.NotEncodable
import leo.modules.output.LPoutput.NewLpDatastructures.{Level, LpSig, LpTerm}

/** Reconstruction entry points for standalone clausification steps.
  *
  * Each entry point receives resolved parent proof terms in source-parent order.
  * Proof bodies use NewLpDatastructures; LPoutput owns their declaration wrappers.
  */
object ClausificationEncoding {
  private object Shared {
    // Add helpers here when they are shared by the clausification encoders.
  }

  /** Residual clausification for both FullCNF and RenameCNF.
    */
  def encCnf(step: ClauseProxy,
             parentProofs: Seq[LpTerm[Level.Obj]],
             sig: LpSig): EncodeResult = {
    NotEncodable(s"CNF step ${step.id}: residual clausification reconstruction is not implemented yet")
  }

  /** One monomorphic term-Skolemization step, including its definition handling.
    */

  // todo: Dedicated handling of the skolem def now being an explicit parent node
  def encSkolem(step: ClauseProxy,
                parentProofs: Seq[LpTerm[Level.Obj]],
                sig: LpSig): EncodeResult = {


    NotEncodable(s"Skolemization step ${step.id}: standalone term-Skolemization reconstruction is not implemented yet")
  }

  /** Selection of one clause from a clausified conjunction.
    */
  def encCnfConj(step: ClauseProxy,
                 parentProofs: Seq[LpTerm[Level.Obj]],
                 sig: LpSig): EncodeResult = {
    NotEncodable(s"CNF conjunction step ${step.id}: conjunction-selection reconstruction is not implemented yet")
  }
}
