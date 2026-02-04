package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript

sealed trait EncodeResult

object EncodeResult {
  final case class Encoded(scripts: Seq[LpProofScript]) extends EncodeResult
  final case class NotEncodable(reason: String) extends EncodeResult
}

