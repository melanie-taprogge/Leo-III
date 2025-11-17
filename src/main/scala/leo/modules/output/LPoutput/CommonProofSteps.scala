package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.OldLpDatastructures.Encodings._
import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures._


/**
  * Representations of the accessory rules
  *
  * @author Melanie Taprogge
  */

object CommonProofSteps {

  object ScriptBuilders {
    def assumeClauseVars(enCl: lpClauseInst): Seq[lpProofScriptStep] =
      Option.when(enCl.metaVars.nonEmpty)(lpAssume(enCl.metaVars)).toSeq
  }

}
