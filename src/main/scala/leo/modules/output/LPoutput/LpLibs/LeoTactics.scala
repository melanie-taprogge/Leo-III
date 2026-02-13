package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.Level
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Eval, RewritePattern}
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
object LeoTactics {

  //todo: do naming uniformly

  object Names {

    // ** Names as Strings
    // Handling implicit transformations
    private val removeBotTacS = "removeTrivialFalse"


    val allAscii = Seq(removeBotTacS)

    private[LeoTactics] val removeBotTac_S: SymRef = SymRef.LP(QName.local(removeBotTacS))

  }

  object MLTerms {
    import Names._

    private[LeoTactics] val removeBotTac = LpTerm.Const[Level.Meta](removeBotTac_S)
  }

  object EvalApp {

    import MLTerms._

    def removeBot(rewritePattern: RewritePattern) = Eval(LpTerm.App(removeBotTac,Seq(Arg.Explicit[Level.Meta](LpTerm.LpString(rewritePattern)))))
  }


}

