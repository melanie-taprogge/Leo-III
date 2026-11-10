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
    private val boolIdsPatternS = "boolIds_pattern"
    private val repeatS = "#repeat"


    val allAscii = Seq(removeBotTacS, boolIdsPatternS)

    private[LeoTactics] val removeBotTac_S: SymRef = SymRef.LP(QName.local(removeBotTacS))
    private[LeoTactics] val boolIdsPattern: SymRef = SymRef.LP(QName.local(boolIdsPatternS))
    private[LeoTactics] val repeat: SymRef = SymRef.LP(QName.local(repeatS))

  }

  object MLTerms {
    import Names._

    private[LeoTactics] val removeBotTac = LpTerm.Const[Level.Meta](removeBotTac_S)
    private[LeoTactics] val boolIdsPatternTac = LpTerm.Const[Level.Meta](boolIdsPattern)
    private[LeoTactics] val repeatTac = LpTerm.Const[Level.Meta](repeat)
  }

  object EvalApp {

    import MLTerms._

    def removeBot(rewritePattern: RewritePattern) = Eval(LpTerm.App(removeBotTac,Seq(Arg.Explicit[Level.Meta](LpTerm.LpString(rewritePattern)))))

    /** Normalize Boolean structure at the supplied selector until no rule applies. */
    def repeatBoolIdsAt(pattern: RewritePattern): Eval = {
      val tactic = LpTerm.App[Level.Meta](boolIdsPatternTac,
        Seq(Arg.Explicit[Level.Meta](LpTerm.LpString(pattern))))
      Eval(LpTerm.App[Level.Meta](repeatTac, Seq(Arg.Explicit[Level.Meta](tactic))))
    }
  }


}

