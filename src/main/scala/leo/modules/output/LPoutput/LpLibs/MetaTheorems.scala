package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.Level
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Eval, RewritePattern}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{LpInt, LpList}
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
object MetaTheorems {

  //todo: do naming uniformly

  object Names {

    // ** Names as Strings
    // Remove bottom from clause
    private val deleteBotsS = "deleteBots"


    val allAscii = Seq(deleteBotsS)

    private[MetaTheorems] val deleteBotsS_S: SymRef = SymRef.LP(QName.local(deleteBotsS))

  }

  object MLTerms {
    import Names._

    private[MetaTheorems] val deleteBots_T = LpTerm.Const[Level.Meta](deleteBotsS_S)
  }

  object Inst {

    import MLTerms._

    def deleteBots(postDeletionClause: Seq[LpTerm[Level.Obj]], botIdxList: Seq[Int]) = LpTerm.App[Level.Meta](deleteBots_T,Seq(Arg.Explicit(LpList(botIdxList.map(LpInt(_)))),Arg.Explicit(LpList(postDeletionClause.map(LpTerm.Obj(_))))))
  }


}

