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
    private val transformNS = "transform_n"


    val allAscii = Seq(deleteBotsS,transformNS)

    private[MetaTheorems] val deleteBotsS_S: SymRef = SymRef.LP(QName.local(deleteBotsS))
    private[MetaTheorems] val transformNS_S: SymRef = SymRef.LP(QName.local(transformNS))

  }

  object MLTerms {
    import Names._

    private[MetaTheorems] val deleteBots_T = LpTerm.Const[Level.Meta](deleteBotsS_S)
    private[MetaTheorems] val transformNS_T = LpTerm.Const[Level.Obj](transformNS_S)
  }

  object Inst {

    import MLTerms._

    def deleteBots(postDeletionClause: Seq[LpTerm[Level.Obj]], botIdxList: Seq[Int]) =
      LpTerm.App[Level.Meta](deleteBots_T,Seq(Arg.Explicit(LpList(botIdxList.map(LpInt(_)))),Arg.Explicit(LpList(postDeletionClause.map(LpTerm.Obj(_))))))

    def transform_n(initialLit: LpTerm[Level.Obj], clauseLhs: Seq[LpTerm[Level.Obj]], clauseRhs: Seq[LpTerm[Level.Obj]], derivedLits: Seq[LpTerm[Level.Obj]], ruleProof: LpTerm[Level.Obj], proofClauseOrig: LpTerm[Level.Obj]) =
      LpTerm.App[Level.Obj](transformNS_T,Seq(Arg.Implicit(initialLit), Arg.Explicit(LpList(clauseLhs)), Arg.Explicit(LpList(derivedLits)), Arg.Explicit(LpList(clauseRhs)), Arg.Explicit(ruleProof), Arg.Explicit(proofClauseOrig)))
  }


}

