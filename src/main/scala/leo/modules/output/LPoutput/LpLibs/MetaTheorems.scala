package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.LpLibs.ND.Terms.topIntro
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
    private val permuteS = "permute"


    val allAscii = Seq(deleteBotsS,transformNS,permuteS)

    private[MetaTheorems] val deleteBotsS_S: SymRef = SymRef.LP(QName.local(deleteBotsS))
    private[MetaTheorems] val transformNS_S: SymRef = SymRef.LP(QName.local(transformNS))
    private[MetaTheorems] val permuteS_S: SymRef = SymRef.LP(QName.local(permuteS))

  }

  object MLTerms {
    import Names._

    private[MetaTheorems] val deleteBots_T = LpTerm.Const[Level.Meta](deleteBotsS_S)
    private[MetaTheorems] val transformNS_T = LpTerm.Const[Level.Obj](transformNS_S)
    private[MetaTheorems] val permute_T = LpTerm.Const[Level.Obj](permuteS_S)
  }

  object Inst {

    import MLTerms._

    def deleteBots(postDeletionClause: Seq[lpLiteralInst], botIdxList: Seq[Int]) = {
      deleteBotsTerms(postDeletionClause.map(_.term), botIdxList)
    }

    def deleteBotsTerms(postDeletionClause: Seq[LpTerm[Level.Obj]], botIdxList: Seq[Int]) =
      LpTerm.App[Level.Meta](deleteBots_T, Seq(Arg.Explicit(LpList(botIdxList.map(LpInt(_)))), Arg.Explicit(LpList(postDeletionClause.map(LpTerm.Obj(_))))))

    def transform_nTerms(initialLit: LpTerm[Level.Obj], clauseLhs: Seq[LpTerm[Level.Obj]], clauseRhs: Seq[LpTerm[Level.Obj]], derivedLits: Seq[LpTerm[Level.Obj]], ruleProof: LpTerm[Level.Obj], proofClauseOrig: LpTerm[Level.Obj]) =
      LpTerm.App[Level.Obj](transformNS_T,Seq(Arg.Implicit(initialLit), Arg.Explicit(LpList(clauseLhs)), Arg.Explicit(LpList(derivedLits)), Arg.Explicit(LpList(clauseRhs)), Arg.Explicit(ruleProof), Arg.Explicit(proofClauseOrig)))

    def transform_n(initialLit: lpLiteralInst, clauseLhs: Seq[lpLiteralInst], clauseRhs: Seq[lpLiteralInst], derivedLits: Seq[lpLiteralInst], ruleProof: LpTerm[Level.Obj], proofClauseOrig: LpTerm[Level.Obj]) =
      transform_nTerms(initialLit.term,clauseLhs.map(_.term),clauseRhs.map(_.term),derivedLits.map(_.term),ruleProof,proofClauseOrig)

    def permute(σ: Seq[Int], origClauseLits: Seq[lpLiteralInst], prfBefore: LpTerm[Level.Obj]) = {
      permuteTerms(σ,origClauseLits.map(_.term),prfBefore)
    }

    def permuteTerms(σ: Seq[Int], origClauseLits: Seq[LpTerm[Level.Obj]], prfBefore: LpTerm[Level.Obj]) = {
      val intsAsLpNums = LpList[Level.Obj](σ.map(LpInt(_)))
      LpTerm.App[Level.Obj](permute_T, Seq(Arg.Explicit(intsAsLpNums), Arg.Explicit(LpList(origClauseLits)), Arg.Explicit(topIntro), Arg.Explicit(prfBefore)))
    }

  }


}

