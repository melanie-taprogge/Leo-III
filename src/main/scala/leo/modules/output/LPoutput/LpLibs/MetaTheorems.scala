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
    private val selectConjunctS = "∧ₑₙ"


    val allAscii = Seq(deleteBotsS,transformNS,permuteS)

    private[MetaTheorems] val deleteBotsS_S: SymRef = SymRef.LP(QName.local(deleteBotsS))
    private[MetaTheorems] val transformNS_S: SymRef = SymRef.LP(QName.local(transformNS))
    private[MetaTheorems] val permuteS_S: SymRef = SymRef.LP(QName.local(permuteS))
    private[MetaTheorems] val selectConjunctS_S: SymRef = SymRef.LP(QName.local(selectConjunctS))

    private[MetaTheorems] val mapAndLeftSym: SymRef = SymRef.LP(QName.local("mapAndLeft"))
    private[MetaTheorems] val mapAndRightSym: SymRef = SymRef.LP(QName.local("mapAndRight"))
    private[MetaTheorems] val mapOrLeftSym: SymRef = SymRef.LP(QName.local("mapOrLeft"))
    private[MetaTheorems] val mapOrRightSym: SymRef = SymRef.LP(QName.local("mapOrRight"))
    private[MetaTheorems] val conjTransformSym: SymRef = SymRef.LP(QName.local("conj_transform"))
    private[MetaTheorems] val disjTransformSym: SymRef = SymRef.LP(QName.local("transform"))

  }

  object MLTerms {
    import Names._

    private[MetaTheorems] val deleteBots_T = LpTerm.Const[Level.Meta](deleteBotsS_S)
    private[MetaTheorems] val transformNS_T = LpTerm.Const[Level.Obj](transformNS_S)
    private[MetaTheorems] val permute_T = LpTerm.Const[Level.Obj](permuteS_S)
    private[MetaTheorems] val selectConjunct_T = LpTerm.Const[Level.Obj](selectConjunctS_S)

    val mapAndLeft: LpTerm.Const[Level.Meta] = LpTerm.Const[Level.Meta](mapAndLeftSym)
    val mapAndRight: LpTerm.Const[Level.Meta] = LpTerm.Const[Level.Meta](mapAndRightSym)
    val mapOrLeft: LpTerm.Const[Level.Meta] = LpTerm.Const[Level.Meta](mapOrLeftSym)
    val mapOrRight: LpTerm.Const[Level.Meta] = LpTerm.Const[Level.Meta](mapOrRightSym)
    val conjTransform: LpTerm.Const[Level.Meta] = LpTerm.Const[Level.Meta](conjTransformSym)
    val disjTransform: LpTerm.Const[Level.Meta] = LpTerm.Const[Level.Meta](disjTransformSym)
  }

  object Inst {

    import MLTerms._

    /** Select a conjunct at a valid zero-based index; the index condition reduces to ⊤. */
    def selectConjunct(conjuncts: Seq[LpTerm[Level.Obj]], index: Int,
                       parentProof: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App[Level.Obj](selectConjunct_T, Seq(
        Arg.Explicit(LpInt[Level.Obj](index)), Arg.Explicit(LpList(conjuncts)),
        Arg.Explicit(topIntro[Level.Obj]), Arg.Explicit(parentProof)))

    def deleteBots(postDeletionClause: Seq[lpLiteralInst], botIdxList: Seq[Int]) = {
      deleteBotsTerms(postDeletionClause.map(_.term), botIdxList)
    }

    def deleteBotsTerms(postDeletionClause: Seq[LpTerm[Level.Obj]], botIdxList: Seq[Int]) =
      LpTerm.App[Level.Meta](deleteBots_T, Seq(Arg.Explicit(LpList(botIdxList.map(LpInt(_)))), Arg.Explicit(LpList(postDeletionClause.map(LpTerm.Obj(_))))))

    def transform_nTerms(initialLit: LpTerm[Level.Obj], clauseLhs: Seq[LpTerm[Level.Obj]], clauseRhs: Seq[LpTerm[Level.Obj]], derivedLits: Seq[LpTerm[Level.Obj]], ruleProof: LpTerm[Level.Obj], proofClauseOrig: LpTerm[Level.Obj]) =
      LpTerm.App[Level.Obj](transformNS_T,Seq(Arg.Implicit(initialLit), Arg.Explicit(LpList(clauseLhs)), Arg.Explicit(LpList(derivedLits)), Arg.Explicit(LpList(clauseRhs)), Arg.Explicit(ruleProof), Arg.Explicit(proofClauseOrig)))

    def transform_n(initialLit: lpLiteralInst, clauseLhs: Seq[lpLiteralInst], clauseRhs: Seq[lpLiteralInst], derivedLits: Seq[lpLiteralInst], ruleProof: LpTerm[Level.Obj], proofClauseOrig: LpTerm[Level.Obj]) =
      {
        if (clauseLhs.isEmpty && clauseRhs.isEmpty) LpTerm.App(ruleProof,Seq(Arg.Explicit(proofClauseOrig)))
        else transform_nTerms(initialLit.term,clauseLhs.map(_.term),clauseRhs.map(_.term),derivedLits.map(_.term),ruleProof,proofClauseOrig)
      }

    def permute(σ: Seq[Int], origClauseLits: Seq[lpLiteralInst], prfBefore: LpTerm[Level.Obj]) = {
      permuteTerms(σ,origClauseLits.map(_.term),prfBefore)
    }

    def permuteTerms(σ: Seq[Int], origClauseLits: Seq[LpTerm[Level.Obj]], prfBefore: LpTerm[Level.Obj]) = {
      val intsAsLpNums = LpList[Level.Obj](σ.map(LpInt(_)))
      LpTerm.App[Level.Obj](permute_T, Seq(Arg.Explicit(intsAsLpNums), Arg.Explicit(LpList(origClauseLits)), Arg.Explicit(topIntro), Arg.Explicit(prfBefore)))
    }

  }


}

