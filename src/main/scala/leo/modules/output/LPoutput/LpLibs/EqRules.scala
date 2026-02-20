package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.Level
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
object EqRules {

  //todo: do naming uniformly

  object Names {

    // ** Names as Strings
    // Simplifications of PropExt.lp in Standard Library
    private val negEq_idem = "¬=_idem"
    private val orBot = "∨⊥"
    private val eqTop = "=⊤"
    private val eqBot = "=⊥"
    private val negEqBot = "=⊥'"


    // Standard Library Theorems of Equality
    private val eqImpS = "=⇒"

    val allAscii = Seq()

    private[EqRules] val negEq_idem_S: SymRef = SymRef.LP(QName.local(negEq_idem))
    private[EqRules] val orBot_S: SymRef = SymRef.LP(QName.local(orBot))
    private[EqRules] val eqTop_S: SymRef = SymRef.LP(QName.local(eqTop))
    private[EqRules] val eqBot_S: SymRef = SymRef.LP(QName.local(eqBot))
    private[EqRules] val negEqBot_S: SymRef = SymRef.LP(QName.local(negEqBot))

    private[EqRules] val eqImp_S: SymRef = SymRef.LP(QName.local(eqImpS))

  }

  object AsTerms {
    import Names._

    def lpSimp_negEq_idem[L <: Level] = LpTerm.Const[L](negEq_idem_S)
    def lpSimp_orBot[L <: Level] = LpTerm.Const[L](orBot_S)
    def lpSimp_eqTop[L <: Level] = LpTerm.Const[L](eqTop_S)
    def lpSimp_eqBot[L <: Level] = LpTerm.Const[L](eqBot_S)
    def lpSimp_negEqBot[L <: Level] = LpTerm.Const[L](negEqBot_S)
    def eqImp[L <: Level] = LpTerm.Const[L](eqImp_S)

  }


}

object FunRules {

  object Names {

    // ** Names as Strings
    private val decomp_step = "Decomp_step"
    private val decomp_single = "Decomp_single"

    val allAscii = Seq(decomp_step,decomp_single)

    private[FunRules] val decomp_step_S: SymRef = SymRef.LP(QName.local(decomp_step))
    private[FunRules] val decomp_single_S: SymRef = SymRef.LP(QName.local(decomp_single))
  }

  object AsTerms {

    import Names._

    def decompStep[L <: Level] = LpTerm.Const[L](decomp_step_S)
    def mkDecompStepObj(a: OlType, b: OlType, s: LpTerm[Level.Obj], t: LpTerm[Level.Obj], f: LpTerm[Level.Obj], g: LpTerm[Level.Obj], h0: Option[LpTerm[Level.Obj]]): LpTerm[Level.Obj] = {
      val maybeH: Seq[Arg.Explicit[Level.Obj]] = h0 match {
        case Some(term) => Seq(Arg.Explicit(term))
        case None => Seq.empty
      }
      LpTerm.App(decompStep[Level.Obj], Seq(Arg.ImplicitTypeArg[Level.Obj](a), Arg.ImplicitTypeArg[Level.Obj](b), Arg.Explicit(s), Arg.Explicit(t), Arg.Explicit(f), Arg.Explicit(g)) ++ maybeH)
    }

    def DecompStepRes(a: OlType, b: OlType, s: LpTerm[Level.Obj], t: LpTerm[Level.Obj], f: LpTerm[Level.Obj], g: LpTerm[Level.Obj]): (LpTerm[Level.Obj],LpTerm[Level.Obj]) = {
      val newEqLit = LogicConst.Not(LogicConst.Eq(a,s,t))
      val newAppHdEq = LogicConst.Not(LogicConst.Eq(b,f,g))
      (newAppHdEq,newEqLit)
    }

    def decompSingle[L <: Level] = LpTerm.Const[L](decomp_single_S)
    def mkDecompSingleObj(a: OlType, b: OlType, s: LpTerm[Level.Obj], t: LpTerm[Level.Obj], f: LpTerm[Level.Obj], h0: Option[LpTerm[Level.Obj]]): LpTerm[Level.Obj] = {
      val maybeH: Seq[Arg.Explicit[Level.Obj]] = h0 match {
        case Some(term) => Seq(Arg.Explicit(term))
        case None => Seq.empty
      }
      LpTerm.App(decompSingle[Level.Obj], Seq(Arg.ImplicitTypeArg[Level.Obj](a), Arg.ImplicitTypeArg[Level.Obj](b), Arg.Explicit(s), Arg.Explicit(t), Arg.Explicit(f)) ++ maybeH)
    }

    def DecompSingleResult(a: OlType, s: LpTerm[Level.Obj], t: LpTerm[Level.Obj]): LpTerm[Level.Obj] = {
      LogicConst.Not(LogicConst.Eq(a,s,t))
    }
  }

}

