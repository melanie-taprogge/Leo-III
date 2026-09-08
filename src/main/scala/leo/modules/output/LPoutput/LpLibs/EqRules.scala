package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.Level
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
object EqRules {

  //todo: do naming uniformly

  object Names {

    // ** Names as Strings
    // Simplifications of PropExt.lp in Standard Library
    private val negEq_idem = "¬=_irrefl"
    private val orBot = "∨⊥"
    private val eqTop = "=⊤"
    private val topEq = "⊤="
    private val eqBot = "=⊥"
    private val botEq = "⊥="
    private val negEqBot = "=⊥'"
    private val negBotEq = "⊥='"
    private val expand_lit = "expand_lit"


    // Standard Library Theorems of Equality
    private val eqImpS = "=⇒"

    val allAscii = Seq(expand_lit)

    private[EqRules] val negEq_idem_S: SymRef = SymRef.LP(QName.local(negEq_idem))
    private[EqRules] val orBot_S: SymRef = SymRef.LP(QName.local(orBot))
    private[EqRules] val eqTop_S: SymRef = SymRef.LP(QName.local(eqTop))
    private[EqRules] val topEq_S: SymRef = SymRef.LP(QName.local(topEq))
    private[EqRules] val eqBot_S: SymRef = SymRef.LP(QName.local(eqBot))
    private[EqRules] val botEq_S: SymRef = SymRef.LP(QName.local(botEq))
    private[EqRules] val negEqBot_S: SymRef = SymRef.LP(QName.local(negEqBot))
    private[EqRules] val negBotEq_S: SymRef = SymRef.LP(QName.local(negBotEq))
    private[EqRules] val expand_lit_S: SymRef = SymRef.LP(QName.local(expand_lit))

    private[EqRules] val eqImp_S: SymRef = SymRef.LP(QName.local(eqImpS))

  }

  object AsTerms {
    import Names._

    def lpSimp_negEq_idem[L <: Level] = LpTerm.Const[L](negEq_idem_S)
    def lpSimp_orBot[L <: Level] = LpTerm.Const[L](orBot_S)
    def lpSimp_eqTop[L <: Level] = LpTerm.Const[L](eqTop_S)
    def lpSimp_topEq[L <: Level] = LpTerm.Const[L](topEq_S)
    def lpSimp_eqBot[L <: Level] = LpTerm.Const[L](eqBot_S)
    def lpSimp_botEq[L <: Level] = LpTerm.Const[L](botEq_S)
    def lpSimp_negEqBot[L <: Level] = LpTerm.Const[L](negEqBot_S)
    def lpSimp_negBotEq[L <: Level] = LpTerm.Const[L](negBotEq_S)
    def expandLit[L <: Level] = LpTerm.Const[L](expand_lit_S)
    def eqImp[L <: Level] = LpTerm.Const[L](eqImp_S)

    def mkExpandLit(a: OlMonoType, b: OlMonoType, f: LpTerm[Level.Obj], g: LpTerm[Level.Obj]): LpTerm[Level.Meta] =
      LpTerm.App(expandLit[Level.Meta], Seq(Arg.ImplicitTypeArg[Level.Meta](a), Arg.ImplicitTypeArg[Level.Meta](b), Arg.Explicit(LpTerm.Obj(f)), Arg.Explicit(LpTerm.Obj(g))))

  }

  trait LitNormRules {
    def lpConst[L <: Level]: LpTerm[L]
    def applyTo(l: lpLiteralInst): Option[lpLiteralInst]
  }

  object EqTop extends LitNormRules {
    import AsTerms.lpSimp_eqTop
    def lpConst[L <: Level] = lpSimp_eqTop

    def applyTo(l: lpLiteralInst): Option[lpLiteralInst] = l.term match {
      case LogicConst.Eq(_, lhs, LogicConst.Top) => Some(lpLiteralInst(lhs,true,false))
      case LogicConst.Not(LogicConst.Eq(_, lhs, LogicConst.Top)) => Some(lpLiteralInst(LogicConst.Not(lhs),false,false))
      case _ => None
    }
  }

  object TopEq extends LitNormRules {
    import AsTerms.lpSimp_topEq
    def lpConst[L <: Level] = lpSimp_topEq

    def applyTo(l: lpLiteralInst): Option[lpLiteralInst] = l.term match {
      case LogicConst.Eq(_, LogicConst.Top, rhs) => Some(lpLiteralInst(rhs, true, false))
      case LogicConst.Not(LogicConst.Eq(_, LogicConst.Top, rhs)) => Some(lpLiteralInst(LogicConst.Not(rhs), false, false))
      case _ => None
    }
  }

  object EqBot extends LitNormRules {

    import AsTerms.lpSimp_eqBot

    def lpConst[L <: Level] = lpSimp_eqBot

    def applyTo(l: lpLiteralInst): Option[lpLiteralInst] = l.term match {
      case LogicConst.Eq(_, lhs, LogicConst.Bot) => Some(lpLiteralInst(LogicConst.Not(lhs), false, false))
      case LogicConst.Not(LogicConst.Eq(_, lhs, LogicConst.Bot)) => Some(lpLiteralInst(LogicConst.Not(LogicConst.Not(lhs)), false, false))
      case _ => None
    }
  }

  object BotEq extends LitNormRules {

    import AsTerms.lpSimp_botEq

    def lpConst[L <: Level] = lpSimp_botEq

    def applyTo(l: lpLiteralInst): Option[lpLiteralInst] = l.term match {
      case LogicConst.Eq(_, LogicConst.Bot, rhs) => Some(lpLiteralInst(LogicConst.Not(rhs), false, false))
      case LogicConst.Not(LogicConst.Eq(_, LogicConst.Bot, rhs)) => Some(lpLiteralInst(LogicConst.Not(LogicConst.Not(rhs)), false, false))
      case _ => None
    }
  }

  object NegEqBot extends LitNormRules {

    import AsTerms.lpSimp_negEqBot

    def lpConst[L <: Level] = lpSimp_negEqBot

    def applyTo(l: lpLiteralInst): Option[lpLiteralInst] = l.term match {
      case LogicConst.Not(LogicConst.Eq(_, lhs, LogicConst.Bot)) => Some(lpLiteralInst(lhs, true, false))
      case LogicConst.Not(LogicConst.Not(LogicConst.Eq(_, lhs, LogicConst.Bot))) => Some(lpLiteralInst(LogicConst.Not(lhs), false, false))
      case _ => None
    }
  }

  object NegBotEq extends LitNormRules {

    import AsTerms.lpSimp_negBotEq

    def lpConst[L <: Level] = lpSimp_negBotEq

    def applyTo(l: lpLiteralInst): Option[lpLiteralInst] = l.term match {
      case LogicConst.Not(LogicConst.Eq(_, LogicConst.Bot, rhs)) => Some(lpLiteralInst(rhs, true, false))
      case LogicConst.Not(LogicConst.Not(LogicConst.Eq(_, LogicConst.Bot, rhs))) => Some(lpLiteralInst(LogicConst.Not(rhs), false, false))
      case _ => None
    }
  }


}

object FunRules {

  object Names {

    // ** Names as Strings
    private val decomp_step = "Decomp_step"
    private val decomp_single = "Decomp_single"
    private val lift_decomp_step_binder = "lift_decomp_step_binder"
    private val lift_decomp_single_binder = "lift_decomp_single_binder"

    val allAscii = Seq(decomp_step,decomp_single,lift_decomp_step_binder,lift_decomp_single_binder)

    private[FunRules] val decomp_step_S: SymRef = SymRef.LP(QName.local(decomp_step))
    private[FunRules] val decomp_single_S: SymRef = SymRef.LP(QName.local(decomp_single))
    private[FunRules] val lift_decomp_step_binder_S: SymRef = SymRef.LP(QName.local(lift_decomp_step_binder))
    private[FunRules] val lift_decomp_single_binder_S: SymRef = SymRef.LP(QName.local(lift_decomp_single_binder))
  }

  object AsTerms {

    import Names._

    def decompStep[L <: Level] = LpTerm.Const[L](decomp_step_S)
    def mkDecompStepObj(a: OlMonoType, b: OlMonoType, s: LpTerm[Level.Obj], t: LpTerm[Level.Obj], f: LpTerm[Level.Obj], g: LpTerm[Level.Obj], h0: Option[LpTerm[Level.Obj]]): LpTerm[Level.Obj] = {
      val maybeH: Seq[Arg.Explicit[Level.Obj]] = h0 match {
        case Some(term) => Seq(Arg.Explicit(term))
        case None => Seq.empty
      }
      LpTerm.App(decompStep[Level.Obj], Seq(Arg.ImplicitTypeArg[Level.Obj](a), Arg.ImplicitTypeArg[Level.Obj](b), Arg.Explicit(s), Arg.Explicit(t), Arg.Explicit(f), Arg.Explicit(g)) ++ maybeH)
    }

    def DecompStepRes(a: OlMonoType, b: OlMonoType, s: LpTerm[Level.Obj], t: LpTerm[Level.Obj], f: LpTerm[Level.Obj], g: LpTerm[Level.Obj]): (lpLiteralInst, lpLiteralInst) = {
      val newEqLit = lpLiteralInst(LogicConst.Not(LogicConst.Eq(a, s, t)), false, true)
      val newAppHdEq = lpLiteralInst(LogicConst.Not(LogicConst.Eq(b, f, g)), false, true)
      (newAppHdEq, newEqLit)
    }

    def decompSingle[L <: Level] = LpTerm.Const[L](decomp_single_S)
    def mkDecompSingleObj(a: OlMonoType, b: OlMonoType, s: LpTerm[Level.Obj], t: LpTerm[Level.Obj], f: LpTerm[Level.Obj], h0: Option[LpTerm[Level.Obj]]): LpTerm[Level.Obj] = {
      val maybeH: Seq[Arg.Explicit[Level.Obj]] = h0 match {
        case Some(term) => Seq(Arg.Explicit(term))
        case None => Seq.empty
      }
      LpTerm.App(decompSingle[Level.Obj], Seq(Arg.ImplicitTypeArg[Level.Obj](a), Arg.ImplicitTypeArg[Level.Obj](b), Arg.Explicit(s), Arg.Explicit(t), Arg.Explicit(f)) ++ maybeH)
    }

    def DecompSingleResult(a: OlMonoType, s: LpTerm[Level.Obj], t: LpTerm[Level.Obj]): lpLiteralInst = {
      lpLiteralInst(LogicConst.Not(LogicConst.Eq(a,s,t)),false,true)
    }

    /**
      * One-binder lifting lemma for Decomp_step.
      *
      * The Lambdapi theorem has the following schematic shape:
      *   (Π x, π (¬ lhs x = rhs x) -> π (¬ cl x = cr x ∨ ¬ el x = er x))
      *   -> π (¬ (λx. lhs x) = (λx. rhs x))
      *   -> π (¬ (λx. cl x) = (λx. cr x) ∨ ¬ (λx. el x) = (λx. er x))
      */
    def liftDecompStepBinder[L <: Level] = LpTerm.Const[L](lift_decomp_step_binder_S)

    def mkLiftDecompStepBinderObj(binderTy: OlMonoType, resultTy: OlMonoType, residualTy: OlMonoType, argTy: OlMonoType, lhs: LpTerm[Level.Obj], rhs: LpTerm[Level.Obj], lhsResidual: LpTerm[Level.Obj], rhsResidual: LpTerm[Level.Obj], lhsArg: LpTerm[Level.Obj], rhsArg: LpTerm[Level.Obj], bodyProof: Option[LpTerm[Level.Obj]]): LpTerm[Level.Obj] = {
      val maybeBodyProof = bodyProof.map(Arg.Explicit[Level.Obj]).toSeq
      LpTerm.App(liftDecompStepBinder[Level.Obj], Seq(Arg.ImplicitTypeArg[Level.Obj](binderTy), Arg.ImplicitTypeArg[Level.Obj](resultTy), Arg.ImplicitTypeArg[Level.Obj](residualTy), Arg.ImplicitTypeArg[Level.Obj](argTy), Arg.Explicit(lhs), Arg.Explicit(rhs), Arg.Explicit(lhsResidual), Arg.Explicit(rhsResidual), Arg.Explicit(lhsArg), Arg.Explicit(rhsArg)) ++ maybeBodyProof)
    }

    /**
      * Result shape of a Decomp_step instance lifted under `binders`.
      *
      * Returns the initial literal and the two replacement literals:
      *   ¬((λ xs. f xs (s xs)) = (λ xs. g xs (t xs)))
      *   ↦ ¬((λ xs. f xs) = (λ xs. g xs)) ∨ ¬((λ xs. s xs) = (λ xs. t xs))
      */
    def LiftedDecompStepResult(binders: Seq[LpTerm.Var[Level.Obj]], argTy: OlMonoType, resultTy: OlMonoType, lhsArg: LpTerm[Level.Obj], rhsArg: LpTerm[Level.Obj], lhsFun: LpTerm[Level.Obj], rhsFun: LpTerm[Level.Obj]): (lpLiteralInst, Vector[lpLiteralInst]) = {
      val funTy = OlMonoType.Fun(Seq(argTy,resultTy))
      val initial = lpLiteralInst.equality(lpTermBuilder.funTy(binders,resultTy), lpTermBuilder.lam(binders,LpTerm.App(lhsFun,Seq(Arg.Explicit(lhsArg)))), lpTermBuilder.lam(binders,LpTerm.App(rhsFun,Seq(Arg.Explicit(rhsArg)))), polarity = false)
      val residual = lpLiteralInst.equality(lpTermBuilder.funTy(binders,funTy), lpTermBuilder.lam(binders,lhsFun), lpTermBuilder.lam(binders,rhsFun), polarity = false)
      val argLit = lpLiteralInst.equality(lpTermBuilder.funTy(binders,argTy), lpTermBuilder.lam(binders,lhsArg), lpTermBuilder.lam(binders,rhsArg), polarity = false)
      (initial,Vector(residual,argLit))
    }

    /**
      * One-binder lifting lemma for Decomp_single.
      *
      * This is the single-result analogue of `lift_decomp_step_binder`:
      *   (Π x, π (¬ lhs x = rhs x) -> π (¬ cl x = cr x))
      *   -> π (¬ (λx. lhs x) = (λx. rhs x))
      *   -> π (¬ (λx. cl x) = (λx. cr x))
      */
    def liftDecompSingleBinder[L <: Level] = LpTerm.Const[L](lift_decomp_single_binder_S)

    def mkLiftDecompSingleBinderObj(binderTy: OlMonoType, resultTy: OlMonoType, argTy: OlMonoType, lhs: LpTerm[Level.Obj], rhs: LpTerm[Level.Obj], lhsArg: LpTerm[Level.Obj], rhsArg: LpTerm[Level.Obj], bodyProof: Option[LpTerm[Level.Obj]]): LpTerm[Level.Obj] = {
      val maybeBodyProof = bodyProof.map(Arg.Explicit[Level.Obj]).toSeq
      LpTerm.App(liftDecompSingleBinder[Level.Obj], Seq(Arg.ImplicitTypeArg[Level.Obj](binderTy), Arg.ImplicitTypeArg[Level.Obj](resultTy), Arg.ImplicitTypeArg[Level.Obj](argTy), Arg.Explicit(lhs), Arg.Explicit(rhs), Arg.Explicit(lhsArg), Arg.Explicit(rhsArg)) ++ maybeBodyProof)
    }

    /**
      * Result shape of a Decomp_single instance lifted under `binders`.
      *
      * Returns the initial literal and its single replacement literal:
      *   ¬((λ xs. f (s xs)) = (λ xs. f (t xs)))
      *   ↦ ¬((λ xs. s xs) = (λ xs. t xs))
      */
    def LiftedDecompSingleResult(binders: Seq[LpTerm.Var[Level.Obj]], argTy: OlMonoType, resultTy: OlMonoType, lhsArg: LpTerm[Level.Obj], rhsArg: LpTerm[Level.Obj], hd: LpTerm[Level.Obj]): (lpLiteralInst, Vector[lpLiteralInst]) = {
      val initial = lpLiteralInst.equality(lpTermBuilder.funTy(binders,resultTy), lpTermBuilder.lam(binders,LpTerm.App(hd,Seq(Arg.Explicit(lhsArg)))), lpTermBuilder.lam(binders,LpTerm.App(hd,Seq(Arg.Explicit(rhsArg)))), polarity = false)
      val argLit = lpLiteralInst.equality(lpTermBuilder.funTy(binders,argTy), lpTermBuilder.lam(binders,lhsArg), lpTermBuilder.lam(binders,rhsArg), polarity = false)
      (initial,Vector(argLit))
    }
  }

}
