package leo.modules.output.LPoutput.NewLpDatastructures

import leo.Out
import leo.modules.output.LPoutput.NewLpDatastructures.Stmt._
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm._
import leo.modules.output.LPoutput.NewLpDatastructures.Proof._
import leo.datastructures.{Signature, isPropSet}
import leo.modules.HOLSignature
import leo.modules.output.LPoutput.NewLpDatastructures.Arg.Implicit
import leo.modules.output.LPoutput.NewLpDatastructures.LogicConst
import leo.modules.output.LPoutput.NewLpDatastructures.Prefixes._
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
import leo.modules.output.LPoutput.NewLpDatastructures.lpSysStrings._
import leo.modules.output.LPoutput.NewLpDatastructures.tptpConstMappings.{LeoConstants, leoBinders, leoTypedConnectives, leoUntypedConnectives}

import scala.collection.immutable.{AbstractSeq, LinearSeq}


final case class RenderOptions(sigPrefix: Boolean = true, formulaPrefix: Boolean = true, monomorphic: Boolean = true)

object Renderer {

  def stmt(s: Stmt, sig: LpSig, ro: RenderOptions = RenderOptions()): String = s match {
    case Declaration(n, params, res, imps) =>
      val imp = if (imps.isEmpty) "" else s" ${imps.map { case (n, t) => s"[${name(n)} : ${ty(t, ro, sig)}]" }.mkString(" ")}"
      val par = if (params.isEmpty) "" else s" ${params.map { case (n, t) => s"(${name(n)} : ${ty(t, ro, sig)})" }.mkString(" ")}"
      s"symbol ${name(n)}$imp$par: ${ty(res, ro, sig)};\n"

    case Definition(n, params, tyOpt, body, imps, mods) =>
      val mod = if (mods.isEmpty) "" else mods.map {
        case Opaque => "opaque "
      }.mkString("")
      val imp = if (imps.isEmpty) "" else s" ${imps.map { case (n, t) => s"[${name(n)} : ${ty(t, ro, sig)}]" }.mkString(" ")}"
      val par = if (params.isEmpty) "" else s" ${params.map { case (n, t) => s"(${name(n)} : ${ty(t, ro, sig)})" }.mkString(" ")}"
      val colonTy = tyOpt.fold("")(t => s": ${ty(t, ro, sig)}")
      val eq = body match {
        case DefBody.LpTermBody(t0) => " " + renderTerm(t0, ro, sig) + ";"
        case DefBody.ProofBody(p) => "\n" + "begin\n" + indent(proof(p, ro, sig)) + "\nend;"
      }
      s"${mod}symbol ${name(n)}$imp$par$colonTy ≔$eq\n"

    case Rule(h, vars, rhs) =>
      val vs = if (vars.isEmpty) "" else " " + vars.map(name).mkString(" ")
      s"rule ${renderTerm(h, ro, sig)}$vs ↪ ${renderTerm(rhs, ro, sig)};\n"
  }

  def LpTermObj(t: LpTerm[Level.Obj], sig: LpSig, ro: RenderOptions = RenderOptions()): String = termP(t, ro, 100, sig)

  def LpTermMeta(t: LpTerm[Level.Meta], sig: LpSig, ro: RenderOptions = RenderOptions()): String = renderTerm(t, ro, sig)

  def typ(t: LpType, sig: LpSig, ro: RenderOptions = RenderOptions()): String = ty(t, ro, sig)

  def proofText(p: Proof, sig: LpSig, ro: RenderOptions = RenderOptions()): String = proof(p, ro, sig)

  def LpQname(qn: QName, ro: RenderOptions = RenderOptions()): String = qname(qn, ro)


  def proof(p: Proof, ro: RenderOptions, sig: LpSig): String = p match {
    case Refine(t, subs) =>
      val sub = subs.map(sp => "\n" + indent(curly(proof(sp, ro, sig)))).mkString("")
      s"refine ${renderTerm(t, ro, sig)}$sub"
    case Have(n, ty0, pr) =>
      s"have ${name(n)} : ${ty(ty0, ro, sig)}\n" + indent(curly(proof(pr, ro, sig)))
    case Rewrite(pattern, rule, side) =>
      val sside = side match {
        case Side.Left => " left ";
        case Side.Right => " right ";
        case Side.Any => " "
      }
      val pat = pattern.fold("") { p => s".[${name(p.hole)} in ${renderTerm(p.LpTerm, ro, sig)}] " }
      s"rewrite$sside$pat${renderTerm(rule, ro, sig)}"
    case Reflexivity => "reflexivity"
    case Simplify(ns) => s"simplify ${ns.map(name).mkString(" ")}"
    case Repeat(step) => s"repeat ${proof(step, ro, sig)}"
    case Eval(tac) => s"eval ${renderTerm(tac, ro, sig)}"
  }

  // ── procedure aware printer ───────────────────────────────────────────────────
  private object Prec {
    val Atom = 100
    val App = 90
    val Not = 80
    val Eq = 70
    val Imp = 60
    val Or = 50
    val And = 40
    val Min = 0
  }

  private def paren(need: Boolean, s: String) = if (need) s"($s)" else s

  private def bin(op: String, pOp: Int, lhs: String, lPrec: Int, rhs: String, rPrec: Int, ctx: Int) = {
    paren(ctx >= pOp, s"$lhs $op $rhs")
  }


  private def termP(t: LpTerm[Level.Obj], ro: RenderOptions, ctx: Int, sig: LpSig): String = {
    t match {

      // Infix forms via extractors (object level only)
      case LogicConst.And(l, r) =>
        val ls = termP(l, ro, Prec.And, sig);
        val rs = termP(r, ro, Prec.And, sig)
        bin(andStr, Prec.And, ls, Prec.And, rs, Prec.And, ctx)

      case LogicConst.Or(l, r) =>
        val ls = termP(l, ro, Prec.Or, sig);
        val rs = termP(r, ro, Prec.Or, sig)
        bin(orStr, Prec.Or, ls, Prec.Or, rs, Prec.Or, ctx)

      case LogicConst.Imp(l, r) =>
        val ls = termP(l, ro, Prec.Imp, sig);
        val rs = termP(r, ro, Prec.Imp - 1, sig)
        bin(impStr, Prec.Imp, ls, Prec.Imp, rs, Prec.Imp, ctx)

      case LogicConst.Eq(_, l, r) => //todo: add option to print type
        val ls = termP(l, ro, Prec.Eq + 1, sig);
        val rs = termP(r, ro, Prec.Eq + 1, sig)
        bin(eqStr, Prec.Eq, ls, Prec.Eq, rs, Prec.Eq, ctx)

      case LogicConst.Not(x) =>
        val xs = termP(x, ro, Prec.Not, sig)
        paren(ctx > Prec.Not, s"$negStr $xs")

      // some of the leo connectives i do nor represent explicitly
      // todo: either also hanlde the unapplied cases or handle them differently, for instance by defining rules for them

      case LpTerm.App(LpTerm.Const(SymRef.Leo(HOLSignature.!===.key)), Seq(Arg.ExplicitTypeArg(t), Arg.Explicit(l), Arg.Explicit(r))) =>
        termP(LogicConst.Not(LogicConst.Eq(t,l,r)),ro,Prec.Not,sig)

      // Quantifiers: ∀ (λ (x : T) …)
      case LogicConst.Forall(bind, body) =>
        val bodyStr = termP(body, ro, Prec.Min, sig)
        val (n, t0) = bind
        val bStr = s"(${n.value} : ${ty(t0, ro, sig)})"
        s"($forAllStr(λ $bStr, $bodyStr))"

      case LogicConst.Exists(bind, body) =>
        val bodyStr = termP(body, ro, Prec.Min, sig)
        val (n, t0) = bind
        val bStr = s"(${n.value} : ${ty(t0, ro, sig)})"
        s"($exStr(λ $bStr, $bodyStr))"

      case LogicConst.Choice(bind, body) =>
        val bodyStr = termP(body, ro, Prec.Min, sig)
        val (n, t0) = bind
        val bStr = s"(${n.value} : ${ty(t0, ro, sig)})"
        s"($choiceStr(λ $bStr, $bodyStr))"

      // Generic cases (as you already had)
      case LpTerm.Var(n, _) => n.value
      //case LpTerm.Const(n) => qname(n,ro)

      case LpTerm.Const(SymRef.Leo(i)) if ((leoTypedConnectives ++ leoUntypedConnectives ++ leoBinders).contains(i)) =>
        val ifs = qname(sig.termNames(i), ro)
        s"($ifs)"

      case LpTerm.Const(SymRef.Leo(i)) =>
        val name = sig.termNames(i)
        qname(name, ro)
      case LpTerm.Const(SymRef.LP(qn)) => qname(qn, ro)

      case LpTerm.Lam(bind, body) =>
        val (n, t0) = bind
        val dec = t0 match {
          case Some(t00) => s"(${n.value} : ${ty(t00, ro, sig)})"
          case None => n.value
        }
        paren(ctx > Prec.Min, s"λ $dec, ${termP(body, ro, Prec.Min, sig)}")

      case LpTerm.App(LpTerm.Const(SymRef.Leo(i)), args) if ((leoBinders).keySet.toSeq.contains(i)) =>
        val ifs = qname(sig.termNames(i), ro)
        val encArgs: Seq[String] = args match {
          case Nil => Seq()
          case Arg.ExplicitTypeArg(t) +: remArgs => s"[${olTy(t, ro, sig)}]" +: renderArgs(remArgs,ro,sig)
          case _ => renderArgs(args, ro, sig)
        }
        paren(ctx > Prec.App, s"($ifs) ${encArgs.mkString(" ")}")

      case LpTerm.App(LpTerm.Const(SymRef.Leo(i)), args) if ((leoTypedConnectives).keySet.toSeq.contains(i)) =>
        val ifs0 = qname(sig.termNames(i), ro)
        val parenF = s"($ifs0)"
        val encArgs: Seq[String] = args match {
          case Nil => Seq()
          case Arg.ExplicitTypeArg(t) +: remArgs => s"[${olTy(t, ro, sig)}]" +: renderArgs(remArgs, ro, sig)
          case _ => renderArgs(args, ro, sig)
        }
        paren(ctx > Prec.App, s"$parenF ${encArgs.mkString(" ")}")

      case LpTerm.App(LpTerm.Const(SymRef.Leo(i)), args) if ((leoUntypedConnectives).keySet.toSeq.contains(i)) =>
        val ifs0 = qname(sig.termNames(i), ro)
        val parenF = s"($ifs0)"
        val encArgs = renderArgs(args, ro, sig)
        paren(ctx > Prec.App, s"$parenF ${encArgs.mkString(" ")}")

       case LpTerm.App(f, args) =>
        val ifs = termP(f, ro, Prec.App, sig)
        val encArgs = renderArgs(args, ro, sig)
        paren(ctx > Prec.App, s"$ifs ${encArgs.mkString(" ")}")
    }
  }

  private def renderArg(args: Arg[Level.Obj], ro: RenderOptions, sig: LpSig) = {
    args match {
      case Implicit(t) => s"[${termP(t, ro, 0, sig)}]"
      case Arg.Explicit(t) => termP(t, ro, Prec.Atom, sig)
      case Arg.ImplicitTypeArg(ty) => s"[${olTy(ty, ro, sig)}]"
      case Arg.ExplicitTypeArg(ty) => olTy(ty, ro, sig)
    }
  }
  private def renderArgs(args: Seq[Arg[Level.Obj]], ro: RenderOptions, sig: LpSig) = {
    args.map(ar => renderArg(ar, ro, sig))
  }


  // ── helpers ─────────────────────────────────────────────────────────────────
  private def name(n: Name): String = n.value

  private def qname(q: QName, ro: RenderOptions): String = q.file match {
    case Some(Prefix(mod)) if ro.sigPrefix => s"${mod.value}.${q.local.value}"
    case _ => q.local.value
  }

  private def indent(s: String): String = s.linesIterator.map("\t" + _).mkString("\n")

  private def curly(s: String): String = s"{" + s + "}"

  private def ty(t: LpType, ro: RenderOptions, sig: LpSig): String = t match {
    case LpType.LpSet => "Set"
    case LpType.El(ol) => s"$elStr ${olTy(ol, ro, sig)}"
    case LpType.Pi(bs, body) =>
      val b = bs.map {
        case `Var`(n, Some(t)) => s"(${name(n)} : ${ty(t, ro, sig)})"
        case `Var`(n, None) => s"${name(n)}"
      }.mkString(", Π ")
      s"Π $b, ${ty(body, ro, sig)}"
    case LpType.Arrow(a, b) => s"(${ty(a, ro, sig)} → ${ty(b, ro, sig)})"
    case LpType.Prf(a) => s"$prfStr ${termP(a, ro, Prec.Atom, sig)}"
  }

  private def olTy(ol: OlType, ro: RenderOptions, sig: LpSig): String = ol match {
    //case OlType.O => oTyStr
    //case OlType.I => iTyStr
    case OlType.Base(SymRef.LP(qn)) => qname(qn, ro)
    case OlType.Base(SymRef.Leo(id)) => qname(sig.typeNames(id), ro)
    case OlType.TyVar(n) => name(n)
    case OlType.Fun(args) => s"(${args.map(olTy(_, ro, sig)).mkString(s" $tyConStr ")})"
  }

  private def renderTerm[L <: Level](t: LpTerm[L], ro: RenderOptions, sig: LpSig): String = {
    t match {
      case Var(n, _) => name(n)
      case Const(SymRef.LP(qn)) => qname(qn, ro)
      case Const(SymRef.Leo(id)) => qname(sig.termNames(id), ro)
      case Lam(binding, body) =>
        val bodyStr = renderTerm(body, ro, sig)
        val (n, t0) = binding
        val dec = t0 match {
          case Some(t00) => s"(${name(n)} : ${ty(t00, ro, sig)})"
          case None => name(n)
        }
        s"(λ $dec, $bodyStr)"
      case App(f, args) =>
        val (imps, exps) = args.partition(_.isInstanceOf[Arg.Implicit[_]])
        val is = if (imps.isEmpty) "" else " " + imps.map { case Arg.Implicit(t1) => s"[${renderTerm(t1, ro, sig)}]" }.mkString(" ")
        val es = if (exps.isEmpty) "" else " " + exps.map { case Arg.Explicit(t1) => renderTerm(t1, ro, sig) }.mkString(" ")
        s"(${renderTerm(f, ro, sig)}$is$es)"
    }
  }
}

object pretty {
  implicit val ro: RenderOptions = RenderOptions()

  implicit class StmtOps(private val s: Stmt) extends AnyVal {
    def pretty(implicit sig: LpSig): String = Renderer.stmt(s,sig, ro)
  }

  implicit class ObjLpTermOps(private val t: LpTerm[Level.Obj]) extends AnyVal {
    def pretty(implicit sig: LpSig): String = Renderer.LpTermObj(t, sig, ro)   // <- fixed
  }

  implicit class MetaLpTermOps(private val t: LpTerm[Level.Meta]) extends AnyVal {
    def pretty(implicit sig: LpSig): String = Renderer.LpTermMeta(t, sig, ro)
  }

  implicit class TypeOps(private val t: LpType) extends AnyVal {
    def pretty(implicit sig: LpSig): String = Renderer.typ(t, sig, ro)
  }

  implicit class ProofOps(private val p: Proof) extends AnyVal {
    def pretty(implicit sig: LpSig): String = Renderer.proofText(p, sig, ro)
  }

  implicit class QNameOps(private val p: QName) extends AnyVal {
    def pretty(implicit sig: LpSig): String = Renderer.LpQname(p, ro)
  }
}




