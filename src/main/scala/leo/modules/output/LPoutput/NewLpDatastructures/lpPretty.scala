package leo.modules.output.LPoutput.NewLpDatastructures

import leo.modules.output.LPoutput.NewLpDatastructures.Stmt._
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm._
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript._
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
import leo.modules.output.LPoutput.NewLpDatastructures.nameGeneration.{nameInt, nameRational, nameReal}
import leo.modules.output.LPoutput.NewLpDatastructures.tptpConstMappings.{leoBinders, leoTypedConnectives, leoUntypedConnectives}
import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures.PrettyConfig

//////////////////////////////////////////
// Utility for pretty printing Lambdai
// Statements, Terms and Types
//////////////////////////////////////////

/** Render Options dictating prefixing and level of implicitness of typing (depending on weather the problem is monomorphic) */
final case class RenderOptions(sigPrefix: Boolean = true, formulaPrefix: Boolean = true, monomorphic: Boolean = true)

object Renderer {

  // ** Printing of Statements

  /**
    * Print Lambdapi statements (declarations, definitions, rules)
    *
    * @param s     original statement
    * @param sig Lambdapi Signature
    * @param ro Render Options dictating prefixing and level of implicitness of typing (depending on weather the problem is monomorphic)
    * @return The statement as a string
    * */
  def stmt(s: Stmt, sig: LpSig, ro: RenderOptions = RenderOptions()): String = s match {
    case Declaration(n, params, res, imps) =>
      val imp = if (imps.isEmpty) "" else s" ${imps.map { case (n, t) => s"[${n.value} : ${ty(t, ro, sig)}]" }.mkString(" ")}"
      val par = if (params.isEmpty) "" else s" ${params.map { case (n, t) => s"(${n.value} : ${ty(t, ro, sig)})" }.mkString(" ")}"
      s"symbol ${n.value}$imp$par: ${ty(res, ro, sig)};\n"

    case Definition(n, params, tyOpt, body, imps, mods) =>
      val mod = if (mods.isEmpty) "" else mods.map {
        case Opaque => "opaque "
      }.mkString("")
      val imp = if (imps.isEmpty) "" else s" ${imps.map { case (n, t) => s"[${n.value} : ${ty(t, ro, sig)}]" }.mkString(" ")}"
      val par = if (params.isEmpty) "" else s" ${params.map { case (n, t) => s"(${n.value} : ${ty(t, ro, sig)})" }.mkString(" ")}"
      val colonTy = tyOpt.fold("")(t => s": ${ty(t, ro, sig)}")
      val eq = body match {
        case DefBody.LpTermBody(t0) => " " + renderTerm(t0, ro, sig) + ";"
        case DefBody.ProofBody(p) =>
          val proofScript = p.map(step =>
            indent(proof(step, ro, sig))).mkString("\n")
          "\n" + "begin\n" + proofScript + "\nend;"
      }
      s"${mod}symbol ${n.value}$imp$par$colonTy ≔$eq\n"

    case Rule(h, vars, rhs) =>
      val vs = if (vars.isEmpty) "" else " " + vars.map(_.value).mkString(" ")
      s"rule ${renderTerm(h, ro, sig)}$vs ↪ ${renderTerm(rhs, ro, sig)};\n"
  }

  /**
    * Print Lambdapi proof scripts
    *
    * @param p   proof script to be encoded
    * @param ro  Render Options dictating prefixing and level of implicitness of typing (depending on weather the problem is monomorphic)
    * @param sig Lambdapi Signature
    * @return The proof script as a string
    * */
  def proof(p: LpProofScript, ro: RenderOptions, sig: LpSig): String = {
    p match {
    case Refine(t, subs) =>
      val proofScript = if (subs.isEmpty) "" else s"\n${curly(subs.map(step => indent(proof(step, ro, sig))).mkString("\n"))}"
      s"refine ${renderTerm(t, ro, sig)}$proofScript;"
    case Have(n, ty0, pr) =>
      //val proofScript = curly(pr.map(step => indent(proof(step, ro, sig))).mkString("\n"))
      val proofScript = curly(pr.map {
        case Left(step) => proof(step, ro, sig)
        case Right(lpScript) => lpScript.pretty(PrettyConfig(ro.sigPrefix, ro.formulaPrefix))
      }.mkString("\n"))
      s"have ${n.value} : ${ty(ty0, ro, sig)}\n" + indent(proofScript) + ";"
    case Rewrite(pattern, rule, side) =>
      val sside = side match {
        case Side.Left => " left ";
        case Side.Right => " "
      }
      val pat = pattern.fold("") { p => s".[${termP(p.hole, ro, 0, sig)} in ${termP(p.LpTerm, ro, 0, sig)}] " }
      s"rewrite$sside$pat${renderTerm(rule, ro, sig)};"
    case Reflexivity => "reflexivity;"
    case Simplify(ns,onlyBeta) =>
      val maybeRuleOff = if (onlyBeta) " rule off " else ""
      s"simplify ${ns.map(_.value).mkString(" ")}$maybeRuleOff;"
    case Repeat(step) => s"repeat ${proof(step, ro, sig)};"
    case Eval(tac) => s"eval ${renderTerm(tac, ro, sig)};"
    case Comment(com) => s"// $com;"
    case Admit => s"admit;"
    case Assume(vars) => s"assume ${vars.map(_.value).mkString(" ")};"
  }
  }

  // ** Printing of terms

  /**
    * Print encoded Meta-level terms
    *
    * @param t   Lambdapi Object-level type
    * @param ro  Render Options dictating prefixing and level of implicitness of typing (depending on weather the problem is monomorphic)
    * @param sig Lambdapi Signature
    * @return The type as a string
    * */
  private def renderTerm(t: LpTerm[Level.Meta], ro: RenderOptions, sig: LpSig): String = {
    t match {
      case Var(n, _) => n.value
      case Const(SymRef.LP(qn)) => qname(qn, ro)
      case Const(SymRef.Leo(id)) => qname(sig.termNames(id), ro)
      case Lam(binding, body) =>
        val bodyStr = renderTerm(body, ro, sig)
        val (n, t0) = binding
        val dec = t0 match {
          case Some(t00) => s"(${n.value} : ${ty(t00, ro, sig)})"
          case None => n.value
        }
        s"(λ $dec, $bodyStr)"
      case App(f, args) =>
        val (imps, exps) = args.partition(arg => arg.isInstanceOf[Arg.Implicit[_]] || arg.isInstanceOf[Arg.ImplicitTypeArg[_]])
        val is = if (imps.isEmpty) "" else " " + imps.map {
          case Arg.Implicit(t1) => s"[${renderTerm(t1, ro, sig)}]"
          case Arg.ImplicitTypeArg(t1) => s"[${olTy(t1, ro, sig)}]"
        }.mkString(" ")
        val es = if (exps.isEmpty) "" else " " + exps.map {
          case Arg.Explicit(t1) => renderTerm(t1, ro, sig)
          case Arg.ExplicitTypeArg(t1) => olTy(t1, ro, sig)

        }.mkString(" ")
        s"(${renderTerm(f, ro, sig)}$is$es)"
      case Wildcard() => "_"
      case Obj(t) => termP(t, ro, Prec.Atom, sig)
      case TptpInt(n) => qname(QName.in(Prefix.Sig, nameInt(n)), ro)
      case LpString(t) => s"\"${renderTerm(t,  ro, sig)}\""
      case LpInt(n) => n.toString()
      case RewritePattern(pattern, hole) => s".[${termP(hole, ro, Prec.Atom, sig)} in ${termP(pattern, ro, Prec.Atom, sig)}]"
      case LpList(els) => if (els.isEmpty) "□" else s"(${els.map(renderTerm(_, ro, sig)).mkString(" ⸬ ")} ⸬ □)"
    }
  }

  /**
    * Print object-logical encoded terms
    *
    * @param t  Lambdapi Object-level term
    * @param ro  Render Options dictating prefixing and level of implicitness of typing (depending on weather the problem is monomorphic)
    * @param ctx the Prec of the environemnt
    * @param sig Lambdapi Signature
    * @return The object level term as a string
    * */
  def termP(t: LpTerm[Level.Obj], ro: RenderOptions, ctx: Int, sig: LpSig): String = {
    t match {

      // ** Binary connectives
      case LogicConst.And(l, r) =>
        val ls = termP(l, ro, Prec.And, sig)
        val rs = termP(r, ro, Prec.And, sig)
        bin(andStr, Prec.And, ls, rs, ctx)
      case LogicConst.Or(l, r) =>
        val ls = termP(l, ro, Prec.Or, sig)
        val rs = termP(r, ro, Prec.Or, sig)
        bin(orStr, Prec.Or, ls, rs, ctx)
      case LogicConst.Imp(l, r) =>
        val ls = termP(l, ro, Prec.Imp, sig)
        val rs = termP(r, ro, Prec.Imp - 1, sig)
        bin(impStr, Prec.Imp, ls, rs, ctx)
      case LogicConst.Eq(_, l, r) => //todo: add option to print type
        val ls = termP(l, ro, Prec.Eq + 1, sig)
        val rs = termP(r, ro, Prec.Eq + 1, sig)
        bin(eqStr, Prec.Eq, ls, rs, ctx)

      // ** Unary connectives
      case LogicConst.Not(x) =>
        val xs = termP(x, ro, Prec.Not, sig)
        paren(ctx > Prec.Not, s"$negStr $xs")

      // ** TPTP connectives abstracted away in the Lambdapi encoding
      case LogicConst.InEq(t, l, r) => //todo: add option to print type
        termP(LogicConst.Not(LogicConst.Eq(t, l, r)),ro, ctx, sig)

      // ** Binders
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

      // ** Placeholder
      case Wildcard() => "_"

      // ** Variables
      case LpTerm.Var(n, _) => n.value

      // ** Unapplied connectives
      case LpTerm.Const(SymRef.Leo(i)) if (leoTypedConnectives ++ leoUntypedConnectives ++ leoBinders).contains(i) =>
        val ifs = qname(sig.termNames(i), ro)
        s"($ifs)"

      // ** generic Constants
      case LpTerm.Const(SymRef.Leo(i)) =>
        val name = sig.termNames(i)
        qname(name, ro)
      case LpTerm.Const(SymRef.LP(qn)) => qname(qn, ro)

      // ** Lambda abstraction
      case LpTerm.Lam(bind, body) =>
        val (n, t0) = bind
        val dec = t0 match {
          case Some(t00) => s"(${n.value} : ${ty(t00, ro, sig)})"
          case None => n.value
        }
        paren(ctx > Prec.Min, s"λ $dec, ${termP(body, ro, Prec.Min, sig)}")

        // ** partially applied connectives
      case LpTerm.App(LpTerm.Const(SymRef.Leo(i)), args) if leoBinders.keySet.toSeq.contains(i) =>
        val ifs = qname(sig.termNames(i), ro)
        val encArgs: Seq[String] = args match {
          case Nil => Seq()
          case Arg.ExplicitTypeArg(t) +: remArgs => s"[${olTy(t, ro, sig)}]" +: renderArgs(remArgs,ro,sig)
          case _ => renderArgs(args, ro, sig)
        }
        paren(ctx > Prec.App, s"($ifs) ${encArgs.mkString(" ")}")
      case LpTerm.App(LpTerm.Const(SymRef.Leo(i)), args) if leoTypedConnectives.keySet.toSeq.contains(i) =>
        val ifs0 = qname(sig.termNames(i), ro)
        val parenF = s"($ifs0)"
        val encArgs: Seq[String] = args match {
          case Nil => Seq()
          case Arg.ExplicitTypeArg(t) +: remArgs => s"[${olTy(t, ro, sig)}]" +: renderArgs(remArgs, ro, sig)
          case _ => renderArgs(args, ro, sig)
        }
        paren(ctx > Prec.App, s"$parenF ${encArgs.mkString(" ")}")
      case LpTerm.App(LpTerm.Const(SymRef.Leo(i)), args) if leoUntypedConnectives.keySet.toSeq.contains(i) =>
        val ifs0 = qname(sig.termNames(i), ro)
        val parenF = s"($ifs0)"
        val encArgs = renderArgs(args, ro, sig)
        paren(ctx > Prec.App, s"$parenF ${encArgs.mkString(" ")}")

        // ** generic application
       case LpTerm.App(f, args) =>
        val ifs = termP(f, ro, Prec.App, sig)
        val encArgs = renderArgs(args, ro, sig)
        paren(ctx > Prec.App, s"$ifs ${encArgs.mkString(" ")}")

        // ** numbers
      case TptpInt(n) => qname(QName.in(Prefix.Sig,nameInt(n)),ro)
      case TptpRational(n0, n1) => qname(QName.in(Prefix.Sig,nameRational(n0, n1)),ro)
      case TptpReal(n0, n1, n2) => qname(QName.in(Prefix.Sig,nameReal(n0, n1, n2)),ro)
      case LpInt(n) => n.toString()
      case LpList(els) => if (els.isEmpty) "□" else s"(${els.map(termP(_, ro, Prec.Not, sig)).mkString(" ⸬ ")} ⸬ □)"
    }
  }

  private object Prec {
    val Atom = 100
    val App = 90
    val Not = 80
    val Eq = 70
    val Imp = 40
    val Or = 50
    val And = 60
    val Min = 0
  }

  /** Enclose term in parenthesis if necessary */
  private def paren(need: Boolean, s: String) = if (need) s"($s)" else s

  /**
    * Enclose binary-connective term in parenthesis if necessary
    *
    * @param op  the binary operator as a string
    * @param pOp the Prec of the operator
    * @param ctx the Prec of the environemnt
    * @param lhs the term on the left as a string
    * @param rhs the term on the right as a string
    * @return The binary formula as a string enclosed in parenthesis if necessary
    * */
  private def bin(op: String, pOp: Int, lhs: String, rhs: String, ctx: Int) = paren(ctx >= pOp, s"$lhs $op $rhs")


  /** Helper for printing an individual argument */
  private def renderArg(arg: Arg[Level.Obj], ro: RenderOptions, sig: LpSig) = {
    arg match {
      case Arg.Implicit(t) => s"[${termP(t, ro, 0, sig)}]"
      case Arg.Explicit(t) => termP(t, ro, Prec.Atom, sig)
      case Arg.ImplicitTypeArg(ty) => s"[${olTy(ty, ro, sig)}]"
      case Arg.ExplicitTypeArg(ty) => olTy(ty, ro, sig)
    }
  }

  /** Helper for printing a sequence of arguments */
  private def renderArgs(args: Seq[Arg[Level.Obj]], ro: RenderOptions, sig: LpSig) = {
    args.map(ar => renderArg(ar, ro, sig))
  }

  /** Helper for printing a name with potential prefixes */
  def qname(q: QName, ro: RenderOptions): String = q.file match {
    case Some(p) =>
      p match {
        case Prefix.Sig => if (ro.sigPrefix) s"S.${q.local.value}" else q.local.value
        case Prefix.Formula => if (ro.formulaPrefix) s"F.${q.local.value}" else q.local.value
      }
    case _ => q.local.value
  }

  /** Helper for adding indents to a string */
  private def indent(s: String): String = s.linesIterator.map("\t" + _).mkString("\n")

  /** Helper for enclosing a term in curly brackets */
  private def curly(s: String): String = s"{" + s + "}"


  // ** Printing of Types

  /**
    * Print encoded Meta-level types
    *
    * @param t   Lambdapi Object-level type
    * @param ro  Render Options dictating prefixing and level of implicitness of typing (depending on weather the problem is monomorphic)
    * @param sig Lambdapi Signature
    * @return The type as a string
    * */
  def ty(t: LpType, ro: RenderOptions, sig: LpSig): String = t match {
    case LpType.LpSet => "Set"
    case LpType.El(ol) => s"$elStr ${olTy(ol, ro, sig)}"
    case LpType.Pi(bs, body) =>
      val b = bs.map {
        case `Var`(n, Some(t)) => s"(${n.value} : ${ty(t, ro, sig)})"
        case `Var`(n, None) => s"${n.value}"
      }.mkString(", Π ")
      s"Π $b, ${ty(body, ro, sig)}"
    case LpType.Arrow(a, b) => s"(${ty(a, ro, sig)} → ${ty(b, ro, sig)})"
    case LpType.Prf(a) => s"$prfStr ${termP(a, ro, Prec.Atom, sig)}"
    case LpType.Old(st) => st
  }

  /**
    * Print encoded Object-level types
    *
    * @param t   Lambdapi Object-level type
    * @param ro  Render Options dictating prefixing and level of implicitness of typing (depending on weather the problem is monomorphic)
    * @param sig Lambdapi Signature
    * @return The type as a string
    * */
  private def olTy(ol: OlType, ro: RenderOptions, sig: LpSig): String = ol match {
    case OlType.Base(SymRef.LP(qn)) => qname(qn, ro)
    case OlType.Base(SymRef.Leo(id)) => qname(sig.typeNames(id), ro)
    case OlType.TyVar(n) => n.value
    case OlType.Fun(args) => s"(${args.map(olTy(_, ro, sig)).mkString(s" $tyConStr ")})"
  }
}




