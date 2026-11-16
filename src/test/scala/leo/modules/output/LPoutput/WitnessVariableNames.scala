package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.NewLpDatastructures._

/** Rename term variables in generated Lambdapi examples before rendering.
  * The caller supplies a collision-free map for the selected proof context.
  * Use a different map when Leo reuses a name for a different variable.
  */
private[LPoutput] final case class WitnessVariableNames(names: Map[String, String]) {
  private def name(original: Name): Name = Name(names.getOrElse(original.value, original.value))

  private def variable[L <: Level](original: LpTerm.Var[L]): LpTerm.Var[L] =
    LpTerm.Var(name(original.name), original.ty.map(ty))

  def ty(original: LpType): LpType = original match {
    case LpType.Prf(formula) => LpType.Prf(term(formula))
    case LpType.Pi(binders, result) => LpType.Pi(binders.map(variable(_)), ty(result))
    case LpType.Arrow(domain, result) => LpType.Arrow(ty(domain), ty(result))
    case other => other
  }

  private def term[L <: Level](original: LpTerm[L]): LpTerm[L] = original match {
    case v: LpTerm.Var[L] => variable(v)
    case LpTerm.Lam((binder, binderType), body) =>
      LpTerm.Lam(name(binder) -> binderType.map(ty), term(body))
    case LpTerm.App(head, args) =>
      LpTerm.App(term(head), args.map {
        case Arg.Explicit(argument) => Arg.Explicit(term(argument))
        case Arg.Implicit(argument) => Arg.Implicit(term(argument))
        case typeArgument => typeArgument
      })
    case LpTerm.Let((binder, binderType), value, body) =>
      LpTerm.Let(name(binder) -> ty(binderType), term(value), term(body))
    case LpTerm.LpString(contents) => LpTerm.LpString(term(contents))
    case LpTerm.Obj(value) => LpTerm.Obj(term(value))
    case LpTerm.LpList(elements) => LpTerm.LpList(elements.map(term(_)))
    case other => other
  }

  private def proof(body: LpProofScript.Body): LpProofScript.Body = body.map {
    case Left(step) => Left(tactic(step))
    case Right(_) => sys.error("Variable renaming requires a structured Lambdapi proof body")
  }

  def tactic(original: LpProofScript): LpProofScript = original match {
    case LpProofScript.Assume(binders) => LpProofScript.Assume(binders.map(name))
    case LpProofScript.Refine(value, subproof) => LpProofScript.Refine(term(value), subproof.map(tactic))
    case LpProofScript.Have(local, statement, subproof) => LpProofScript.Have(local, ty(statement), proof(subproof))
    case LpProofScript.Rewrite(pattern, rule, side) =>
      LpProofScript.Rewrite(pattern.map(p => p.copy(LpTerm = term(p.LpTerm), hole = term(p.hole))), term(rule), side)
    case LpProofScript.Repeat(step) => LpProofScript.Repeat(tactic(step))
    case LpProofScript.Try(step) => LpProofScript.Try(tactic(step))
    case LpProofScript.Eval(value) => LpProofScript.Eval(term(value))
    case other => other
  }

  private def parameters(params: Seq[(Name, LpType)]): Seq[(Name, LpType)] =
    params.map { case (binder, binderType) => name(binder) -> ty(binderType) }

  def declaration(original: Stmt.Declaration): Stmt.Declaration =
    original.copy(params = parameters(original.params), result = ty(original.result),
      implicitParams = parameters(original.implicitParams))

  def definition(original: Stmt.Definition): Stmt.Definition = {
    val body = original.body match {
      case Stmt.DefBody.LpTermBody(value) => Stmt.DefBody.LpTermBody(term(value))
      case Stmt.DefBody.ProofBody(steps) => Stmt.DefBody.ProofBody(proof(steps))
    }
    original.copy(params = parameters(original.params), ty = original.ty.map(ty), body = body,
      implicitParams = parameters(original.implicitParams))
  }
}
