package leo.modules.output.LPoutput.NewLpDatastructures

import LogicConst._
import leo.Out
import leo.datastructures.{Clause, fuseMaps}
import leo.modules.output.LPoutput.NewLpDatastructures.Lifting.{ProofTerm, liftOlVars}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Var
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.Pi
import leo.modules.output.LPoutput.NewLpDatastructures.OlMonoType.TyVar

//////////////////////////////////////////
// smart constructors for things like clauses, conjunctions, disjunctions, etc.
//////////////////////////////////////////

/** Constructors for n-ary versions of terms with binary connectives*/
object nAry {

  private def mk(con: LpTerm.Const[Level.Obj], terms: Seq[LpTerm[Level.Obj]]): LpTerm[Level.Obj] = {
    terms match {
      case Nil => identity(con)
      case t +: Nil => t
      case _ => terms.init.foldRight(terms.last)((term, accumulator) => LpTerm.App(con,Seq(Arg.Explicit(term),Arg.Explicit(accumulator))))
    }
  }

  /**
    * Convenience constructor for n-ary conjunction
    *
    * @param terms A sequence of encoded Object-Level terms
    * @return If the given sequence is non-empty, returns a conjunction of the terms
    *         For empty sequences, top is returned
    * */
  def conjunction(terms: Seq[LpTerm[Level.Obj]]): LpTerm[Level.Obj] =
    mk(cAnd, terms)

  /**
    * Convenience constructor for n-ary disjunction
    *
    * @param terms A sequence of encoded Object-Level terms
    * @return If the given sequence is non-empty, returns a disjunction of the terms
    *         For empty sequences, bottom is returned
    * */
  def disjunction(terms: Seq[LpTerm[Level.Obj]]): LpTerm[Level.Obj] =
    mk(cOr, terms)

  /** helper */
  private def identity(conn: LpTerm[Level.Obj]): LpTerm[Level.Obj] = conn match {
    case `cAnd` => Top
    case `cOr` => Bot
    case _ => throw new Exception(s"Error in LP-Encoding: Trying to construct a binary connective term for 0 elements and connective $conn")
  }
}

/**
  * Small smart constructors for recurring object-level Lambdapi AST fragments.
  *
  * These helpers deliberately stay close to the core AST:
  *   - binders are ordinary `LpTerm.Var[Level.Obj]` values
  *   - lambda binders reuse the variable name and type
  *   - Π binders are obtained by lifting those same object variables
  */
object lpTermBuilder {

  /** Apply an object-level term to explicit object-level arguments. */
  def app(f: LpTerm[Level.Obj], args: Seq[LpTerm[Level.Obj]]): LpTerm[Level.Obj] =
    if (args.isEmpty) f else LpTerm.App(f,args.map(Arg.Explicit[Level.Obj]))

  /** Substitute a free, named object-level variable without crossing a same-named binder. */
  def substituteVariable(term: LpTerm[Level.Obj],
                         variable: Name,
                         replacement: LpTerm[Level.Obj]): LpTerm[Level.Obj] = term match {
    case current @ LpTerm.Var(name, _) => if (name == variable) replacement else current
    case current @ LpTerm.Const(_) => current
    case current @ LpTerm.Wildcard() => current
    case current @ LpTerm.TptpInt(_) => current
    case current @ LpTerm.LpInt(_) => current
    case current @ LpTerm.TptpRational(_, _) => current
    case current @ LpTerm.TptpReal(_, _, _) => current
    case LpTerm.LpList(elements) =>
      LpTerm.LpList(elements.map(substituteVariable(_, variable, replacement)))
    case current @ LpTerm.Lam((binderName, _), _) if binderName == variable => current
    case LpTerm.Lam(binder, body) =>
      LpTerm.Lam(binder, substituteVariable(body, variable, replacement))
    case LpTerm.App(function, args) =>
      LpTerm.App(
        substituteVariable(function, variable, replacement),
        args.map {
          case Arg.Explicit(argument) => Arg.Explicit(substituteVariable(argument, variable, replacement))
          case Arg.Implicit(argument) => Arg.Implicit(substituteVariable(argument, variable, replacement))
          case typeArgument => typeArgument
        }
      )
  }

  /** Apply arguments and beta-reduce the leading object-level lambda binders. */
  def betaApply(function: LpTerm[Level.Obj],
                args: Seq[Arg[Level.Obj]]): LpTerm[Level.Obj] = {
    def applyRemaining(current: LpTerm[Level.Obj], remaining: Seq[Arg[Level.Obj]]): LpTerm[Level.Obj] =
      (current, remaining) match {
        case (LpTerm.Lam((binderName, _), body), Arg.Explicit(argument) +: tail) =>
          applyRemaining(substituteVariable(body, binderName, argument), tail)
        case (LpTerm.Lam((binderName, _), body), Arg.Implicit(argument) +: tail) =>
          applyRemaining(substituteVariable(body, binderName, argument), tail)
        case (_, Seq()) => current
        case _ => LpTerm.App(current, remaining)
      }
    applyRemaining(function, args)
  }

  /** Reference to a proof-local Lambdapi symbol. */
  def localObj(name: Name): LpTerm[Level.Obj] =
    LpTerm.Const[Level.Obj](SymRef.LP(QName.local(name.value)))

  /** The HOL type of an object-level variable encoded as `τ a`. */
  def olTy(v: Var[Level.Obj]): OlMonoType = v.ty match {
    case Some(LpType.El(ty)) => ty
    case other => throw new IllegalArgumentException(s"Expected object variable with HOL type, got $other")
  }

  /** Wrap an object-level term in lambdas over the given object variables. */
  def lam(binders: Seq[Var[Level.Obj]], body: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
    binders.foldRight(body) { case (v, acc) => LpTerm.Lam[Level.Obj](v.name -> v.ty, acc) }

  /** Wrap a meta-level type in Π binders over the given object variables. */
  def pi(binders: Seq[Var[Level.Obj]], body: LpType): LpType =
    if (binders.isEmpty) body else Pi(binders.map(Lifting.OlVarM(_)), body)

  /** Build the object-level function type represented by lambda-wrapping a term of `bodyTy`. */
  def funTy(binders: Seq[Var[Level.Obj]], bodyTy: OlMonoType): OlMonoType =
    if (binders.isEmpty) bodyTy else OlMonoType.Fun(binders.map(olTy) :+ bodyTy)

  /** Build a proof type of the form `π premise -> π (l1 ∨ ... ∨ ln)`. */
  def proofArrow(premise: lpLiteralInst, derived: Seq[lpLiteralInst]): LpType =
    LpType.Arrow(LpType.Prf(premise.term), LpType.Prf(nAry.disjunction(derived.map(_.term))))

  /** Build the type of a possibly binder-lifted literal transformation rule. */
  def ruleType(binders: Seq[Var[Level.Obj]], premise: lpLiteralInst, derived: Seq[lpLiteralInst]): LpType =
    pi(binders, proofArrow(premise, derived))
}
/**
  * A Lambdapi representation of a literal.
  *
  * @param term the literal represented as an `LpTerm`
  * @param polarity the polarity of the literal
  * @param eq a boolean indicating weather the literal is equational or not
  */
case class lpLiteralInst(term: LpTerm[Level.Obj], polarity: Boolean, eq: Boolean) {

  private def stripLeadingNeg(term0: LpTerm[Level.Obj], n: Int = 0): (LpTerm[Level.Obj],Int) = {
    term0 match {
      case LogicConst.Not(body) => stripLeadingNeg(body,n + 1)
      case _ => (term0,n)
    }
  }

  private def wrapInNeg(term0: LpTerm[Level.Obj], n: Int): LpTerm[Level.Obj] ={
    if (n > 0)  wrapInNeg(LogicConst.Not(term0),n-1)
    else term0
  }

  /**
    * The proposition represented by this literal without its polarity wrapper.
    *
    * A negative encoded literal is expected to store its proposition below one
    * leading negation. `None` reports a malformed value instead of silently
    * returning the already-negated term.
    */
  def unsignedTerm: Option[LpTerm[Level.Obj]] = {
    if (polarity) Some(term)
    else term match {
      case LogicConst.Not(body) => Some(body)
      case _ => None
    }
  }

  def flipIfEq: lpLiteralInst = {
    val strippedEq = stripLeadingNeg(term)
    strippedEq._1 match {
      case LogicConst.Eq(ty, lhs, rhs) =>
        val flippedEq = LogicConst.Eq(ty, rhs, lhs)
        val wrappedEq = wrapInNeg(flippedEq,strippedEq._2)
        lpLiteralInst(wrappedEq,polarity,eq)
      case _ => Out.lp_debug_info(s"could not flip: ${strippedEq._1}"); this
    }
  }

  /** Type of the sides of an equational literal, ignoring leading negations. */
  def equalitySideType: Option[OlMonoType] = {
    stripLeadingNeg(term)._1 match {
      case LogicConst.Eq(ty, _, _) => Some(ty)
      case _ => None
    }
  }

  def termEq(lit2: lpLiteralInst) = {
    this.term == lit2.term
  }
}

object lpLiteralInst {
  /** Construct an equational literal; `sideType` is the type of `lhs` and `rhs`. */
  def equality(sideType: OlMonoType,
               lhs: LpTerm[Level.Obj],
               rhs: LpTerm[Level.Obj],
               polarity: Boolean): lpLiteralInst = {
    val equality = LogicConst.Eq(sideType, lhs, rhs)
    lpLiteralInst(
      if (polarity) equality else LogicConst.Not(equality),
      polarity,
      eq = true
    )
  }
}

/**
  * A Lambdapi representation of a clause.
  *
  * @param term the disjunction of the clause’s literals, represented as an `LpTerm`
  * @param lits the original list of object-level literals
  * @param vars the clause’s bound variables, each either a term variable or a type variable
  * @param asMl the clause encoded as a meta-level type (Dependant types for clause-variables and propositions encoded as types)
  */
case class lpClauseInst(term: LpTerm[Level.Obj], lits: Seq[lpLiteralInst], vars: Seq[Either[Var[Level.Obj],TyVar]], asMl: LpType) {
  /** Returns `vars` as a plain sequence of `lpOlTerm`. */
  def metaVars: Seq[Var[Level.Meta]] = vars.map(liftOlVars)

  def termEq(cl2: lpClauseInst) = {
    this.term == cl2.term
  }
}

object lpClauseInst {

  /**
    * Construct a clause instance from its literals and bound variables.
    *
    * This creates the disjunction of `lits`, lifts bound variables to the meta-level,
    * and builds the corresponding meta-level Π-type ending in a `ProofTerm`.
    *
    * @param lits the object-level literals of the clause
    * @param vars the clause's object-level bound variables
    * @return the corresponding `lpClauseInst`
    */
  def apply(lits: Seq[lpLiteralInst], vars: Seq[Either[Var[Level.Obj], TyVar]]): lpClauseInst = { // used to translate -> now directly use
    val disjunction = nAry.disjunction(lits.map(_.term))
    val liftedVars = vars.map(liftOlVars)
    val mlTerm = if (liftedVars.nonEmpty) Pi(liftedVars,ProofTerm(disjunction)) else ProofTerm(disjunction)
    lpClauseInst(disjunction,lits,vars,mlTerm)
  }

  private def apply_to_single(cl: Clause, fullBvarsMap: Map[Int, String]) = {
    val encCls = ClauseEncoding.lits2Lp(cl.lits, fullBvarsMap)
    val encVars = TermEncoding.vars2Lp(cl.implicitlyBound, fullBvarsMap).map(Left(_))
    lpClauseInst(encCls,encVars)
  }

  /**
    * Encode a sequence of clauses into Lambdapi, producing both their translated
    * clause instances and a map of all implicitly bound variables.
    */
  def apply_to_set(cls: Seq[Clause]): (Map[Int, String], Seq[lpClauseInst]) = {
    val allImpBoundVars = cls.flatMap(_.implicitlyBound).distinct.sortBy(_._1).reverse
    val fullBvarsMap = ClauseEncoding.clauseVars2LP(allImpBoundVars)._2
    val encCls = cls.map(cl => apply_to_single(cl, fullBvarsMap))
    (fullBvarsMap, encCls)
  }

  def apply_to_pair(cl0: Clause, cl1: Clause): (Map[Int, String], lpClauseInst, lpClauseInst) = {
    val allImpBoundVars = Seq(cl0,cl1).flatMap(_.implicitlyBound).distinct.sortBy(_._1).reverse
    val fullBvarsMap = ClauseEncoding.clauseVars2LP(allImpBoundVars)._2
    val encCls0 = apply_to_single(cl0, fullBvarsMap)
    val encCls1 = apply_to_single(cl1, fullBvarsMap)
    (fullBvarsMap, encCls0, encCls1)
  }
}
