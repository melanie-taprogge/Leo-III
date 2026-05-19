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

  def termEq(lit2: lpLiteralInst) = {
    this.term == lit2.term
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



