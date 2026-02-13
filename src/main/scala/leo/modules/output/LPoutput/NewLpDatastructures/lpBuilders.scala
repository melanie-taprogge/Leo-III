package leo.modules.output.LPoutput.NewLpDatastructures

import LogicConst._
import leo.datastructures.Clause
import leo.modules.output.LPoutput.NewLpDatastructures.Lifting.{ProofTerm, liftOlVars}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Var
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.Pi
import leo.modules.output.LPoutput.NewLpDatastructures.OlType.TyVar

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
  * A Lambdapi representation of a clause.
  *
  * @param term the disjunction of the clause’s literals, represented as an `LpTerm`
  * @param lits the original list of object-level literals
  * @param vars the clause’s bound variables, each either a term variable or a type variable
  * @param asMl the clause encoded as a meta-level type (Dependant types for clause-variables and propositions encoded as types)
  */
case class lpClauseInst(term: LpTerm[Level.Obj], lits: Seq[LpTerm[Level.Obj]], vars: Seq[Either[Var[Level.Obj],TyVar]], asMl: LpType) {
  /** Returns `vars` as a plain sequence of `lpOlTerm`. */
  def metaVars: Seq[Var[Level.Meta]] = vars.map(liftOlVars)
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
  def apply(lits: Seq[LpTerm[Level.Obj]], vars: Seq[Either[Var[Level.Obj], TyVar]]): lpClauseInst = { // used to translate -> now directly use
    val disjunction = nAry.disjunction(lits)
    val liftedVars = vars.map(liftOlVars)
    val mlTerm = if (liftedVars.nonEmpty) Pi(liftedVars,ProofTerm(disjunction)) else ProofTerm(disjunction)
    lpClauseInst(disjunction,lits,vars,mlTerm)
  }

  /**
    * Encode a sequence of clauses into Lambdapi, producing both their translated
    * clause instances and a map of all implicitly bound variables.
    */
  def apply_to_set(cls: Seq[Clause]): (Map[Int, String], Seq[lpClauseInst]) = {
    val allImpBoundVars = cls.flatMap(_.implicitlyBound).distinct.sortBy(_._1).reverse
    val fullBvarsMap = ClauseEncoding.clauseVars2LP(allImpBoundVars)._2
    val encCls = cls.map(cl => ClauseEncoding.lits2Lp(cl.lits, fullBvarsMap))
    val encVars: Seq[Seq[Either[Var[Level.Obj], TyVar]]] = cls.map(cl => TermEncoding.vars2Lp(cl.implicitlyBound, fullBvarsMap).map(Left(_)))
    (fullBvarsMap, encCls.zip(encVars).map(ecnCl => lpClauseInst(ecnCl._1, ecnCl._2)))
  }
}



