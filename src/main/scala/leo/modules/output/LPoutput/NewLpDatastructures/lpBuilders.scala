package leo.modules.output.LPoutput.NewLpDatastructures

// smart constructors for things like clauses, conjunctions, disjunctions, etc.
import LogicConst._
import leo.datastructures.Clause
import leo.modules.output.LPoutput.Lifting.{ProofTerm, liftOlVars}
import leo.modules.output.LPoutput.NewLpDatastructures.Encoder.{clauseLits2Lp, clauseVars2LP, vars2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Var}
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{Pi}
import leo.modules.output.LPoutput.NewLpDatastructures.OlType.TyVar

// n-ary conjunctions or disjuncions

object nAry {

  /** Smart constructor for binary conjunctions/ disjunctions: handles 0/1-ary cases. */
  def mk(con: LpTerm.Const[Level.Obj], terms: Seq[LpTerm[Level.Obj]]): LpTerm[Level.Obj] = {
    terms match {
      case Nil => identity(con)
      case t +: Nil => t
      case _ => terms.init.foldRight(terms.last)((term, accumulator) => LpTerm.App(con,Seq(Arg.Explicit(term),Arg.Explicit(accumulator))))
    }
  }


  /** Convenience constructors for common connectives. */
  def conjunction(terms: Seq[LpTerm[Level.Obj]]): LpTerm[Level.Obj] =
    mk(cAnd, terms)

  def disjunction(terms: Seq[LpTerm[Level.Obj]]): LpTerm[Level.Obj] =
    mk(cOr, terms)

  /** helper */
  private def identity(conn: LpTerm[Level.Obj]): LpTerm[Level.Obj] = conn match {
    case `cAnd` => Top
    case `cOr` => Bot
    case _ => throw new Exception(s"Error in LP-Encoding: Trying to construct a binary connective term for 0 elements and connective ${conn}")
  }
}


case class lpClauseInst(
                         term: LpTerm[Level.Obj],
                         lits: Seq[LpTerm[Level.Obj]],
                         vars: Seq[Either[Var[Level.Obj],TyVar]],
                         asMl: LpType
                       ) {
  /** Returns `vars` as a plain sequence of `lpOlTerm`. */
  def metaVars: Seq[Var[Level.Meta]] = vars.map(liftOlVars(_)) //todo: Do i actually need cariables to ever be OL?
}

object lpClauseInst {
  def apply(lits: Seq[LpTerm[Level.Obj]], vars: Seq[Either[Var[Level.Obj], TyVar]]): lpClauseInst = { // used to translate -> now directly use
    val disjunction = nAry.disjunction(lits)
    val liftedVars = vars.map(liftOlVars(_))
    val mlTerm = if (liftedVars.nonEmpty) Pi(liftedVars,ProofTerm(disjunction)) else ProofTerm(disjunction)
    lpClauseInst(disjunction,lits,vars,mlTerm)
  }

  def apply_to_set(cls: Seq[Clause]): (Map[Int, String], Seq[lpClauseInst]) = {
    val allImpBoundVars = cls.flatMap(_.implicitlyBound).distinct.sortBy(_._1).reverse
    val fullBvarsMap = clauseVars2LP(allImpBoundVars)._2
    val encCls = cls.map(cl => clauseLits2Lp(cl.lits, fullBvarsMap)._1)
    val encVars: Seq[Seq[Either[Var[Level.Obj], TyVar]]] = cls.map(cl => vars2Lp(cl.implicitlyBound, fullBvarsMap).map(Left(_)))
    (fullBvarsMap, encCls.zip(encVars).map(ecnCl => lpClauseInst(ecnCl._1, ecnCl._2)))
  }
}



