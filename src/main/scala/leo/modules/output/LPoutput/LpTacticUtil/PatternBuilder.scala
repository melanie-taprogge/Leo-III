package leo.modules.output.LPoutput.LpTacticUtil

import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{RewritePattern, Side}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Wildcard
import leo.modules.output.LPoutput.NewLpDatastructures.{HolBaseTypes, Level, LogicConst, LpTerm, OlType, QName, SymRef, nAry}

object PatternBuilder {

  /**
    * Wrapper for additional information concerning the properties of the literal necessary to generate rewrite pattern for entire clauses
    *
    * @param position The index of the literal in the clause
    * @param sideIfEq Indicates if the pattern is supposed to only target one side of an equational literal.
    *                 None => Literal is targeted as a whole
    *                 Some(Side.Left) / Some(Side.Right) => The pattern will target the specific side
    * @param polarity Indicates if the pattern is supposed to only target the body of a literal with negative polarity
    *                 True: Polarity is positive or entire (potentially negated) literal should be targeted
    *                 False: Literal is negative and pattern should target the body only.
    */
  case class PatternInfo(position: Int,
                         sideIfEq: Option[(Side, OlType)],
                         polarity: Boolean)

  /**
    * Generator for pattern-terms targeting specific sub-structures of Literals.
    *
    * @param info Wrapped information regarding the sub-structures to be targeted
    * @param hole Shape of the term to be used as a whole, typically a pattern variable like "x"
    * @return A term to be used to construct a rewrite pattern for the Lambdapi rewrite-tactic
    */
  def generatePatternLit(info: PatternInfo, hole: LpTerm[Level.Obj]): LpTerm[Level.Obj] = {
    val maybeEqLit = if (info.sideIfEq.isDefined) info.sideIfEq.get match {
      case (Side.Left, ty) => LogicConst.Eq(ty, Wildcard[Level.Obj], hole)
      case (Side.Right, ty) => LogicConst.Eq(ty, hole, Wildcard[Level.Obj])
    } else hole
    if (info.polarity) maybeEqLit else LogicConst.Not(maybeEqLit)
  }

  /**
    * Generator for patterns to be used for the Lambdapi rewrite-tactic to target specific literals or sub-structures thereof in a clause.
    *
    * @param termPosSeq Sequence of wrapped information for each literal to be targeted (defining the index and the the sub-structures of interest)
    * @param clauseLen  Number of literals in the clause the pattern is generated for
    * @return A rewrite pattern to be used to instansiate the Lambdapi rewrite-tactic
    */
  def generateClausePattern(termPosSeq: Seq[PatternInfo], clauseLen: Int): RewritePattern = {
    val patternVar = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("x")))
    val maxTermPos = termPosSeq.map(_.position).max
    assert(maxTermPos < clauseLen, s"Error in Lambdapi encoidng when generating a pattern: Literal index (${maxTermPos} out of bounds for clause of length $clauseLen)")
    var args: Seq[LpTerm[Level.Obj]] = Seq.fill(clauseLen)(Wildcard[Level.Obj])
    termPosSeq foreach { pos =>
      args = args.updated(pos.position, generatePatternLit(pos, patternVar))
    }
    RewritePattern(nAry.disjunction(args), patternVar)
  }

  /** Enclose the pattern given in a Lambdapi-Rewrite-Pattern in an equality, useful when proving steps like "clause A = Clause B" */
  def embedPatternInEq(pat: RewritePattern, side: Side): RewritePattern = {
    val term = pat.LpTerm
    val embTerm = side match {
      case Side.Left => LogicConst.Eq(HolBaseTypes.O, term, Wildcard[Level.Obj])
      case Side.Right => LogicConst.Eq(HolBaseTypes.O, Wildcard[Level.Obj], term)
    }
    RewritePattern(embTerm, pat.hole)
  }
}
