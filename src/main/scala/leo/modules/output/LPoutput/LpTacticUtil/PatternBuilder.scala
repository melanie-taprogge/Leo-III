package leo.modules.output.LPoutput.LpTacticUtil

import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{RewritePattern, Side}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, HolBaseTypes, Level, LogicConst, LpTerm, OlMonoType, QName, SymRef, nAry}

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
                         sideIfEq: Option[(Side, OlMonoType)],
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
      case (Side.Left, ty) => LogicConst.Eq(ty, Wildcard[Level.Obj](), hole)
      case (Side.Right, ty) => LogicConst.Eq(ty, hole, Wildcard[Level.Obj]())
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
    var args: Seq[LpTerm[Level.Obj]] = Seq.fill(clauseLen)(Wildcard[Level.Obj]())
    termPosSeq foreach { pos =>
      args = args.updated(pos.position, generatePatternLit(pos, patternVar))
    }
    RewritePattern(nAry.disjunction(args), patternVar)
  }

  /**
    * Build a rewrite pattern focused on one literal of a clause.
    *
    * This overload is useful when the caller has already built the exact
    * pattern term for the targeted literal, for example after searching for a
    * rewrite occurrence inside that literal.
    */
  def generateClausePattern(litIdx: Int,
                            clauseLen: Int,
                            patternTerm: LpTerm[Level.Obj],
                            patternVar: LpTerm[Level.Obj] = Const[Level.Obj](SymRef.LP(QName.local("x")))): RewritePattern = {
    assert(litIdx < clauseLen, s"Error in Lambdapi encoding when generating a pattern: Literal index ($litIdx out of bounds for clause of length $clauseLen)")
    val args = Seq.fill(clauseLen)(Wildcard[Level.Obj]()).updated(litIdx, patternTerm)
    RewritePattern(nAry.disjunction(args), patternVar)
  }

  /** Enclose the pattern given in a Lambdapi-Rewrite-Pattern in an equality, useful when proving steps like "clause A = Clause B" */
  def embedPatternInEq(pat: RewritePattern, side: Side): RewritePattern = {
    val term = pat.LpTerm
    val embTerm = side match {
      case Side.Left => LogicConst.Eq(HolBaseTypes.O, term, Wildcard[Level.Obj]())
      case Side.Right => LogicConst.Eq(HolBaseTypes.O, Wildcard[Level.Obj](), term)
    }
    RewritePattern(embTerm, pat.hole)
  }

  /**
    * Find exact occurrences of an encoded rewrite LHS in a term.
    *
    * The result contains:
    *   - a Lambdapi rewrite pattern that targets the found occurrences;
    *   - the term obtained by replacing those occurrences with the RHS;
    *   - the number of occurrences found;
    *   - whether any occurrence appeared below a Lambdapi binder.
    *
    * This intentionally performs only exact encoded-term matching. It does not
    * instantiate non-ground rewrite rules.
    */
  def findRWTerm(termRwMap: Map[LpTerm[Level.Obj], LpTerm[Level.Obj]],
                 searchIn: LpTerm[Level.Obj],
                 rwUnderBinder: Boolean = false,
                 patternVar: LpTerm[Level.Obj] = Const[Level.Obj](SymRef.LP(QName.local("x"))),
                 currentX: Int = 0): (LpTerm[Level.Obj], LpTerm[Level.Obj], Int, Boolean) = {
    termRwMap.get(searchIn) match {
      case Some(rewritten) => (patternVar, rewritten, currentX + 1, rwUnderBinder)
      case None =>
        searchIn match {
          case Const(_) | LpTerm.Var(_, _) | LpTerm.TptpInt(_) | LpTerm.LpInt(_) |
               LpTerm.TptpRational(_, _) | LpTerm.TptpReal(_, _, _) | Wildcard() =>
            (Wildcard[Level.Obj](), searchIn, 0, false)
          case LpTerm.Lam(binder, body) =>
            val (patternBody, rewrittenBody, counter, rwUnderBinder0) = findRWTerm(termRwMap, body, rwUnderBinder = true, patternVar, 0)
            val pattern = if (counter == 0) Wildcard[Level.Obj]() else LpTerm.Lam[Level.Obj](binder, patternBody)
            (pattern, LpTerm.Lam[Level.Obj](binder, rewrittenBody), counter, rwUnderBinder0)
          case LogicConst.Not(body) =>
            val (patternBody, rewrittenBody, counter, rwUnderBinder0) = findRWTerm(termRwMap, body, rwUnderBinder, patternVar, 0)
            val pattern = if (counter == 0) Wildcard[Level.Obj]() else LogicConst.Not(patternBody)
            (pattern, LogicConst.Not(rewrittenBody), counter, rwUnderBinder0)
          case LogicConst.And(lhs, rhs) =>
            findRWTermInBinaryConnective(LogicConst.And.apply, termRwMap, lhs, rhs, rwUnderBinder, patternVar)
          case LogicConst.Or(lhs, rhs) =>
            findRWTermInBinaryConnective(LogicConst.Or.apply, termRwMap, lhs, rhs, rwUnderBinder, patternVar)
          case LogicConst.Imp(lhs, rhs) =>
            findRWTermInBinaryConnective(LogicConst.Imp.apply, termRwMap, lhs, rhs, rwUnderBinder, patternVar)
          case LogicConst.Eq(ty, lhs, rhs) =>
            findRWTermInBinaryConnective(LogicConst.Eq(ty, _, _), termRwMap, lhs, rhs, rwUnderBinder, patternVar)
          case LpTerm.App(f, args) =>
            val (patternF, rewrittenF, hdCounter, hdUnderBinder) = findRWTerm(termRwMap, f, rwUnderBinder, patternVar, 0)
            var counter = hdCounter
            var underBinder = hdUnderBinder
            val (patternArgs, rewrittenArgs) = args.map {
              case arg @ Arg.Explicit(argTerm) =>
                val (patternArg, rewrittenArg, argCounter, argUnderBinder) = findRWTerm(termRwMap, argTerm, rwUnderBinder, patternVar, 0)
                counter += argCounter
                underBinder = underBinder || argUnderBinder
                val patternArg0 =
                  if (argCounter == 0) Wildcard[Level.Obj]()
                  else patternArg
                (arg.copy(t = patternArg0), arg.copy(t = rewrittenArg))
              case arg @ Arg.Implicit(argTerm) =>
                val (patternArg, rewrittenArg, argCounter, argUnderBinder) = findRWTerm(termRwMap, argTerm, rwUnderBinder, patternVar, 0)
                counter += argCounter
                underBinder = underBinder || argUnderBinder
                val patternArg0 =
                  if (argCounter == 0) Wildcard[Level.Obj]()
                  else patternArg
                (arg.copy(t = patternArg0), arg.copy(t = rewrittenArg))
              case other => (other, other)
            }.unzip
            val pattern = if (counter == 0) Wildcard[Level.Obj]() else LpTerm.App[Level.Obj](patternF, patternArgs)
            (pattern, LpTerm.App[Level.Obj](rewrittenF, rewrittenArgs), counter, underBinder)
          case LpTerm.LpList(_) =>
            (Wildcard[Level.Obj](), searchIn, 0, false)
        }
    }
  }

  /** Same occurrence-search logic as above, specialized to binary logical connectives. */
  private def findRWTermInBinaryConnective(constructor: (LpTerm[Level.Obj], LpTerm[Level.Obj]) => LpTerm[Level.Obj],
                                           termRwMap: Map[LpTerm[Level.Obj], LpTerm[Level.Obj]],
                                           lhs: LpTerm[Level.Obj],
                                           rhs: LpTerm[Level.Obj],
                                           rwUnderBinder: Boolean,
                                           patternVar: LpTerm[Level.Obj]): (LpTerm[Level.Obj], LpTerm[Level.Obj], Int, Boolean) = {
    val (patternLhs, rewrittenLhs, counterLhs, rwUnderBinderLhs) = findRWTerm(termRwMap, lhs, rwUnderBinder, patternVar, 0)
    val (patternRhs, rewrittenRhs, counterRhs, rwUnderBinderRhs) = findRWTerm(termRwMap, rhs, rwUnderBinder, patternVar, 0)
    val counter = counterLhs + counterRhs
    val pattern =
      if (counter == 0) Wildcard[Level.Obj]()
      else constructor(
        if (counterLhs == 0) Wildcard[Level.Obj]() else patternLhs,
        if (counterRhs == 0) Wildcard[Level.Obj]() else patternRhs
      )
    (pattern, constructor(rewrittenLhs, rewrittenRhs), counter, rwUnderBinderLhs || rwUnderBinderRhs)
  }
}
