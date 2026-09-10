package leo.modules.output.LPoutput.LpTacticUtil

import leo.datastructures.Term.{:::>, TypeLambda, ∙}
import leo.datastructures.{Clause, Literal, Position, RewriteOccurrence, Term}
import leo.modules.HOLSignature.{&, Choice, Exists, Forall, Impl, Not, TyForall, ===, !===, |||}
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{RewritePattern, Side}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, HolBaseTypes, Level, LogicConst, LpTerm, OlMonoType, QName, SymRef, nAry}

object PatternBuilder {

  /** A Lambdapi pattern focused at one Leo term position and the selected Leo subterm. */
  final case class PositionPattern(pattern: LpTerm[Level.Obj], subterm: Term)

  /**
    * The surrounding pattern of one recorded clause position, with the concrete
    * pattern at that position left open until the rewrite form has been chosen.
    */
  final case class ClausePositionPatternContext(selectedTerm: Term,
                                                plugTerm: LpTerm[Level.Obj] => LpTerm[Level.Obj]) {
    def plug(targetPattern: RewritePattern): RewritePattern =
      RewritePattern(plugTerm(targetPattern.LpTerm), targetPattern.hole)
  }

  /** The surrounding pattern of one term position, before its target is supplied. */
  private final case class PositionPatternContext(plugTerm: LpTerm[Level.Obj] => LpTerm[Level.Obj],
                                                  subterm: Term)

  private val RewriteUnderBinderReason = "Rewriting under binders not possible"
  private val DefaultPatternHole = Const[Level.Obj](SymRef.LP(QName.local("x")))

  /**
    * Translate a Leo term position into a Lambdapi rewrite pattern.
    *
    * The returned pattern contains exactly one occurrence of `targetPattern`, at
    * the position selected by `position`; all other term components are
    * wildcards. Explicit type arguments are retained because they occupy
    * positions in Leo's application spine and must remain well-typed in the
    * generated Lambdapi pattern.
    *
    * Positions below object- or type-level binders are currently rejected:
    * Lambdapi patterns for those occurrences require binder-aware pattern
    * variables, which the output encoding cannot yet express safely.
    */
  def leoPosition2LpPattern(term: Term,
                            position: Position,
                            targetPattern: LpTerm[Level.Obj] = DefaultPatternHole): Either[String, PositionPattern] =
    leoPosition2LpPatternContext(term, position).map { context =>
      PositionPattern(context.plugTerm(targetPattern), context.subterm)
    }

  private def leoPosition2LpPatternContext(term: Term,
                                           position: Position): Either[String, PositionPatternContext] = {
    if (position == Position.root) {
      Right(PositionPatternContext(identity, term))
    } else {
      val currentPosition = position.posHead

      // if position.tail can be encoded as a a pattern, take the result and wrap it.
      def descend(selected: Term,
                  wrap: LpTerm[Level.Obj] => LpTerm[Level.Obj]): Either[String, PositionPatternContext] =
        leoPosition2LpPatternContext(selected, position.tail).map { result =>
          PositionPatternContext(target => wrap(result.plugTerm(target)), result.subterm)
        }

      def invalidPosition(expected: String): Left[String, PositionPatternContext] =
        Left(s"Invalid Leo position ${position.pretty} in ${term.pretty}: expected $expected")

      term match {
        case left ||| right =>
          currentPosition match {
            case 1 => descend(left, LogicConst.Or(_, Wildcard[Level.Obj]()))
            case 2 => descend(right, LogicConst.Or(Wildcard[Level.Obj](), _))
            case _ => invalidPosition("disjunction argument 1 or 2")
          }

        case left & right =>
          currentPosition match {
            case 1 => descend(left, LogicConst.And(_, Wildcard[Level.Obj]()))
            case 2 => descend(right, LogicConst.And(Wildcard[Level.Obj](), _))
            case _ => invalidPosition("conjunction argument 1 or 2")
          }

        case Impl(left, right) =>
          currentPosition match {
            case 1 => descend(left, LogicConst.Imp(_, Wildcard[Level.Obj]()))
            case 2 => descend(right, LogicConst.Imp(Wildcard[Level.Obj](), _))
            case _ => invalidPosition("implication argument 1 or 2")
          }

        // Equality has one explicit type argument before its two term
        // arguments, hence the Leo positions 2 and 3.
        case left === right =>
          val encodedType = type2LP(left.ty)
          currentPosition match {
            case 2 => descend(left, LogicConst.Eq(encodedType, _, Wildcard[Level.Obj]()))
            case 3 => descend(right, LogicConst.Eq(encodedType, Wildcard[Level.Obj](), _))
            case _ => invalidPosition("equality argument 2 or 3")
          }

        case left !=== right =>
          val encodedType = type2LP(left.ty)
          currentPosition match {
            case 2 => descend(left, pattern => LogicConst.Not(LogicConst.Eq(encodedType, pattern, Wildcard[Level.Obj]())))
            case 3 => descend(right, pattern => LogicConst.Not(LogicConst.Eq(encodedType, Wildcard[Level.Obj](), pattern)))
            case _ => invalidPosition("disequality argument 2 or 3")
          }

        case Not(body) =>
          if (currentPosition == 1) descend(body, LogicConst.Not.apply)
          else invalidPosition("negation argument 1")

        case _ :::> _ | Forall(_) | Exists(_) | Choice(_) | TyForall(_) | TypeLambda(_) =>
          Left(RewriteUnderBinderReason)

        case head ∙ args =>
          val wildcardArguments: Seq[Arg[Level.Obj]] = args.map {
            case Left(_) => Arg.Explicit(Wildcard[Level.Obj]())
            case Right(ty) => Arg.ExplicitTypeArg(type2LP(ty))
          }

          if (currentPosition == 0) {
            descend(head, pattern => LpTerm.App[Level.Obj](pattern, wildcardArguments))
          } else if (currentPosition > 0 && currentPosition <= args.length) {
            args(currentPosition - 1) match {
              case Left(argument) =>
                descend(argument, pattern =>
                  LpTerm.App[Level.Obj](
                    Wildcard[Level.Obj](),
                    wildcardArguments.updated(currentPosition - 1, Arg.Explicit(pattern))
                  )
                )
              case Right(_) =>
                Left(s"Leo position ${position.pretty} points into a type argument; term rewriting there is not encodable")
            }
          } else {
            invalidPosition(s"application head 0 or argument between 1 and ${args.length}")
          }

        case _ =>
          invalidPosition("a subterm position")
      }
    }
  }

  /**
    * Validate and prepare the context surrounding one recorded RewriteSimp
    * occurrence without yet deciding the concrete pattern used at that site.
    */
  def prepareClausePositionPattern(clause: Clause,
                                   occurrence: RewriteOccurrence): Either[String, ClausePositionPatternContext] = {
    if (!clause.lits.isDefinedAt(occurrence.literalIndex)) {
      Left(s"RW: Recorded literal index ${occurrence.literalIndex} is out of bounds for clause of length ${clause.lits.length}")
    } else {
      val literal = clause.lits(occurrence.literalIndex)
      if (!literal.equational && occurrence.side == Literal.rightSide) {
        Left("RW: Recorded a right-side rewrite occurrence in a non-equational literal")
      } else {
        val selectedSide = Literal.selectSide(literal, occurrence.side)
        leoPosition2LpPatternContext(selectedSide, occurrence.position).flatMap { positionContext =>
          if (positionContext.subterm != occurrence.redex) {
            Left(s"RW: Recorded redex does not match the subterm at position ${occurrence.position.pretty}")
          } else {
            val wrapSide: LpTerm[Level.Obj] => LpTerm[Level.Obj] = if (literal.equational) {
              val encodedType = type2LP(literal.left.ty)
              if (occurrence.side == Literal.leftSide) {
                term => LogicConst.Eq(encodedType, term, Wildcard[Level.Obj]())
              } else {
                term => LogicConst.Eq(encodedType, Wildcard[Level.Obj](), term)
              }
            } else identity

            val plugTerm = (target: LpTerm[Level.Obj]) => {
              val sidePattern = wrapSide(positionContext.plugTerm(target))
              val literalPattern = if (literal.polarity) sidePattern else LogicConst.Not(sidePattern)
              generateClausePattern(
                occurrence.literalIndex,
                clause.lits.length,
                literalPattern,
                DefaultPatternHole
              ).LpTerm
            }
            Right(ClausePositionPatternContext(positionContext.subterm, plugTerm))
          }
        }
      }
    }
  }

  /**
    * Build a Lambdapi rewrite pattern for one recorded RewriteSimp occurrence.
    *
    * The recorded position is relative to one side of one Leo literal. This
    * method restores the surrounding literal and clause structure while keeping
    * every component outside the selected path as a wildcard. `targetPattern`
    * describes what should be placed at the recorded occurrence; it is `x` for
    * an ordinary rewrite and may, for example, be `x _` when a lifted equality
    * rewrites the head of the recorded application.
    */
  def generateClausePositionPattern(clause: Clause,
                                    occurrence: RewriteOccurrence,
                                    targetPattern: RewritePattern = RewritePattern(DefaultPatternHole, DefaultPatternHole)): Either[String, RewritePattern] =
    prepareClausePositionPattern(clause, occurrence).map(_.plug(targetPattern))

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
    embedPatternInBinaryConnective(pat, side, LogicConst.Eq(HolBaseTypes.O, _, _))
  }

  /** Enclose a rewrite pattern on one selected side of a binary connective. */
  def embedPatternInBinaryConnective(pat: RewritePattern,
                                     side: Side,
                                     connective: (LpTerm[Level.Obj], LpTerm[Level.Obj]) => LpTerm[Level.Obj]): RewritePattern = {
    val embeddedTerm = side match {
      case Side.Left => connective(pat.LpTerm, Wildcard[Level.Obj]())
      case Side.Right => connective(Wildcard[Level.Obj](), pat.LpTerm)
    }
    RewritePattern(embeddedTerm, pat.hole)
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
