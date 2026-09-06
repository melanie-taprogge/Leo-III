package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.{LitNorm, LiteralInfo, LiteralTransformation}
import leo.modules.output.LPoutput.LpLibs.EqRules.AsTerms.{lpSimp_botEq, lpSimp_eqBot, lpSimp_eqTop, lpSimp_negBotEq, lpSimp_negEqBot, lpSimp_topEq}
import leo.modules.output.LPoutput.LpLibs.EqRules._
import leo.modules.output.LPoutput.LpLibs.ND.Terms.eqSym
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Rewrite, Side}
import leo.modules.output.LPoutput.NewLpDatastructures.{HolBaseTypes, Level, LogicConst, LpTerm, lpLiteralInst}

object ImplicitTransformationUtil {

  // Literal Normalisazion

  /**
    * LiteralInfo2LiteralTransformation — Reindex literal transformations
    *
    * Converts input LiteralInfo sequence, which describes transformations relative
    * to a freshly generated block of literals, into a global
    * LiteralTransformation instance suitable for clause-level rewriting.
    *
    * Notes:
    * • This function performs only index translation, it does NOT validate
    * transformation consistency or clause bounds.
    *
    * @param litInfo Transformation metadata relative to generated literals
    * @param setOff  Global clause index where generated literals begin
    * @return Clause-level LiteralTransformation instance
    */
  def LiteralInfo2LiteralTransforamtion(litInfo: Seq[LiteralInfo], setOff: Int) = {
    Out.lp_debug_info(s"generating LiteralTransformation for $litInfo, using set-off $setOff")
    litInfo.zipWithIndex.foldLeft[LiteralTransformation](LiteralTransformation()) { (acc, infoIdx) =>
      // the first transofrmation we handle will affect the leftmost one of the generated literals
      val newIdx = setOff + (infoIdx._2)
      if (infoIdx._1.flip) LiteralTransformation(acc.flippedLits :+ newIdx, acc.normalizedEq)
      else if (infoIdx._1.normalize.isDefined) LiteralTransformation(acc.flippedLits, acc.normalizedEq :+ (newIdx, infoIdx._1.normalize.get))
      else acc
    }
  }

  /**
    * Take as an argument the tracked normalisazion mode applied to a literal and return the corresponding encoded
    * Lambdapi rule
    *
    * @param normMode The tracked normalisazion mode
    * @return The encoded Lambpdai rule name as a meta-level term
    */
  def litNorm2lpRule(normMode: LitNorm) = normMode match {
    case LitNorm.TopL => TopEq
    case LitNorm.TopR => EqTop
    case LitNorm.BotL => BotEq
    case LitNorm.BotR => EqBot
    case LitNorm.NegBotL => NegBotEq
    case LitNorm.NegBotR => NegEqBot
  }

  /**
    * Apply the literal ordering/normalisation operations recorded by Leo to an
    * encoded clause. This is the forward counterpart of
    * `reconstructBeforeLiteralNormalisation`.
    */
  def applyLiteralTransformations(lits: Seq[lpLiteralInst],
                                  transformations: LiteralTransformation): Option[Seq[lpLiteralInst]] = {
    val normalisationMap = transformations.normalizedEq.toMap
    if (transformations.transforamtionsHappened) {
      Some(lits.zipWithIndex.map { case (lit, index) =>
        if (transformations.flippedLits.contains(index)) {
          lit.flipIfEq
        } else if (normalisationMap.contains(index)) {
          val appliedRule = litNorm2lpRule(normalisationMap(index))
          Out.lp_debug_info(s"trying to apply normalisation $appliedRule to ${lit.term}")
          val transformedLit = appliedRule.applyTo(lit)
          Out.lp_debug_info(s"resulting in $transformedLit")
          transformedLit match {
            case Some(result) => result
            case None => return None
          }
        } else {
          lit
        }
      })
    } else Some(lits)
  }

  /**
    * Reconstruct the equational literals that existed immediately before
    * `Literal.mkOrdered` normalized the result of a rewrite step.
    */
  def reconstructBeforeLiteralNormalisation(lits: Seq[lpLiteralInst],
                                             transformations: LiteralTransformation): Either[String, Vector[lpLiteralInst]] = {
    def at(index: Int): Either[String, lpLiteralInst] =
      if (lits.isDefinedAt(index)) Right(lits(index))
      else Left(s"literal transformation index $index is outside a clause of length ${lits.length}")

    val afterNormalisation = transformations.normalizedEq.foldLeft[Either[String, Vector[lpLiteralInst]]](Right(lits.toVector)) {
      case (left @ Left(_), _) => left
      case (Right(current), (index, mode)) =>
        at(index).flatMap { normalizedLit =>
          normalizedLit.unsignedTerm.toRight(s"negative literal does not have the expected encoded negation: ${normalizedLit.term}").flatMap { body =>
            def booleanEquality(lhs: LpTerm[Level.Obj],
                                rhs: LpTerm[Level.Obj],
                                polarity: Boolean): lpLiteralInst =
              lpLiteralInst.equality(HolBaseTypes.O, lhs, rhs, polarity)

            mode match {
              case LitNorm.TopL => Right(current.updated(index, booleanEquality(LogicConst.Top, body, normalizedLit.polarity)))
              case LitNorm.TopR => Right(current.updated(index, booleanEquality(body, LogicConst.Top, normalizedLit.polarity)))
              case LitNorm.BotL if !normalizedLit.polarity => Right(current.updated(index, booleanEquality(LogicConst.Bot, body, polarity = true)))
              case LitNorm.BotR if !normalizedLit.polarity => Right(current.updated(index, booleanEquality(body, LogicConst.Bot, polarity = true)))
              case LitNorm.NegBotL if normalizedLit.polarity => Right(current.updated(index, booleanEquality(LogicConst.Bot, body, polarity = false)))
              case LitNorm.NegBotR if normalizedLit.polarity => Right(current.updated(index, booleanEquality(body, LogicConst.Bot, polarity = false)))
              case _ => Left(s"literal $index has polarity ${normalizedLit.polarity}, incompatible with normalization mode $mode")
            }
          }
        }
    }

    afterNormalisation.flatMap { current =>
      transformations.flippedLits.foldLeft[Either[String, Vector[lpLiteralInst]]](Right(current)) {
        case (left @ Left(_), _) => left
        case (Right(acc), index) =>
          if (!acc.isDefinedAt(index)) Left(s"literal flip index $index is outside a clause of length ${acc.length}")
          else if (!acc(index).eq) Left(s"literal $index was recorded as flipped but is not equational")
          else Right(acc.updated(index, acc(index).flipIfEq))
      }
    }
  }

  /**
    * verifyLiteralNormalisazion — generate Lambdapi rewrite tactic applications to verify Leo’s
    * literal normalisation as implicit transformations during other steps.
    *
    * Context (where it is used):
    * Leo may additionally perform *literal-level normalisation* on some equational literals
    * while performing a given infernce rule. Two operations are possible:
    *
    *   - "eq normalisation": turning an equation/inequality into a canonical boolean shape
    *     (Top/Bot cases), sometimes requiring an extra symmetry flip depending on whether the
    *     normalisation happens on the left or right side (see `LitNorm.{TopL,TopR,BotL,BotR}`).
    *
    *   - "flip": applying equality symmetry to selected equational literals (recorded in
    *     `addInfo.flippedLits`), so that the clause literals match Leo’s post-step orientation.
    *
    * What this function returns:
    * A sequence of `Rewrite` proof scripts that rewrite exactly the affected literals in the
    * clause. Rewriting is done via clause-patterns generated by
    * `PatternBuilder.generateClausePattern`, targeting literal positions with`PatternInfo`.
    *
    * Implementation outline:
    * 1) For each entry in `addInfo.normalizedEq`, emit a rewrite using the corresponding theorem
    * (`lpSimp_eqTop` / `lpSimp_eqBot`). If the normalisation mode requires a symmetry flip
    * (TopL/BotL), record that position in `newFlipSteps`.
    * 2) Carry out recorded flips (`addInfo.flippedLits`) with flips induced by normalisation
    * (`newFlipSteps`). Assert that these sets do not overlap (they correspond to disjoint
    * normalisation scenarios).
    * 3) If flips are required, emit clause-level rewrite tactic applications using `eqSym`, targeting all
    * relevant positions in sequence.
    *
    * Indexing / bookkeeping:
    * - The transformation info refers to literal positions in the *child* clause.
    * - During reconstruction we may have inserted or permuted literals; `old2NewIdx` is used to
    * map recorded positions to the current clause layout.
    * - `goalLits` is the child clause used to recover the polarity for pattern generation.
    *
    * @param addInfo   Literal-level transformation info recorded by DetUniSimp (normalisations + flips).
    * @param goalLitPolarities  The polarities of the target clause literals (typically `child.cl.lits`)
    *                           used for polarity lookup. These are the literals that are in the goal,
    *                           i.e. the one that the rewrite tactic is to be applied to.
    * @param clauseLen Total number of literals in the clause at the point the rewrites will be applied
    *                  (e.g. `ctxt.substClauseLen` in the substitution subproof).
    * @param idxMap    The literal-Indices given in addInfo refer to the index in the orginal
    *                  child clause. As previous steps in the verification may already have changed
    *                  the positions, it may be necessary to map the original position to the new one.
    *                  If no operations have been performed that effected the position, an identity map
    *                  can simply be used here.
    * @return Sequence of `Rewrite` scripts to be inserted before the substitution refine step.
    */
  def verifySubstitutionLiteralNormalisazion(addInfo: LiteralTransformation, goalLitPolarities:  Seq[Boolean], clauseLen: Int, idxMap: Int => Int = identity): Seq[Rewrite] = {
    // todo: maybe change to not take a list of goal lits but just a map of the indices to the polarities?

    Out.lp_debug_info(s"polarity vec: $goalLitPolarities")
    //val polarities = goalLits.map(_.polarity)

    // helper for looking up the mapped index and polarity of a given index
    def generatePatternInfo(id: Int): PatternBuilder.PatternInfo = {
      val idxInGoal = idxMap(id)
      if (goalLitPolarities.isDefinedAt(idxInGoal)) PatternBuilder.PatternInfo(idxInGoal, None, goalLitPolarities(idxInGoal))
      else {
        Out.lp_debug_info(s"Warning: trying to generate pattern for literal with index $id, which is out of bounds for goal literals. Using default polarity positive")
        PatternBuilder.PatternInfo(idxInGoal, None, true)
      }
    }

    // flipping may be necessary either in cases where normalisazion is applied, or in cases where only flipping was used
    //var newFlipSteps: Seq[Int] = Seq.empty

    // first, handle the literals that need normalisazion
    val maybeNormalizeSteps: Seq[Rewrite] = if (addInfo.normalizedEq.nonEmpty) {
      Out.lp_debug_info(s"need to normalize: ${addInfo.normalizedEq}")
      addInfo.normalizedEq.map { pair =>
        val (pos, normMode) = pair
        val rule: LpTerm[Level.Meta] = litNorm2lpRule(normMode).lpConst
        val patternInfo = generatePatternInfo(pos)
        val pattern = PatternBuilder.generateClausePattern(Seq(patternInfo), clauseLen)
        Rewrite(Some(pattern), rule, Side.Left)
      }
    } else Seq.empty

    // sanity check: we ony need to flip literals that are equational and we only need to rewrite literals to an euational form if they are non-equational. Therefore, there can never be an overlap between the two
    //assert(addInfo.flippedLits.intersect(newFlipSteps).isEmpty, s"Error in Lambdapi Encoding: Trying to verify literal-normalisazion, but found contradicroty input (${addInfo.flippedLits.intersect(newFlipSteps)})")

    // secondly, all the flip steps are carried out in subsequent rewrite tactic applications
    //val allFlipSteps = (addInfo.flippedLits ++ newFlipSteps).sorted
    val allFlipSteps = (addInfo.flippedLits).sorted
    val maybeFlipStep: Seq[Rewrite] = if (allFlipSteps.nonEmpty) {
      Out.lp_debug_info(s"the following literals need to be flipped: $allFlipSteps")
      val flipInfo = allFlipSteps.map(generatePatternInfo)
      Out.lp_debug_info(s"pattern info: $flipInfo")
      val flipPatterns = flipInfo.map(flipInfo0 => PatternBuilder.generateClausePattern(Seq(flipInfo0), clauseLen))
      flipPatterns.map(flipPattern0 => Rewrite(Some(flipPattern0), eqSym))
    } else Seq.empty

    maybeNormalizeSteps ++ maybeFlipStep
  }

}
