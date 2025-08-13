package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.SimplificationEncoding._
import scala.collection.mutable
import leo.Out
import leo.modules.output.LPoutput.lpInferenceRuleEncoding.metaPermutation

/**
  * Representations of the accessory rules
  *
  * @author Melanie Taprogge
  */

//todo: encode proofs properly

object AccessoryRules {

  /** Encoding of rule (T : Set) (x : τ T): π((x = y) = (y = x)) */
  object lpStd_eq_sym extends lpTerm {
    override def pretty: String = "eq_sym"
    def inst(ty: lpOlType, lhsRhs: Option[(lpOlTerm, lpOlTerm)] = None): lpFunctionApp = {
      val allArgs = if (lhsRhs.isDefined) Seq(ty, lhsRhs.get._1, lhsRhs.get._2) else Seq(ty)
      lpFunctionApp(lpStd_eq_sym, Seq(), allArgs)
    }
  }

  ////////////////////////////////////////////////////////////////
  ////////// Transform from non-eauational to equational literals and back
  ////////////////////////////////////////////////////////////////

  // positive propositional literals to equational ones

  /** Encoding of rule (x : τ o): π (x = (x = ⊤)) */
  case object mkPosPropPosLit extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_eqTop.name
    override def rwLeft: Boolean = true
    def transformLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop), x0, lpOlTop)
    def origLit(x0: lpOlTerm): (lpOlTerm) = x0
  }

  /** Encoding of rule (x : τ o): π (x = (¬ ((¬ x) = ⊤))) */
  case object mkPosPropNegLit extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_negNotEqTop.name
    override def rwLeft: Boolean = true
    def transformLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)), lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)
    def origLit(x0: lpOlTerm): (lpOlTerm) = x0
  }

  /** Encoding of rule (x : τ o): π (x = ¬ (x = ⊥)) */
  case object mkPosPropNegEqBot extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_negEqBot.name
    override def rwLeft: Boolean = true
  }

  /** Encoding of rule (x : τ o): π (x = (¬ x = ⊥)) */
  case object mkPropEqBot extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_negNotEqBot.name
    override def rwLeft: Boolean = true
  }

  // negative propositional literals to equational ones

  /** Encoding of rule (x : τ o): π (¬ x = (¬ x = ⊤)) */
  case object mkNegPropPosLit extends lpSimpRuleVersion {
    override def term: lpTerm = lpSimp_notEqTop.name
    override def rwLeft: Boolean = true
    def transformLit(x0: lpOlTerm): (lpOlTerm,lpOlTerm,lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop),lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop)
    def origLit(x0: lpOlTerm): (lpOlTerm) =  lpOlUnaryConnectiveTerm(lpNot, x0)
  }

  /** Encoding of rule (x : τ o): π ((¬ x) = (¬ (x = ⊤))) */
  case object mkNegPropNegLit extends lpSimpRuleVersion {
    // x: (π ((¬ x) = (¬ (x = ⊤))))
    override def term: lpConstantTerm = lpSimp_negEqTop.name
    override def rwLeft: Boolean = true
    def transformLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop)), x0, lpOlTop)
    def origLit(x0: lpOlTerm): (lpOlTerm) = lpOlUnaryConnectiveTerm(lpNot, x0)
  }

  /** Encoding of rule (x : τ o): π (¬ x = (x = ⊥)) */
  case object mkNegPropEqBot extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_eqBot.name
    override def rwLeft: Boolean = true
  }

  /** Encoding of rule (x : τ o): π (¬ x = ¬ (¬ x = ⊥)) */
  case object mkNegPropNegEqBot extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_negNotEqBot.name
    override def rwLeft: Boolean = true
  }


  // positive equational literals to propositional one

  /** Encoding of rule (x : τ o): π ((x = ⊤) = x) */
  case object mkPosLitPosProp extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_eqTop.name
    override def rwLeft: Boolean = false
    def instanciate(x0: lpOlTerm) = lpFunctionApp(term, Seq(x0))
    def transformLit(x0: lpOlTerm): (lpOlTerm) = x0
    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop), x0, lpOlTop)
  }

  /** Encoding of rule (x : τ o): π ((⊤ = x) = x) */
  case object mkTopEqPosProp extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_topEq.name
    override def rwLeft: Boolean = false
  }

  /** Encoding of rule (x : τ o): π (((¬ x) = ⊤) = (¬ x)) */
  case object mkPosLitNegProp extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_notEqTop.name
    override def rwLeft: Boolean = false
    def instanciate(x0: lpOlTerm) = lpFunctionApp(term, Seq(x0))
    def transformLit(x0: lpOlTerm): (lpOlTerm) = lpOlUnaryConnectiveTerm(lpNot, x0)
    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop), lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)
  }

  /** Encoding of rule (x : τ o): π ((⊥ = x) = (¬ x)) */
  case object mkBotEqNegProp extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_botEq.name
    override def rwLeft: Boolean = false
  }

  // negative equational literals to propositional ones

  /** Encoding of rule (x : τ o): π ((¬ (x = ⊤)) = (¬ x)) */
  case object mkNegLitNegProp extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_negEqTop.name
    override def rwLeft: Boolean = false
    def instanciate(x0: lpOlTerm) = lpFunctionApp(term, Seq(x0))
    def transformLit(x0: lpOlTerm): (lpOlTerm) = lpOlUnaryConnectiveTerm(lpNot, x0)
    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop)), x0, lpOlTop)
  }

  /** Encoding of rule (x : τ o): π ((¬ ((¬ x) = ⊤)) = x) */
  case object mkNegLitPosProp extends lpSimpRuleVersion {
    override def term: lpConstantTerm = lpSimp_negNotEqTop.name
    override def rwLeft: Boolean = false
    def instanciate(x0: lpOlTerm) = lpFunctionApp(term, Seq(x0))
    def transformLit(x0: lpOlTerm): (lpOlTerm) = x0
    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)), lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)
  }


  def equationalForm(lit: lpOlTerm, desiredPolarity: Boolean): (lpOlTerm, lpOlTerm, lpOlTerm) = {
    lit match {
      case lpOlUnaryConnectiveTerm(lpNot, t) =>
        if (desiredPolarity == true) {
          mkPosLitNegProp.origLit(t)
        } else {
          mkNegLitNegProp.origLit(t)
        }
      case _ =>
        if (desiredPolarity == true) {
          val instRule = lpFunctionApp(mkPosLitPosProp.term, Seq(lit))
          mkPosLitPosProp.origLit(lit)
        } else {
          val instRule = lpFunctionApp(mkNegLitPosProp.term, Seq(lit))
          mkNegLitPosProp.origLit(lit)
        }
    }
  }

  def makeLiteralEquational_proofSkript(lits: Seq[lpOlTerm], origClause: lpClause, sourceBefore: lpTerm, desiredEquational: Boolean, desiredPolarity: Boolean, nameStept: lpConstantTerm): (lpProofScriptStep, Map[lpOlTerm, (lpOlTerm, lpOlTerm, lpOlTerm)], Seq[lpOlTerm], Set[lpStatement]) = {

    // Takes a literal and an desired polarity and returns the transformed versions

    var usedSymbols: Set[lpStatement] = Set.empty

    // order the literals according to their occurence in the clause
    var orderedLits: Seq[lpOlTerm] = Seq.empty
    var litsToFind = origClause.lits
    val positionsInClause: mutable.HashMap[lpOlTerm, Int] = mutable.HashMap.empty
    var litsAfter: Seq[lpOlTerm] = Seq.empty
    litsToFind foreach { lit =>
      if (lits.contains(lit)) { //todo: check that each literal was actually found too.
        orderedLits = orderedLits :+ lit
        positionsInClause.update(lit, origClause.lits.indexOf(lit))
        litsAfter = litsAfter :+ lpOlNothing
      } else litsAfter = litsAfter :+ lit
      litsToFind = litsToFind.filterNot(_ != lit)
    }
    if (litsToFind.nonEmpty) throw new Exception("not all literals could be found")

    var rewriteSteps: Seq[lpRewrite] = Seq.empty
    val transformations: mutable.HashMap[lpOlTerm, (lpOlTerm, lpOlTerm, lpOlTerm)] = mutable.HashMap.empty

    Out.lp_debug_info(s"processing the literals ${orderedLits.map(_.pretty).mkString(", ")}")

    orderedLits foreach { lit =>

      val rewritePattern = generateClausePatternTerm(Seq(positionsInClause(lit)), origClause.lits.length, None)

      Out.lp_debug_info(s"Considering literal ${lit.pretty} ${if (rewritePattern.isDefined) s"at positions ${rewritePattern.get.pretty}"}")

      if (desiredEquational) {
        Out.lp_debug_info(s"Trying to transform to equality...")
        lit match {
          case lpOlUnaryConnectiveTerm(lpNot, t) =>
            if (desiredPolarity == true) {
              usedSymbols = usedSymbols + mkPosLitNegProp
              rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkPosLitNegProp.term)
              val transformedLit = mkPosLitNegProp.origLit(t)
              litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit._1)
              transformations.update(lit, transformedLit)
            } else {
              val instRule = lpFunctionApp(mkNegLitNegProp.term, Seq(t))
              usedSymbols = usedSymbols + mkNegLitNegProp
              rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, instRule)
              val transformedLit = mkNegLitNegProp.origLit(t)
              litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit._1)
              transformations.update(lit, transformedLit)
            }
          case _ =>
            if (desiredPolarity == true) {
              val instRule = lpFunctionApp(mkPosLitPosProp.term, Seq(lit))
              usedSymbols = usedSymbols + mkPosLitPosProp
              rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, instRule)
              val transformedLit = mkPosLitPosProp.origLit(lit)
              litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit._1)
              transformations.update(lit, transformedLit)
            } else {
              val instRule = lpFunctionApp(mkNegLitPosProp.term, Seq(lit))
              usedSymbols = usedSymbols + mkNegLitPosProp
              rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, instRule)
              val transformedLit = mkNegLitPosProp.origLit(lit)
              litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit._1)
              transformations.update(lit, transformedLit)
            }
        }
      } else {
        Out.lp_debug_info(s"Trying to transform to non-equality...")
        lit match {
          case lpOlTypedBinaryConnectiveTerm(lpotype, lpEq, lhs, lpTop) =>
            lhs match {
              case lpOlUnaryConnectiveTerm(`lpNot`, t) =>
                usedSymbols = usedSymbols + mkNegPropPosLit
                rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkNegPropPosLit.term, true)
                val transformedLit = mkNegPropPosLit.origLit(t)
                litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)
                transformations.update(lit, (transformedLit, lpOlNothing, lpOlNothing))
              case _ =>
                Out.lp_debug_info(s"${lhs.pretty}")
                usedSymbols = usedSymbols + mkPosPropPosLit
                rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkPosPropPosLit.term, true)
                val transformedLit = mkPosPropPosLit.origLit(lhs)
                litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)
                transformations.update(lit, (transformedLit, lpOlNothing, lpOlNothing))
                //throw new Exception("2")
            }
          case lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpotype, lpEq, lhs, lpTop)) =>
            lhs match {
              case lpOlUnaryConnectiveTerm(lpNot, t) =>
                usedSymbols = usedSymbols + mkPosPropNegLit
                rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkPosPropNegLit.term, true)
                val transformedLit = mkPosPropNegLit.origLit(t)
                litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)
                transformations.update(lit, (transformedLit, lpOlNothing, lpOlNothing))
              case _ =>
                usedSymbols = usedSymbols + mkNegPropNegLit
                rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkNegPropNegLit.term, true)
                val transformedLit = mkNegPropNegLit.origLit(lhs)
                litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)
                transformations.update(lit, (transformedLit, lpOlNothing, lpOlNothing))
            }

          case _ => throw new Exception(s"trying to convert equational literal but wrong format was given: ${lit.pretty}")
        }
      }
    }
    // Combine into a have step
    val clauseAfter = lpClause(origClause.impBoundVars, litsAfter)
    val haveStep = lpHave(nameStept.name, clauseAfter.withoutQuant.prf, lpProofScript(rewriteSteps :+ lpRefine(lpFunctionApp(sourceBefore, Seq()))))
    (haveStep, transformations.toMap, clauseAfter.lits, usedSymbols)
  }

  def flipStep(litCount: Int, clauseLen: Int, pol: Boolean, eqType: lpOlType) = {
    val rewritePatternEq = lpRewritePattern(generateClausePattern(Seq(litCount), clauseLen, pol))
    lpRewrite(Some(rewritePatternEq), lpFunctionApp(flipLiteral().name, Seq.empty, Seq(eqType)))
  }

  def extractSides(lit0:lpOlTerm):(Option[lpOlTerm], Option[lpOlTerm], Option[lpOlType], Boolean, Boolean)={
    lit0 match {
      case lpOlUnaryConnectiveTerm(`lpNot`, body) =>
        body match {
          case lpOlTypedBinaryConnectiveTerm(`lpEq`, ty, lhs, rhs) => (Some(lhs), Some(rhs), Some(ty), false, true)
          case _ => (Some(body), None, None, false, false)
        }
      case lpOlTypedBinaryConnectiveTerm(`lpEq`, ty, lhs, rhs) => (Some(lhs), Some(rhs), Some(ty), true, true)
      case _ => (Some(lit0), None, None, true, false)
    }
  }
  def isFlippedVersion(lit0: lpOlTerm, lit1: lpOlTerm, litCount: Int, clauseLen: Int): (Option[lpRewrite]) = {
    val (lhs0, rhs0, ty0, pol0, eq0) = extractSides(lit0)
    val (lhs1, rhs1, _, pol1, eq1) = extractSides(lit1)
    if ((eq0 == eq1) && (pol0 == pol1) && (rhs0 == lhs1) && (lhs0 == rhs1)) {
      val rewriteStep = flipStep(litCount,clauseLen,pol0,ty0.get)
      Some(rewriteStep)
    }
    else None
  }

  // todo: restructure to use lpLiterl as input
  def transformLiteral(lit0 : lpOlTerm, lit1 : lpOlTerm, litCount: Int, clauseLen:Int): (Seq[lpProofScriptStep], Set[lpStatement], Boolean) = {
    Out.lp_debug_info(s"Trying to transform literal ${lit0.pretty} to ${lit1.pretty}")
    // todo: compare modulo alpha conversion?

    // Transform two literals into each other, including cases of eq-sym application, transformation to and from equality literal inclduing ones where we insert bottom rather than top

    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    var canEncode = false
    var flip: Boolean = false
    val rewritePattern = Some(lpRewritePattern(generateClausePattern(Seq(litCount), clauseLen)))

    // first we register the two sides of the literals and weather or not the literals are negative
    val (lhs0, rhs0, ty0, pol0, _) = extractSides(lit0)
    val (lhs1, rhs1, ty1, pol1, _) = extractSides(lit1)

    // then we detect which transformations to apply
    canEncode = if (ty0.isDefined && !ty1.isDefined) {
      // we transform to non equational form
      Out.lp_debug_info(s"Transformation from equational to non-equational form neccesary...")
      Out.lp_debug_info(s"lhs0: ${lhs0.get.pretty}, rhs0: ${rhs0.get.pretty}, lhs1: ${lhs1.get.pretty}")
      Out.lp_debug_info(s"Seq(lhs0,rhs0).contains(lhs1): ${Seq(lhs0,rhs0).contains(lhs1)}, Seq(lhs0,rhs0).contains(lpOlBot): ${Seq(lhs0,rhs0).contains(Some(lpOlBot))}, Seq(lhs0,rhs0).contains(lpOlTop): ${Seq(lhs0,rhs0).contains(Some(lpOlTop))}")
      // first we detect if we want to transform from bottom or to top
      if((Seq(lhs0,rhs0).contains(lhs1) || Seq(lhs0.get,rhs0.get).contains(lpOlUnaryConnectiveTerm(lpNot,lhs1.get))) && (Seq(lhs0,rhs0).contains(Some(lpOlBot)) || Seq(lhs0,rhs0).contains(Some(lpOlTop)))) {
        // detect if we need to swap sides
        flip = (rhs0 == lhs1)
        // we need to transform to non-equational literal
        val (necessaryRule, necessaryFlip): (Option[lpSimpRuleVersion], Boolean) = if (!pol0) {
          if (!pol1) {
            // go from neg eq to neg non-eq
            // // x: (π ((¬ (x = ⊤)) = (¬ x)))
            if ((lhs0 == lhs1 && rhs0 == Some(lpOlTop)) || (rhs0 == lhs1 && lhs0 == Some(lpOlTop))) {
              // go to top
              (Some(mkNegLitNegProp), false)
            } else {
              // go to bottom
              (None, false) // todo
            }
          } else {
            // go from neg eq to pos non-eq
            // x: (π ((¬ ((¬ x) = ⊤)) = x))
            if ((lhs0.get == lpOlUnaryConnectiveTerm(lpNot, lhs1.get) && rhs0 == Some(lpOlTop)) || (rhs0 == lhs1 && lhs0 == Some(lpOlTop))) {
              // go to top
              (Some(mkNegLitPosProp), false)
            } else {
              // go to bottom
              (None, false) // todo
            }
          }
        } else {
          if (!pol1) {
            // go from pos eq to neg non-eq
            // x: (π (((¬ x) = ⊤) = (¬ x)))
            if ((lhs0.get == lpOlUnaryConnectiveTerm(lpNot, lhs1.get) && rhs0 == Some(lpOlTop)) || (rhs0.get == lpOlUnaryConnectiveTerm(lpNot, lhs1.get)) && lhs0 == Some(lpOlTop)) {
              // go to top
              (Some(mkPosLitNegProp), true)
            } else {
              // go to bottom
              (None, true) // todo
            }
          } else {
            // go from pos eq to pos non-eq
            // x: (π ((x = ⊤) = x))
            if ((lhs0 == lhs1 && rhs0 == Some(lpOlTop)) || (rhs0 == lhs1 && lhs0 == Some(lpOlTop))) {
              // go to top
              (Some(mkPosLitPosProp), true)

            } else {
              // go to bottom
              (None, true) // todo
            }
          }
        }
        necessaryRule match {
          case Some(rule) =>
            if (flip) {
              usedSymbols = usedSymbols + flipLiteral()
              allSteps = allSteps :+ flipStep(litCount, clauseLen, necessaryFlip, ty0.get)
              Out.lp_debug_info(s"Applying ${flipLiteral()} to flip literal ${lit0.pretty}")
            }
            usedSymbols = usedSymbols + rule
            allSteps = allSteps :+ lpRewrite(rewritePattern, lpFunctionApp(rule.term, Seq()))
            Out.lp_debug_info(s"Applying ${rule.term} to transform equational literal to non-equational form")
            true
          case None =>
            Out.lp_debug_info(s"Unencoded transformation 1")
            false
        }
      } else false
    } else if (!ty0.isDefined && ty1.isDefined) {
      // we need to transform to equational literal
      Out.lp_debug_info(s"Transformation from non-equational to equational form neccesary...")
      Out.lp_debug_info(s"lhs0: ${lhs0.get.pretty}, lhs1: ${lhs1.get.pretty}, rhs1: ${rhs1.get.pretty},")
      // analogous to the previous case
      if ((Seq(lhs1, rhs1).contains(lhs0) || Seq(lhs1.get, rhs1.get).contains(lpOlUnaryConnectiveTerm(lpNot, lhs0.get))) && (Seq(lhs1, rhs1).contains(Some(lpOlBot)) || Seq(lhs1, rhs1).contains(Some(lpOlTop)))) {

        // detect if we need to swap sides
        flip = (lhs0 == rhs1) // alphaEquivalent(lhs0.get, rhs1.get)

        val (necessaryRule, necessaryFlip): (Option[lpSimpRuleVersion], Boolean) = if (!pol0) {
          if (!pol1) {
            // go from neg non-eq to neg eq
            // x: (π ((¬ x) = (¬ (x = ⊤))))
            // if ((alphaEquivalent(lhs1, lhs0) && alphaEquivalent(rhs1, Some(lpOlTop))) || (alphaEquivalent(rhs1, lhs0) && alphaEquivalent(lhs1, Some(lpOlTop)))) {
            if ((lhs1 == lhs0 && rhs1 == Some(lpOlTop)) || (rhs1 == lhs0 && lhs1 == Some(lpOlTop))) {
              // go to top
              (Some(mkNegPropNegLit), false)
            } else {
              // go to bottom
              (Some(mkNegPropNegEqBot), false)
            }
          } else {
            // go from neg non-eq to pos eq
            // x: (π ((¬ x) = ((¬ x) = ⊤)))
            if ((lhs1.get == lpOlUnaryConnectiveTerm(lpNot, lhs0.get) && rhs1 == Some(lpOlTop)) || (rhs1 == lpOlUnaryConnectiveTerm(lpNot, lhs0.get) && lhs1 == Some(lpOlTop))) {
              // go to top
              (Some(mkNegPropPosLit), true)
            } else {
              // go to bottom
              (Some(mkNegPropEqBot), true)
            }
          }
        } else {
          if (!pol1) {
            // go from pos non-eq to neg eq
            // x: (π (x = (¬ ((¬ x) = ⊤))))
            if ((lpOlUnaryConnectiveTerm(lpNot, lhs0.get) == lhs1.get && rhs1 == Some(lpOlTop)) || (lpOlUnaryConnectiveTerm(lpNot, lhs0.get) == rhs1.get && lhs1 == Some(lpOlTop))) {
              // go to top
              (Some(mkPosPropNegLit), false)
            } else {
              // go to bottom
              (Some(mkPosPropNegEqBot), false) // todo
            }
          } else {
            // go from pos non-eq to pos eq
            // Prf(= [o] a (= [o] a ⊤))
            if ((lhs1 == lhs0 && rhs1 == Some(lpOlTop)) || (rhs1 == lhs0 && lhs1 == Some(lpOlTop))) {
              // go to top
              (Some(mkPosPropPosLit), true)

            } else {
              // go to bottom
              (Some(mkPropEqBot), true) // todo
            }
          }
        }
        necessaryRule match {
          case Some(rule) =>
            usedSymbols = usedSymbols + rule
            allSteps = allSteps :+ lpRewrite(rewritePattern, lpFunctionApp(rule.term, Seq()), true)
            Out.lp_debug_info(s"Applying ${rule.term} to transform non-equational literal to equational form")
            if (flip) {
              usedSymbols = usedSymbols + flipLiteral()
              allSteps = allSteps :+ flipStep(litCount, clauseLen, necessaryFlip, ty1.get)
              Out.lp_debug_info(s"Applying ${flipLiteral()} to flip literal ${lit0.pretty}")
            }
            true
          case None =>
            Out.lp_debug_info(s"Unencoded transformation 2")
            false
        }
    } else false
    } else if (ty0.isDefined && ty1.isDefined) {
      // both literals are equational, maybe we need to switch sides or transform bot/ top and polarity
      if (Seq(lhs0,rhs0).contains(lhs1) && Seq(lhs0,rhs0).contains(rhs1)){
        // the only possible difference is if the sides differ:
        if (lhs0 != lhs1){
          val necessaryFlip = if (pol0) true else false
          usedSymbols = usedSymbols + flipLiteral()
          allSteps = allSteps :+ flipStep(litCount,clauseLen,necessaryFlip,ty0.get)
          Out.lp_debug_info(s"Applying ${flipLiteral()} to flip literal ${lit0.pretty}")
          true
        }else {
          Out.lp_debug_info(s"Literals are already identical")
          true
        } // In this case, the sides are already the same
      } else if ((lhs1.get == lit0) && (rhs1.get == lpOlTop)){
        // transformation to equality literal for positive case
        allSteps = allSteps :+ lpRewrite(rewritePattern, lpFunctionApp(lpStd_eq_sym,Seq(lpFunctionApp(mkPosPropPosLit.term,Seq(lpOlTypedBinaryConnectiveTerm(lpEq,ty0.get,lhs0.get,rhs0.get))))))
        //Out.lp_debug_info(s"Applying ${eqLift_script().name.pretty} to un-lift literal ${lit0.pretty}")
        true
      } else {
        Out.lp_debug_info(s"Unencoded transformation between equational literals, $lit0")
        false
      }
    } else {
      // both literals are non-equational and should already be the same
      assert(lit0 == lit1)
      Out.lp_debug_info(s"Literals are already identical")
      // maybe transform bot to not top and vice versa?
      true
    }
    if (canEncode) Out.lp_debug_info(s"success")
    (allSteps,usedSymbols,canEncode)
  }

  ////////////////////////////////////////////////////////////////
  ////////// Change order within literals
  ////////////////////////////////////////////////////////////////

  case class flipLiteral() extends lpDefinedRules {
    // [T] (x y : τ T) : π((x = y) = (y = x))

    val T = lpOlUserDefinedMonoType("T")
    val x = lpOlTypedVar(lpOlConstantTerm("x"),T)
    val y = lpOlTypedVar(lpOlConstantTerm("y"),T)

    override def name: lpConstantTerm = lpConstantTerm("=_sym")

    override def ty: lpMlType = {
      lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x, y), lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, y, x)).prf
      }

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x, y), ty, Seq(T))

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptStringProof("assume T x y;\n    have H1: π(x = y) → π(y = x)\n        {assume h;\n        symmetry;\n        refine h};\n    have H2: π(y = x) → π(x = y)\n        {assume h;\n        symmetry;\n        refine h};\n    refine propExt (x = y) (y = x) H1 H2")))

    override def pretty: String = lpDefinition(name, Seq(x, y), Some(ty), proof, Seq(T)).pretty

    def instanciate(ty: lpOlType, x0: Option[lpOlTerm] = None, y0: Option[lpOlTerm] = None): lpFunctionApp = {
      val x = x0 match {
        case Some(term) => Seq(term)
        case None => Seq()
      }
      val y = y0 match {
        case Some(term) => Seq(term)
        case None => Seq()
      }
      lpFunctionApp(name, x ++ y,Seq(ty))
    }

    def res(polarity: Boolean, T0: lpOlPolyType, x0: lpOlTerm, y0: lpOlTerm) = { // todo unite encoding with type
      if (polarity) lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, x0)
      else lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, x0))
    }
  }

  def flipEqLiteralsProofScript(lits: Seq[(lpOlTerm, lpOlType)], origClause: lpClause, sourceBefore: lpTerm, nameStept: lpConstantTerm): (lpProofScriptStep, Seq[lpOlTerm], Set[lpStatement]) = {

    // change order within literals of a given clause

    var usedSymbols: Set[lpStatement] = Set.empty

    val litsTypeMap = lits.toMap

    if (lits.isEmpty) throw new Exception(s"Function flipEqLiteralsProofScript called but no literals to flip were provided.")

    // order the literals according to their occourence in the clause
    var orderedLits: Seq[(lpOlTerm, lpOlType)] = Seq.empty
    var litsToFind = origClause.lits
    val positionsInClause: mutable.HashMap[lpOlTerm, Int] = mutable.HashMap.empty
    var litsAfter: Seq[lpOlTerm] = Seq.empty

    Out.lp_debug_info(s"lits to fine: ${lits.map(_._1.pretty)}")
    litsToFind foreach { lit =>
      Out.lp_debug_info(s"processing literal ${lit.pretty}")
      if (lits.map(pair => pair._1).contains(lit)) {
        Out.lp_debug_info("yes")
        orderedLits = orderedLits :+ (lit, litsTypeMap(lit))
        positionsInClause.update(lit, origClause.lits.indexOf(lit))
        litsAfter = litsAfter :+ lpOlNothing
      } else litsAfter = litsAfter :+ lit
      litsToFind = litsToFind.filterNot(_ != lit)
    }

    var rewriteSteps: Seq[lpRewrite] = Seq.empty

    orderedLits foreach { pair =>

      val lit = pair._1
      val litType = pair._2

      val (lhs0, rhs0, ty0, ispos) = lit match { //todo: summarize

        case lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpeq, ty, rhs, lhs)) =>
          (rhs, lhs, ty, false)

        case lpOlTypedBinaryConnectiveTerm(lpeq, ty, rhs, lhs) =>
          (rhs, lhs, ty, true)

        case _ => throw new Exception(s"unexpected literal form in Function flipEqLiteralsProofScript in Lambdapi encoding")

      }

      val rewritePattern = generateClausePatternTerm(Seq(positionsInClause(lit)), origClause.lits.length, None, lpOlUntypedVar(lpConstantTerm("x")), ispos)

      usedSymbols = usedSymbols + flipLiteral()
      rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, lpFunctionApp(flipLiteral().name, Seq(), Seq(litType)))
      val transformedLit = flipLiteral().res(ispos,ty0.lift2Poly, lhs0, rhs0)
      litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)

    }
    // Combine into a have step
    val clauseAfter = lpClause(origClause.impBoundVars, litsAfter)
    val haveStep = lpHave(nameStept.name, clauseAfter.withoutQuant.prf, lpProofScript(rewriteSteps :+ lpRefine(lpFunctionApp(sourceBefore, Seq()))))
    (haveStep, litsAfter, usedSymbols)
  }


  ////////////////////////////////////////////////////////////////
  ////////// Literal level transformations
  ////////////////////////////////////////////////////////////////


  def containsLpLits(literals0: Seq[lpOlTerm], literals1: Seq[lpOlTerm]):Boolean = {
    literals0.forall(literals1.contains)
  }

  def permutationStepSkript(literals0: Seq[lpOlTerm], literals1: Seq[lpOlTerm],before:lpTerm)={
    val permutation = literals0.map(item => literals1.indexOf(item))
    metaPermutation.instanciate(permutation,literals0,before)
  }

  def deleteDoubleLiterals(literals0: Seq[lpOlTerm], indxList: Seq[Int], before: lpTerm) = {
    val outputIndx = indxList.distinct
    //metaPermutation.instanciate(permutation, literals0, before)
  }

  ////////////////////////////////////////////////////////////////
  ////////// Transitivity of Implication
  ////////////////////////////////////////////////////////////////

  case class implicationTransitivity(patternVarName: String = "x") extends lpDefinedRules {
    // (a b c : El o): (Prf a → Prf b) → (Prf b → Prf c) → (Prf a → Prf c)
    // todo ->stdlib

    val a = lpOlConstantTerm("a")
    val b = lpOlConstantTerm("b")
    val c = lpOlConstantTerm("c")

    override def name: lpConstantTerm = lpConstantTerm("inpTrans")

    override def ty: lpMlType = lpMlFunctionType(Seq(lpMlFunctionType(Seq(a.prf,b.prf)),lpMlFunctionType(Seq(b.prf,c.prf)),lpMlFunctionType(Seq(a.prf,c.prf))))

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptStringProof("assume x;\n    refine propExt (¬ x) ((¬ x) = ⊤) _ _\n        {assume h1;\n        refine propExt (¬ x) ⊤ _ _ \n            {assume h2;\n            refine ⊤I}\n            {assume h2;\n            refine h1}}\n        {assume h1;\n        have H1: Prf((¬ x) = ⊤) → Prf(¬ x)\n            {assume h2;\n            refine (=def [o] (¬ x) ⊤ h2 (λ z, z)) ⊤I};\n        refine H1 h1}")))

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), Some(ty), proof).pretty
  }
}
