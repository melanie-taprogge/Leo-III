package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures._
import leo.modules.output.LPoutput.SimplificationEncoding._
import leo.Out
import leo.modules.output.LPoutput.lpInferenceRuleEncoding.metaPermutation

/**
  * Representations of the accessory rules
  *
  * @author Melanie Taprogge
  */

object AccessoryRules {

  /** Encoding of rule (T : Set) (x : τ T): π((x = y) = (y = x)) */
  object lpStd_eq_sym extends lpNameRef {
    override def name = lpConstantTerm("eq_sym")
    def inst(ty: lpOlType, lhsRhs: Option[(lpOlTerm, lpOlTerm)] = None): lpFunctionApp = {
      val allArgs = if (lhsRhs.isDefined) Seq(ty, lhsRhs.get._1, lhsRhs.get._2) else Seq(ty)
      lpFunctionApp(lpStd_eq_sym.name, Seq(), allArgs)
    }
  }

  ////////////////////////////////////////////////////////////////
  ////////// Transform from non-eauational to equational literals and back
  ////////////////////////////////////////////////////////////////


  def equationalForm(lit: lpOlTerm, desiredPolarity: Boolean): (lpOlTerm, lpOlTerm, lpOlTerm) = {
    lit match {
      case lpOlUnaryConnectiveTerm(`lpNot`, t) =>
        if (desiredPolarity == true) {
          lpSimp_notEqTop.origLit(t)
        } else {
          lpSimp_negEqTop.origLit(t)
        }
      case _ =>
        if (desiredPolarity == true) {
          lpSimp_eqTop.origLit(lit)
        } else {
          lpSimp_negNotEqTop.origLit(lit)
        }
    }
  }

  def flipStep(litCount: Int, clauseLen: Int, pol: Boolean, eqType: lpOlType, embedInPattern: Option[lpOlTerm => lpOlTerm] = None): lpRewrite = {
    val rewritePatternEq = generateClausePattern(Seq(litCount), clauseLen, pol)
    val pattern = if (!embedInPattern.isDefined) rewritePatternEq else embedInPattern.get(rewritePatternEq)
    lpRewrite(Some(lpRewritePattern(pattern)), lpFunctionApp(flipLiteral.name, Seq.empty, Seq(eqType)))
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
  def transformLiteral(lit0 : lpOlTerm, lit1 : lpOlTerm, litCount: Int, clauseLen:Int, embedInPattern: Option[lpOlTerm => lpOlTerm] = None, useFallback: Boolean = false): (Seq[lpProofScriptStep], Boolean) = {
    Out.lp_debug_info(s"Trying to transform literal ${lit0.pretty} to ${lit1.pretty}")
    // todo: compare modulo alpha conversion?

    // Transform two literals into each other, including cases of eq-sym application, transformation to and from equality literal inclduing ones where we insert bottom rather than top

    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    var canEncode = false
    var flip: Boolean = false
    val clausePattern = generateClausePattern(Seq(litCount), clauseLen)
    val embclausePattern =
      if (!embedInPattern.isDefined) clausePattern
      else embedInPattern.get(clausePattern)
    val rewritePattern = Some(lpRewritePattern(embclausePattern))

    def flipRewriteStep(pol: Boolean, eqType: lpOlType): lpProofScriptStep = {
      val ordinaryRewrite = flipStep(litCount, clauseLen, pol, eqType, embedInPattern)
      // Unfolding ⤳d only helps for functional equality and fails if no dependent arrow is present.
      if (useFallback && eqType.isInstanceOf[lpOlFunctionType]) {
        lpRewriteWithDepArrowFallback(ordinaryRewrite.rewritePattern0, ordinaryRewrite.rewriteTerm, ordinaryRewrite.rwRhs)
      }
      else ordinaryRewrite
    }

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
        val (necessaryRule, necessaryFlip): (Option[lpNameRef], Boolean) = if (!pol0) {
          if (!pol1) {
            // go from neg eq to neg non-eq
            // // x: (π ((¬ (x = ⊤)) = (¬ x)))
            if ((lhs0 == lhs1 && rhs0 == Some(lpOlTop)) || (rhs0 == lhs1 && lhs0 == Some(lpOlTop))) {
              // go to top
              (Some(lpSimp_negEqTop), false)
            } else {
              // go to bottom
              (None, false) // todo
            }
          } else {
            // go from neg eq to pos non-eq
            // x: (π ((¬ ((¬ x) = ⊤)) = x))
            if ((lhs0.get == lpOlUnaryConnectiveTerm(lpNot, lhs1.get) && rhs0 == Some(lpOlTop)) || (rhs0 == lhs1 && lhs0 == Some(lpOlTop))) {
              // go to top
              (Some(lpSimp_negNotEqTop), false)
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
              (Some(lpSimp_notEqTop), true)
            } else {
              // go to bottom
              (None, true) // todo
            }
          } else {
            // go from pos eq to pos non-eq
            // x: (π ((x = ⊤) = x))
            if ((lhs0 == lhs1 && rhs0 == Some(lpOlTop)) || (rhs0 == lhs1 && lhs0 == Some(lpOlTop))) {
              // go to top
              (Some(lpSimp_eqTop), true)

            } else {
              // go to bottom
              (None, true) // todo
            }
          }
        }
        necessaryRule match {
          case Some(rule) =>
            if (flip) {
              allSteps = allSteps :+ flipRewriteStep(necessaryFlip, ty0.get)
              Out.lp_debug_info(s"Applying ${flipLiteral} to flip literal ${lit0.pretty}")
            }
            allSteps = allSteps :+ lpRewrite(rewritePattern, lpFunctionApp(rule.name, Seq()))
            Out.lp_debug_info(s"Applying ${rule.name} to transform equational literal to non-equational form")
            true
          case None =>
            Out.lp_debug_info(s"Unencoded transformation 1")
            false
        }
      } else if (lhs0 == rhs0) {
        if (!pol0 && (lhs1 == Some(lpOlBot))) {
          allSteps = allSteps :+ lpRewrite(rewritePattern, lpSimp_negEq_idem.instanciate(ty1.get, lhs1))
          true
        } else if (pol0 && (lhs1 == Some(lpOlTop))) {
          allSteps = allSteps :+ lpRewrite(rewritePattern, lpSimp_eq_idem.instanciate(ty1.get, lhs1))
          true
        } else false
      }else false
    } else if (!ty0.isDefined && ty1.isDefined) {
      // we need to transform to equational literal
      Out.lp_debug_info(s"Transformation from non-equational to equational form neccesary...")
      Out.lp_debug_info(s"lhs0: ${lhs0.get.pretty}, lhs1: ${lhs1.get.pretty}, rhs1: ${rhs1.get.pretty},")
      // analogous to the previous case
      if ((Seq(lhs1, rhs1).contains(lhs0) || Seq(lhs1.get, rhs1.get).contains(lpOlUnaryConnectiveTerm(lpNot, lhs0.get))) && (Seq(lhs1, rhs1).contains(Some(lpOlBot)) || Seq(lhs1, rhs1).contains(Some(lpOlTop)))) {

        // detect if we need to swap sides
        flip = (lhs0 == rhs1) // alphaEquivalent(lhs0.get, rhs1.get)

        val (necessaryRule, necessaryFlip): (Option[lpNameRef], Boolean) = if (!pol0) {
          if (!pol1) {
            // go from neg non-eq to neg eq
            // x: (π ((¬ x) = (¬ (x = ⊤))))
            // if ((alphaEquivalent(lhs1, lhs0) && alphaEquivalent(rhs1, Some(lpOlTop))) || (alphaEquivalent(rhs1, lhs0) && alphaEquivalent(lhs1, Some(lpOlTop)))) {
            if ((lhs1 == lhs0 && rhs1 == Some(lpOlTop)) || (rhs1 == lhs0 && lhs1 == Some(lpOlTop))) {
              // go to top
              (Some(lpSimp_negEqTop), false)
            } else {
              // go to bottom
              (Some(lpSimp_negNotEqBot), false)
            }
          } else {
            // go from neg non-eq to pos eq
            // x: (π ((¬ x) = ((¬ x) = ⊤)))
            if ((lhs1.get == lpOlUnaryConnectiveTerm(lpNot, lhs0.get) && rhs1 == Some(lpOlTop)) || (rhs1 == lpOlUnaryConnectiveTerm(lpNot, lhs0.get) && lhs1 == Some(lpOlTop))) {
              // go to top
              (Some(lpSimp_notEqTop), true)
            } else {
              // go to bottom
              (Some(lpSimp_eqBot), true)
            }
          }
        } else {
          if (!pol1) {
            // go from pos non-eq to neg eq
            // x: (π (x = (¬ ((¬ x) = ⊤))))
            if ((lpOlUnaryConnectiveTerm(lpNot, lhs0.get) == lhs1.get && rhs1 == Some(lpOlTop)) || (lpOlUnaryConnectiveTerm(lpNot, lhs0.get) == rhs1.get && lhs1 == Some(lpOlTop))) {
              // go to top
              (Some(lpSimp_negNotEqTop), false)
            } else {
              // go to bottom
              (Some(lpSimp_negEqBot), false) // todo
            }
          } else {
            // go from pos non-eq to pos eq
            // Prf(= [o] a (= [o] a ⊤))
            if ((lhs1 == lhs0 && rhs1 == Some(lpOlTop)) || (rhs1 == lhs0 && lhs1 == Some(lpOlTop))) {
              // go to top
              (Some(lpSimp_eqTop), true)

            } else {
              // go to bottom
              (Some(lpSimp_negNotEqBot), true) // todo
            }
          }
        }
        necessaryRule match {
          case Some(rule) =>
            allSteps = allSteps :+ lpRewrite(rewritePattern, lpFunctionApp(rule.name, Seq()), true)
            Out.lp_debug_info(s"Applying ${rule.name} to transform non-equational literal to equational form")
            if (flip) {
              allSteps = allSteps :+ flipRewriteStep(necessaryFlip, ty1.get)
              Out.lp_debug_info(s"Applying ${flipLiteral} to flip literal ${lit0.pretty}")
            }
            true
          case None =>
            Out.lp_debug_info(s"Unencoded transformation 2")
            false
        }
    } else if (lhs1 == rhs1) {
        if (!pol1 && (lhs0 == Some(lpOlBot))){
          allSteps = allSteps :+ lpRewrite(rewritePattern, lpSimp_negEq_idem.instanciate(ty1.get, lhs1),true)
          true
        } else if (pol1 && (lhs0 == Some(lpOlTop))){
          allSteps = allSteps :+ lpRewrite(rewritePattern, lpSimp_eq_idem.instanciate(ty1.get, lhs1), true)
          true
        } else false
      } else false
    } else if (ty0.isDefined && ty1.isDefined) {
      // both literals are equational, maybe we need to switch sides or transform bot/ top and polarity
      if (Seq(lhs0,rhs0).contains(lhs1) && Seq(lhs0,rhs0).contains(rhs1)){
        // the only possible difference is if the sides differ:
        if (lhs0 != lhs1){
          val necessaryFlip = if (pol0) true else false
          allSteps = allSteps :+ flipRewriteStep(necessaryFlip, ty0.get)
          Out.lp_debug_info(s"Applying ${flipLiteral} to flip literal ${lit0.pretty}")
          true
        }else {
          Out.lp_debug_info(s"Literals are already identical")
          true
        } // In this case, the sides are already the same
      } else if ((lhs1.get == lit0) && (rhs1.get == lpOlTop)){
        // transformation to equality literal for positive case
        allSteps = allSteps :+ lpRewrite(rewritePattern, lpFunctionApp(lpStd_eq_sym.name,Seq(lpFunctionApp(lpSimp_eqTop.name,Seq(lpOlTypedBinaryConnectiveTerm(lpEq,ty0.get,lhs0.get,rhs0.get))))))
        //Out.lp_debug_info(s"Applying ${eqLift_script().name.pretty} to un-lift literal ${lit0.pretty}")
        true
      } else {
        Out.lp_debug_info(s"Unencoded transformation between equational literals, $lit0")
        false
      }
    } else {
      // both literals are non-equational
      // -> They either are already the same ...
      if(lit0 == lit1){
        Out.lp_debug_info(s"Literals are already identical")
        // maybe transform bot to not top and vice versa?
        true
      }else{ // todo maybe check this first? may be more efficient...
        (lit0, lit1) match {
          // ... or we transform back and forth between top and bottom with negations
          case (`lpOlBot`,lpOlUnaryConnectiveTerm(`lpNot`,`lpOlTop`)) =>
            allSteps = allSteps :+ lpRewrite(rewritePattern, lpFunctionApp(lpSimp_negTop.name, Seq()), true)
            true
          case (lpOlUnaryConnectiveTerm(`lpNot`, `lpOlTop`), `lpOlBot`) =>
            allSteps = allSteps :+ lpRewrite(rewritePattern, lpFunctionApp(lpSimp_negTop.name, Seq()))
            true
          case _ => throw new Exception(s"Unable to transform ${lit0.pretty} to ${lit1.pretty}")
        }
        // ... or one is a double negation of the other todo
      }
    }
    if (canEncode) Out.lp_debug_info(s"success")
    (allSteps,canEncode)
  }

  ////////////////////////////////////////////////////////////////
  ////////// Change order within literals
  ////////////////////////////////////////////////////////////////

  case object flipLiteral extends lpNameRef {

    override def name: lpConstantTerm = lpConstantTerm("=_sym")

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

}
