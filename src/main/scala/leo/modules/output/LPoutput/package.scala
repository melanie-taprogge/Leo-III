package leo.modules.output

import leo.datastructures.{Clause, Literal, Signature, Term, Type}
import leo.modules.HOLSignature.{===, Not, |||}
import leo.modules.output.LPoutput.Encodings.type2LP
import leo.modules.output.LPoutput.lpDatastructures.{lpConstantTerm, lpEq, lpFunctionApp, lpHave, lpLambdaTerm, lpNot, lpOlConstantTerm, lpOlLambdaTerm, lpOlPolyType, lpOlTerm, lpOlTypedBinaryConnectiveTerm, lpOlTypedVar, lpOlUnaryConnectiveTerm, lpOlUntypedBinaryConnectiveTerm, lpOlUntypedBinaryConnectiveTerm_multi, lpOlUntypedVar, lpOlUserDefinedPolyType, lpOlWildcard, lpOr, lpOtype, lpProofScript, lpProofScriptStep, lpRefine, lpReflexivity, lpRewritePattern, lpTerm, lpTypedVar, lpUntypedVar}

package object LPoutput {

  ////////////////////////////////////////////////////////////////
  ////////// Name Generation
  ////////////////////////////////////////////////////////////////

  def nameHypothesis(usedH: Int): lpConstantTerm = {
    lpConstantTerm(s"h${usedH + 1}")
  }

  def nameBottom(usedB: Int): lpOlConstantTerm = {
    lpOlConstantTerm(s"b${usedB + 1}")
  }

  def nameX(usedX: Int): lpOlConstantTerm = {
    lpOlConstantTerm(s"x${usedX + 1}")
  }

  def nameType(usedT: Int): lpOlPolyType = {
    lpOlUserDefinedPolyType(s"t${usedT + 1}")
  }

  def nameStep(number: Int): lpConstantTerm = {
    lpConstantTerm(s"step${number}")
  }

  def nestedLorIlApp(lhs: Seq[lpOlTerm], rhs: Seq[lpOlTerm], prfRhs: lpTerm): lpFunctionApp = {
    // iterativeley construct the proofs for disjunctions of literals based on a proof for the rhs. This is necessary to avoid errors in cases where (a \lor b) \lor (c \lor d ( ...
    // would otherwise been proven
    if (lhs.length == 0) throw new Exception("trying to pass empty lhs to nestedLorIlApp")
    if (lhs.length == 1) NaturalDeductionRules.orIr().instanciate(lhs.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, rhs), Some(prfRhs))
    else {
      val currentVar = lhs.last
      val newLhs = lhs.init
      val newRhs = Seq(currentVar) ++ rhs
      val newProof = NaturalDeductionRules.orIr().instanciate(currentVar, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, rhs), Some(prfRhs))
      nestedLorIlApp(newLhs, newRhs, newProof)
    }
  }

  def clauseRuleQuantification(parent: Clause, bVarMap: Map[Int, String], sig: Signature): (Seq[lpTypedVar], Seq[lpUntypedVar]) = {
    //throw new Exception("CHANGE clauseRuleQuantification")

    var clauseQuantification: Seq[lpTypedVar] = Seq.empty
    var applySymbolsToParent: Seq[lpUntypedVar] = Seq.empty
    parent.implicitlyBound foreach { name_type =>
      //clauseQuantification.append(s"(${bVarMap(name_type._1)}: $Els($uparrow ${type2LP(name_type._2, sig)._1}))")
      clauseQuantification = clauseQuantification :+ lpTypedVar(lpConstantTerm(bVarMap(name_type._1)), type2LP(name_type._2, sig)._1.lift2Meta)
      //applySymbolsToParent = applySymbolsToParent ++ Seq(bVarMap(name_type._1))
      applySymbolsToParent = applySymbolsToParent :+ lpUntypedVar(lpConstantTerm(bVarMap(name_type._1)))
    }
    (clauseQuantification, applySymbolsToParent)

  }

  def findLitInClause(lit: Literal, parent: Clause): Int = {
    val indicesOfOccurrence: IndexedSeq[Int] = parent.lits.indices.filter(index => parent.lits(index) == lit)
    val positionInClause = if (indicesOfOccurrence.length == 1) indicesOfOccurrence.head
    else if (indicesOfOccurrence.length == 0) throw new Exception(s"literal to transform not found in clause when attempfing to generate lp encoding")
    else throw new Exception(s"literal to transform found more than once when attempfing to generate lp encoding")
    positionInClause
  }

  def generateClausePatternTerm(varPos: Int, clauseLen: Int, eqPos: Option[Int] = None, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpOlConstantTerm("x")), polarity: Boolean = true): Option[lpRewritePattern] = {
    // given the position of the literal that a rule should be applied to in a clause and weather or not this clause in embedded in an equality to be proven,
    // generate a rewrite pattern

    val maybeNegatedPatternVar = {
      if (polarity) patternVar
      else lpOlUnaryConnectiveTerm(lpNot, patternVar)
    }

    val clausePattern = if (clauseLen > 1) {
      val args = Seq.fill(clauseLen)(lpOlWildcard).updated(varPos, maybeNegatedPatternVar)
      lpOlUntypedBinaryConnectiveTerm_multi(lpOr, args)
    } else {
      maybeNegatedPatternVar
    }

    eqPos match {
      case Some(pos) =>
        val patternEq = {
          if (pos == 0) lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, clausePattern, lpOlWildcard)
          else if (pos == 1) lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlWildcard, clausePattern)
          else throw new Exception(s"position $pos provided to encode position in equality")
        }
        Some(lpRewritePattern(patternEq, patternVar))
      case None =>
        if (clausePattern == maybeNegatedPatternVar) None
        else Some(lpRewritePattern(clausePattern, patternVar))
    }
  }

  def acessSubterm(t: Term, position: Seq[Int], sig: Signature, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x"))): (lpOlTerm, Term) = {
    // generate a pattern for the application of rewriting
    //todo: for longer clauses we need to loop through the literals and for literals we need to consider both sides

    // if the length of position is 1, we arrived at the last step and want to provide a proof
    if (position.length == 0) (patternVar, t)

    else {

      val currentPosition = position.head
      t match {
        case tl ||| tr =>
          if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(tr, position.tail, sig, patternVar)
            (lpOlUntypedBinaryConnectiveTerm(lpOr, intermediatePattern, lpOlWildcard), intermediateTerm)
          }
          else if (currentPosition == 2) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(tl, position.tail, sig, patternVar)
            (lpOlUntypedBinaryConnectiveTerm(lpOr, lpOlWildcard, intermediatePattern), intermediateTerm)
          }
          else throw new Exception(s"invalid position $currentPosition vor connective ${lpOr.pretty}")
        case Not(t2) =>
          if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(t2, position.tail, sig, patternVar)
            (lpOlUnaryConnectiveTerm(lpNot, intermediatePattern), intermediateTerm)
          }
          else throw new Exception(s"invalid position $currentPosition vor connective ${lpOr.pretty}")
        case tl === tr =>
          val ty = type2LP(tl.ty, sig, Set())._1
          if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(tr, position.tail, sig, patternVar)
            (lpOlTypedBinaryConnectiveTerm(lpEq, ty, intermediatePattern, lpOlWildcard), intermediateTerm)
          }
          else if (currentPosition == 2) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(tl, position.tail, sig, patternVar)
            (lpOlTypedBinaryConnectiveTerm(lpEq, ty, lpOlWildcard, intermediatePattern), intermediateTerm)
          }
          else throw new Exception(s"invalid position $currentPosition vor connective ${lpOr.pretty}")

        case _ => throw new Exception(s"connective not encoded?")
      }
    }
  }

  def wholeHaveRewriteStep(rewriteSteps: Seq[lpProofScriptStep], nameStep: String, nameSubStep: String, before: lpOlTerm, sourceBefore: lpTerm, after: lpOlTerm): lpHave = {
    //todo: use this in my simplification steps?

    // In many cases, we want to generate Sub-Steps for rewritings in proofs that first prove the equality of Term A and B (when for instance B is a simplified version of A)
    // And then prove B given A. This function generates such steps.

    // 1. Proof equality
    val equalityToProve = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, after, before)
    val withAddedReflexivity = lpProofScript(rewriteSteps :+ lpReflexivity())
    val subStep = lpHave(nameSubStep, equalityToProve.prf, withAddedReflexivity)

    // 2. Proof the "after" given the equality
    //val stepProof = lpProofScript(Seq(subStep,lpRefine(lpFunctionApp(lpConstantTerm(nameSubStep),Seq(lpUseful.Identity,sourceBefore)))))
    //val stepProof = lpProofScript(Seq(subStep,lpRefine(lpUseful.applyToEqualityTerm(lpOtype,after,before,lpOlConstantTerm(nameSubStep),lpOlLambdaTerm(Seq(lpOlTypedVar(lpOlConstantTerm("x"),lpOtype)),lpOlConstantTerm("x")),Some(sourceBefore)))))
    val stepProof = lpProofScript(Seq(subStep, lpRefine(NaturalDeductionRules.eqDef().instanciate(lpOtype.lift2Poly, after, before, Some(lpOlConstantTerm(nameSubStep)), Some(lpOlLambdaTerm(Seq(lpOlTypedVar(lpOlConstantTerm("x"), lpOtype)), lpOlConstantTerm("x"))), Some(sourceBefore)))))

    // the whole Have step:
    lpHave(nameStep, after.prf, stepProof)
  }

  final def clauseImplicitsToTPTPQuantifierList_map(implicitlyQuantified: Seq[(Int, Type)])(sig: Signature): Map[Int, String] = {
    // shoretened version to only consruct the map
    //todo either incorporate somewhere or make it a proper function
    val count = implicitlyQuantified.size
    var resultBindingMap: Map[Int, String] = Map()

    var curImplicitlyQuantified = implicitlyQuantified
    var i = 0
    while (i < count) {
      val (scope, _) = curImplicitlyQuantified.head
      curImplicitlyQuantified = curImplicitlyQuantified.tail
      val name = intToName(count - i - 1)
      resultBindingMap = resultBindingMap + (scope -> name)
      i = i + 1
    }
    resultBindingMap
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// USEFUL TERMS //////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  object Identity extends lpTerm {
    val x1 = lpUntypedVar(lpConstantTerm("x"))
    val definition = lpLambdaTerm(Seq(x1), x1)

    override def pretty: String = definition.pretty
  }

}
