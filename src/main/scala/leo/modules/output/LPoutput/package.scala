package leo.modules.output

import leo.Out
import leo.datastructures.Term.∙
import leo.datastructures.{Clause, Literal, Signature, Term, Type}
import leo.modules.HOLSignature.{===, HOLBinaryConnective, Not, |||}
import leo.modules.output.LPoutput.Encodings.type2LP
import leo.modules.output.LPoutput.lpDatastructures.{lpConstantTerm, lpDeclaration, lpDefinition, lpElWitness, lpEq, lpFunctionApp, lpHave, lpLambdaTerm, lpNot, lpOlBot, lpOlConstantTerm, lpOlFunctionApp, lpOlLambdaTerm, lpOlPolyType, lpOlQuantifiedTerm, lpOlTerm, lpOlTop, lpOlType, lpOlTypedBinaryConnectiveTerm, lpOlTypedVar, lpOlUnaryConnectiveTerm, lpOlUntypedBinaryConnectiveTerm, lpOlUntypedBinaryConnectiveTerm_multi, lpOlUntypedVar, lpOlUserDefinedPolyType, lpOlUserDefinedType, lpOlWildcard, lpOr, lpOtype, lpProofScript, lpProofScriptStep, lpRefine, lpReflexivity, lpRewritePattern, lpScheme, lpSet, lpSet2Schme, lpTerm, lpTypedVar, lpUntypedVar, lpWildcard}

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

  val lambdapiNames = Set(
    lpOtype.pretty, lpWildcard.pretty, lpSet.pretty, lpScheme.pretty,
    lpSet2Schme.pretty, lpEq.pretty, lpElWitness.pretty) // todo:generate automatically

  val lpAllowedRegEx = """^[^\t\r\n :,;`(){}\[\]".@$|?/]+$"""
  val lpKeywords = Set(
    "require", "open", "symbol", "notation", "builtin", "opaque",
    "rule", "unif_rule", "coerce_rule", "inductive", "proof",
    "assume", "apply", "refine", "simplify", "rewrite", "have",
    "print", "proofterm", "assert", "assertnot", "compute",
    "constant", "injective", "commutative", "associative",
    "in", "notation", "reflexivity", "admit", "right", "left") ++ lambdapiNames

  def findSafeName(str: String, sig: Signature): String = {
    val newName = s"${str}_"
    if (!sig.exists(newName)) newName
    else findSafeName(newName, sig)
  }

  private final val partiallyAlliedTPTPmap = //Vector("=", "!=", "&", "|", "~", "!", "?")
  // symbol =_part (a : Set) ≔ λ (x y : τ a), x = y;
    Map.apply("~" -> "¬_part", "=" -> "=_part", "!=" -> "!=_part", "&" -> "∧_part", "|" -> "∨_part", "!" -> "∀_part", "?" -> "∃_part")

  final def lpEscapeName(str: String,sig: Signature): String = {
    if (partiallyAlliedTPTPmap.keySet.contains(str)) {
      return partiallyAlliedTPTPmap(str)
    } //throw new Exception(s"found illegal $str")
    else if (lpKeywords.contains(str)) {
      val newName = findSafeName(str,sig)
      //Out.lp_debug_info(s"renamed $str to $newName")
      return newName
    }
    if (!str.matches(lpAllowedRegEx)){
      val newName = s"{|$str|}"
      Out.lp_debug_info(s"renamed $str to $newName")
      newName
    }
    else str
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

  def generateClausePattern(termPos:Int,clauseLen:Int, polarity:Boolean = true, patternTerm:lpOlTerm = lpOlUntypedVar(lpOlConstantTerm("x"))): lpOlUntypedBinaryConnectiveTerm_multi ={
    val litPol = if (polarity) patternTerm else lpOlUnaryConnectiveTerm(lpNot,patternTerm)
    val args = Seq.fill(clauseLen)(lpOlWildcard).updated(termPos, litPol)
    lpOlUntypedBinaryConnectiveTerm_multi(lpOr, args)
  }


  def generateClausePatternTerm(varPos: Int, clauseLen: Int, eqPos: Option[Int] = None, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpOlConstantTerm("x")), polarity: Boolean = true): Option[lpRewritePattern] = {
    // given the position of the literal that a rule should be applied to in a clause and weather or not this clause in embedded in an equality to be proven,
    // generate a rewrite pattern

    val maybeNegatedPatternVar = {
      if (polarity) patternVar
      else lpOlUnaryConnectiveTerm(lpNot, patternVar)
    }

    val clausePattern = if (clauseLen > 1) {
      generateClausePattern(varPos,clauseLen,true,maybeNegatedPatternVar)
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
        //case HOLBinaryConnective(lhs,rhs) => throw new Exception("")
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
          else throw new Exception(s"invalid position $currentPosition for connective ${lpOr.pretty}")
        //case f ∙ args =>
          //val (intermediatePattern, intermediateTerm) = acessSubterm(args(currentPosition +1), position.tail, sig, patternVar)
          //throw new Exception(s"this is an application to ${f.pretty}")

        case _ => throw new Exception(s"connective ${t.pretty} not encoded?")
      }
    }
  }
  def findRWTerm(searchFor:lpOlTerm, searchIn:lpOlTerm, replaceWith:lpOlTerm, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x"))): (lpRewritePattern, lpOlTerm) = {
    val (patternTerm, rewrittenTerm,counter, rwUnderBinder) = findRWTerm0(searchFor,searchIn,replaceWith, false, patternVar,0)
    if (counter != 1) throw new Exception(s"when trying to locate ${searchFor.pretty} in ${searchIn.pretty}, ${counter} occurrences were found")
    val rewritePattern = lpRewritePattern(patternTerm,patternVar)
    (rewritePattern,rewrittenTerm)
  }
  def findRWTerm0(searchFor:lpOlTerm, searchIn:lpOlTerm, replaceWith:lpOlTerm, rwUnderBinder:Boolean = false, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x")), currentX:Int = 0): (lpOlTerm, lpOlTerm, Int, Boolean) = {
    // find a specific subterm for the application of a rewrite operation
    // this function returns: The rewrite-pattern, the term modulo rewriting and an integer signaling how often the pattern was found.

    if (searchIn == searchFor) (patternVar,replaceWith, currentX + 1, rwUnderBinder)
    else {
      searchIn match {
        case `lpOlTop` =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case `lpOlBot` =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case lpOlConstantTerm(_) =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case lpOlTypedVar(_,_) =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case lpOlUntypedVar(lpConstantTerm(_)) =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case lpOlLambdaTerm(vars,body) =>
        val (patternbody, rewrittenbody0, counter, _) = findRWTerm0(searchFor, body, replaceWith, rwUnderBinder, patternVar, 0)
        val pattern = if (counter == 0) lpOlWildcard else lpOlLambdaTerm(vars, patternbody)
        val rewrittenTerm = lpOlLambdaTerm(vars, rewrittenbody0)
        (pattern, rewrittenTerm, counter, true)
      case lpOlQuantifiedTerm(quantifier, vars, body) =>
        val (patternbody, rewrittenbody0, counter, _) = findRWTerm0(searchFor, body, replaceWith, rwUnderBinder, patternVar, 0)
        val pattern = if (counter == 0) lpOlWildcard else lpOlQuantifiedTerm(quantifier, vars, patternbody)
        val rewrittenTerm = lpOlQuantifiedTerm(quantifier, vars, rewrittenbody0)
        (pattern, rewrittenTerm, counter, true)
      case lpOlUnaryConnectiveTerm(con, term) =>
          val (patternTerm, rewrittenTerm0, counter, rwUnderBinder0) = findRWTerm0(searchFor, term, replaceWith, rwUnderBinder, patternVar, 0)
          // to make sure patterns are not longer than necessary, we check weather rewriting at a specific position happend and - if this is not the case - just give "-"
          val pattern = if (counter == 0) lpOlWildcard else lpOlUnaryConnectiveTerm(con, patternTerm)
          val rewrittenTerm = lpOlUnaryConnectiveTerm(con, rewrittenTerm0)
          (pattern, rewrittenTerm, counter, rwUnderBinder0)
        case lpOlUntypedBinaryConnectiveTerm(con,lhs,rhs) =>
          val (patternLhs, rewrittenLhs, counterLhs, rwUnderBinderLhs) = findRWTerm0(searchFor, lhs, replaceWith, rwUnderBinder, patternVar, 0)
          val (patternRhs, rewrittenRhs, counterRhs, rwUnderBinderRhs) = findRWTerm0(searchFor, rhs, replaceWith, rwUnderBinder, patternVar, 0)
          // to make sure patterns are not longer than necessary, we check weather rewriting at a specific position happend and - if this is not the case - just give "-"
          val newCounter = counterLhs + counterRhs
          val pattern = if (newCounter == 0) lpOlWildcard else lpOlUntypedBinaryConnectiveTerm(con,patternLhs,patternRhs)
          val rewrittenTerm = lpOlUntypedBinaryConnectiveTerm(con,rewrittenLhs,rewrittenRhs)
          (pattern, rewrittenTerm, newCounter, rwUnderBinderLhs || rwUnderBinderRhs)
        case lpOlUntypedBinaryConnectiveTerm_multi(con, args) =>
          val intermediateResult = args.map(arg => findRWTerm0(searchFor, arg, replaceWith, rwUnderBinder, patternVar, 0))
          // to make sure patterns are not longer than necessary, we check weather rewriting at a specific position happend and - if this is not the case - just give "-"
          val newCounter = intermediateResult.map(_._3).sum
          val pattern = if (newCounter == 0) lpOlWildcard else lpOlUntypedBinaryConnectiveTerm_multi(con, intermediateResult.map(_._1))
          val rewrittenTerm = lpOlUntypedBinaryConnectiveTerm_multi(con, intermediateResult.map(_._2))
          val rwUnderBinder0 = intermediateResult.map(_._4).contains(true)
          (pattern, rewrittenTerm, newCounter, rwUnderBinder0)
        case lpOlTypedBinaryConnectiveTerm(con, ty, lhs, rhs) =>
          val (patternLhs, rewrittenLhs, counterLhs, rwUnderBinderLhs) = findRWTerm0(searchFor, lhs, replaceWith, rwUnderBinder, patternVar, 0)
          val (patternRhs, rewrittenRhs, counterRhs, rwUnderBinderRhs) = findRWTerm0(searchFor, rhs, replaceWith, rwUnderBinder, patternVar, 0)
          // to make sure patterns are not longer than necessary, we check weather rewriting at a specific position happend and - if this is not the case - just give "-"
          val newCounter = counterLhs + counterRhs
          val pattern = if (newCounter == 0) lpOlWildcard else lpOlTypedBinaryConnectiveTerm(con, ty, patternLhs, patternRhs)
          val rewrittenTerm = lpOlTypedBinaryConnectiveTerm(con, ty, rewrittenLhs, rewrittenRhs)
          (pattern, rewrittenTerm, newCounter, rwUnderBinderLhs || rwUnderBinderRhs)
        case lpOlFunctionApp(head,args) =>
          val (patternHead, termHead, counterHead, rwUnderBinderHead) = findRWTerm0(searchFor, head, replaceWith, rwUnderBinder, patternVar, 0)
          var patternsArgs: Seq[Either[lpOlTerm,lpOlType]] = Seq.empty
          var termsArgs: Seq[Either[lpOlTerm,lpOlType]] = Seq.empty
          var rwUnderBinderArg = false
          var countersArgs = 0
          args foreach{ arg =>
            arg match {
              case Left(term) =>
                val (patternArg0, termArg, counterArg, rwUnderBinderArg0) = findRWTerm0(searchFor, term, replaceWith, rwUnderBinder, patternVar, 0)
                val patternArg = if (counterArg == 0) lpOlWildcard else patternArg0
                patternsArgs = patternsArgs :+ Left(patternArg)
                termsArgs = termsArgs :+ Left(termArg)
                countersArgs = countersArgs + counterArg
                if (rwUnderBinderArg0) rwUnderBinderArg = true
              case Right(ty) =>
                patternsArgs = patternsArgs :+ Left(lpOlWildcard)
                termsArgs = termsArgs :+ Right(ty)
            }
          }
          val pattern = if (counterHead + countersArgs == 0) lpOlWildcard else lpOlFunctionApp(patternHead, patternsArgs)
          val rewtrittenTerm = lpOlFunctionApp(termHead, termsArgs)
          (pattern,rewtrittenTerm,countersArgs, rwUnderBinderArg || rwUnderBinderHead)

          // just for testing
        case _ => throw new Exception(s"encountered unexptcted term $searchIn when trying to find term ${searchFor.pretty} in ${searchIn.pretty}")
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
