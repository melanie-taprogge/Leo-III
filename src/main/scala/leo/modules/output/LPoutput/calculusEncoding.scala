package leo.modules.output.LPoutput

import leo.datastructures.Clause.maxImplicitlyBound
import leo.datastructures.Literal.{asTerm, vars}
import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.LPoutput.Encodings._
import leo.datastructures.{Clause, ClauseProxy, Literal, Signature, Term}
import leo.modules.HOLSignature._
import leo.modules.calculus.{BoolExt, Unification}
import leo.modules.output.intToName
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.Transformations._
import leo.modules.output.LPoutput.SimplificationEncoding
import leo.modules.output.LPoutput.lpInferenceRuleEncoding.{funextPosEq_rev, polaritySwitchEqLit, polaritySwitchNonEqLit}
import leo.modules.output.LPoutput.lpUseful
import leo.modules.output.ToTPTP.clauseImplicitsToTPTPQuantifierList

import scala.collection.mutable


object calculusEncoding {

  // general principles

  // name new variables for LP proofs:
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

  def npp(a: String, PrfAorA: String, symbolTypeMap: Map[String, String]): String = {


    ""
  }

  // construct a proof for the application of rules to literals
  def cOR(a: lpOlTerm, b: lpOlTerm, PrfaIMPb: lpTerm, c: lpOlTerm, d: lpOlTerm, PrfcIMPd: lpTerm, PrfaORc: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int)) = {
    // a b c d: (Prf a → Prf b) → (Prf c → Prf d) → (Prf(a ∨ c)) → (Prf(b ∨ d))
    // λ a b c d (h1: Prf a → Prf b) (h2: Prf c → Prf d) (h3: Prf (a ∨ c)), h3 (b ∨ d) (λ h4 b1 h5 _, h5 (h1 h4)) (λ h4 b1 _ h6, h6 (h2 h4));
    //throw new Exception(s"CHANGE cOR")

    var hCount = parameters._1
    var bCount = parameters._2

    //val abstractions: StringBuffer = new StringBuffer("")
    var abstractions: Seq[lpTypedVar] = Seq.empty

    //// introduce hypothesis variables if necessary

    // if there is no proof for a => b, this could mean that either ...
    val hyp1 = if (PrfaIMPb == lpOlNothing) {
      // ...we only want to proof (Prf c → Prf d) → (Prf(a ∨ c)) → (Prf(a ∨ d)), in this case b = ""
      // then we do not need this hypothesis at all and assign it to "":
      if (b == lpOlNothing) lpOlNothing
      // ... or that we do indeed want the rule for b as well but we do not have the proof but abstract over it
      // In this case we want to create a fresh variable for the hypothesis
      else nameHypothesis(hCount)
      // if we have provided a proof we instanciate the hypothesis with it
    } else PrfaIMPb
    // if we have used a fresh variable for the hypothesis we abstract over it and increase the h-counter:
    if ((PrfaIMPb == lpOlNothing) & (b != lpOlNothing)) {
      hCount = hCount + 1
      //abstractions.append(s"($hyp1 : $Prf $a $rightarrow $Prf $b) ")
      abstractions = abstractions :+ lpTypedVar(hyp1,lpMlFunctionType(Seq(a.prf,b.prf)))
    }

    // the same procedure fot the second hypothesis
    val hyp2 = if (PrfcIMPd == lpOlNothing) {
      if (d == lpOlNothing) lpOlNothing
      else nameHypothesis(hCount)
    } else PrfcIMPd
    if ((PrfcIMPd == lpOlNothing) & (d != lpOlNothing)) {
      hCount = hCount + 1
      //abstractions.append(s"($hyp2 : $Prf $c $rightarrow $Prf $d) ")
      abstractions = abstractions :+ lpTypedVar(hyp2,lpMlFunctionType(Seq(c.prf,d.prf)))
    }

    // similarly we encode the third hypothesis (Prf(a ∨ c)) but in this case a and c always have to be provided
    val hyp3 = if (PrfaORc == lpOlNothing) nameHypothesis(hCount) else PrfaORc
    if (PrfaORc == lpOlNothing) {
      hCount = hCount + 1
      //abstractions.append(s"($hyp3 : $Prf($a $lor $c)) ")
      abstractions = abstractions :+ lpTypedVar(hyp3,lpOlUntypedBinaryConnectiveTerm(lpOr,a,c).prf)
    }

    // if we have any abstractions, we need to add lambda:
    //val finalAbstrations: String = if (abstractions.toString != "") s"$LPlambda $abstractions , " else ""

    // hypotheses that will never be instanciated
    val hyp4 = nameHypothesis(hCount)
    hCount = hCount + 1
    val hyp5 = nameHypothesis(hCount)
    hCount = hCount + 1
    val hyp6 = nameHypothesis(hCount)
    hCount = hCount + 1
    val bot1 = nameBottom(bCount)
    bCount = bCount + 1

    // now we want to proof slightly different rules depending on weather only a, only b or both were provided:
    var lambdaTerm: lpTerm = lpOlNothing
    if (b != lpOlNothing) {
      if (d != lpOlNothing) {
        //throw new Exception(s"test this version of cOr 1")
        // (Prf a → Prf b) → (Prf c → Prf d) → (Prf(a ∨ c)) → (Prf(b ∨ d))
        //val lambdaTermStr = s"($finalAbstrations$hyp3 ($b ∨ $d) ($LPlambda $hyp4 $bot1 $hyp5 _,                                                                      $hyp5 ($hyp1 $hyp4)) ($LPlambda $hyp4 $bot1 _ $hyp6,                                                                                                $hyp6 ($hyp2 $hyp4)))"
        lambdaTerm = lpLambdaTerm(abstractions,lpFunctionApp(hyp3,Seq(lpOlUntypedBinaryConnectiveTerm(lpOr,b,d),lpLambdaTerm(Seq(lpUntypedVar(hyp4),lpUntypedVar(bot1),lpUntypedVar(hyp5),lpUntypedVar(lpWildcard)),lpFunctionApp(hyp5,Seq(lpFunctionApp(hyp1,Seq(hyp4))))),lpLambdaTerm(Seq(lpUntypedVar(hyp4),lpUntypedVar(bot1),lpUntypedVar(lpWildcard),lpUntypedVar(hyp6)),lpFunctionApp(hyp6,Seq(lpFunctionApp(hyp2,Seq(hyp4))))))))
      } else {
        throw new Exception(s"test this version of cOr 2") //likely wrong becasue this was probably coppied from the first case and that was wrong and changes were copied blindly...
        // (Prf a → Prf b) → (Prf(a ∨ c)) → (Prf(b ∨ c))
        //val lambdaTermStr = s"($finalAbstrations$hyp3 ($b ∨ $c) ($LPlambda $hyp4 $bot1 $hyp5 _, $hyp5 ($hyp1 $hyp4)) ($LPlambda $hyp4 $bot1 _ $hyp6, $hyp6 $hyp4))"
        lambdaTerm = lpLambdaTerm(abstractions,lpFunctionApp(hyp3,Seq(lpOlUntypedBinaryConnectiveTerm(lpOr,b,d),lpLambdaTerm(Seq(lpUntypedVar(hyp4),lpUntypedVar(bot1),lpUntypedVar(hyp5),lpUntypedVar(lpWildcard)),lpFunctionApp(hyp5,Seq(lpFunctionApp(hyp1,Seq(hyp4))))),lpLambdaTerm(Seq(lpUntypedVar(hyp4),lpUntypedVar(bot1),lpUntypedVar(lpWildcard),lpUntypedVar(hyp6)),hyp6))))
      }
    } else if (d != lpOlNothing) {
      throw new Exception(s"test this version of cOr 3") //likely wrong becasue this was probably coppied from the first case and that was wrong and changes were copied blindly...
      // (Prf c → Prf d) → (Prf(a ∨ c)) → (Prf(a ∨ d))
      //val lambdaTermStr =   s"($finalAbstrations$hyp3 ($a ∨ $d) ($LPlambda $hyp4 $bot1 $hyp5 _, $hyp5 $hyp4)                                                                                                    ($LPlambda $hyp4 $bot1 _ $hyp6, $hyp6 ($hyp2 $hyp4)))"
      lambdaTerm = lpLambdaTerm(abstractions,lpFunctionApp(hyp3,Seq(lpOlUntypedBinaryConnectiveTerm(lpOr,a,d),lpLambdaTerm(Seq(lpUntypedVar(hyp4),lpUntypedVar(bot1),lpUntypedVar(hyp5),lpUntypedVar(lpWildcard)),lpFunctionApp(hyp5,Seq(hyp4))),lpLambdaTerm(Seq(lpUntypedVar(hyp4),lpUntypedVar(bot1),lpUntypedVar(lpWildcard),lpUntypedVar(hyp6)),lpFunctionApp(hyp6,Seq(lpFunctionApp(hyp2,Seq(hyp4))))))))
    } else {
      throw new Exception(s"for the application of cOR, neither b nor d were provided")
    }
    (lambdaTerm, (hCount, bCount, parameters._3, parameters._4))
  }


  // given a clause and a sequence of rule applications on the literals, execute these rule applications
  def ruleAppClause(cl0 : Clause, cl1 : Clause, transformations: Seq[lpTerm], sig:Signature, parameters0: (Int, Int, Int, Int)):(lpTerm,(Int, Int, Int, Int))={
    //throw new Exception("CHANGE RULEAPPCLAUSE")

    // todo: universal quantification over free variables -> pass on bVars
    // this function provies a term of type Prf(cl0) -> Prf(cl1)
    // transformations should have the proof as a lpTerm for applied rules or lpOlNothing if the literal was not transformed
    var parameters = parameters0
    if (cl0.lits.length != transformations.length){
      throw new Exception(s"failed to apply rules to clause ${cl0.pretty}, wrong number of rule applications were given")
    }else if (transformations.length >= 2){
      //throw new Exception(s"application of rules to multi-literal clause is implemented but not tested. remove this exception and test carefully")
      // go over the literals one by one and always encode the transition of the left one and pass on the rest to this function again
      val leftLit0 = clause2LP_unquantified(Clause(cl0.lits.head), Set.empty, sig)._2
      val leftLit1 = if (transformations.head != lpOlNothing) clause2LP_unquantified(Clause(cl1.lits.head), Set.empty, sig)._2 else lpOlNothing
      val leftLitRule = if (transformations.head != lpOlNothing) transformations.head else lpOlNothing
      val rightLit0 = clause2LP_unquantified(Clause(cl0.lits.tail), Set.empty, sig)._2
      val rightLit1 = if (transformations.tail.forall(_ == lpOlNothing)) clause2LP_unquantified(Clause(cl1.lits.tail), Set.empty, sig)._2 else lpOlNothing
      val rightLitRule = if (transformations.tail.forall(_ == lpOlNothing)) {
        val (res,newParm) = ruleAppClause(Clause(cl0.lits.tail), Clause(cl1.lits.tail), transformations.tail, sig, parameters)
        parameters = newParm
        res
      } else lpOlNothing
      if (leftLit1!=lpOlNothing | rightLit1!=lpOlNothing){
        // if rules were applied we want to transform this
        cOR(leftLit0,leftLit1,leftLitRule,rightLit0,rightLit1,rightLitRule,lpOlNothing,parameters)
      }else{
        throw new Exception(s"no rules applied to $cl0, yet runAppClauses was called")
      }
    }else{
      (transformations.head,parameters) // is this correct?
    }

  }

  def ruleAppClause_new(transformations: Seq[(lpOlTerm,lpOlTerm,lpTerm)], parameters0: (Int, Int, Int, Int)): (lpTerm,(Int, Int, Int, Int)) = {
    // todo: universal quantification over free variables -> pass on bVars
    //throw new Exception("CHANGE RULEAPPCLAUSENEW")

    // this function provies a term of type Prf(cl0) -> Prf(cl1)
    // transformations should have the proof as a lpTerm for applied rules or lpOlNothing if the literal was not transformed

    var parameters = parameters0
    //print(s"transformed clauses: ${transformations.map(_._1)}\n")
    //print(s"transformeations to perform: ${transformations.map(_._3)}\n")

    // we step wise construct a multi literal disjunction by looking at one left literal at a time
    if (transformations.length >= 2) {
      //throw new Exception(s"application of rules to multi-literal clause is implemented but not tested. remove this exception and test carefully")
      val leftLit0 = transformations.head._1
      val leftLit1 = transformations.head._2
      val leftLitRule = if (transformations.head._3 != lpOlNothing) transformations.head._3 else {
        val (selfProof, parametersNew) = selfImp(leftLit0,parameters)
        parameters = parametersNew
        selfProof
      }
      //print(s"leftLitRule: $leftLitRule\n")
      //val restLits0: String = s"(${transformations.tail.map(_._1).mkString(s" $lor ")})"
      val restLits0: lpOlTerm = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,transformations.tail.map(_._1))
      //val restLits1: String = s"(${transformations.tail.map(_._2).mkString(s" $lor ")})"
      val restLits1: lpOlTerm = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,transformations.tail.map(_._2))
      val restLitsRule: lpTerm = if (!(transformations.tail.map(_._3).forall(_ == lpOlNothing))) {
        val (res, newParm) = ruleAppClause_new(transformations.tail, parameters)
        parameters = newParm
        res
      } else {
        val (selfProof, parametersNew) = selfImp(restLits0, parameters)
        parameters = parametersNew
        selfProof
      }
      //print(s"rightLitRule: $restLitsRule\n")
      //print(s"unappliedLambdaTerm cor: \n${cOR(lpOlConstantTerm("a"),lpOlConstantTerm("b"),lpOlNothing,lpOlConstantTerm("c"),lpOlConstantTerm("d"),lpOlNothing,lpOlNothing,(0,0,0,0))._1.pretty}\n")
      cOR(leftLit0, leftLit1, leftLitRule, restLits0, restLits1, restLitsRule, lpOlNothing, parameters)
    } else {
      (transformations.head._3, parameters) // is this correct?
    }
  }


  def clauseRuleQuantification (parent: Clause, bVarMap: Map[Int, String], sig: Signature):(Seq[lpTypedVar],Seq[lpUntypedVar])={
    //throw new Exception("CHANGE clauseRuleQuantification")

    var clauseQuantification: Seq[lpTypedVar] = Seq.empty
    var applySymbolsToParent: Seq[lpUntypedVar] = Seq.empty
    parent.implicitlyBound foreach { name_type =>
      //clauseQuantification.append(s"(${bVarMap(name_type._1)}: $Els($uparrow ${type2LP(name_type._2, sig)._1}))")
      clauseQuantification = clauseQuantification :+ lpTypedVar(lpConstantTerm(bVarMap(name_type._1)),type2LP(name_type._2, sig)._1.lift2Meta)
      //applySymbolsToParent = applySymbolsToParent ++ Seq(bVarMap(name_type._1))
      applySymbolsToParent = applySymbolsToParent :+ lpUntypedVar(lpConstantTerm(bVarMap(name_type._1)))
    }
    (clauseQuantification,applySymbolsToParent)

  }
  def encPolaritySwitchLit(l: Literal, bVarMap: Map[Int, String], sig: Signature, parameters: (Int, Int, Int, Int)): (Boolean, lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // encode the proofs for the switch rules of the literals
    // like PolaritySwtich.apply in Normalization rules
    // but Insted of using the can apply earlier, i just tested weather I applied anything here!
    // if something was changed I retunr (True,proof), otherwise (False,"")

    //throw new Exception("CHANGE encPolaritySwitchLit")

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val hyp1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val hyp2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val hyp3 = nameHypothesis(hCount)
    hCount = hCount + 1
    val bot1 = nameBottom(bCount)
    bCount = bCount + 1
    val bot2 = nameBottom(bCount)
    bCount = bCount + 1
    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1

    if (l.equational) {
      throw new Exception("CHANGE equational encPolaritySwitchLit")
      // todo: test this
      /*
      (l.left, l.right) match {
        case (Not(l2), Not(r2)) =>
          val encLeft = term2LP(l.left, bVarMap, sig, Set.empty)._1
          val encRight = term2LP(l.right, bVarMap, sig, Set.empty)._1
          // proof term for Prf(eq [↑ o] (¬ a) (¬ b)) → Prf(eq [↑ o] a b)
          if (l.polarity) (true, s"($LPlambda ($hyp1: $Prf ($equ [$uparrow $oType] ($lnot $encLeft) ($lnot $encRight))) $x1 ($hyp2 : $Prf ($x1 $encLeft)), $propExt_name ($lnot ($lnot $encRight)) $encRight ($npp_name $encRight) ($LPlambda $hyp3 $bot1 $bot2, $bot1 $hyp3 $bot2) $x1 ($hyp1 ($LPlambda $x2, $x1 ($lnot $x2)) ($propExt_name $encLeft ($lnot ($lnot $encLeft)) ($LPlambda $hyp3 $bot1 $bot2, $bot1 $hyp3 $bot2) ($npp_name $encLeft) $x1 $hyp2)))", (hCount, bCount, xCount), usedSymbols + propExt_name)
          // proof term for Prf(¬ (eq [↑ o] (¬ a) (¬ b))) → Prf(¬ (eq [↑ o] a b))
          else (true, s"($LPlambda ($hyp1 : $Prf ($lnot ($equ [$uparrow $oType] ($lnot $encLeft) ($lnot $encRight)))) ($hyp2 : $Prf ($equ [$uparrow $oType] $encLeft $encRight)), $hyp1 ($LPlambda $x1 $hyp3, $hyp2 ($LPlambda $x2, $x1 ($lnot $x2)) $hyp3))", (hCount, bCount - 2, xCount), usedSymbols)
        case _ => (false, "", parameters, usedSymbols)
      }

       */
    } else {
      //throw new Exception("CHANGE non eq encPolaritySwitchLit")
      l.left match {
        case Not(l2) =>
          if (l.polarity) {
            throw new Exception("TEST non eq encPolaritySwitchLit for positive lit")
            // todo: test
            /*
            // in this case the encoded literal does not change
            (false, lpOlNothing, parameters, Set.empty)
             */
          } else {
            // In this case we need to apply npp in the encoding
            val encLit = term2LP(l2, bVarMap, sig, Set.empty)._1
            //(true, s"($npp_name $encLit)", parameters, Set(npp_name))
            (true, lpFunctionApp(lpNpp.name,Seq(encLit)),parameters,Set(lpNpp))
            //Literal(l2, !l.polarity)
          }
        case _ => throw new Exception("TEST non eq encPolaritySwitchLit for non negated lit")//(false, "", parameters, usedSymbols)
      }
    }
  }

  def encPolaritySwitchClause(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, sig: Signature, parameters0: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // like control.switchPolarity

    //throw new Exception("CHANGE encPolaritySwitchClause")

    var parameters = parameters0
    var usedSymbols: Set[lpStatement] = Set.empty

    var transformations: Seq[lpTerm] = Seq.empty

    val bVarMap = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

    val litsIt = parent.cl.lits.iterator

    while (litsIt.hasNext) {
      val lit = litsIt.next()
      val (wasApplied, ruleProof, parametersNew, usedSymbolsNew) = encPolaritySwitchLit(lit, bVarMap, sig, parameters)
      //print(s"endoed lit: ${ruleProof.pretty}\n")
      if (wasApplied) {
        parameters = parametersNew
        usedSymbols = usedSymbols ++ usedSymbolsNew
        // add the proof to the list of transformations that will be inserted into the proof of the clause application
        transformations = transformations.appended(ruleProof)
      } else {
        // do nothing but add to track
        transformations = transformations.appended(lpOlNothing)
      }
    }
    if (transformations.forall(_ == "")) {
      throw new Exception(s"encPolaritySwitchClause was called but polarity was not switched for any literals")
    } else {
      val (encProofRule, newParameters) = ruleAppClause(parent.cl, child.cl, transformations, sig, parameters)
      //(s"$encProofRule $parentNameLpEnc", newParameters, usedSymbols)
      (lpFunctionApp(encProofRule,Seq(parentNameLpEnc)), newParameters, usedSymbols)
    }
  }

  def encPolaritySwitchClause_proofScript(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Set[lpStatement]) = {

    var usedSymbols: Set[lpStatement] = Set.empty

    val bVarMap = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    var allRewriteSteps: Seq[lpProofScriptStep] = Seq.empty
    var polaritySwitchCount: Int = 0

    // first: abstract over the variables free in the child
    val freeVarsChild = child.cl.implicitlyBound.map(var0 => lpUntypedVar(lpConstantTerm(bVarMap(var0._1))))
    if (freeVarsChild.nonEmpty) allSteps = allSteps :+ lpAssume(freeVarsChild)

    // second: Go over the literals of the parent and apply polarity switch if applicable
    parent.cl.lits foreach { origLit =>
      if (origLit.equational){
        (origLit.left, origLit.right) match{
          case (Not(l),Not(r)) =>
            // in this case we just transform the literal of form a = b to (¬ a) = (¬ b)
            val encLeft = term2LP(l,bVarMap,sig)._1
            val encRight = term2LP(r,bVarMap,sig)._1
            val transfLit = Literal.apply(l,r,origLit.polarity)

            // prove the equality between the lit before and after transformation
            val equalityToProve = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,encLeft,encRight),term2LP(asTerm(origLit),bVarMap,sig)._1)
            val polaritySwitchStep = lpRefine(polaritySwitchEqLit.instanciate(encLeft,encRight))
            val polaritySwitchName = s"PolaritySwitch$polaritySwitchCount"
            polaritySwitchCount = polaritySwitchCount + 1
            val havepolaritySwitchStep = lpHave(polaritySwitchName,equalityToProve.prf,lpProofScript(Seq(polaritySwitchStep)))
            allSteps = allSteps :+ havepolaritySwitchStep
            usedSymbols = usedSymbols + polaritySwitchEqLit

            // apply this as a rewrite rule to the clause
            val posInClause = findLitInClause(transfLit,child.cl)
            val patternVar = lpOlUntypedVar(lpOlConstantTerm("x"))
            val patternTerm = if (origLit.polarity) patternVar else lpOlUnaryConnectiveTerm(lpNot,patternVar)
            val rewritePattern = generateClausePatternTerm(posInClause,child.cl.lits.length,None,patternVar,patternTerm)
            val rewriteStep = lpRewrite(rewritePattern,lpConstantTerm(polaritySwitchName))
            allRewriteSteps = allRewriteSteps :+ rewriteStep
          case _ => // nothing happens in this case
        }
      }else if (!origLit.polarity)
        origLit.left match {
        case Not(l) =>
          // in this case we just transform the literal of form a to (¬ ¬ a)
          val encLeft = term2LP(l, bVarMap, sig)._1
          val transfLit = Literal.apply(l, true)

          // prove the equality between the lit before and after transformation
          val equalityToProve = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, encLeft, lpOlUnaryConnectiveTerm(lpNot,lpOlUnaryConnectiveTerm(lpNot,encLeft)))
          val polaritySwitchStep = lpRefine(polaritySwitchNonEqLit.instanciate(encLeft))
          val polaritySwitchName = s"PolaritySwitch$polaritySwitchCount"
          polaritySwitchCount = polaritySwitchCount + 1
          val havepolaritySwitchStep = lpHave(polaritySwitchName, equalityToProve.prf, lpProofScript(Seq(polaritySwitchStep)))
          allSteps = allSteps :+ havepolaritySwitchStep
          usedSymbols = usedSymbols + polaritySwitchNonEqLit

          // apply this as a rewrite rule to the clause
          val posInClause = findLitInClause(transfLit, child.cl)
          val rewritePattern = generateClausePatternTerm(posInClause, child.cl.lits.length, None)
          val rewriteStep = lpRewrite(rewritePattern, lpConstantTerm(polaritySwitchName))
          allRewriteSteps = allRewriteSteps :+ rewriteStep

        case _ => // nothing happens in this case
      }
    }
    allSteps = allSteps ++ allRewriteSteps


    // last step: apply the variables we abstracted over to the parent clause and refine with it

    // assuming the variables are not renamed, we can just apply the impbound vars that were already present in the parent
    allSteps = allSteps :+ lpRefine(lpFunctionApp(parentNameLpEnc, freeVarsChild))

    (lpProofScript(allSteps), usedSymbols)
    }

  def encFuncExtPosLit(l0: Literal, l1: Literal, appliedVars: Seq[lpUntypedVar], bVarMap: Map[Int, String], sig: Signature, parameters: (Int, Int, Int, Int)): (Boolean, lpTerm, (Int, Int, Int, Int)) = {
    // encode the proofs for the FunExt rules of the literals
    // if something was changed I return (True,proof), otherwise (False,"")
    //throw new Exception("CHANGE encFuncExtPosLit")

    // [S T : Set] f g a b ... : Prf(eq [↑ (T ⤳ T ⤳ ... ⤳ S)] f g) →  Prf(eq [↑ S] (f a b ...) (g a b ...))

    if (l0.equational & l1.equational){

      if (appliedVars.nonEmpty){

        var xCount = parameters._3
        val x1 = nameX(xCount)
        xCount = xCount + 1
        val x2 = nameX(xCount)
        xCount = xCount + 1
        var hCount = parameters._1
        val h1 = nameHypothesis(hCount)
        hCount = hCount + 1

        val funcType0 = type2LP(l0.left.ty, sig)._1
        val funcType1 = type2LP(l1.left.ty, sig)._1
        val encRight = term2LP(l0.right, bVarMap, sig)._1
        val encLeft = term2LP(l0.left, bVarMap, sig)._1

         /*
        val funcType0 = "(ι ⤳ o)"
        val funcType1 = "o"
        val encRight = "f2"
        val encLeft = "g2"
        val allAppliedVars = appliedVars.mkString(" ")

          */

        // todo: for polymorphic types I will need to make the instantiation of eq with scheme instead of set possible
        //val lambdaTerm_str = s"($LPlambda (h1 : $Prf($equ [$uparrow ($funcType0)] $encLeft $encRight)) ($x2: $Els ($uparrow ($funcType1 $HOLarrow $oType))), h1 ($LPlambda $x1, $x2 ($x1 $allAppliedVars)))"
        val lambdaTerm = lpLambdaTerm(Seq(lpTypedVar(h1,lpOlTypedBinaryConnectiveTerm(lpEq,funcType0,encLeft,encRight).prf),lpTypedVar(x1,lpOlFunctionType(Seq(funcType1,lpOtype)).lift2Meta)),lpFunctionApp(h1,Seq(lpLambdaTerm(Seq(lpUntypedVar(x2)),lpFunctionApp(x1,Seq(lpFunctionApp(x2,appliedVars)))))))

        (true, lambdaTerm, (hCount,parameters._2,xCount, parameters._4))
      }else throw new Exception(s"trying to apply FunExt LP encoding but no variables to apply were supplied")

    }else throw new Exception(s"trying to apply FunExt LP encoding but either the parent ${l0.pretty} or the child ${l1.pretty} is not equational")

  }


  def encFuncExtPosClause(child: ClauseProxy, parent: ClauseProxy, editedLiterals: Seq[(Literal,Literal)], parentNameLpEnc: lpConstantTerm, sig: Signature, parameters0: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int)) = {

    // todo: in some cases the order of the literals is changed by Leo ...
    if (editedLiterals.length > 0){

      val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

      var parameters = parameters0

      // extract the information about the names of the freshly applied variables so they can be universally quantified over
      var allFreshVarsClause: Set[lpTypedVar] = Set.empty
      // first we add the variables of the clause itself
      // track the rule applications in order to apply the clauseRuleApplication
      var transformations: Seq[lpTerm] = Seq.empty
      val editedLiteralsMap = editedLiterals.toMap
      parent.cl.lits foreach {origLit =>
        val edLit = editedLiteralsMap.getOrElse(origLit,origLit)
        if (edLit != origLit){
          // if the literal has been edited, track the newly applied variables and proof the application of funExt
          val freshVars = edLit.left.fv.diff(origLit.left.fv)
          var appliedVars: Seq[lpUntypedVar] = Seq.empty
          freshVars foreach { freshVar =>
            appliedVars = appliedVars :+ lpUntypedVar(lpConstantTerm(bVarMap(freshVar._1)))
            allFreshVarsClause = allFreshVarsClause + lpTypedVar(lpConstantTerm(bVarMap(freshVar._1)),type2LP(freshVar._2, sig)._1.lift2Meta)
          }
          if (!origLit.polarity) throw new Exception(s"functional extensionality of negative literals not encoded yet")
          else{
            // encode the positive funExt
            val (wasApplied, funExtProofTerm,parametersNew) = encFuncExtPosLit(origLit,edLit,appliedVars,bVarMap,sig,parameters)
            parameters = parametersNew
            //print(s"proofTerm for lit:\n${funExtProofTerm.pretty}\n")
            transformations = transformations ++ Seq(funExtProofTerm)
          }
        }else{
          // for the literals that were not changed, we simply add lpOlNothing to the transformations
          transformations = transformations :+ lpOlNothing
        }
      }

      // we also need to quantify over the variables that the clause implicitly quantified over and apply them to the previous stps in their application to the rule
      //var clauseQuantification: StringBuffer = new StringBuffer()
      var clauseQuantification: Set[lpTypedVar] = Set.empty
      //var applySymbolsToParent: Seq[String] = Seq.empty
      var applySymbolsToParent: Seq[lpUntypedVar] = Seq.empty
      parent.cl.implicitlyBound foreach{ var0 =>
        //clauseQuantification.append(s"(${bVarMap(name_type._1)}: $Els($uparrow ${type2LP(name_type._2, sig)._1}))")
        clauseQuantification = clauseQuantification + lpTypedVar(lpConstantTerm(bVarMap(var0._1)),type2LP(var0._2, sig)._1)
        //applySymbolsToParent = applySymbolsToParent ++ Seq(bVarMap(name_type._1))
        applySymbolsToParent = applySymbolsToParent :+ lpUntypedVar(lpConstantTerm(bVarMap(var0._1)))
      }

      if (transformations.length > 1) {
        // this is not implemented but idealy just passing transformations to clauseRulApp (or whatever the function is called) should do the trick
        throw new Exception(s"encFuncExtPosClause not implemented for clauses longer than one literal")
      }
      else{
        // quantify over all variables in  allFreshVarsClause and clauseQuantification
        val lambdaTerm = lpLambdaTerm((allFreshVarsClause ++ clauseQuantification).toSeq,lpFunctionApp(transformations.head,Seq(lpFunctionApp(parentNameLpEnc,applySymbolsToParent))))
        //(s"${universalQuantification.toString} ${clauseQuantification.toString}, ${transformations.head} ($parentNameLpEnc ${applySymbolsToParent.mkString(" ")})",parameters)
        (lambdaTerm,parameters)
      }

    } else throw new Exception(s"encFuncExtPosClause was called but no edited literals were provided")

    /*
    print(s"parent: ${child.annotation.parents.head.pretty}\n")
    child.furtherInfo.FuncExtInfo foreach { pair =>
      print(s"before: \n${pair._1.pretty}\nvars: ${vars(pair._2)}\n")
      //print(s"before as lp: \n${term2LP(pair._1.left,Map.empty,sig)}${term2LP(pair._1.right,Map.empty,sig)}\nvars: ${vars(pair._2)}\n")
      print(s"after: \n${pair._2.pretty}\nvars: ${vars(pair._2)}\n")
      // extract those variables that are in the child but not in the parent along with their types:
      val difFV = (pair._2.left.fv.diff(pair._1.left.fv), pair._2.right.fv.diff(pair._1.right.fv))
      print(s"variables left side: ${((intToName(difFV._1.head._1 - 1)))}: ${type2LP(difFV._1.head._2, sig)._1}\n")
      print(s"name of vars: ${(sig(2).name)}\n")
    }
    print(s"child: ${child.pretty}\n")
    print(s"\n")

     */
  }

  def encFuncExtPosClause_script(child: ClauseProxy, parent: ClauseProxy, editedLiterals: Seq[(Literal, Literal)], parentNameLpEnc: lpConstantTerm, sig: Signature, parameters0: (Int, Int, Int, Int)): (lpProofScript, Set[lpStatement]) = {

    // todo: in some cases the order of the literals is changed by Leo ...

    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    var usedSymbols: Set[lpStatement] = Set.empty

    if (editedLiterals.length > 0) {

      val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

      var allRewriteSteps: Seq[lpProofScriptStep] = Seq.empty


      // first: abstract over the variables free in the child
      val freeVarsChild = child.cl.implicitlyBound.map(var0 => lpUntypedVar(lpConstantTerm(bVarMap(var0._1))))
      if (freeVarsChild.nonEmpty) allSteps = allSteps :+ lpAssume(freeVarsChild)

      // second: for each literal that funct ext was applied to, proof after=before to use as a rewrite rule later on
      var editLitCount = 0
      val editedLiteralsMap = editedLiterals.toMap
      parent.cl.lits foreach { origLit =>
        val edLit = editedLiteralsMap.getOrElse(origLit, origLit)
        if (edLit != origLit) {
          val nameEqFactStep = s"EqFact$editLitCount"
          editLitCount = editLitCount + 1
          val encOrigLitLhs = term2LP(origLit.left, bVarMap, sig)._1
          val encOrigLitRhs = term2LP(origLit.right, bVarMap, sig)._1
          val encOrigLit = term2LP(asTerm(origLit), bVarMap, sig)._1
          val encEditLit = term2LP(asTerm(edLit), bVarMap, sig)._1
          val equalityToProve = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, encEditLit, encOrigLit)
          // the proof
          // if the literal has been edited, track the newly applied variables and proof the application of funExt
          val freshVars = edLit.fv.diff(origLit.fv)
          var appliedVars: Seq[lpOlUntypedVar] = Seq.empty
          freshVars foreach { freshVar =>
            appliedVars = appliedVars :+ lpOlUntypedVar(lpOlConstantTerm(bVarMap(freshVar._1)))
            //allFreshVarsClause = allFreshVarsClause + lpTypedVar(lpConstantTerm(bVarMap(freshVar._1)), type2LP(freshVar._2, sig)._1.lift2Meta)
          }
          val refinewithFunExt = {
            if (!origLit.polarity) throw new Exception(s"functional extensionality of negative literals not encoded yet")
            else {
              usedSymbols = usedSymbols + funextPosEq_rev(appliedVars.length)
              lpRefine(funextPosEq_rev(appliedVars.length).instanciate(None, encOrigLitLhs, encOrigLitRhs, appliedVars))
            }
          }
          allSteps = allSteps :+ lpHave(nameEqFactStep, equalityToProve.prf, lpProofScript(Seq(refinewithFunExt)))

          // also add the proper rewrite pattern and construct the clause
          val posInClause = findLitInClause(edLit, child.cl)
          val rewritePattern = generateClausePatternTerm(posInClause, child.cl.lits.length)
          val rewriteStep = lpRewrite(rewritePattern, lpConstantTerm(nameEqFactStep))
          allRewriteSteps = allRewriteSteps :+ rewriteStep
        }
      }
      allSteps = allSteps ++ allRewriteSteps

      // now the goal should be as the before clause!
      val impBoundParent = parent.cl.implicitlyBound.map(var0 => lpUntypedVar(lpConstantTerm(bVarMap(var0._1))))
      // assuming the variables are not renamed, we can just apply the impbound vars that were already present in the parent
      allSteps = allSteps :+ lpRefine(lpFunctionApp(parentNameLpEnc, impBoundParent))

    }
    (lpProofScript(allSteps),usedSymbols)
  }


  def encBoolExtLit(l0: Literal, version: String, bVarMap: Map[Int, String], sig: Signature, parameters: (Int, Int, Int, Int)): (Boolean, lpTerm, (Int, Int, Int, Int)) = {
    // encode the proofs for the FunExt rules of the literals
    // if something was changed I return (True,proof), otherwise (False,"")
    //throw new Exception("CHANGE encBoolExtLit")

    // there are three different version a literal can be transformed with boolExt, these versions correspond to the modes:
    // posL: positve literals with negation on the left side, proof term of type Prf(eq [↑ o] a b) → Prf(a ∨ (¬ b))
    // posR positve literals with negation on the right side, proof term of type Prf(eq [↑ o] a b) → Prf((¬ a) ∨ b)
    // negL ...
    // negR ...

    var xCount = parameters._3
    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1

    var hCount = parameters._1
    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h4 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h5 = nameHypothesis(hCount)
    hCount = hCount + 1

    var bCount = parameters._2
    val b1 = nameBottom(bCount)
    bCount = bCount + 1

    val encLeft = term2LP(l0.left, bVarMap, sig)._1
    val encRight = term2LP(l0.right, bVarMap, sig)._1


    //todo: return correct parameters
    // todo: encode lambda terms properly
    if (version == "posL") {
      //val lambdaTerm_str = s"λ (h1 : Prf (eq [↑ o] $encLeft $encRight)),                                                                  em $encRight ($encLeft ∨ ¬ $encRight)                                                                      (λ h2 b1 h3 _,                                                                             h3 (h1 (λ $x1,                                                        eq [↑ o] $x1 $encLeft)                                          (λ $x2 h5, h5)                                            (λ $x1, $x1) h2)) (λ h2 b1 _ h4, h4 h2)"
      val lambdaTerm = lpLambdaTerm(Seq(lpTypedVar(h1,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,encLeft, encRight).prf)),lpFunctionApp(lpEm.name,Seq(encRight,lpOlUntypedBinaryConnectiveTerm(lpOr,encLeft,lpOlUnaryConnectiveTerm(lpNot,encRight)),lpLambdaTerm(Seq(lpUntypedVar(h2),lpUntypedVar(b1),lpUntypedVar(h3),lpUntypedVar(lpWildcard)),lpFunctionApp(h3,Seq(lpFunctionApp(h1,Seq(lpLambdaTerm(Seq(lpUntypedVar(x1)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x1,encLeft)),lpLambdaTerm(Seq(lpUntypedVar(x2),lpUntypedVar(h5)),h5),lpLambdaTerm(Seq(lpUntypedVar(x1)),x1),h2))))),lpLambdaTerm(Seq(lpUntypedVar(h2),lpUntypedVar(b1),lpUntypedVar(lpWildcard),lpUntypedVar(h4)),lpFunctionApp(h4,Seq(h2))))))
      //print(s"\nencoding left side: \n${lambdaTerm.pretty}\n")
      (true, lambdaTerm, (hCount,bCount,xCount, parameters._4))
    } else if (version == "posR") {
      val lambdaTerm_Str = s"λ (h1 : Prf (eq [↑ o] $encLeft $encRight)),                                                                   em $encLeft (¬ $encLeft ∨ $encRight)                                                                      (λ h2 b1 _ h4,                                                                               h4 (h1 (λ $x1,                                                      $x1) h2))                           (λ h2 b1 h3 _, h3 h2)"
      ////val lambdaTerm = s"λ (h1 : Prf (eq [↑ o] $encLeft $encRight)), em $encRight ($encLeft ∨ ¬ $encRight) (λ h2 b1 h3 _, h3 (h1 (λ $x1, eq [↑ o] $x1 $encLeft) (λ $x2 h5, h5) (λ $x1, $x1) h2)) (λ h2 b1 _ h4, h4 h2)"
      val lambdaTerm = lpLambdaTerm(Seq(lpTypedVar(h1,lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, encLeft, encRight).prf)), lpFunctionApp(lpEm.name, Seq(encLeft, lpOlUntypedBinaryConnectiveTerm(lpOr, lpOlUnaryConnectiveTerm(lpNot, encLeft), encRight), lpLambdaTerm(Seq(lpUntypedVar(h2), lpUntypedVar(b1), lpUntypedVar(lpWildcard), lpUntypedVar(h4)), lpFunctionApp(h4, Seq(lpFunctionApp(h1, Seq(lpLambdaTerm(Seq(lpUntypedVar(x1)), x1), h2))))), lpLambdaTerm(Seq(lpUntypedVar(h2), lpUntypedVar(b1), lpUntypedVar(h3), lpUntypedVar(lpWildcard)), lpFunctionApp(h3, Seq(h2))))))
      //print(s"\nencoding right side: \n${lambdaTerm.pretty}\n")
      (true, lambdaTerm, parameters)
    } else {
      throw new Exception(s"BoolExt lit version not encoded yet")
    }

  }



  def generateClorRule(positions: Seq[Boolean], proofNames: String)={
    // generate a proof script to only transform single literals in clauses and still proof the entire clause
    // the positions vector then encodes how many literals the remaining clause has and for positions a clause application has to be prooven

    // first we generate a list of variables and stuff
    // in this step we also construct the transformtion to be prooven and start assuming variables and hypothesis
    var clause0: Seq[lpOlUntypedVar] = Seq.empty
    var clause1: Seq[lpOlUntypedVar] = Seq.empty

    // To construct the type of the rule we are proving here, we need to require the proofs for the transforamtions of the individual literals
    var trnsformationProofs: Seq[lpMlType] = Seq.empty

    // we track the variable and hypothesis names we need to assume in the proof script
    var varsToBeAssumed: Seq[lpOlUntypedVar] = Seq.empty
    var hypothesisToBeAssumed: Seq[lpUntypedVar] = Seq.empty
    var quantifiedVars: Seq[lpTypedVar] = Seq.empty

    // map each variable that is transformed to the hypothesis representing this transfomration
    val transHypName: mutable.HashMap[lpOlUntypedVar,lpUntypedVar] = mutable.HashMap.empty

    var varCount = 0
    var hypCount = 0
    positions foreach {pos =>
      val variableOrig = lpOlUntypedVar(lpConstantTerm(s"x$varCount"))
      clause0 = clause0 :+ variableOrig
      varsToBeAssumed = varsToBeAssumed :+ variableOrig
      quantifiedVars = quantifiedVars :+ lpTypedVar(lpConstantTerm(s"x$varCount"),lpOtype)
      if (pos){
        // we add the changed variable to the new clause
        varCount = varCount + 1
        val variableNew = lpOlUntypedVar(lpConstantTerm(s"x$varCount"))
        varsToBeAssumed = varsToBeAssumed :+ variableNew
        quantifiedVars = quantifiedVars :+ lpTypedVar(lpConstantTerm(s"x$varCount"),lpOtype)
        clause1 = clause1 :+ variableNew
        // since we want to transform this literal, we need to provide a proof that we can indeed do so. We assume it in the script as a hypothesis.
        trnsformationProofs = trnsformationProofs :+ lpMlFunctionType(Seq(variableOrig.prf,variableNew.prf))
        val newHypo = lpUntypedVar(lpConstantTerm(s"h$hypCount"))
        hypCount = hypCount + 1
        hypothesisToBeAssumed = hypothesisToBeAssumed :+ newHypo
        // and we add it to the map
        transHypName += (variableOrig -> newHypo)
      }else{
        clause1 = clause1 :+ lpOlUntypedVar(lpConstantTerm(s"x$varCount"))
      }
      varCount = varCount + 1
    }

    // whith this we can construct the type of the rule we proof and can begin the proof script
    val clause0enc = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,clause0)
    val clause1enc = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,clause1)

    // the las hypothesis we assume is clause0
    val newHypo = lpUntypedVar(lpConstantTerm(s"h$hypCount"))
    hypCount = hypCount + 1
    hypothesisToBeAssumed = hypothesisToBeAssumed :+ newHypo

    // we add these two as prf terms to the type we are trying to proof
    val typeOfRule = lpMlDependType(quantifiedVars,lpMlFunctionType(trnsformationProofs ++ Seq(clause0enc.prf, clause1enc.prf)))

    def nestedLorIlApp(lhs:Seq[lpOlTerm], rhs:Seq[lpOlTerm], prfRhs: lpTerm): lpFunctionApp ={
      // iterativeley construct the proofs for disjunctions of literals based on a proof for the rhs. This is necessary to avoid errors in cases where (a \lor b) \lor (c \lor d ( ...
      // would otherwise been proven
      if (lhs.length == 1) lpUseful.orIr().instanciate(lhs.head,lpOlUntypedBinaryConnectiveTerm_multi(lpOr,rhs),Some(prfRhs))
      else{
        val currentVar = lhs.last
        val newLhs = lhs.init
        val newRhs = Seq(currentVar) ++ rhs
        val newProof = lpUseful.orIr().instanciate(currentVar,lpOlUntypedBinaryConnectiveTerm_multi(lpOr,rhs),Some(prfRhs))
        nestedLorIlApp(newLhs,newRhs,newProof)
      }
    }

    def gen0(positionsGen: Seq[Boolean], clause0Gen: Seq[lpOlUntypedVar], clause1Unprocessed0: Seq[lpOlUntypedVar], clause1Processed0: Seq[lpOlUntypedVar], hCountGen0: Int, currentAssumtion: lpUntypedVar): (lpProofScriptStep, Set[lpStatement]) = {

      var usedSymbols: Set[lpStatement] = Set.empty
      var hCountGen = hCountGen0

      val clause1Unprocessed = clause1Unprocessed0.tail
      val clause1Processed = clause1Processed0 :+ clause1Unprocessed0.head

      if (positionsGen.length == 1) {
        val refLhs = if (positionsGen.head) lpFunctionApp(transHypName.getOrElse(clause0Gen.head, throw new Exception("key not found generateClorRule")), Seq(currentAssumtion)) else currentAssumtion
        // in this case the current hypothesis should be the proof for we are looking for //todo ?
        //(lpProofScript(Seq(lpRefine(lpFunctionApp(refLhs, Seq())))), usedSymbols)
        val proofRhs = lpFunctionApp(refLhs, Seq())
        val completeProof = nestedLorIlApp(clause1Processed0,clause1Unprocessed0,proofRhs)
        ((lpProofScript(Seq(lpRefine(completeProof))),Set()))

      } else {
        // the clause is longer than 0 => we need to apply ∨E
        val orElInstantiation = lpUseful.orE().instanciate(clause0Gen.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause0Gen.tail), lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Processed ++ clause1Unprocessed), Some(lpOlWildcard), Some(lpOlWildcard), Some(currentAssumtion))
        usedSymbols = usedSymbols + lpUseful.orE()
        // then we need two proofs: that the lhs of clause0 implies clause1 and the same for the rhs.
        val (lhs, rhs): (lpProofScript, lpProofScript) = {
          // the lhs does not have to be transformed
          val newHyp = lpUntypedVar(lpConstantTerm(s"h$hCountGen"))
          val newAssumeStep = lpAssume(Seq(newHyp))
          hCountGen = hCountGen + 1
          // depending on weather or not the lhs was transformed, we need either a hypothesis represnting a proof of itself or one representing the proof of its transformatons
          val refLhs = if (positionsGen.head) lpFunctionApp(transHypName.getOrElse(clause0Gen.head, throw new Exception("key not found generateClorRule")), Seq(newHyp)) else newHyp
          val lhsRefineStep = {
            if (clause1Processed.length == 1) {
              usedSymbols = usedSymbols + lpUseful.orIl()
              lpRefine(lpUseful.orIl().instanciate(clause1Processed.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed), Some(refLhs)))
            }
            else {
              lpRefine(lpUseful.orIr().instanciate(lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Processed0), lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed0), Some(lpUseful.orIl().instanciate(clause1Unprocessed0.head,(lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed0.tail)),Some(refLhs)))))
              val proofrhs = lpUseful.orIl().instanciate(clause1Unprocessed0.head,(lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed0.tail)),Some(refLhs))
              val completeProof = nestedLorIlApp(clause1Processed0,clause1Unprocessed0,proofrhs)
              usedSymbols = usedSymbols + lpUseful.orIl() + lpUseful.orIr
              lpRefine(completeProof)
            }
          }
          usedSymbols = usedSymbols + lpUseful.orIl()
          if (!positionsGen.tail.forall(_ == false)) {
            // some of the other literals yet have to be transformed
            val (rhsProof, newUsedSymbols) = gen0(positionsGen.tail, clause0Gen.tail, clause1Unprocessed, clause1Processed, hCountGen, newHyp)
            usedSymbols = usedSymbols ++ newUsedSymbols
            (lpProofScript(Seq(newAssumeStep, lhsRefineStep)), lpProofScript(Seq(newAssumeStep, rhsProof)))
          } else {
            // no transformations left to proof! So we can simply assume both sides and refine with the application of the assumption to the right lor-introduction
            //val rhsRefineStep = lpRefine(lpUseful.orIr().instanciate(lpOlUntypedBinaryConnectiveTerm_multi(lpOr,clause1Processed), lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed), Some(newHyp)))
            val completeProof = nestedLorIlApp(clause1Processed,clause1Unprocessed,newHyp)
            usedSymbols = usedSymbols + lpUseful.orIr() + lpUseful.orIr()
            //(lpProofScript(Seq(newAssumeStep, lhsRefineStep)), lpProofScript(Seq(newAssumeStep, rhsRefineStep)))
            (lpProofScript(Seq(newAssumeStep, lhsRefineStep)), lpProofScript(Seq(newAssumeStep,lpRefine(completeProof))))
          }
        }
        val proofScript = lpProofScript(Seq(lpRefine(orElInstantiation, Seq(lhs, rhs))))
        (proofScript, usedSymbols)
      }
    }

    // now we can construct the overall proof!
    val assumeStep = lpAssume(varsToBeAssumed ++ hypothesisToBeAssumed)
    val (proof, usedSymbols) = gen0(positions,clause0,clause1,Seq.empty,hypCount,hypothesisToBeAssumed.last)
    val haveStep = lpHave(proofNames,typeOfRule,lpProofScript(Seq(assumeStep,proof)))

    (haveStep, usedSymbols)
  }

  def encBoolExtClause(child: ClauseProxy, parent: ClauseProxy ,parentNameLpEnc: lpConstantTerm, sig: Signature, parameters0: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int),Set[lpStatement]) = {

    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

    var transformations: Seq[lpTerm] = Seq.empty

    var parameters = parameters0


    // we also need to quantify over the variables that the clause implicitly quantified over and apply them to the previous stps in their application to the rule
    //val clauseQuantification: StringBuffer = new StringBuffer()
    var clauseQuantification: Set[lpTypedVar] = Set.empty
    //var applySymbolsToParent: Seq[String] = Seq.empty
    var applySymbolsToParent: Seq[lpUntypedVar] = Seq.empty
    parent.cl.implicitlyBound foreach { var0 =>
      //clauseQuantification.append(s"(${bVarMap(var0._1)}: $Els($uparrow ${type2LP(var0._2, sig)._1}))")
      clauseQuantification = clauseQuantification + lpTypedVar(lpConstantTerm(bVarMap(var0._1)),type2LP(var0._2, sig)._1.lift2Meta)
      //applySymbolsToParent = applySymbolsToParent ++ Seq(bVarMap(name_type._1))
      applySymbolsToParent = applySymbolsToParent :+ lpUntypedVar(lpConstantTerm(bVarMap(var0._1)))
    }


    // seq of literals to which a corresponding clause has to be found in parents
    // todo: instead track which children belong to which parents
    val toDo: Seq[Literal] = child.cl.lits
    parent.cl.lits. foreach{ lit =>

      if(BoolExt.canApply(lit)){
        // compute the possible literals that oculd result from an application of BoolExt to this literal
        val possibleRes = BoolExt.apply(lit)
        // check if they possible new literals are in the new clauses of the child clause
        if (toDo.containsSlice(possibleRes._1) | toDo.containsSlice(possibleRes._2)){
          //todo: for now i simply map these together but to be safe i should check weather i can account for all the literals in the result while applying transformations
          // that only need each literal of the parent once
          if (toDo.containsSlice(possibleRes._1)){
            if (lit.polarity){
              // Prf(eq [↑ o] a b) → Prf((¬ a) ∨  b)
              val encoding = encBoolExtLit(lit, "posR", bVarMap, sig, parameters)._2
              transformations = transformations :+ encoding
            }else{
              throw new Exception(s"mode of BoolExt enc not yet implemented 1")
            }
          }
          if (toDo.containsSlice(possibleRes._2)){
            if (lit.polarity) {
              // Prf(eq [↑ o] a b) → Prf(a ∨ (¬ b))
              val encoding = encBoolExtLit(lit,"posL",bVarMap,sig,parameters)._2
              transformations = transformations :+ encoding
            } else {
              throw new Exception(s"mode of BoolExt enc not yet implemented 2")
            }
          }

        }else throw new Exception(s"no bool Ext applied to value that it should have been applied to: ${term2LP(asTerm(lit),bVarMap,sig)._1}")
      } else{
        transformations = transformations :+ lpOlNothing
      }
      // first test if the literal was edited or is also in child
    }

    if (transformations.length > 1) {
      // this is not implemented but idealy just passing transformations to clauseRulApp (or whatever the function is called) should do the trick
      throw new Exception(s"encBoolExtClause not implemented for clauses longer than one literal") //todo : i think i do not even have to diff. cases once this is implemented, instead this can probably also handle the lower case
    }
    else {
      val lambdaTerm = lpLambdaTerm(clauseQuantification.toSeq,lpFunctionApp(transformations.head,Seq(lpFunctionApp(parentNameLpEnc,applySymbolsToParent))))
      (s"($LPlambda ${clauseQuantification.toString}, (${transformations.head}) ($parentNameLpEnc ${applySymbolsToParent.mkString(" ")}))", parameters, Set("em"))//todo: add em axiom
      (lambdaTerm, parameters, Set(lpEm))
    }

    // todo: in some cases the order of the literals is changed by Leo ...

  }

  def encBoolExtClause_proofScript(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, addInfo: Set[(Literal,Seq[Literal])], sig: Signature): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {

    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

    // we also need to quantify over the variables that the clause implicitly quantified over and apply them to the previous stps in their application to the rule
    var clauseQuantification: Set[lpTypedVar] = Set.empty
    var applySymbolsToParent: Seq[lpUntypedVar] = Seq.empty
    parent.cl.implicitlyBound foreach { var0 =>
      clauseQuantification = clauseQuantification + lpTypedVar(lpConstantTerm(bVarMap(var0._1)), type2LP(var0._2, sig)._1.lift2Meta)
      applySymbolsToParent = applySymbolsToParent :+ lpUntypedVar(lpConstantTerm(bVarMap(var0._1)))
    }

    // find out what literals of the parent were used to get to what literals in the child
    print(s"\nencoding boolext\n")
    addInfo foreach{ info =>
      print(s"addInfo: ${term2LP(asTerm(info._1),bVarMap,sig)._1.pretty} -> ${term2LP(asTerm((info._2(0))),bVarMap,sig)._1.pretty} and ${term2LP(asTerm((info._2(1))),bVarMap,sig)._1.pretty}\n")

    }

    /*
    // seq of literals to which a corresponding clause has to be found in parents
    // todo: instead track which children belong to which parents
    val toDo: Seq[Literal] = child.cl.lits
    parent.cl.lits.foreach { lit =>

      if (BoolExt.canApply(lit)) {
        // compute the possible literals that oculd result from an application of BoolExt to this literal
        val possibleRes = BoolExt.apply(lit)
        // check if they possible new literals are in the new clauses of the child clause
        if (toDo.containsSlice(possibleRes._1) | toDo.containsSlice(possibleRes._2)) {
          //todo: for now i simply map these together but to be safe i should check weather i can account for all the literals in the result while applying transformations
          // that only need each literal of the parent once
          if (toDo.containsSlice(possibleRes._1)) {
            if (lit.polarity) {
              // Prf(eq [↑ o] a b) → Prf((¬ a) ∨  b)
              val encoding = encBoolExtLit(lit, "posR", bVarMap, sig, parameters)._2
              transformations = transformations :+ encoding
            } else {
              throw new Exception(s"mode of BoolExt enc not yet implemented 1")
            }
          }
          if (toDo.containsSlice(possibleRes._2)) {
            if (lit.polarity) {
              // Prf(eq [↑ o] a b) → Prf(a ∨ (¬ b))
              val encoding = encBoolExtLit(lit, "posL", bVarMap, sig, parameters)._2
              transformations = transformations :+ encoding
            } else {
              throw new Exception(s"mode of BoolExt enc not yet implemented 2")
            }
          }

        } else throw new Exception(s"no bool Ext applied to value that it should have been applied to: ${term2LP(asTerm(lit), bVarMap, sig)._1}")
      } else {
        transformations = transformations :+ lpOlNothing
      }
      // first test if the literal was edited or is also in child
    }

    if (transformations.length > 1) {
      // this is not implemented but idealy just passing transformations to clauseRulApp (or whatever the function is called) should do the trick
      throw new Exception(s"encBoolExtClause not implemented for clauses longer than one literal") //todo : i think i do not even have to diff. cases once this is implemented, instead this can probably also handle the lower case
    }
    else {
      val lambdaTerm = lpLambdaTerm(clauseQuantification.toSeq, lpFunctionApp(transformations.head, Seq(lpFunctionApp(parentNameLpEnc, applySymbolsToParent))))
      (s"($LPlambda ${clauseQuantification.toString}, (${transformations.head}) ($parentNameLpEnc ${applySymbolsToParent.mkString(" ")}))", parameters, Set("em")) //todo: add em axiom
      (lambdaTerm, parameters, Set(lpEm))
    }

    // todo: in some cases the order of the literals is changed by Leo ...

     */
    (lpOlNothing,(0,0,0,0),Set.empty)
  }


  def encEqFactNegInst(T:lpType, otherLit_l:lpOlTerm, otherLit_r:lpOlTerm, maxLit_l: lpOlTerm, maxLit_r: lpOlTerm, parameters: (Int, Int, Int, Int)):(lpTerm,(Int, Int, Int, Int),Set[lpStatement])={
    // for now I just use the symbol instead of the lambda term:
    //todo: Instanciate actual lambda Term
    //todo: return parameters and used symbols
    val eqFactNegDef = s"Π [T: Scheme], Π x: Els T, Π y: Els T, Π z: Els T, Π v: Els T, Prf (¬ (eq x y) ∨ ¬ (eq z v)) → Prf (¬ (eq x y) ∨ (¬ (eq x z) ∨ ¬ (eq y v)))"
    val eqFactNegName = lpConstantTerm(s"eqFactNeg [$uparrow ${T.pretty}]")
    val lambdaTerm_str = s"($eqFactNegName [$uparrow $T] $otherLit_l $otherLit_r $maxLit_l $maxLit_r)"
    val lambdaTerm = lpFunctionApp(eqFactNegName,Seq(otherLit_l,otherLit_r,maxLit_l,maxLit_r))
    ((lambdaTerm, parameters,Set.empty))
  }


  def encEqFactPosInst(T: lpType, otherLit_l: lpOlTerm, otherLit_r: lpOlTerm, maxLit_l: lpOlTerm, maxLit_r: lpOlTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // for now I just use the symbol instead of the lambda term:
    //throw new Exception("CHANGE encEqFactPosInst")
    //todo: Instanciate actual lambda Term
    //todo: return parameters and used symbols
    val eqFactNegDef = s""
    val eqFactName = lpConstantTerm(s"eqFactPos [$uparrow ${T.pretty}]") //todo: make sure this is alwyas lifted to scheme when you change the encoding
    val lambdaTerm_str = s"($eqFactName [$uparrow $T] $otherLit_l $otherLit_r $maxLit_l $maxLit_r)"
    val lambdaTerm = lpFunctionApp(eqFactName,Seq(otherLit_l,otherLit_r,maxLit_l,maxLit_r))
    ((lambdaTerm, parameters, Set.empty))
  }

  def makeLiteralEquational(lit: Literal,desiredPolarity: Boolean,bVarMap: Map[Int, String], sig: Signature,parameters0: (Int, Int, Int, Int)):(lpOlTerm,lpOlTerm,lpTerm,lpTerm,lpOlTerm,lpOlTerm, (Int, Int, Int, Int), Set[lpStatement])={
    // this is the old version that produces proof terms rather than proof scripts

    // takes a literal and an desired polarity and returns:
    // - the encoded version of the literal itself and the equational version
    // - the lambda term of type Prf lit -> Prf eqLit as well as Prf eqLit -> Prf lit
    // - the left and right side of the new equational literal

    val encodedLit = term2LP(asTerm(lit), bVarMap, sig)._1

    var parameters = parameters0
    var usedSymbols: Set[lpStatement] = Set.empty


    if (desiredPolarity== true){
      if (lit.polarity== true){
        val (prfForward, parametersNew, usedSymbolsNew) = mkPosPropPosLit(encodedLit, parameters)
        parameters = parametersNew
        usedSymbols = usedSymbolsNew
        // define variables to use for the instanciation of the rule
        //otherLit_l = encodedOtherLit
        val lit_l = encodedLit
        //otherLit_r = HOLtop
        val lit_r = lpOlTop
        //otherLitAsEq = s"($equ [$uparrow o] $encodedOtherLit $HOLtop)"
        val litAsEq = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lit_l,lit_r)
        //transformations_step1 = transformations_step1 :+ (encodedOtherLit, otherLitAsEq, transf)
        // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
        // for this we can already construct the rule using the information derived here
        val (prfBack, parametersNewBack, usedSymbolsNewBack) = mkPosLitPosProp(encodedLit, parameters)
        parameters = parametersNewBack
        usedSymbols = usedSymbolsNewBack
        //transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, transfBack)
        (encodedLit,litAsEq,prfForward,prfBack,lit_l,lit_r,parameters,usedSymbols)
      }else {
        // turn a negative non equational literal into a positive equational one
        asTerm(lit) match {
          case Not(t) =>
            val encodedOtherLitPos = term2LP(t, bVarMap, sig)._1
            val (prfForward, parametersNew, usedSymbolsNew) = mkNegPropPosLit(encodedOtherLitPos, parameters)
            parameters = parametersNew
            usedSymbols = usedSymbolsNew
            // define variables to use for the instanciation of the rule
            //otherLit_l = s"($lnot $encodedOtherLitPos)"
            val lit_l = lpOlUnaryConnectiveTerm(lpNot, encodedOtherLitPos)
            //otherLit_r = HOLtop
            val lit_r = lpOlTop
            //otherLitAsEq = s"($equ [$uparrow o] $otherLit_l $HOLtop)"
            val litAsEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lit_l, lit_r)
            //transformations_step1 = transformations_step1 :+ (encodedOtherLit, otherLitAsEq, transf)
            // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
            // for this we can already construct the rule using the information derived here
            val (prfBack, parametersNewBack, usedSymbolsNewBack) = mkPosLitNegProp(encodedOtherLitPos, parameters)
            parameters = parametersNewBack
            usedSymbols = usedSymbolsNewBack
            //transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, transfBack)
            (encodedLit, litAsEq, prfForward, prfBack, lit_l, lit_r,parameters,usedSymbols)
          case _ => throw new Exception(s"when trying to proof transition of ${encodedLit.pretty} to equational form, max lit with wrong form was found")
        }
      }
    }else{
      if (lit.polarity == true) {
        // turn a positive non equational literal into a negative equational one
        val (prfForward, parametersNew, usedSymbolsNew) = mkPosPropNegLit(encodedLit, parameters)
        parameters = parametersNew
        usedSymbols = usedSymbolsNew
        // define variables to use for the instanciation of the rule
        //otherLit_l = s"($lnot $encodedLit)"
        val lit_l = lpOlUnaryConnectiveTerm(lpNot,encodedLit)
        //otherLit_r = HOLtop
        val lit_r = lpOlTop
        //otherLitAsEq = s"($lnot($equ [$uparrow o] ($lnot $encodedLit) $HOLtop))"
        val litAsEq = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUnaryConnectiveTerm(lpNot,encodedLit),lit_r))
        //transformations_step1 = transformations_step1 :+ (encodedLit, otherLitAsEq, prfForward)
        // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
        // for this we can already construct the rule using the information derived here
        val (prfBack, parametersNewBack, usedSymbolsNewBack) = mkNegLitPosProp(encodedLit, parameters)
        parameters = parametersNewBack
        usedSymbols = usedSymbolsNewBack
        //transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, prfBack)
        (encodedLit,litAsEq,prfForward,prfBack,lit_l,lit_r,parameters,usedSymbols)
      } else {
        asTerm(lit) match {
          case Not(t) =>
            val encodedOtherLitPos = term2LP(t, bVarMap, sig)._1
            val (prfForward, parametersNew, usedSymbolsNew) = mkNegPropNegLit(encodedOtherLitPos, parameters)
            parameters = parametersNew
            usedSymbols = usedSymbolsNew
            // define variables to use for the instanciation of the rule
            //otherLit_l = encodedOtherLitPos
            //otherLit_r = HOLtop
            val lit_l = encodedOtherLitPos
            val lit_r = lpOlTop
            //otherLitAsEq = s"($lnot($equ [$uparrow o] $encodedOtherLitPos $HOLtop))"
            val litAsEq = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lit_l,lit_r))
            //transformations_step1 = transformations_step1 :+ (encodedOtherLit, otherLitAsEq, transf)
            // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
            // for this we can already construct the rule using the information derived here
            val (prfBack, parametersNewBack, usedSymbolsNewBack) = mkNegLitNegProp(encodedOtherLitPos, parameters)
            parameters = parametersNewBack
            usedSymbols = usedSymbolsNewBack
            //transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, transfBack)
            (encodedLit,litAsEq,prfForward,prfBack,lit_l,lit_r,parameters,usedSymbols)
          case _ => throw new Exception(s"when trying to encode EqFact, max lit with wrong form was found")
        }

      }
    }
  }

  def findLitInClause(lit: Literal, parent: Clause): Int = {
    val indicesOfOccurrence: IndexedSeq[Int] = parent.lits.indices.filter(index => parent.lits(index) == lit)
    val positionInClause = if (indicesOfOccurrence.length == 1) indicesOfOccurrence.head
    else if (indicesOfOccurrence.length == 0) throw new Exception(s"literal to transform not found in clause when attempfing to generate lp encoding")
    else throw new Exception(s"literal to transform found more than once when attempfing to generate lp encoding")
    positionInClause
  }

  def generateClausePatternTerm(varPos: Int, clauseLen: Int, eqPos: Option[Int] = None, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpOlConstantTerm("x")),wrapperTerm: lpOlTerm = lpOlUntypedVar(lpOlConstantTerm("x"))): Option[lpRewritePattern] = {
    // given the position of the literal that a rule should be applied to in a clause and weather or not this clause in embedded in an equality to be proven,
    // generate a rewrite pattern

    val clausePattern = if (clauseLen > 1) {
      val args = Seq.fill(clauseLen)(lpOlWildcard).updated(varPos, patternVar)
      lpOlUntypedBinaryConnectiveTerm_multi(lpOr, args)
    } else {
      patternVar
    }

    eqPos match {
      case Some(pos) =>
        val patternEq = {
          if (pos == 0) lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, clausePattern, lpOlWildcard)
          else if (pos == 0) lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlWildcard, clausePattern)
          else throw new Exception(s"position $pos provided to encode position in equality")
        }
        Some(lpRewritePattern(patternEq, patternVar))
      case None =>
        if (clausePattern == patternVar) None
        else Some(lpRewritePattern(clausePattern, patternVar))
    }
  }

  def encEqFactLiterals(otherLit:Literal, maxLit: Literal, uc1Orig: Literal, cv2Orig: Literal,  bVarMap: Map[Int, String], sig: Signature, parameters0: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    //throw new Exception("CHANGE encEqFactLiterals")
    // todo: I think many questions would be solved by just getting the other lit that was returned, do eqfactoring according to it and change polarity of literals accordingly

    // todo: somehow use the original unification constraints to dermine the polarity, the order etc.
    var parameters = parameters0
    var usedSymbols: Set[lpStatement] = Set.empty

    // the values that we will pass on to the instanciation of the actual rule will be defined during this step
    var otherLit_l: lpOlTerm = lpOlNothing
    var otherLit_r: lpOlTerm = lpOlNothing
    var maxLit_l: lpOlTerm = lpOlNothing
    var maxLit_r: lpOlTerm = lpOlNothing

    // several steps are necessary for the encoding:
    // 1. if some of the literals are not equational, we first need to proof the transition to the equational case
    // 2. in this notation we can proof the equal factoring
    // 3. We proof the transition back to the non-equational case

    // todo: also look at cases where the order is different (i.e) the other literal is not the first one

    // we define polariy depending on how we encode the literals. The polarity decides which of the EqFact Rules we apply
    //var polarity0: Option[Boolean] = None

    // 1.: If necessary, we encode the literals as equational ones
    //todo make sure you really did consider all the cases (all combinations of polarity that can lead to factring inclding the flex heads)
    // and make sure that it is not possible that i flip the polarity of two flex head literals in a different way than leo, that would lead to other results
    var transformations_step1: Seq[(lpOlTerm, lpOlTerm, lpTerm)] = Seq.empty
    var transformations_step2: Seq[(lpOlTerm, lpOlTerm, lpTerm)] = Seq.empty
    var otherLitAsEq: lpOlTerm = lpOlNothing
    var maxLitAsEq: lpOlTerm = lpOlNothing
    var encStep1: lpTerm = lpOlNothing

    val polarityOfRule = maxLit.polarity //todo: instead make it polyrity of other lit after rule application

    if (!otherLit.equational | !maxLit.equational) { // todo make a function that just takes the literals and the desired polarity and makes them equational
      // we detect the polarity of the max literal to make sure the other Literal shares it

      // we first adjust the polarity of the other lit and make it equational if necessary
      if (!otherLit.equational){
        val (encodedOtherLit, otherLitAsEq0, prfForward_ol, prfBack_ol, lit_l_ol, lit_r_ol,parametersNew_ol,usedSymbolsNew_ol) = makeLiteralEquational(otherLit, polarityOfRule, bVarMap, sig, parameters)
        otherLit_l = lit_l_ol
        otherLit_r = lit_r_ol
        otherLitAsEq = otherLitAsEq0
        transformations_step1 = transformations_step1 :+ (encodedOtherLit, otherLitAsEq, prfForward_ol)
        transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, prfBack_ol)
        parameters = parametersNew_ol
        usedSymbols = usedSymbolsNew_ol
        /*
        if (!(otherLit.polarity == polarityOfRule)){
          if(otherLit.polarity){
            // we need to make it negative!
            // apply the translation rule
            /*
            val (transf, parametersNew, usedSymbolsNew) = mkPosPropNegLit(encodedOtherLit, parameters)
            parameters = parametersNew
            usedSymbols = usedSymbolsNew
            // define variables to use for the instanciation of the rule
            otherLit_l = s"($lnot $encodedOtherLit)"
            otherLit_r = HOLtop
            otherLitAsEq = s"($lnot($equ [$uparrow o] ($lnot $encodedOtherLit) $HOLtop))"
            transformations_step1 = transformations_step1 :+ (encodedOtherLit, otherLitAsEq, transf)
            // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
            // for this we can already construct the rule using the information derived here
            val (transfBack, parametersNewBack, usedSymbolsNewBack) = mkNegLitPosProp(encodedOtherLit, parameters)
            parameters = parametersNewBack
            usedSymbols = usedSymbolsNewBack
            transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, transfBack)
             */
          }else {
            // neg Prop pos Lit
            /*
            asTerm(otherLit) match {
              case Not(t) =>
                val encodedOtherLitPos = term2LP(t, bVarMap, sig)._1
                val (transf, parametersNew, usedSymbolsNew) = mkNegPropPosLit(encodedOtherLitPos, parameters)
                parameters = parametersNew
                usedSymbols = usedSymbolsNew
                // define variables to use for the instanciation of the rule
                otherLit_l = s"($lnot $encodedOtherLitPos)"
                otherLit_r = HOLtop
                otherLitAsEq = s"($equ [$uparrow o] $otherLit_l $HOLtop)"
                transformations_step1 = transformations_step1 :+ (encodedOtherLit, otherLitAsEq, transf)
                // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
                // for this we can already construct the rule using the information derived here
                val (transfBack, parametersNewBack, usedSymbolsNewBack) = mkPosLitNegProp(encodedOtherLitPos, parameters)
                parameters = parametersNewBack
                usedSymbols = usedSymbolsNewBack
                transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, transfBack)
              case _ => throw new Exception(s"when trying to encode EqFact, max lit with wrong form was found")
            }
            */
          }
        }else{
          // just make it equational
          if (otherLit.polarity){
            // posProp to posEq
            val (transf, parametersNew, usedSymbolsNew) = mkPosPropPosLit(encodedOtherLit, parameters)
            parameters = parametersNew
            usedSymbols = usedSymbolsNew
            // define variables to use for the instanciation of the rule
            otherLit_l = encodedOtherLit
            otherLit_r = HOLtop
            otherLitAsEq = s"($equ [$uparrow o] $encodedOtherLit $HOLtop)"
            transformations_step1 = transformations_step1 :+ (encodedOtherLit, otherLitAsEq, transf)
            // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
            // for this we can already construct the rule using the information derived here
            val (transfBack, parametersNewBack, usedSymbolsNewBack) = mkPosLitPosProp(encodedOtherLit, parameters)
            parameters = parametersNewBack
            usedSymbols = usedSymbolsNewBack
            transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, transfBack)
          }else{
            // negProp to negEq
            asTerm(otherLit) match {
              case Not(t) =>
                val encodedOtherLitPos = term2LP(t, bVarMap, sig)._1
                val (transf, parametersNew, usedSymbolsNew) = mkNegPropNegLit(encodedOtherLitPos, parameters)
                parameters = parametersNew
                usedSymbols = usedSymbolsNew
                // define variables to use for the instanciation of the rule
                otherLit_l = encodedOtherLitPos
                otherLit_r = HOLtop
                otherLitAsEq = s"($lnot($equ [$uparrow o] $encodedOtherLitPos $HOLtop))"
                transformations_step1 = transformations_step1 :+ (encodedOtherLit, otherLitAsEq, transf)
                // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
                // for this we can already construct the rule using the information derived here
                val (transfBack, parametersNewBack, usedSymbolsNewBack) = mkNegLitNegProp(encodedOtherLitPos, parameters)
                parameters = parametersNewBack
                usedSymbols = usedSymbolsNewBack
                transformations_step2 = transformations_step2 :+ (otherLitAsEq, encodedOtherLit, transfBack)
              case _ => throw new Exception(s"when trying to encode EqFact, max lit with wrong form was found")
            }
          }
        }
        */
      }else{
        // case where it is equatinal, just instanciate with equality
        throw new Exception(s"EqFactoring for positive polarity not encoded yet 3")
      }

      // MAX LIT
      if (!maxLit.equational){
        val (encodedMaxLit, maxLitAsEq0, prfForward_ml, _, lit_l_ml, lit_r_ml, parametersNew_ml, usedSymbolsNew_ml) = makeLiteralEquational(maxLit, polarityOfRule, bVarMap, sig, parameters)
        maxLit_l = lit_l_ml
        maxLit_r = lit_r_ml
        maxLitAsEq = maxLitAsEq0
        transformations_step1 = transformations_step1 :+ (encodedMaxLit, maxLitAsEq, prfForward_ml)
        //transformations_step2 = transformations_step2 :+ (maxLitAsEq, encodedMaxLit, prfBack_ml)
        parameters = parametersNew_ml
        usedSymbols = usedSymbolsNew_ml
        /*
        if (!(maxLit.polarity == polarityOfRule)) {
          // change polarity of max lit and make it equatinal
          if (maxLit.polarity) {
            // posProp to negEq
            //val encodedMaxLitNeg = term2LP(Not(asTerm(maxLit)), bVarMap, sig)._1
            val (transf, parametersNew, usedSymbolsNew) = mkPosPropNegLit(encodedMaxLit, parameters)
            parameters = parametersNew
            usedSymbols = usedSymbolsNew
            // define variables to use for the instanciation of the rule
            maxLit_l = s"($lnot $encodedMaxLit)"
            maxLit_r = HOLtop
            maxLitAsEq = s"($lnot($equ [$uparrow o] $maxLit_l $HOLtop))"
            transformations_step1 = transformations_step1 :+ (encodedMaxLit, maxLitAsEq, transf)
          } else {
            // negProp to posEq
            // todo
            throw new Exception(s"EqFactoring for positive polarity not encoded yet 5")
          }
        }else{
          // only make it equational
          if (maxLit.polarity) {
            // posProp to posEq
            //todo
            val (transf, parametersNew, usedSymbolsNew) = mkPosPropPosLit(encodedMaxLit, parameters)
            parameters = parametersNew
            usedSymbols = usedSymbolsNew
            // define variables to use for the instanciation of the rule
            maxLit_l = encodedMaxLit
            maxLit_r = HOLtop
            maxLitAsEq = s"($equ [$uparrow o] $encodedMaxLit $HOLtop)"
            transformations_step1 = transformations_step1 :+ (encodedMaxLit, maxLitAsEq, transf)
          }else{
            // negProp to negEq
            asTerm(maxLit) match {
              case Not(t) =>
                val encodedMaxLitPos = term2LP(t, bVarMap, sig)._1
                val (transf, parametersNew, usedSymbolsNew) = mkNegPropNegLit(encodedMaxLitPos, parameters)
                parameters = parametersNew
                usedSymbols = usedSymbolsNew
                // define variables to use for the instanciation of the rule
                maxLit_l = encodedMaxLitPos
                maxLit_r = HOLtop
                maxLitAsEq = s"($lnot($equ [$uparrow o] $encodedMaxLitPos $HOLtop))"
                transformations_step1 = transformations_step1 :+ (encodedMaxLit, maxLitAsEq, transf)
              case _ => throw new Exception(s"when trying to encode EqFact, max lit with wrong form was found")
            }
          }
        }
        */
      }else{
        // only do identity
        // todo
        throw new Exception(s"EqFactoring for positive polarity not encoded yet 7")
      }

      //print(s"transformations_step1 :\n ${transformations_step1.map(trans => trans._3.pretty).mkString(s"\n")}\n")

      val (encStep1_0, parametersNew) = ruleAppClause_new(transformations_step1, parameters)
      encStep1 = encStep1_0
      parameters = parametersNew
      //print(s"encoded step: $encStep1\n")
    } else {
      // if both literals are equational, we can simply encode the left and right side
      otherLit_l = term2LP(otherLit.left, bVarMap, sig)._1
      otherLit_r = term2LP(otherLit.right, bVarMap, sig)._1
      maxLit_l = term2LP(maxLit.left, bVarMap, sig)._1
      maxLit_r = term2LP(maxLit.right, bVarMap, sig)._1
      // todo: What to do if i neednt encode the clauses?
    }

    //print(s"parameters before step 2: $parameters\n")
    // STEP 2: actually apply the equal factoring
    // define the strings we use to instanciate the rules
    val ty = if(maxLit.equational) maxLit.left.ty else asTerm(maxLit).ty //todo: check if all have same type and throw error otherwise
    val encType = type2LP(ty, sig)._1
    var encStep2: lpTerm = lpOlNothing
    if(polarityOfRule){
      // apply rule for positive equal factoring
      val (encStep2_0, parametersNew, usedSymbolsNew) = encEqFactPosInst(encType, otherLit_l, otherLit_r, maxLit_l, maxLit_r, parameters)
      encStep2 = encStep2_0
      parameters = parametersNew
      usedSymbols = usedSymbols ++ usedSymbolsNew
    } else {
      // apply rule for negative equal factoring
      val (encStep2_0, parametersNew, usedSymbolsNew) = encEqFactNegInst(encType,otherLit_l,otherLit_r,maxLit_l,maxLit_r,parameters)
      encStep2 = encStep2_0
      parameters = parametersNew
      usedSymbols = usedSymbols ++ usedSymbolsNew
      //print(s"encoding of the EqFactoring itself: $encStep2 \n" )
    }


    // STEP 3: encoding back
    // if the formulas were encoded in the beginning, we need a backwards encoding to the original non equational notation!
    var uc1: lpOlTerm = lpOlNothing
    var uc1Final: lpOlTerm = lpOlNothing
    var uc2: lpOlTerm = lpOlNothing
    var uc2Eq: lpOlTerm = lpOlNothing
    if (!otherLit.equational | !maxLit.equational) {
      // the backwards encoding of other literals was already defined in step 1, the encoding of the unification constraint literals is as follows:
      // the first one will always be equational since it contains the left sides of otherLit and maxLit. Therefore we add it to transformations as the before and after and
      // provide a term of type /Pi x , Prf x -> Prf x as a transformation rule

      // if the maxLiteral is not equational, the second unification constraint will not be equational either.
      // We can already define the rule to transform it back to the non-equational encoding
      // Due to the ordering of literals, the order may change however. We need to test this here using the unification constraint we tracked during the oringinal application of the rule:
      // We test this by comparing the left side of the unification constraing with the left side of the other litera:
      val otherLitL = if (otherLit.equational) otherLit.left else asTerm(otherLit)
      if (otherLitL == uc1Orig.left){
        // in this case the order is as it is proven by the rule application
        //uc1 = s"($lnot($equ [$uparrow o] $otherLit_l $maxLit_l))"
        uc1 = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,otherLit_l,maxLit_r))
        uc1Final = uc1
        val (uc1Rule, parametersNewUc1) = selfImp(uc1, parameters)
        parameters = parametersNewUc1
        transformations_step2 = transformations_step2 :+ (uc1, uc1, uc1Rule)
      }else if ((otherLitL == uc1Orig.right)|(Not(otherLitL) == uc1Orig.right)|(otherLitL == Not(uc1Orig.right))){
        // the order was changed, we need to "stack" the rule for the change of the order here too
        // apply the two sides of the literal to the proof of equational commutativity
        val (uc1Rule, parametersNewUc1) = inEqCom(lpOtype.lift2Poly,otherLit_l,maxLit_l,parameters)
        //print(s"uc1Rule: \ntype ${uc1Rule.pretty};\n")
        //print(s"uninstanciated ineqcom: \ntype ${inEqCom(lpOtype.lift2Poly,lpOlConstantTerm("a"),lpOlConstantTerm("b"),parameters)._1.pretty};\n")
        //print(s"uc1Rule: ${uc1Rule.pretty}\n")
        parameters = parametersNewUc1
        // now we define what uc1 looks like before and after:
        //uc1 = s"($lnot($equ [$uparrow o] $otherLit_l $maxLit_l))"
        uc1 = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,otherLit_l,maxLit_l))
        //uc1Final = s"($lnot($equ [$uparrow o] $maxLit_l $otherLit_l))"
        uc1Final = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,maxLit_l,otherLit_l))
        transformations_step2 = transformations_step2 :+ (uc1, uc1Final, uc1Rule)
        //print(s"symbol changeOrder : Prf($uc1) $rightarrow Prf($uc1Final) $colonEq \n$uc1Rule;\n")
      }else throw new Exception(s"the first unification constraint encoded in LP encoding does not match the one derived by Leo")


      // the second unification constraint is non equational - and thus requires a backwards encoding - iff the max literals were non equational
      //todo : check weather order has to be changed here too!
      if (maxLit_r == lpOlTop) {
        // todo: if we have a negative left side of other lit, should we encode the backwards translation as double negation here or is it eliminated right away?
        //  define exceptin to test this:
        if (otherLit.equational){
          otherLit.left match {
            case Not(_) =>
              throw new Exception(s"test what happens wigh eqFactoring back encoding here")
          }
        }
        // we translate back to a non eq literal
        val (uc2_rule,parametersNewUc2,usedSymbolsNewUc2) = mkNegLitNegProp(otherLit_r,parameters)
        //uc2Eq_str = s"($lnot($equ [$uparrow $oType] $otherLit_r $otherLit_r))"
        //throw new Exception(s"i highly doubt that this is correct, double check")
        uc2Eq = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,otherLit_r,otherLit_r)) //todo: can this be right? same thing on both sides
        //uc2_str = s"($lnot $otherLit_r)"
        uc2 = lpOlUnaryConnectiveTerm(lpNot,otherLit_r)
        parameters = parametersNewUc2
        usedSymbols = usedSymbolsNewUc2
        transformations_step2 = transformations_step2 :+ (uc2Eq,uc2,uc2_rule)
        //print(s"uc2:\n${uc2Eq.pretty}\n${uc2.pretty}\n${uc2_rule.pretty}\n")

      } else if (otherLit_l == lpOlTop) {
        throw new Exception(s"Eq factoring with non equational maxLit and equational other lits! Check how this needs to be backwards encoded after rule application!")
      } else {
        // no backwards encoding necessary because both literals were equational!
        //uc2 = s"($lnot($equ [$uparrow o] $otherLit_l $otherLit_r))"
        uc2 = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,otherLit_l,otherLit_r))
        uc2Eq = uc2
        val (selfImpUc2, parametersNewUc2) = selfImp(uc2, parameters)
        parameters = parametersNewUc2
        transformations_step2 = transformations_step2 :+ (uc2, uc2, selfImpUc2)
      }

      // combine into one rule for the backwards encoding:
      val (encStep3,parametersNewBack) = ruleAppClause_new(transformations_step2,parameters)
      parameters = parametersNewBack

      //print(s"transformations_step2 :\n ${transformations_step2.map(trans => trans._3.pretty).mkString(s"\n")}\n")

      val encodedOtherLit = term2LP(asTerm(otherLit), bVarMap, sig)._1
      val encodedMaxLit = term2LP(asTerm(maxLit), bVarMap, sig)._1
      val encParent = lpOlUntypedBinaryConnectiveTerm(lpOr,encodedOtherLit,encodedMaxLit)

      // combine all of the above steps into the overall lambda Term!
      //val afterStep1 = s"($otherLitAsEq $lor $maxLitAsEq)"
      val afterStep1 = lpOlUntypedBinaryConnectiveTerm(lpOr,otherLitAsEq,maxLitAsEq)
      //val afterStep2 = s"($otherLitAsEq $lor $uc1 $lor $uc2Eq)"
      val afterStep2 = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,Seq(otherLitAsEq,uc1,uc2Eq))
      //val encChild = s"($encodedOtherLit $lor $uc1Final $lor $uc2)"
      val encChild = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,Seq(encodedOtherLit,uc1Final,uc2))
      val (allSteps, parametersNew4, usedSymbolsNew4) = impTrans4(encParent, afterStep1, afterStep2, encChild, encStep1, encStep2, encStep3, parameters)
      parameters = parametersNew4
      usedSymbols = usedSymbolsNew4

      /*
      print(s"symbol EqFact_step1 : Prf(${encParent.pretty}) $rightarrow Prf(${afterStep1.pretty}) $colonEq \n${encStep1.pretty};\n")
      print(s"symbol EqFact_step2 : Prf(${afterStep1.pretty}) $rightarrow Prf(${afterStep2.pretty}) $colonEq \n${encStep2.pretty};\n")
      print(s"symbol EqFact_step3 : Prf(${afterStep2.pretty}) $rightarrow Prf(${encChild.pretty}) $colonEq \n${encStep3.pretty};\n")
      print(s"everyting put together: ${allSteps.pretty}\n\n")


       */




      (allSteps,parameters,usedSymbols)


      // setup for tests
      /*
      print(s"transformations 2: $transformations_step2\n")
      print(s"back encoding: $encStep3\n")

      print(s"symbol before1: Prf(${transformations_step2(0)._1});\n")
      print(s"symbol before2: Prf(${transformations_step2(1)._1});\n")
      print(s"symbol before3: Prf(${transformations_step2(2)._1});\n")
      print(s"symbol after1: Prf(${transformations_step2(0)._2});\n")
      print(s"symbol after2: Prf(${transformations_step2(1)._2});\n")
      print(s"symbol after3: Prf(${transformations_step2(2)._2});\n")
      print(s"symbol rule1: Prf(${transformations_step2(0)._1}) $rightarrow Prf(${transformations_step2(0)._2}) \n$colonEq ${transformations_step2(0)._3};\n")
      print(s"symbol rule2: Prf(${transformations_step2(1)._1}) $rightarrow Prf(${transformations_step2(1)._2}) \n$colonEq ${transformations_step2(1)._3};\n")
      print(s"symbol rule3: Prf(${transformations_step2(2)._1}) $rightarrow Prf(${transformations_step2(2)._2}) \n$colonEq ${transformations_step2(2)._3};\n")
      val transformations_test = Seq(("before1","after1","rule1"),("before2","after2","rule2"),("before3","after3","rule3"))
      print(s"type ${ruleAppClause_new(transformations_test,parameters)._1};\n")
      print(s"test: ${ruleAppClause_new(Seq(("a","a",s"(($LPlambda x (h: Prf x), h)a)"),("a","a",s"(($LPlambda x (h: Prf x), h)a)")),(0,0,0))._1};\n")
      print(s"test2: ${ruleAppClause_new(Seq(transformations_step2(0),transformations_step2(1)),parameters)._1};\n")
       */
    }else{
      // if both literals were equational to begin with, we can simply return step2 whight the encodings to equational form and back
      (encStep2,parameters,usedSymbols)
    }


  }

  def encEqFactClause(child: ClauseProxy, parent: ClauseProxy, additionalInfo: (Literal, Literal, Literal, Literal, Boolean, Boolean), parentNameLpEnc: lpConstantTerm, sig: Signature, parameters0: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    //throw new Exception("CHANGE encEqFactClause")
    // todo: outsource the transformation to equality literals?
    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

    val transformations: Seq[(String, String, String)] = Seq.empty

    var parameters = parameters0

    var usedSymbols: Set[String] = Set.empty

    // the additional information necessary to encode the step:
    val (otherLit, maxLit, ur1, ur2, wasUnified, wasSimplified) = additionalInfo

    if (wasUnified) throw new Exception(s"Error encoding equal factoring: type unification not encoded yet")
    if (wasSimplified) throw new Exception(s"Error encoding equal factoring: simplification not encoded yet")

    /*
    print(s"child: ${{clause2LP(child.cl, Set.empty, sig)._1}}\n")
    print(s"parent: ${clause2LP(parent.cl, Set.empty, sig)._1}\n")
    print(s"otherLit: ${term2LP(asTerm(otherLit), bVarMap, sig)._1}\n")
    print(s"maxLit: ${term2LP(asTerm(maxLit), bVarMap, sig)._1}\n")
    print(s"ur1: ${term2LP(asTerm(ur1), bVarMap, sig)._1}\n")
    print(s"ur2: ${term2LP(asTerm(ur2), bVarMap, sig)._1}\n")
    print(s"wasUnified: $wasUnified\n")
    print(s"wasSimplified: $wasSimplified\n")
     */

    // if variables were quantified over in the original formula, we need to extract them and quanify over them in the new term and apply them to the constructed rule
    val (clauseQuantification, applySymbolsToParent) = clauseRuleQuantification(parent.cl, bVarMap, sig)

    if (parent.cl.lits.length == 2){
      val (encFactoring, parametersNew, usedSymbolsNew) = encEqFactLiterals(otherLit, maxLit, ur1, ur2, bVarMap, sig, parameters)
      //print(s"\nencoding of complete eqFactoring Step: \ntype $encFactoring;\n")

      //val lambdaTerm_str = s"($LPlambda $clauseQuantification, ($encFactoring) ($parentNameLpEnc $applySymbolsToParent))"
      val lambdaTerm = lpLambdaTerm(clauseQuantification,lpFunctionApp(encFactoring,Seq(lpFunctionApp(parentNameLpEnc,applySymbolsToParent))))

      (lambdaTerm, parametersNew, usedSymbolsNew)
    } else {
      throw new Exception(s"eqFacoring with more literal besides the max and the other lit not encoded yet")
    }

  }

  def encSubtermSimp(simpRule: String, t0: lpOlTerm, t1: lpOlTerm, hCount: Int, stepName: String, tab: Int): lpProofScriptStep ={

    // the type of the simplification proof
    val ty = lpMlFunctionType(Seq(t0.prf, t1.prf))

    simpRule match {
      case "Simp1" =>
        val argument = t1
        val ruleApplication = lpRefine(lpFunctionApp(SimplificationEncoding.Simp1.name,Seq(argument)))
        lpHave(stepName,ty,ruleApplication.toProofScrips,tab)

      case _ =>
        throw new Exception(s"Simplification Rule $simpRule not encoded yet")
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

  def simplificationInfoToSteps(parent: Clause, additionalInfo: Seq[(Seq[Int],String,Term,Term)], sig: Signature):(Seq[lpProofScriptStep],Set[lpStatement])={
    var usedSymbols: Set[lpStatement] = Set.empty
    var rewriteSteps: Seq[lpProofScriptStep] = Seq.empty

    additionalInfo foreach { tuple =>
      val (appliedSimpRule, needsTypeInst) = SimplificationEncoding.SimpRuleMap(tuple._2)
      usedSymbols = usedSymbols + appliedSimpRule
      val (rewritePattern0, termAtRewriteVar) = acessSubterm(Clause.asTerm(parent), tuple._1, sig)
      //print(s"enc parent term: ${term2LP(tuple._3,bVars,sig,Set.empty)._1.pretty}\n")
      //the pattern we need to match can not only be determined based on the terms because we also need to account for the
      // equality between the child and parent clause we added!
      val rewritePattern = lpRewritePattern(lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, rewritePattern0, lpOlWildcard))
      val rewriteStep = if (needsTypeInst) {
        // in this case we need to find out the type of the terms in this equality to instanciate the simplification rule with them
        val ty = termAtRewriteVar match {
          case tl === tr =>
            type2LP(tl.ty, sig, Set.empty)._1
          //todo: can equivalence also occour here
          case _ => throw new Exception(s"detected connective other than equality where equality was exprected")
        }
        lpRewrite(Option(rewritePattern), lpFunctionApp(appliedSimpRule.name, Seq(lpConstantTerm(s"[${ty.lift2Poly.pretty}]"))))
      }
      else lpRewrite(Option(rewritePattern), appliedSimpRule.name)
      //print(s"position: ${tuple._1}\n")
      //print(s"${rewriteStep.pretty}\n")
      rewriteSteps = rewriteSteps :+ rewriteStep
    }
    (rewriteSteps,usedSymbols)
  }


  def simplificationProofScript(child: Clause, parent: Clause, additionalInfo: Seq[(Seq[Int],String,Term,Term)], symbolsToUnfold: Set[Signature.Key], parentNameLpEnc: lpConstantTerm, quantifiedVars: Seq[lpUntypedVar], bVars: Map[Int, String], sig: Signature):(lpProofScript, Set[lpStatement])={

    // proof the equality between a parent and a child term given a set of rewrite rules and their positions
    var usedSymbols: Set[lpStatement] = Set.empty

    val simplificationStepName: String = {
      if (additionalInfo.nonEmpty) {
        if (symbolsToUnfold.nonEmpty) "DefExpAndSimp" else "Simp"
      } else {
        if (symbolsToUnfold.nonEmpty) "DefExp" else throw new Exception(s"Nothing was expanded or simplified in simplification step")
      }
    }


    // the complete proof script consists of 3 steps:
    // 1. If necessary, unfold definitions
    // 2. Proof the equality between the parent and the child clause
    // 3. By applying identity (λ x ,x) and the parent term encoding to the equality proven in 2, we can conclude the child

    var allProofStep: Seq[lpProofScriptStep] = Seq.empty
    var rewriteSteps: Seq[lpProofScriptStep] = Seq.empty

    //// 1. Unfold necessary definitions
    if (symbolsToUnfold.nonEmpty) {
      rewriteSteps = rewriteSteps :+ lpProofScriptCommentLine("Unfold necessary definitions")
      val unfoldVars = symbolsToUnfold.map(sym => lpConstantTerm(sig(sym).name))
      rewriteSteps = rewriteSteps :+ lpSimplify(unfoldVars)
      if (additionalInfo.nonEmpty) rewriteSteps = rewriteSteps :+ lpProofScriptCommentLine("Application of simplification rules")
    }

    //// 2. Equality between parent and child
    val (additionalSteps, usedSymbolsNew) = simplificationInfoToSteps(parent, additionalInfo, sig)
    rewriteSteps = rewriteSteps ++ additionalSteps
    usedSymbols = usedSymbols ++ usedSymbolsNew
    val encParent = term2LP(Clause.asTerm(parent),bVars,sig)._1
    val encChild = term2LP(Clause.asTerm(child),bVars,sig)._1
    // at the end, only something like x=x should remain of the focussed goal. We add the tactic "reflexivity" to prove this.
    rewriteSteps = rewriteSteps :+ lpReflexivity()

    // we proof that the term before the transformation = the term after the transformation
    val eqSimpTerm = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,encParent,encChild).prf
    val haveStep = lpHave(simplificationStepName,eqSimpTerm,lpProofScript(rewriteSteps))

    allProofStep = allProofStep :+ haveStep


    //// 3. Refine step
    val application = lpFunctionApp(lpConstantTerm(simplificationStepName),Seq(lpUseful.Identity, lpFunctionApp(parentNameLpEnc,quantifiedVars)))
    val applicationStep = lpRefine(application)
    allProofStep = allProofStep :+ applicationStep

    // combine all steps into one proof script
    val proofScript = lpProofScript(allProofStep)

    (proofScript, usedSymbols)
  }

  def encDefExSimp(child: ClauseProxy, parent: ClauseProxy, additionalInfoSimp: Seq[(Seq[Int],String,Term,Term)], additionalInfoDefExp: Seq[Signature.Key], parentNameLpEnc: lpConstantTerm, sig: Signature):(lpProofScript, Set[lpStatement], Set[Signature.Key])={

    //print(s"parent: ${clause2LP(parent.cl,Set.empty,sig)._1.pretty}\nchild: ${clause2LP(child.cl,Set.empty,sig)._1.pretty}\n")

    val defsWereExpanded: Boolean = additionalInfoDefExp.nonEmpty
    val wasSimplified: Boolean = additionalInfoSimp.nonEmpty
    val wasEtaExp: Boolean = false

    val bVars = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

    var usedSymbols: Set[lpStatement] = Set.empty
    var allProofStep: Seq[lpProofScriptStep] = Seq.empty

    // todo: since we might have eta expanision this might have to be changed

    val encSimpChild = if (wasEtaExp) throw new Exception("lp proof for eta expansion not encoded yet") else term2LP(Clause.asTerm(child.cl), bVars, sig)._1

    //// 1. Abstraction step
    val quantifiedVars = clauseRuleQuantification(parent.cl, bVars, sig)._2
    if (quantifiedVars.length > 0) {
      throw new Exception(s"the encoding of simplifications with implicitly quantified vars is not tested yet, comment this and check carefully")
      val assumeStep = lpAssume(quantifiedVars)
      allProofStep = allProofStep :+ assumeStep
    }


    //// 2. Proof defExpansion and / or simplification
    if (wasSimplified){
      val (simpProof, usedSymbolsSimplification) = simplificationProofScript(child.cl,parent.cl,additionalInfoSimp,additionalInfoDefExp.toSet,parentNameLpEnc,quantifiedVars,bVars,sig)
      usedSymbols = usedSymbols ++ usedSymbolsSimplification
      if (parent.cl.lits.length != child.cl.lits.length) throw new Exception(s"when simplifying to ${encSimpChild.pretty} a literal was deleted, this is not yet encoded")

      allProofStep = allProofStep :+ simpProof
    }

    // combine all steps into one proof script
    val proofScript = lpProofScript(allProofStep)

    (proofScript, usedSymbols, additionalInfoDefExp.toSet)

  }


  def substituteVarTerm(t: lpOlTerm, subsMap: Map[String,lpOlTerm]): lpOlTerm = {
    // given a substitution map and a term, substitute all occurrences of given variables in a term
    // todo: this is not ordered, is that problematic?

    def substituteTypedVarsTerm(var0: lpOlTypedVar, subsMap: Map[String, lpOlTerm]): lpOlTypedVar = {
      // apply substitution to a typed variable
      if (subsMap.contains(var0.name.pretty)) {
        subsMap(var0.name.pretty) match {
          case lpOlTypedVar(name1, _) => lpOlTypedVar(name1, var0.ty)
          case lpOlUntypedVar(name1) => lpOlTypedVar(lpOlConstantTerm(name1.pretty), var0.ty)
          case lpOlConstantTerm(name1) => lpOlTypedVar(lpOlConstantTerm(name1), var0.ty)
          case _ => throw new Exception(s"Error in lp Encoding: trying to substitute variable ${var0.pretty} with ${subsMap(var0.name.pretty)}")
        }
      } else var0
    }

    t match{
      case `lpOlTop` =>
        lpOlTop
      case `lpOlBot` => lpOlBot
      case lpOlConstantTerm(name) =>
        subsMap.getOrElse(name,lpOlConstantTerm(name))
      case lpOlTypedVar(name, ty) =>
        // when we encounter the typed var that was quantified in the body, we want to replace it!
        subsMap.getOrElse(name.a, t)
      case lpOlUntypedVar(lpConstantTerm(name)) =>
        if (subsMap.contains(name)) {
          subsMap(name) match {
            case lpOlTypedVar(name1,_) => lpOlUntypedVar(name1)
            case lpOlUntypedVar(name1) => lpOlUntypedVar(lpOlConstantTerm(name1.pretty))
            case lpOlConstantTerm(name1) => lpOlUntypedVar(lpOlConstantTerm(name1))
            case _ => throw new Exception(s"Error in lp Encoding: trying to substitute variable ${t.pretty} with ${subsMap(name).pretty}")
          }
        } else t
      case lpOlLambdaTerm(vars,body) => lpOlLambdaTerm(vars.map(var0 => substituteTypedVarsTerm(var0, subsMap)),substituteVarTerm(body, subsMap))
      case lpOlFunctionApp(f, args) =>
        var encArgs: Seq[lpTerm] = Seq.empty
        args foreach {arg =>
          arg match{
            case a : lpOlTerm => encArgs = encArgs :+ substituteVarTerm(a, subsMap)
            // if the argument is e.g. a type we do not need to substitute anyting
            case _ => encArgs :+ arg
          }
        }
        lpOlFunctionApp(substituteVarTerm(f, subsMap), encArgs)
      case lpOlMonoQuantifiedTerm(quantifier, variables, body) => lpOlMonoQuantifiedTerm(quantifier, variables.map(var0 => substituteTypedVarsTerm(var0, subsMap)), substituteVarTerm(body, subsMap))
      case lpOlUnaryConnectiveTerm(connective, body) => lpOlUnaryConnectiveTerm(connective,  substituteVarTerm(body, subsMap))
      case lpOlUntypedBinaryConnectiveTerm(connective,lhs,rhs) => lpOlUntypedBinaryConnectiveTerm(connective, substituteVarTerm(lhs, subsMap), substituteVarTerm(rhs, subsMap))
      case lpOlTypedBinaryConnectiveTerm(connective, ty, lhs, rhs) => lpOlTypedBinaryConnectiveTerm(connective, ty,  substituteVarTerm(lhs, subsMap),  substituteVarTerm(rhs, subsMap))
      case lpOlUntypedBinaryConnectiveTerm_multi(connective, args) =>
        lpOlUntypedBinaryConnectiveTerm_multi(connective, args.map(arg => substituteVarTerm(arg, subsMap)))
      case _ => throw new Exception(s"encountered unexptcted term $t when trying to do substitution")
    }
  }

  def wholeHaveRewriteStep(rewriteSteps: Seq[lpProofScriptStep], nameStep: String, nameSubStep: String, before: lpOlTerm, sourceBefore: lpTerm, after: lpOlTerm): lpHave = {
    //todo: use this in my simplification steps?

    // In many cases, we want to generate Sub-Steps for rewritings in proofs that first prove the equality of Term A and B (when for instance B is a simplified version of A)
    // And then prove B given A. This function generates such steps.

    // 1. Proof equality
    val equalityToProve = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,before,after)
    val withAddedReflexivity = lpProofScript(rewriteSteps :+ lpReflexivity())
    val subStep = lpHave(nameSubStep, equalityToProve.prf, withAddedReflexivity)

    // 2. Proof the "after" given the equality
    //val stepProof = lpProofScript(Seq(subStep,lpRefine(lpFunctionApp(lpConstantTerm(nameSubStep),Seq(lpUseful.Identity,sourceBefore)))))
    val stepProof = lpProofScript(Seq(subStep,lpRefine(lpUseful.applyToEqualityTerm(lpOtype,before,after,lpOlConstantTerm(nameSubStep),lpOlLambdaTerm(Seq(lpOlTypedVar(lpOlConstantTerm("x"),lpOtype)),lpOlConstantTerm("x")),Some(sourceBefore)))))

    // the whole Have step:
    lpHave(nameStep,after.prf,stepProof)
  }

  def removeUnificationConstraint(uniC: Literal, parent: Clause, sig: Signature): (Seq[lpProofScriptStep], Set[lpStatement])={
    // prove that unification literal can be removed from a clause when they either have the form ¬⊤ or x≠x (modulo unification)

    var usedSymbols: Set[lpStatement] = Set.empty

    // identify the position of the unification literals in parent clause
    val positionInClause = findLitInClause(uniC,parent)
    // todo: make sure this can not occour and if it can make a special case for it (extra function to remove duplicates or sth. like that)
    val patternVar = lpOlUntypedVar(lpOlConstantTerm("x"))


    var rewriteSteps: Seq[lpProofScriptStep] = Seq.empty

    // proof the first transformation depending on the form of the unification constraint
    val rewritePattern_step1 = generateClausePatternTerm(positionInClause, parent.lits.length, Some(0), patternVar)
    if (uniC.equational){
      if (!uniC.polarity){
        // in this case, we need to first show that both sides are equal modulo simplification and then apply a Simp Rule that postulates that x≠x = ⊥
        // the rewrite rule used here needs to explicitly instanciate the used type, therefore we first need to find that type out:
        val ty = type2LP(uniC.left.ty, sig, Set.empty)._1
        val rewriteStep_step1 = lpRewrite(rewritePattern_step1, lpFunctionApp(SimplificationEncoding.Simp10_eq.name,Seq(lpConstantTerm(s"[${ty.lift2Poly.pretty}]"))))
        rewriteSteps = rewriteSteps :+ lpProofScriptCommentLine("Simplify unification constraint of form x≠x to ⊥")
        rewriteSteps = rewriteSteps :+ lpSimplify(Set.empty)
        rewriteSteps = rewriteSteps :+ rewriteStep_step1
        usedSymbols = usedSymbols + SimplificationEncoding.Simp10_eq
      } else throw new Exception(s"Equational positive unification constratint passed on to lambdapi post eqFact encoding?")
    }else{
      // in this case simply we need to prove that 1. ¬⊤ = ⊥
      if (!uniC.polarity){
        val rewriteStep_step1 = lpRewrite(rewritePattern_step1, SimplificationEncoding.Simp16_eq.name)
        rewriteSteps = rewriteSteps :+ lpProofScriptCommentLine("Simplify unification constraint of form ¬⊤ to ⊥")
        rewriteSteps = rewriteSteps :+ rewriteStep_step1
        usedSymbols = usedSymbols + SimplificationEncoding.Simp16_eq
      }else{
        throw new Exception(s"Error: unification constraint passed to LP encoding is non equational and positive")
      }
    }

    // in both cases, the second step is the removal of ⊥ from the clause. This can be done using Simp7:
    val rewritePattern_step2 = generateClausePatternTerm(positionInClause - 1, parent.lits.length - 1, Some(0), patternVar)
    val rewriteStep_step2 = lpRewrite(rewritePattern_step2, SimplificationEncoding.Simp7_eq.name)
    rewriteSteps = rewriteSteps :+ lpProofScriptCommentLine("Remove ⊥ from clause")
    rewriteSteps = rewriteSteps :+ rewriteStep_step2
    usedSymbols = usedSymbols + SimplificationEncoding.Simp7_eq

    (rewriteSteps,usedSymbols)
  }

  def encPreUni(cl: ClauseProxy, parent: ClauseProxy, addInfoUni: (Seq[(Int,Any,Int,Map[Int,String])],Seq[(Int,Any)]), addInfoUniRule: (String, (Literal, Literal)), parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Set[lpStatement]) = {
    // encode different versions of unification (modulo rule applications, ...)

    val bVars = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

    val mode = {
      if (addInfoUniRule._1 == "uniAfterFactoring") "eqFac"
      else throw new Exception(s"the unification mode $addInfoUni is either not set or not encoded yet...")
    }

    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    var usedSymbols: Set[lpStatement] = Set.empty

    val (unboundVarsParent,_,_) = clause2LP_unquantified(parent.cl,Set.empty,sig) // todo: only use this instead of enc. whole clause
    val (unboundVarsChild0,_,_) = clause2LP_unquantified(cl.cl,Set.empty,sig)

    /*
    print(s"\nPREUNI in mode $mode\n")
    val encChild = clause2LP_unquantified(cl.cl,Set.empty,sig)._2
    print(s"encChild ${encChild.pretty}\n")
    val encParent = clause2LP(parent.cl,Set.empty,sig)
    print(s"encParent ${encParent._1.pretty} (that's ${parentNameLpEnc.pretty})\n")

    addInfoUni foreach { unification =>
      val clause = unification._1
      val encClause = clause2LP(clause,Set.empty,sig)
      print(s"clause: ${encClause._1.pretty}\n")
      val uniStuff = unification._2
      print(s"uni stuff 1: ${uniStuff._1.fronts.head.pretty}\n")
      print(s"uni stuff 2: ${uniStuff._2.pretty}\n")
    }
     */

    // Abstract over the free variables
    val unboundVarsChild = unboundVarsChild0.map(var0 => lpUntypedVar(var0.name))
    allSteps = if (unboundVarsChild.nonEmpty) allSteps :+ lpAssume(unboundVarsChild) else allSteps


    // Encode the actual unification and possibly the following simplification
    val typeUnification = addInfoUni._2
    val termUnification = addInfoUni._1

    // Type unification
    if (typeUnification.nonEmpty){
      throw new Exception(s"LP encoding of type unification not encoded yet")
    }

    if (termUnification.nonEmpty){

      // Construct a map for the substitutions
      val subsMap: mutable.HashMap[String,lpOlTerm] = mutable.HashMap.empty
      val varmap = clauseImplicitsToTPTPQuantifierList_map(parent.cl.implicitlyBound)(sig)
      termUnification foreach { termUni =>
      val lpUnboundVar = varmap.apply(termUni._1)
      //print(s"bind $lpUnboundVar with...\n")
      // Term unifications can either be bindings of variables by terms or by variables...
      // Depending on that, the second element of the tuple is either a term or a String
      termUni._2 match{
        case var0: String =>
          throw new Exception("binding by variables not yet encoded (only terms so far)")//todo: is it really variables? I suppose so, but bound ones, no?
        case t: Term =>
          val encBindTerm = term2LP(t,termUni._4,sig)._1 //todo: dont i need the offset? was it an oversight not to use it in term2lp?
          //print(s"${encBindTerm.pretty}\n")
          subsMap += (lpUnboundVar -> encBindTerm)
        case _ => throw new Exception("Encountered unexpected bound object when encoding Unification step in lp")
        }
      }

      // Proof the substitution by applying the terms to be substituted to the parent quanififying over the respective variables
      val encSubstLits = parent.cl.lits.map(lit => substituteVarTerm(term2LP(asTerm(lit),bVars,sig)._1,subsMap.toMap))
      // The application that instanciates the quantified variables with the substituted Terms in lp
      val applyToParent = unboundVarsParent.map(var0 => subsMap.getOrElse(var0.name.pretty, var0))
      val substitution = lpProofScript(Seq(lpRefine(lpFunctionApp(parentNameLpEnc, applyToParent))))
      val substitutionStepName = "Substitution"
      val substitutionHaveStep = lpHave(substitutionStepName,lpOlUntypedBinaryConnectiveTerm_multi(lpOr,encSubstLits).prf,substitution)
      allSteps = allSteps :+ substitutionHaveStep

      // Depending on the mode of Unification, additional steps like the removal of unification constraints have to be proven
      // we carry out the substitution todo would there be an advantage to passing on the substitution in its original form after all and doing the actual substitution here instead of doing it as lambda terms?
      if (Seq("eqFac").contains(mode)){
        // in this case the unification constraints were fulfilled and removed, we thus need to prove that they can be removed
        if (termUnification.length != unboundVarsParent.length) {
          throw new Exception(s"trying to encode the unification that does not bind all free variables, this is implemented but untested, make sure this is done correctly") //todo
        }
        // Remove the first unification constraint
        val uniC1 = addInfoUniRule._2._1
        if (parent.cl.lits.last != uniC1) throw new Exception(s"encoding unification following eqFactoring and found unification constraint 1 in unexpected position")
        val nameStep1Removal = "RemoveUC1"
        val (removeUniC1, usedSymbolsUc1) = removeUnificationConstraint(uniC1, parent.cl,sig)
        usedSymbols = usedSymbols ++ usedSymbolsUc1
        val proofStepUc1 = wholeHaveRewriteStep(removeUniC1, nameStep1Removal, "H1", lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits), lpConstantTerm(substitutionStepName), lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits.init))
        allSteps = allSteps :+ proofStepUc1
        // Remove the second unification constraint
        val uniC2 = addInfoUniRule._2._2
        if (parent.cl.lits.init.last != uniC2) throw new Exception(s"encoding unification following eqFactoring and found unification constraint 2 in unexpected position")
        val nameStep2Removal = "RemoveUC2"
        val (removeUniC2, usedSymbolsUc2) = removeUnificationConstraint(uniC2, Clause(parent.cl.lits.init),sig)
        usedSymbols = usedSymbols ++ usedSymbolsUc2
        val clauseWighoutUC = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits.init.init)
        val proofStepUc2 = wholeHaveRewriteStep(removeUniC2, nameStep2Removal, "H1", lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits.init), lpConstantTerm(nameStep1Removal), clauseWighoutUC)
        allSteps = allSteps :+ proofStepUc2
        //print(s"\nproof step remove 1: \n${proofStepUc1.pretty}\n")
        //print(s"\nproof step remove 2: \n${proofStepUc2.pretty}\n")

        // Now the last step is refining with the last proven term after removal of the last unification constraint
        val refineStep = lpRefine(lpFunctionApp(lpConstantTerm(nameStep2Removal),Seq()))

        allSteps = allSteps :+ refineStep
      }
    }

    val proofScript = lpProofScript(allSteps)
    //print(s"\ncomplete proof script: \n${proofScript.pretty}\n")
    (proofScript, usedSymbols)

  }

  def encRewrite(cl: ClauseProxy, parents: Seq[ClauseProxy], addInfoSimp: Seq[(Seq[Int],String,Term,Term)], parentModoluRw: Option[Clause], parentNameLpEnc: Seq[lpConstantTerm], sig: Signature)={//: (lpProofScript, Set[lpStatement]) = {
    // todo: will there be issues if variables that are bound within the literals have different names?
    // todo: look at cases in which the rewrite rule is not ground specifically

    val rewriteEqClause = parents(1).cl
    val parent = parents(0).cl
    val bVarsRewriteEq = clauseVars2LP(rewriteEqClause.implicitlyBound, sig, Set.empty)._2
    val (rewriteEqImpVars,encRewriteEq0,_) = clause2LP_unquantified(rewriteEqClause,Set.empty,sig)
    var encRewriteEq = encRewriteEq0
    if (rewriteEqImpVars.nonEmpty) throw new Exception(s"encRewrite for non grounded rules is not encoded yet")
    val (parentImpVars,encParent,_) = clause2LP_unquantified(parent,Set.empty,sig)
    val (childImpVars,encChild,_) = clause2LP_unquantified(cl.cl,Set.empty,sig)
    if (childImpVars.nonEmpty) throw new Exception(s"encRewrite for child with free variables is not encoded yet (but only application should be missing :))")
    var sourceBeforeEq: lpTerm = parentNameLpEnc(1)
    val sourceBeforeParent: lpTerm = parentNameLpEnc(0)

    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    //print(s"encRewriteEq: ${encRewriteEq.pretty}\n")
    //print(s"encParent: ${encParent.pretty}\n")

    // 1. If the parent has implicitly bound variables, we assume them
    val impBoundParent = parentImpVars.map(var0 => var0.untyped)
    if (impBoundParent.nonEmpty) allSteps = allSteps :+ lpAssume(impBoundParent)


    // 2. Test if the clause representing the rewrite equation has the right form (only has one literal that is positive and equational)
    // If it is not equational, transform it to an equational one

    // Cases in which clause can not be used as rewrite rule
    if (rewriteEqClause.lits.length != 1) throw new Exception(s"Error attempting to encode rewrite step in LP: found a rewrite rule with more than one literal...")
    val rewriteEq = rewriteEqClause.lits.head
    if (rewriteEq.equational & !rewriteEq.polarity) throw new Exception(s"Error attempting to encode rewrite step in LP: rewrite rule is equational but not positive")

    // Cases in which the literal representing the rewrite rule first has to be transformed
    if (!rewriteEq.equational){
      // construct a proof script for the transformation
      // todo: can simplification be necessary here?
      val (transformStep, transformedRewriteEq) = if (rewriteEq.polarity){
        // transform positive non equational literal to positive equational one
        usedSymbols = usedSymbols + mkPosPropPosLit_script()
        (lpRewrite(None,lpConstantTerm(mkPosPropPosLit_script().name)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,term2LP(rewriteEq.left,bVarsRewriteEq,sig)._1,lpOlTop))
      }else{
        // transform negative non equational literal to positive equational one with bottom on the lhs
        usedSymbols = usedSymbols + mkNegPropEqBot_script()
        (lpRewrite(None,lpConstantTerm(mkNegPropEqBot_script().name)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,term2LP(rewriteEq.left,bVarsRewriteEq,sig)._1,lpOlBot))
      }
      val transformationStepName = "TransformRewriteRuleClause"
      val haveTransformStep = wholeHaveRewriteStep(Seq(transformStep),transformationStepName,"H1",encRewriteEq,sourceBeforeEq,transformedRewriteEq)
      allSteps = allSteps :+ haveTransformStep
      encRewriteEq = transformedRewriteEq
      sourceBeforeEq = lpConstantTerm(transformationStepName)
    }

    // 3. Rewrite the parent
    // todo: will we still find the position if variables have different names? I assume i should prove the rules with quantifications then it should work
    // todo: search within the individual lits rather than in the overal clause?

    val nameRewriteStep = "Rewrite"
    var rewriteSkript: Seq[lpProofScriptStep] = Seq(lpRewrite(None,sourceBeforeEq))

    // 4. Proof simplifications if necessary
    if (addInfoSimp.nonEmpty){
      throw new Exception(s"rewriting with following simplification is implemented but untested, check carefully")
      val (simplificationSteps, usedSymbolsNew) = simplificationInfoToSteps(parentModoluRw.get,addInfoSimp,sig)
      rewriteSkript = rewriteSkript ++ simplificationSteps
      usedSymbols = usedSymbols ++ usedSymbolsNew
    }

    // 5. Combine the steps and refine the goal with the rewriting step
    val haveRewriteStep = wholeHaveRewriteStep(rewriteSkript,nameRewriteStep,"H2",encParent,sourceBeforeParent,encChild)
    allSteps = allSteps :+ haveRewriteStep
    allSteps = allSteps :+ lpRefine(lpFunctionApp(lpConstantTerm(nameRewriteStep),Seq()))
    val finishedProof = lpProofScript(allSteps)

    (finishedProof,usedSymbols)

  }



  }
