package leo.modules.output.LPoutput

import leo.datastructures.Literal.{asTerm, vars}
import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.LPoutput.Encodings._
import leo.datastructures.{Clause, ClauseProxy, Literal, Signature}
import leo.modules.HOLSignature.Not
import leo.modules.calculus.BoolExt
import leo.modules.output.intToName


object calculusEncoding {

  // general principles

  // name new variables for LP proofs:
  def nameHypothesis(usedH: Int): String = {
    s"h${usedH + 1}"
  }

  def nameBottom(usedB: Int): String = {
    s"b${usedB + 1}"
  }

  def nameX(usedX: Int): String = {
    s"x${usedX + 1}"
  }

  def npp(a: String, PrfAorA: String, symbolTypeMap: Map[String, String]): String = {


    ""
  }

  // construct a proof for the application of rules to literals
  def cOR(a: String, b: String, PrfaIMPb: String, c: String, d: String, PrfcIMPd: String, PrfaORc: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int)) = {
    // a b c d: (Prf a → Prf b) → (Prf c → Prf d) → (Prf(a ∨ c)) → (Prf(b ∨ d))
    // λ a b c d (h1: Prf a → Prf b) (h2: Prf c → Prf d) (h3: Prf (a ∨ c)), h3 (b ∨ d) (λ h4 b1 h5 _, h5 (h1 h4)) (λ h4 b1 _ h6, h6 (h2 h4));

    var hCount = parameters._1
    var bCount = parameters._2

    val abstractions: StringBuffer = new StringBuffer("")

    //// introduce hypothesis variables if necessary

    // if there is no proof for a => b, this could mean that either ...
    val hyp1: String = if (PrfaIMPb == "") {
      // ...we only want to proof (Prf c → Prf d) → (Prf(a ∨ c)) → (Prf(a ∨ d)), in this case b = ""
      // then we do not need this hypothesis at all and assign it to "":
      if (b == "") ""
      // ... or that we do indeed want the rule for b as well but we do not have the proof but abstract over it
      // In this case we want to create a fresh variable for the hypothesis
      else nameHypothesis(hCount)
      // if we have provided a proof we instanciate the hypothesis with it
    } else PrfaIMPb
    // if we have used a fresh variable for the hypothesis we abstract over it and increase the h-counter:
    if ((PrfaIMPb == "") & (b != "")) {
      hCount = hCount + 1
      abstractions.append(s"($hyp1 : $Prf $a $rightarrow $Prf $b) ")
    }

    // the same procedure fot the second hypothesis
    val hyp2: String = if (PrfcIMPd == "") {
      if (d == "") ""
      else nameHypothesis(hCount)
    } else PrfcIMPd
    if ((PrfcIMPd == "") & (d != "")) {
      hCount = hCount + 1
      abstractions.append(s"($hyp2 : $Prf $c $rightarrow $Prf $d) ")
    }

    // similarly we encode the third hypothesis (Prf(a ∨ c)) but in this case a and c always have to be provided
    val hyp3: String = if (PrfaORc == "") nameHypothesis(hCount) else s"($PrfaORc)"
    if (PrfaORc == "") {
      hCount = hCount + 1
      abstractions.append(s"($hyp3 : $Prf($a $lor $c)) ")
    }

    // if we have any abstractions, we need to add lambda:
    val finalAbstrations: String = if (abstractions.toString != "") s"$LPlambda $abstractions , " else ""

    // hypotheses that will never be instanciated
    val hyp4: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val hyp5: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val hyp6: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val bot1: String = nameBottom(bCount)
    bCount = bCount + 1

    // now we want to proof slightly different rules depending on weather only a, only b or both were provided:
    var lambdaTerm: String = ""
    if (b != "") {
      if (d != "") {
        // (Prf a → Prf b) → (Prf c → Prf d) → (Prf(a ∨ c)) → (Prf(b ∨ d))
        lambdaTerm = s"($finalAbstrations$hyp3 ($b ∨ $d) ($LPlambda $hyp4 $bot1 $hyp5 _, $hyp5 ($hyp1 $hyp4)) ($LPlambda $hyp4 $bot1 _ $hyp6, $hyp6 ($hyp2 $hyp4)))"
      } else {
        // (Prf a → Prf b) → (Prf(a ∨ c)) → (Prf(b ∨ c))
        lambdaTerm = s"($finalAbstrations$hyp3 ($b ∨ $c) ($LPlambda $hyp4 $bot1 $hyp5 _, $hyp5 ($hyp1 $hyp4)) ($LPlambda $hyp4 $bot1 _ $hyp6, $hyp6 $hyp4))"
      }
    } else if (d != "") {
      // (Prf c → Prf d) → (Prf(a ∨ c)) → (Prf(a ∨ d))
      lambdaTerm = s"($finalAbstrations$hyp3 ($a ∨ $d) ($LPlambda $hyp4 $bot1 $hyp5 _, $hyp5 $hyp4) ($LPlambda $hyp4 $bot1 _ $hyp6, $hyp6 ($hyp2 $hyp4)))"
    } else {
      throw new Exception(s"fot the application of cOR, neither b nor d were provided")
    }

    (lambdaTerm, (hCount, bCount, parameters._3))
  }


  // given a clause and a sequence of rule applications on the literals, execute these rule applications
  def ruleAppClause(cl0 : Clause, cl1 : Clause, transformations: Seq[String], sig:Signature, parameters0: (Int, Int, Int)):(String,(Int, Int, Int))={
    // todo: universal quantification over free variables -> pass on bVars
    // this function provies a term of type Prf(cl0) -> Prf(cl1)
    // transformations should have the proof as a string for applied rules or "" if the literal was not transformed
    var parameters = parameters0
    if (cl0.lits.length != transformations.length){
      throw new Exception(s"failed to apply rules to clause ${cl0.pretty}, wrong number of rule applications were given")
    }else if (transformations.length >= 2){
      //throw new Exception(s"application of rules to multi-literal clause is implemented but not tested. remove this exception and test carefully")
      val leftLit0: String = clause2LP(Clause(cl0.lits.head), Set.empty, sig)._1
      val leftLit1: String = if (transformations.head != "") clause2LP(Clause(cl1.lits.head), Set.empty, sig)._1 else ""
      val leftLitRule: String = if (transformations.head != "") transformations.head else ""
      val rightLit0: String = clause2LP(Clause(cl0.lits.tail), Set.empty, sig)._1
      val rightLit1: String = if (transformations.tail.forall(_ == "")) clause2LP(Clause(cl1.lits.tail), Set.empty, sig)._1 else ""
      val rightLitRule: String = if (transformations.tail.forall(_ == "")) {
        val (res,newParm) = ruleAppClause(Clause(cl0.lits.tail), Clause(cl1.lits.tail), transformations.tail, sig, parameters)
        parameters = newParm
        res
      } else ""
      if (leftLit1!="" | rightLit1!=""){
        // if rules were applied we want to transform this
        cOR(leftLit0,leftLit1,leftLitRule,rightLit0,rightLit1,rightLitRule,"",parameters)
      }else{
        throw new Exception(s"no rules applied to $cl0, yet runAppClauses was called")
      }
    }else{
      (transformations.head,parameters) // is this correct?
    }
    /*
    while (cl0.lits.length >= 2){
      if (transformations.head != Seq.empty){
        if (transformations.tail.forall(_ == Seq.empty)){
          // rules were applied to both sides, proof left side and instanciate cv
          val ruleApplication = cOR(leftLit0,leftLit1,leftLitRule,rightLit0,rightLit1,rightLitRule)
          val res = s"$"
        }else{
          // rules were only applied to the left side
        }
      }else if (transformations.tail.forall(_ == Seq.empty)){
        // rules were only applied to the right side
      }else{
        // no rules were applied, keep clause as it is
      }
      // remove the head of clauses and transformations
    }
    // process the last literal
     */
  }

  def ruleAppClause_new(transformations: Seq[(String,String,String)], parameters0: (Int, Int, Int)): (String,(Int, Int, Int)) = {
    // todo: universal quantification over free variables -> pass on bVars
    // this function provies a term of type Prf(cl0) -> Prf(cl1)
    // transformations should have the proof as a string for applied rules or "" if the literal was not transformed

    var parameters = parameters0
    //print(s"transformed clauses: ${transformations.map(_._1)}\n")
    //print(s"transformeations to perform: ${transformations.map(_._3)}\n")

    // we step wise construct a multi literal disjunction by looking at one left literal at a time
    if (transformations.length >= 2) {
      //throw new Exception(s"application of rules to multi-literal clause is implemented but not tested. remove this exception and test carefully")
      val leftLit0: String = transformations.head._1
      val leftLit1: String = transformations.head._2
      val leftLitRule: String = if (transformations.head._3 != "") transformations.head._3 else {
        val (selfProof, parametersNew) = selfImp("",parameters)
        parameters = parametersNew
        selfProof
      }
      //print(s"leftLitRule: $leftLitRule\n")
      val restLits0: String = s"(${transformations.tail.map(_._1).mkString(s" $lor ")})"
      val restLits1: String = s"(${transformations.tail.map(_._2).mkString(s" $lor ")})"
      val restLitsRule: String = if (transformations.tail.map(_._3).forall(_ != "")) {
        val (res, newParm) = ruleAppClause_new(transformations.tail, parameters)
        parameters = newParm
        res
      } else {
        val (selfProof, parametersNew) = selfImp("", parameters)
        parameters = parametersNew
        selfProof
      }
      //print(s"rightLitRule: $restLitsRule\n")
      cOR(leftLit0, leftLit1, leftLitRule, restLits0, restLits1, restLitsRule, "", parameters)
    } else {
      (transformations.head._3, parameters) // is this correct?
    }
  }


  def clauseRuleQuantification (parent: Clause, bVarMap: Map[Int, String], sig: Signature):(String,String)={
    val clauseQuantification: StringBuffer = new StringBuffer()
    var applySymbolsToParent: Seq[String] = Seq.empty
    parent.implicitlyBound foreach { name_type =>
      clauseQuantification.append(s"(${bVarMap(name_type._1)}: $Els($uparrow ${type2LP(name_type._2, sig)._1}))")
      applySymbolsToParent = applySymbolsToParent ++ Seq(bVarMap(name_type._1))
    }
    (clauseQuantification.toString,applySymbolsToParent.mkString(" "))
  }
  def encPolaritySwitchLit(l: Literal, bVarMap: Map[Int, String], sig: Signature, parameters: (Int, Int, Int), usedSymbols: Set[String]): (Boolean, String, (Int, Int, Int), Set[String]) = {
    // encode the proofs for the switch rules of the literals
    // like PolaritySwtich.apply in Normalization rules
    // but Insted of using the can apply earlier, i just tested weather I applied anything here!
    // if something was changed I retunr (True,proof), otherwise (False,"")

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val hyp1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val hyp2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val hyp3: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val bot1: String = nameBottom(bCount)
    bCount = bCount + 1
    val bot2: String = nameBottom(bCount)
    bCount = bCount + 1
    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1

    if (l.equational) {
      // todo: test this
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
    } else {
      l.left match {
        case Not(l2) =>
          if (l.polarity) {
            // todo: test
            // in this case the encoded literal does not change
            (false, "", parameters, usedSymbols)
          } else {
            // In this case we need to apply npp in the encoding
            val encLit = term2LP(l2, bVarMap, sig, Set.empty)._1
            (true, s"($npp_name $encLit)", parameters, usedSymbols + npp_name)
            //Literal(l2, !l.polarity)
          }
        case _ => (false, "", parameters, usedSymbols)
      }
    }
  }

  def encPolaritySwitchClause(child: ClauseProxy, parent: ClauseProxy, parentInLpEncID: Long, sig: Signature): (String, (Int, Int, Int), Set[String]) = {
    // like control.switchPolarity

    var parameters: (Int, Int, Int) = (0, 0, 0)
    var usedSymbols: Set[String] = Set.empty

    val parentNameLpEnc = s"step$parentInLpEncID"

    var transformations: Seq[String] = Seq.empty

    val bVarMap = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

    val litsIt = parent.cl.lits.iterator

    while (litsIt.hasNext) {
      val lit = litsIt.next()
      val (wasApplied, ruleProof, parametersNew, usedSymbolsNew) = encPolaritySwitchLit(lit, bVarMap, sig, parameters, usedSymbols)
      if (wasApplied) {
        parameters = parametersNew
        usedSymbols = usedSymbolsNew
        // add the proof to the list of transformations that will be inserted into the proof of the clause application
        transformations = transformations.appended(ruleProof)
      } else {
        // do nothing but add to track
        transformations = transformations.appended("")
      }
    }
    if (transformations.forall(_ == "")) {
      throw new Exception(s"encPolaritySwitchClause was called but polarity was not switched for any literals")
    } else {
      val (encProofRule, newParameters) = ruleAppClause(parent.cl, child.cl, transformations, sig, parameters)
      (s"$encProofRule $parentNameLpEnc", newParameters, usedSymbols)
    }
  }

  def encFuncExtPosLit(l0: Literal, l1: Literal, appliedVars: Seq[String], bVarMap: Map[Int, String], sig: Signature, parameters: (Int, Int, Int)): (Boolean, String, (Int, Int, Int)) = {
    // encode the proofs for the FunExt rules of the literals
    // if something was changed I return (True,proof), otherwise (False,"")

    // [S T : Set] f g a b ... : Prf(eq [↑ (T ⤳ T ⤳ ... ⤳ S)] f g) →  Prf(eq [↑ S] (f a b ...) (g a b ...))

    if (l0.equational & l1.equational){

      if (appliedVars.nonEmpty){
        var xCount = parameters._3
        val x1: String = nameX(xCount)
        xCount = xCount + 1
        val x2: String = nameX(xCount)
        xCount = xCount + 1


        val funcType0 = type2LP(l0.left.ty, sig)._1
        val funcType1 = type2LP(l1.left.ty, sig)._1
        val encRight = term2LP(l0.left, bVarMap, sig)._1
        val encLeft = term2LP(l0.right, bVarMap, sig)._1
        val allAppliedVars = appliedVars.mkString(" ")

         /*
        val funcType0 = "(ι ⤳ o)"
        val funcType1 = "o"
        val encRight = "f2"
        val encLeft = "g2"
        val allAppliedVars = appliedVars.mkString(" ")

          */

        // todo: for polymorphic types I will need to make the instantiation of eq with scheme instead of set possible
        //val lambdaTerm = s"($LPlambda (h1 : $Prf($equ [$uparrow ($funcType0)] $encRight $encLeft)) ($x2: $Els ($uparrow ($funcType1 $HOLarrow $oType))), h1 ($LPlambda $x1, $x2 ($x1 $allAppliedVars)))"
        val lambdaTerm = s"($LPlambda (h1 : $Prf($equ [$uparrow ($funcType0)] $encRight $encLeft)) ($x2: $Els ($uparrow ($funcType1 $HOLarrow $oType))), h1 ($LPlambda $x1, $x2 ($x1 $allAppliedVars)))"

        (true, lambdaTerm, (parameters._1,parameters._2,xCount))
      }else throw new Exception(s"trying to apply FunExt LP encoding but no variables to apply were supplied")

    }else throw new Exception(s"trying to apply FunExt LP encoding but either the parent ${l0.pretty} or the child ${l1.pretty} is not equational")
  }


  def encFuncExtPosClause(child: ClauseProxy, parent: ClauseProxy, editedLiterals: Seq[(Literal,Literal)], parentInLpEncID: Long, sig: Signature): (String, (Int, Int, Int)) = {

    // todo: in some cases the order of the literals is changed by Leo ...
    if (editedLiterals.length > 0){

      val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

      var parameters: (Int, Int, Int) = (0, 0, 0)
      var usedSymbols: Set[String] = Set.empty

      val parentNameLpEnc = s"step$parentInLpEncID"

      // extract the information about the names of the freshly applied variables so they can be universally quantified over
      var allFreshVarsClause: Set[(Int,leo.datastructures.Type)] = Set.empty
      // first we add the variables of the clause itself
      // track the rule applications in order to apply the clauseRuleApplication
      var transformations: Seq[String] = Seq.empty
      val editedLiteralsMap = editedLiterals.toMap
      parent.cl.lits foreach {origLit =>
        val edLit = editedLiteralsMap.getOrElse(origLit,origLit)
        if (edLit != origLit){
          // if the literal has been edited, track the newly applied variables and proof the application of funExt
          val freshVars = edLit.left.fv.diff(origLit.left.fv)
          var appliedVars: Seq[String] = Seq.empty
          freshVars foreach { freshVar =>
            appliedVars = appliedVars :+ bVarMap(freshVar._1)
            allFreshVarsClause = allFreshVarsClause + freshVar
          }
          if (!origLit.polarity) throw new Exception(s"functional extensionality of negative literals not encoded yet")
          else{
            // encode the positive funExt
            val (wasApplied, funExtProofTerm,parametersNew) = encFuncExtPosLit(origLit,edLit,appliedVars,bVarMap,sig,parameters)
            parameters = parametersNew
            transformations = transformations ++ Seq(funExtProofTerm)
          }
        }else{
          // for the literals that were not changed, we simply add "" to the transformations
          transformations = transformations ++ Seq("")
        }
      }

      // use all the new variables to build the string that quantifies over them in LP
      var universalQuantification: StringBuffer = new StringBuffer(s"$LPlambda ")
      allFreshVarsClause foreach { name_type =>
        universalQuantification.append(s"(${bVarMap(name_type._1)}: $Els($uparrow ${type2LP(name_type._2, sig)._1}))")
      }

      // we also need to quantify over the variables that the clause implicitly quantified over and apply them to the previous stps in their application to the rule
      var clauseQuantification: StringBuffer = new StringBuffer()
      var applySymbolsToParent: Seq[String] = Seq.empty
      parent.cl.implicitlyBound foreach{ name_type =>
        clauseQuantification.append(s"(${bVarMap(name_type._1)}: $Els($uparrow ${type2LP(name_type._2, sig)._1}))")
        applySymbolsToParent = applySymbolsToParent ++ Seq(bVarMap(name_type._1))
      }

      if (transformations.length > 1) {
        // this is not implemented but idealy just passing transformations to clauseRulApp (or whatever the function is called) should do the trick
        throw new Exception(s"encFuncExtPosClause not implemented for clauses longer than one literal")
      }
      else{
        (s"${universalQuantification.toString} ${clauseQuantification.toString}, ${transformations.head} ($parentNameLpEnc ${applySymbolsToParent.mkString(" ")})",parameters)
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


  def encBoolExtLit(l0: Literal, version: String, bVarMap: Map[Int, String], sig: Signature, parameters: (Int, Int, Int)): (Boolean, String, (Int, Int, Int)) = {
    // encode the proofs for the FunExt rules of the literals
    // if something was changed I return (True,proof), otherwise (False,"")

    // there are three different version a literal can be transformed with boolExt, these versions correspond to the modes:
    // posL: positve literals with negation on the left side, proof term of type Prf(eq [↑ o] a b) → Prf(a ∨ (¬ b))
    // posR positve literals with negation on the right side, proof term of type Prf(eq [↑ o] a b) → Prf((¬ a) ∨ b)
    // negL ...
    // negR ...

    var xCount = parameters._3
    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1

    val encLeft = term2LP(l0.left, bVarMap, sig)._1
    val encRight = term2LP(l0.right, bVarMap, sig)._1


    //todo: return correct parameters
    // todo: encode lambda terms properly
    if (version == "posL") {
      val lambdaTerm = s"λ (h1 : Prf (eq [↑ o] $encLeft $encRight)), em $encRight ($encLeft ∨ ¬ $encRight) (λ h2 b1 h3 _, h3 (h1 (λ $x1, eq [↑ o] $x1 $encLeft) (λ $x2 h5, h5) (λ $x1, $x1) h2)) (λ h2 b1 _ h4, h4 h2)"
      (true, lambdaTerm, parameters)
    } else if (version == "posR") {
      val lambdaTerm = s"λ (h1 : Prf (eq [↑ o] $encLeft $encRight)), em $encLeft (¬ $encLeft ∨ $encRight) (λ h2 b1 _ h4, h4 (h1 (λ $x1, $x1) h2)) (λ h2 b1 h3 _, h3 h2)"
      //val lambdaTerm = s"λ (h1 : Prf (eq [↑ o] $encLeft $encRight)), em $encRight ($encLeft ∨ ¬ $encRight) (λ h2 b1 h3 _, h3 (h1 (λ $x1, eq [↑ o] $x1 $encLeft) (λ $x2 h5, h5) (λ $x1, $x1) h2)) (λ h2 b1 _ h4, h4 h2)"
      (true, lambdaTerm, parameters)
    } else {
      throw new Exception(s"BoolExt lit version not encoded yet")
    }
  }

  def encBoolExtClause(child: ClauseProxy, parent: ClauseProxy ,parentInLpEncID: Long, sig: Signature): (String, (Int, Int, Int),Set[String]) = {

    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

    var transformations: Seq[String] = Seq.empty

    val parentNameLpEnc = s"step$parentInLpEncID"

    var parameters = (0,0,0)


    // we also need to quantify over the variables that the clause implicitly quantified over and apply them to the previous stps in their application to the rule
    val clauseQuantification: StringBuffer = new StringBuffer()
    var applySymbolsToParent: Seq[String] = Seq.empty
    parent.cl.implicitlyBound foreach { name_type =>
      clauseQuantification.append(s"(${bVarMap(name_type._1)}: $Els($uparrow ${type2LP(name_type._2, sig)._1}))")
      applySymbolsToParent = applySymbolsToParent ++ Seq(bVarMap(name_type._1))
    }


    val editedLits : Seq[Literal] = Seq.empty
    // seq of literals to which a corresponding clause has to be found in parents
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
              throw new Exception(s"mode of BoolExt enc not yet implemented 3")
            }
          }
          if (toDo.containsSlice(possibleRes._2)){
            if (lit.polarity) {
              // Prf(eq [↑ o] a b) → Prf(a ∨ (¬ b))
              val encoding = encBoolExtLit(lit,"posL",bVarMap,sig,parameters)._2
              transformations = transformations :+ encoding
            } else {
              throw new Exception(s"mode of BoolExt enc not yet implemented 3")
            }
          }

        }else throw new Exception(s"no bool Ext applied to value that it should have been applied to: ${term2LP(asTerm(lit),bVarMap,sig)._1}")
      } else{
        transformations = transformations :+ ""
      }
      // first test if the literal was edited or is also in child
    }

    if (transformations.length > 1) {
      // this is not implemented but idealy just passing transformations to clauseRulApp (or whatever the function is called) should do the trick
      throw new Exception(s"encBoolExtClause not implemented for clauses longer than one literal")
    }
    else {
      (s"($LPlambda ${clauseQuantification.toString}, (${transformations.head}) ($parentNameLpEnc ${applySymbolsToParent.mkString(" ")}))", parameters, Set("em"))//todo: add em axiom
    }

    // todo: in some cases the order of the literals is changed by Leo ...


  }

  def encEqFactNegInst(T:String, otherLit_l:String, otherLit_r:String, maxLit_l: String, maxLit_r: String, parameters: (Int, Int, Int)):(String,(Int, Int, Int),Set[String])={
    // for now I just use the symbol instead of the lambda term:
    //todo: Instanciate actual lambda Term
    //todo: return parameters and used symbols
    val eqFactNegDef: String = s"Π [T: Scheme], Π x: Els T, Π y: Els T, Π z: Els T, Π v: Els T, Prf (¬ (eq x y) ∨ ¬ (eq z v)) → Prf (¬ (eq x y) ∨ (¬ (eq x z) ∨ ¬ (eq y v)))"
    val eqFactNegName: String = "eqFactNeg"
    val lambdaTerm = s"($eqFactNegName [$uparrow $T] $otherLit_l $otherLit_r $maxLit_l $maxLit_r)"
    ((lambdaTerm, parameters,Set.empty))
  }

  def encEqFactPosInst(T: String, otherLit_l: String, otherLit_r: String, maxLit_l: String, maxLit_r: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // for now I just use the symbol instead of the lambda term:
    //todo: Instanciate actual lambda Term
    //todo: return parameters and used symbols
    val eqFactNegDef: String = s""
    val eqFactName: String = "eqFactPos"
    val lambdaTerm = s"($eqFactName [$uparrow $T] $otherLit_l $otherLit_r $maxLit_l $maxLit_r)"
    ((lambdaTerm, parameters, Set.empty))
  }
  def encEqFactLiterals(otherLit:Literal, maxLit: Literal, uc1Orig: Literal, cv2Orig: Literal,  bVarMap: Map[Int, String], sig: Signature, parameters0: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {

    // todo: I think many questions would be solved by just getting the other lit that was returned, do eqfactoring according to it and change polarity of literals accordingly

    // todo: somehow use the original unification constraints to dermine the polarity, the order etc.
    var parameters = parameters0
    var usedSymbols: Set[String] = Set.empty

    // the values that we will pass on to the instanciation of the actual rule will be defined during this step
    var otherLit_l = ""
    var otherLit_r = ""
    var maxLit_l = ""
    var maxLit_r = ""

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
    var transformations_step1: Seq[(String, String, String)] = Seq.empty
    var transformations_step2: Seq[(String, String, String)] = Seq.empty
    var otherLitAsEq: String = ""
    var maxLitAsEq: String = ""
    var encStep1 = ""

    val encodedOtherLit = term2LP(asTerm(otherLit), bVarMap, sig)._1
    val encodedMaxLit = term2LP(asTerm(maxLit), bVarMap, sig)._1
    val encParent = s"($encodedOtherLit $lor $encodedMaxLit)"

    val polarityOfRule = maxLit.polarity //todo: instead make it polyrity of other lits after rule application

    if (!otherLit.equational | !maxLit.equational) { // todo make a function that just takes the literals and the desired polarity and makes them equational
      // we detect the polarity of the max literal to make sure the other Literal shares it

      // we first adjust the polarity of the other lit and make it equational if necessary
      if (!otherLit.equational){
        if (!(otherLit.polarity == polarityOfRule)){
          if(otherLit.polarity){
            // we need to make it negative!
            // apply the translation rule
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
          }else {
            // neg Prop pos Lit
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
      }else{
        // case where it is equatinal, just instanciate with equality
        throw new Exception(s"EqFactoring for positive polarity not encoded yet 3")
      }

      // MAX LIT
      if (!maxLit.equational){
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
      }else{
        // only do identity
        // todo
        throw new Exception(s"EqFactoring for positive polarity not encoded yet 7")
      }

      //print(s"the transformations: $transformations_step1\n")
      val (encStep1_0, parametersNew) = ruleAppClause_new(transformations_step1, parameters)
      encStep1 = encStep1_0
      parameters = parametersNew
      //print(s"encoded step: $encStep1\n")
    } else {
      // if both literals are equational we can simply encode the left and right side
      otherLit_l = term2LP(otherLit.left, bVarMap, sig)._1
      otherLit_r = term2LP(otherLit.right, bVarMap, sig)._1
      maxLit_l = term2LP(maxLit.left, bVarMap, sig)._1
      maxLit_r = term2LP(maxLit.right, bVarMap, sig)._1
      // todo: What to do if i neednt encode the clauses?
    }

    /*
    if (!otherLit.equational | !maxLit.equational){
      // we detect the polarity of the max literal to make sure the other Literal shares it
      if (maxLit.polarity) {
        if (otherLit.polarity){ //todo: I think this can also result in negative factoring depending on what is the flax head, test this!
          // case where the max lit is positive but factoring is negative

        }else{
          //positive polarity
          throw new Exception(s"EqFactoring for positive polarity not encoded yet 1")
        }
      } else {
        // negative polarity

        // ENCODING OTHERLIT (leave this first since these are the first literals that have to be encoded)
        // check if the other literal is equational, otherwise we need to encode it as equational
        if (!otherLit.equational) {

          // check if the other Lit has the right polarity, if not we encode other literal a as ¬(¬ a = ⊤)
          if (otherLit.polarity) {
            // apply the translation rule
            val (transf, parametersNew, usedSymbolsNew) = mkPosPropNegLit(encodedOtherLit, parameters)
            parameters = parametersNew
            usedSymbols = usedSymbolsNew
            // define variables to use for the instanciation of the rule
            polarity0 = Some(false)
            otherLit_l = s"($lnot $encodedOtherLit)"
            otherLit_r = HOLtop
            otherLitAsEq = s"($lnot($equ [$uparrow o] ($lnot $encodedOtherLit) $HOLtop))"
            transformations_step1 = transformations_step1 :+ (encodedOtherLit,otherLitAsEq,transf)
            // we will need to transverse the translation of the other literal later on, since the other literal remains part of the clause unchanged.
            // for this we can already construct the rule using the information derived here
            val (transfBack, parametersNewBack, usedSymbolsNewBack) = mkNegLitPosProp(encodedOtherLit, parameters)
            parameters = parametersNewBack
            usedSymbols = usedSymbolsNewBack
            transformations_step2 = transformations_step2 :+ (s"($lnot($equ [$uparrow o] ($lnot $encodedOtherLit) $HOLtop))",encodedOtherLit,transfBack)
          } else {
            throw new Exception(s"EqFactoring for positive polarity not encoded yet 5")
          }
        } else {
          throw new Exception(s"this version of Eq factoring is only half heartedly encoded, i think i will need to provide self im proofs here")
          transformations_step1 = transformations_step1 :+ (encodedOtherLit,encodedOtherLit,"")
          // if we did not encode the oher literal, we also will not need to to transform it back later:
          transformations_step2 = transformations_step2 :+ (encodedOtherLit,encodedOtherLit,"")
          otherLitAsEq = encodedOtherLit
        }

        // ENCODING MAXLIT
        // check if the max literal is equational and thus has to be transformed
        if (!maxLit.equational){
          asTerm(maxLit) match{
            case Not(t) =>
              val encodedMaxLitPos = term2LP(t, bVarMap, sig)._1
              val (transf, parametersNew, usedSymbolsNew) = mkNegPropNegLit(encodedMaxLitPos, parameters)
              parameters = parametersNew
              usedSymbols = usedSymbolsNew
              // define variables to use for the instanciation of the rule
              maxLit_l = encodedMaxLitPos
              maxLit_r = HOLtop
              maxLitAsEq = s"($lnot($equ [$uparrow o] $encodedMaxLitPos $HOLtop))"
              transformations_step1 = transformations_step1 :+ (encodedMaxLit,maxLitAsEq,transf)
            case _ => throw new Exception(s"when trying to encode EqFact, max lit with wrong form was found")
          }
        }else {
          throw new Exception(s"this version of Eq factoring is only half heartedly encoded, i think i might have to change polarity here?")
          maxLitAsEq = encodedMaxLit
          transformations_step1 = transformations_step1 :+ (encodedMaxLit,encodedMaxLit,"")
        }
      }
      //print(s"the transformations: $transformations_step1\n")
      val (encStep1_0,parametersNew) = ruleAppClause_new(transformations_step1,parameters)
      encStep1 = encStep1_0
      parameters = parametersNew
      //print(s"encoded step: $encStep1\n")
    } else {
      polarity0 = if (otherLit.polarity == maxLit.polarity) Some(otherLit.polarity) else throw new Exception(s"trying to apply EqFact encoding to two equality literals with different polarity")
      // if both literals are equational we can simply encode the left and right side
      otherLit_l = term2LP(otherLit.left,bVarMap,sig)._1
      otherLit_r = term2LP(otherLit.right,bVarMap,sig)._1
      maxLit_l = term2LP(maxLit.left,bVarMap,sig)._1
      maxLit_r = term2LP(maxLit.right,bVarMap,sig)._1
      // todo: What to do if i neednt encode the clauses?
    }
    */


    // STEP 2: actually apply the equal factoring
    var encStep2 = ""
    // define the strings we use to instanciate the rules
    val ty = if(maxLit.equational) maxLit.left.ty else asTerm(maxLit).ty //todo: check if all have same type and throw error otherwise
    val encType = type2LP(ty, sig)._1
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
    var uc1 = ""
    var uc1Final = ""
    var uc2 = ""
    var uc2Eq = ""
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
        uc1 = s"($lnot($equ [$uparrow o] $otherLit_l $maxLit_l))"
        uc1Final = uc1
        val (uc1Rule, parametersNewUc1) = selfImp(uc1, parameters)
        parameters = parametersNewUc1
        transformations_step2 = transformations_step2 :+ (uc1, uc1, uc1Rule)
      }else if ((otherLitL == uc1Orig.right)|(Not(otherLitL) == uc1Orig.right)|(otherLitL == Not(uc1Orig.right))){
        // the order was changed, we need to "stack" the rule for the change of the order here too
        // apply the two sides of the literal to the proof of equational commutativity
        val (uc1Rule, parametersNewUc1) = inEqCom(s"($uparrow o)",otherLit_l,maxLit_l,parameters)
        parameters = parametersNewUc1
        // now we define what uc1 looks like before and after:
        uc1 = s"($lnot($equ [$uparrow o] $otherLit_l $maxLit_l))"
        uc1Final = s"($lnot($equ [$uparrow o] $maxLit_l $otherLit_l))"
        transformations_step2 = transformations_step2 :+ (uc1, uc1Final, uc1Rule)
        //print(s"symbol changeOrder : Prf($uc1) $rightarrow Prf($uc1Final) $colonEq \n$uc1Rule;\n")
      }else throw new Exception(s"the first unification constraint encoded in LP encoding does not match the one derived by Leo")


      // the second unification constraint is non equational - and thus requires a backwards encoding - iff the max literals were non equational
      //todo : check weather order has to be changed here too!
      if (maxLit_r == HOLtop) {
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
        uc2Eq = s"($lnot($equ [$uparrow $oType] $otherLit_r $otherLit_r))"
        uc2 = s"($lnot $otherLit_r)"
        parameters = parametersNewUc2
        usedSymbols = usedSymbolsNewUc2
        transformations_step2 = transformations_step2 :+ (uc2Eq,uc2,uc2_rule)

      } else if (otherLit_l == HOLtop) {
        throw new Exception(s"Eq factoring with non equational maxLit and equational other lits! Check how this needs to be backwards encoded after rule application!")
      } else {
        // no backwards encoding necessary because both literals were equational!
        uc2 = s"($lnot($equ [$uparrow o] $otherLit_l $otherLit_r))"
        uc2Eq = uc2
        val (selfImpUc2, parametersNewUc2) = selfImp(uc2, parameters)
        parameters = parametersNewUc2
        transformations_step2 = transformations_step2 :+ (uc2, uc2, selfImpUc2)
      }

      // combine into one rule for the backwards encoding:
      val (encStep3,parametersNewBack) = ruleAppClause_new(transformations_step2,parameters)
      parameters = parametersNewBack

      //print(s"back enc. : $encStep3\n")

      // combine all of the above steps into the overall lambda Term!
      val afterStep1 = s"($otherLitAsEq $lor $maxLitAsEq)"
      val afterStep2 = s"($otherLitAsEq $lor $uc1 $lor $uc2Eq)"
      val encChild = s"($encodedOtherLit $lor $uc1Final $lor $uc2)"
      val (allSteps, parametersNew4, usedSymbolsNew4) = impTrans4(encParent, afterStep1, afterStep2, encChild, encStep1, encStep2, encStep3, parameters)
      parameters = parametersNew4
      usedSymbols = usedSymbolsNew4

      /*
      print(s"symbol EqFact_step1 : Prf($encParent) $rightarrow Prf($afterStep1) $colonEq \n$encStep1;\n")
      print(s"symbol EqFact_step2 : Prf($afterStep1) $rightarrow Prf($afterStep2) $colonEq \n$encStep2;\n")
      print(s"symbol EqFact_step3 : Prf($afterStep2) $rightarrow Prf($encChild) $colonEq \n$encStep3;\n")
      print(s"everyting put together: $allSteps\n\n")

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

  def encEqFactClause(child: ClauseProxy, parent: ClauseProxy, additionalInfo: (Literal, Literal, Literal, Literal, Boolean, Boolean), parentInLpEncID: Long, sig: Signature): (String, (Int, Int, Int), Set[String]) = {

    // todo: outsource the transformation to equality literals?
    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

    val parentNameLpEnc = s"step$parentInLpEncID"

    val transformations: Seq[(String, String, String)] = Seq.empty

    var parameters = (0, 0, 0)

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

      val lambdaTerm = s"($LPlambda $clauseQuantification, ($encFactoring) ($parentNameLpEnc $applySymbolsToParent))"

      (lambdaTerm, parametersNew, usedSymbolsNew)
    } else {
      throw new Exception(s"eqFacoring with more literal besides the max and the other lit not encoded yet")
    }

  }



}
