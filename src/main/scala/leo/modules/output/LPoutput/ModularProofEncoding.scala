package leo.modules.output.LPoutput
import leo.Out
import leo.datastructures.Literal.{asTerm, mkLit}
import leo.modules.output.LPoutput.Encodings._
import leo.datastructures.{Clause, ClauseProxy, Literal, Signature, Term}
import leo.modules.HOLSignature._
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.AccessoryRules._
import leo.modules.output.LPoutput.lpInferenceRuleEncoding._
import leo.modules.output.LPoutput.SimplificationEncoding._

import scala.collection.mutable

/** Modular encoding of proofs
  *
  * @author Melanie Taprogge
  */

object ModularProofEncoding {

  ////////////////////////////////////////////////////////////////
  ////////// Additional Leo-III Inferences
  ////////////////////////////////////////////////////////////////

  def encPolaritySwitch(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Set[lpStatement]) = {

    val bVarMap = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    var allRewriteSteps: Seq[lpProofScriptStep] = Seq.empty
    var polaritySwitchCount: Int = 0

    // The modular proof script can consist of the following steps:
    // 1. Abstract over free variables
    // 2. Apply polarity switch to the literals of the parent if applicable
    //    a) Transform (¬ a) = (¬ b) ---> a = b
    //        i)  Define an equality term to rewrite (¬ a) = (¬ b) to a = b using the have tactic
    //        iI) Rewrite the literal
    //    b) Transform (¬ ¬ a) ---> a
    //        i)  Define an equality term to rewrite (¬ ¬ a) to a using the have tactic
    //        iI) Rewrite the literal
    // 3. Apply the variables we abstracted over to the parent clause and refine with it

    // 1. Abstract over free variables
    val freeVarsChild = child.cl.implicitlyBound.map(var0 => lpUntypedVar(lpConstantTerm(bVarMap(var0._1))))
    if (freeVarsChild.nonEmpty) allSteps = allSteps :+ lpAssume(freeVarsChild)

    // 2. Apply polarity switch to the literals of the parent if applicable
    parent.cl.lits foreach { origLit =>
      if (origLit.equational){
        (origLit.left, origLit.right) match{
          case (Not(l),Not(r)) => // case a) Transform (¬ a) = (¬ b) ---> a = b

            val encLeft = term2LP(l,bVarMap,sig)._1
            val encRight = term2LP(r,bVarMap,sig)._1
            val transfLit = Literal.apply(l,r,origLit.polarity)

            // i)  Define an equality term to rewrite (¬ a) = (¬ b) to a = b using the have tactic
            val equalityToProve = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,encLeft,encRight),term2LP(asTerm(origLit),bVarMap,sig)._1)
            val polaritySwitchStep = lpRefine(polaritySwitchEqLit.instanciate(encLeft,encRight))
            val polaritySwitchName = s"PolaritySwitch_$polaritySwitchCount"
            polaritySwitchCount = polaritySwitchCount + 1
            val havePolaritySwitchStep = lpHave(polaritySwitchName,equalityToProve.prf,lpProofScript(Seq(polaritySwitchStep)))
            allSteps = allSteps :+ havePolaritySwitchStep
            usedSymbols = usedSymbols + polaritySwitchEqLit

            // ii) Rewrite the Literal
            val posInClause = findLitInClause(transfLit,child.cl)
            val patternVar = lpOlUntypedVar(lpOlConstantTerm("x"))
            val rewritePattern = generateClausePatternTerm(posInClause,child.cl.lits.length,None,patternVar)
            val rewriteStep = lpRewrite(rewritePattern,lpConstantTerm(polaritySwitchName))
            allRewriteSteps = allRewriteSteps :+ rewriteStep

          case _ => // nothing happens in this case
        }

      }else if (!origLit.polarity)
        origLit.left match {
        case Not(l) => // case b) Transform (¬ ¬ a) ---> a

          val encLeft = term2LP(l, bVarMap, sig)._1
          val transfLit = Literal.apply(l, true)

          // i)  Define an equality term to rewrite (¬ ¬ a) to a using the have tactic
          val equalityToProve = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, encLeft, lpOlUnaryConnectiveTerm(lpNot,lpOlUnaryConnectiveTerm(lpNot,encLeft)))
          val polaritySwitchStep = lpRefine(Simp17_eq.instanciate(encLeft))
          val polaritySwitchName = s"PolaritySwitch$polaritySwitchCount"
          polaritySwitchCount = polaritySwitchCount + 1
          val havepolaritySwitchStep = lpHave(polaritySwitchName, equalityToProve.prf, lpProofScript(Seq(polaritySwitchStep)))
          allSteps = allSteps :+ havepolaritySwitchStep
          usedSymbols = usedSymbols + Simp17_eq

          // ii) Rewrite the Literal
          val posInClause = findLitInClause(transfLit, child.cl)
          val rewritePattern = generateClausePatternTerm(posInClause, child.cl.lits.length, None)
          val rewriteStep = lpRewrite(rewritePattern, lpConstantTerm(polaritySwitchName))
          allRewriteSteps = allRewriteSteps :+ rewriteStep

        case _ => // nothing happens in this case
      }
    }
    allSteps = allSteps ++ allRewriteSteps

    // 3. Apply the variables we abstracted over to the parent clause and refine with it
    allSteps = allSteps :+ lpRefine(lpFunctionApp(parentNameLpEnc, freeVarsChild))

    (lpProofScript(allSteps), usedSymbols)
    }

  def encDefExSimp(child: ClauseProxy, parent: ClauseProxy, additionalInfoSimp: Seq[(Seq[Int], String, Term, Term)], additionalInfoDefExp: Seq[Signature.Key], parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Set[lpStatement], Set[Signature.Key], Option[String]) = {

    // outdated
    // todo: update this function to proof scripts

    val wasSimplified: Boolean = additionalInfoSimp.nonEmpty
    print(s"\n\n WAS SIMPLIFIED: $wasSimplified \n\n")
    if (wasSimplified) (lpProofScript(Seq.empty),Set.empty,Set.empty,Option("encDefExSimp encoding outdated"))
    else {
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
      if (wasSimplified) {
        val (simpProof, usedSymbolsSimplification) = simplificationProofScript(child.cl, parent.cl, additionalInfoSimp, additionalInfoDefExp.toSet, parentNameLpEnc, quantifiedVars, bVars, sig)
        usedSymbols = usedSymbols ++ usedSymbolsSimplification
        if (parent.cl.lits.length != child.cl.lits.length) throw new Exception(s"when simplifying to ${encSimpChild.pretty} a literal was deleted, this is not yet encoded")

        allProofStep = allProofStep :+ simpProof
      }

      // combine all steps into one proof script
      val proofScript = lpProofScript(allProofStep)

      (proofScript, usedSymbols, additionalInfoDefExp.toSet, Option("encDefExSimp encoding outdated"))
    }
  }


  ////////////////////////////////////////////////////////////////
  ////////// Extensionality
  ////////////////////////////////////////////////////////////////

  def encFuncExtPos(child: ClauseProxy, parent: ClauseProxy, editedLiterals: Seq[(Literal, Literal)], parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Set[lpStatement], Option[String]) = {

    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    var usedSymbols: Set[lpStatement] = Set.empty
    var editLitCount = 0

    if (editedLiterals.length > 0) {

      val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

      // The modular proof script can consist of the following steps:
      // 1. Abstract over free variables
      // For each affected literal:
      //    2. If the order within the literal was changed, apply eqSym_eq
      //    3. Instantiate PFE and use it to define a new hypothesis (in the case of a nested application, use impTrans)
      // 4. Use the proven hypothesis to apply the changes to the (instantiated) parent formula, using the appropriate transform rule
      // 5. If the order of literals was changed, generate a permute rule and apply it to permute the literals
      // 6. Refine with the last step

      // 1. Abstract over free variables
      val freeVarsChild = child.cl.implicitlyBound.map(var0 => lpUntypedVar(lpConstantTerm(bVarMap(var0._1))))
      if (freeVarsChild.nonEmpty) allSteps = allSteps :+ lpAssume(freeVarsChild)

      val editedLiteralsMap = editedLiterals.toMap
      var litsAfterFunext: Seq[lpOlTerm] = Seq.empty
      parent.cl.lits foreach { origLit =>
        val edLit = editedLiteralsMap.getOrElse(origLit, origLit)
        val encEditLit = term2LP(asTerm(edLit), bVarMap, sig)._1
        litsAfterFunext = litsAfterFunext :+ encEditLit
        if (edLit != origLit) {

          // 2. If the order within the literal was changed, apply eqSym_eq
          // todo

          // 3. Instantiate PFE and use it to define a new hypothesis
          val namefunExtStep = s"${funExtPosEq_rev().name.pretty}_$editLitCount"
          editLitCount = editLitCount + 1
          // Construction the equality to be proved
          val encOrigLitLhs = term2LP(origLit.left, bVarMap, sig)._1
          val encOrigLitRhs = term2LP(origLit.right, bVarMap, sig)._1
          val encOrigLit = term2LP(asTerm(origLit), bVarMap, sig)._1
          val impToProve = lpMlFunctionType(Seq(encOrigLit.prf,encEditLit.prf))
          // Construction the proof
          // Track the newly applied variables and proof the application of funExt
          val freshVars = edLit.fv.diff(origLit.fv)
          var appliedVars: Seq[lpOlUntypedVar] = Seq.empty
          freshVars foreach { freshVar =>
            appliedVars = appliedVars :+ lpOlUntypedVar(lpOlConstantTerm(bVarMap(freshVar._1)))
          }
          // todo: nested application of funext in cases with more than two applied symbols
          if (appliedVars.length != 1) throw new Exception(s"The LP encoding of FunExt (for positive literals) is not implemented for the application of more than one argument yet")
          val refineWithFunExt = {
            if (!origLit.polarity) throw new Exception(s"The LP encoding of FunExt for negative literals is not implemented yet")
            else {
              usedSymbols = usedSymbols + funExtPosEq_rev()
              lpRefine(funExtPosEq_rev().instanciate(None, encOrigLitLhs, encOrigLitRhs, appliedVars))
            }
          }
          allSteps = allSteps :+ lpHave(namefunExtStep, impToProve, lpProofScript(Seq(refineWithFunExt)))
          Out.lp_debug_info(s"Proving instancion of PFE: ${lpHave(namefunExtStep, impToProve, lpProofScript(Seq(refineWithFunExt))).pretty}")
        }
      }

      // 4. Use the proven hypothesis to apply the changes to the (instanciated) parent formula, using the appropriate transform rule
      val applicationStepName = "FunExtApplication"
      val impBoundParent = parent.cl.implicitlyBound.map(var0 => lpUntypedVar(lpConstantTerm(bVarMap(var0._1))))
      if (editedLiterals.length > 1) {
      throw new Exception("The LP encoding of FunExt (for positive literals) is not implemented for cases where multiple literals were edited yet")
      //allSteps = allSteps :+ lpHave(applicationStepName,)
      // combine the individual hypothesis with transform
      }
      else {
        val refineWithFunExt0 = lpRefine(lpFunctionApp(lpConstantTerm(s"${funExtPosEq_rev().name.pretty}_0"),Seq(lpFunctionApp(parentNameLpEnc, impBoundParent))))
        allSteps = allSteps :+ lpHave(applicationStepName,lpOlUntypedBinaryConnectiveTerm_multi(lpOr,litsAfterFunext).prf,lpProofScript(Seq(refineWithFunExt0)))
      }

      // 5. If the order of literals was changed, generate a permute rule and apply it to permute the literals
      // todo
      val lastStep = applicationStepName

      // 6. Refine with the (instantiated) parent
      // We can not necessarily refine the parent with the assumed variables since we may have introduced new variables in the child
      // Instead we detect the unbound variables of the parent to refine with them
      allSteps = allSteps :+ lpRefine(lpFunctionApp(lpConstantTerm(lastStep),Seq()))
    }
    if (editLitCount == 0) (lpProofScript(allSteps),usedSymbols, Some("FunExt with Top on one side not encoded yet"))
    else (lpProofScript(allSteps),usedSymbols, None)
  }

  def encBoolExt(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, addInfo: Set[(Literal,Seq[Literal])], sig: Signature): (lpProofScript, Set[lpStatement]) = {

    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty

    // The modular proof script can consist of the following steps:
    // 1. Abstract over free variables
    // For each affected literal:
    //    2. Choose the correct encoding ( PBE l , PBE r , NBE p or NBE n ) and instantiate it and use it to define a new hypothesis
    // 3. Prove the application of the rules using the necessary accessory transform rule
    // 4. If the rules resulted in double occurrences of literals, proof the removal using the necessary delete rule
    // 5. If the order of literals was changed, generate a transform rule and apply it to permute the literals
    // 6. Refine with the last proven step

    // 1. Abstract over free variables
    val freeVarsChild = child.cl.implicitlyBound.map(var0 => lpUntypedVar(lpConstantTerm(bVarMap(var0._1))))
    if (freeVarsChild.nonEmpty) allSteps = allSteps :+ lpAssume(freeVarsChild)

    // For each affected literal we need to choose the correct encoding ( PBE l , PBE r , NBE p or NBE n ) and instantiate it and use it to define a new hypothesis
    // Therefore we find out what literals of the parent were transformed to what literals in the child
    var transitions: Seq[lpFunctionApp] = Seq.empty
    addInfo foreach{ info =>
      val (before,afterLhs,afterRhs) = (info._1, info._2(0),info._2(1))
      val beforeLhsEnc =  term2LP(info._1.left,bVarMap,sig)._1
      val beforeRhsEnc =  term2LP(info._1.right,bVarMap,sig)._1
      // Prove this transition
      // There are four possible results of the application of the bool-Ext rule so we first need to identify the applied version:
      // The literal we are encoding can either be of positive or of negative polarity...
      val (lhs,pol): (Boolean,Boolean) = if (before.polarity){
        // -> for positive polarity: The a literal of the form a = b is transformed to (¬ a ∨ b) or (a ∨ ¬ b)
        if (!afterLhs.polarity & afterRhs.polarity) (true,true)
        else if (afterLhs.polarity & !afterRhs.polarity) (false,true)
        else throw new Exception(s"attempting to encode boolExt in lp but found wrong format")
      }else{
        // -> for negative polarity: The a literal of the form ¬ (a = b) is transformed to (¬ a ∨ ¬ b) or (a ∨ b)
        if (afterLhs.polarity & afterRhs.polarity) (true, false)
        else if (!afterLhs.polarity & !afterRhs.polarity) (false, false)
        else throw new Exception(s"attempting to encode boolExt in lp but found wrong format")
      }
      usedSymbols = usedSymbols + lpInferenceRuleEncoding.boolExt(lhs,pol)
      transitions = transitions :+ lpInferenceRuleEncoding.boolExt(lhs,pol).instanciate(beforeLhsEnc,beforeRhsEnc)
    }

    // 3. Prove the application of the rules using the necessary accessory transform rule
    // todo

    // 4. If the rules resulted in double occurrences of literals, proof the removal using the necessary delete rule
    // todo

    // 5. If the order of literals was changed, generate a transform rule and apply it to permute the literals
    // todo

    if (parent.cl.lits.length > 1) throw new Exception(s"Encoding of boolExt in LP for clauses with more than one literal not encoded yet")
    else allSteps = allSteps :+ lpRefine(lpFunctionApp(transitions.head, Seq(lpFunctionApp(parentNameLpEnc, freeVarsChild))))
    val proof = lpProofScript(allSteps)

    // 6. Refine with the last proven step
    (proof,usedSymbols)
  }


  ////////////////////////////////////////////////////////////////
  ////////// Primary Inference Rules
  ////////////////////////////////////////////////////////////////

  def encEqFactLiterals(otherLit: Literal, maxLit: Literal, uc1Orig: Literal, cv2Orig: Literal, parent: Clause, child: Clause, bVarMap: Map[Int, String], sourceBefore: lpTerm, nameStep: lpOlTerm, sig: Signature): (lpProofScriptStep, Set[lpStatement]) = {

    var lastStepName: lpTerm = sourceBefore
    var lastStepLits: Seq[lpOlTerm] = Seq.empty
    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty

    // todo: all this should happen when processing the clause! change before generalizing to longer clauses
    val otherLitEnc = term2LP(asTerm(otherLit),bVarMap,sig)._1
    val maxLitEnc = term2LP(asTerm(maxLit),bVarMap,sig)._1
    val parentEnc = clause2LP(parent,Set.empty,sig)._1

    // the values that we will pass on to the instantiation of the actual rule will be defined during this step and only need to be instantiated here
    var otherLit_l: lpOlTerm = lpOlNothing
    var otherLit_r: lpOlTerm = lpOlNothing
    var maxLit_l: lpOlTerm = lpOlNothing
    var maxLit_r: lpOlTerm = lpOlNothing

    // Identify the two literals to be unified and compose a function proving the rule application including all necessary transformations:
    //    a) If the order of the left- and right-hand sides in either of the literals has to changed in order for the encoded equal factoring rule to associate the sides correctly, apply eqSym_eq
    //    b) If either of the literals is not equational, transform to the equational form with the correct polarity
    //    c) Apply the appropriate version of equal factoring (EqFact_p or EqFact_n)
    //    d) Prove the transformation to non-equational literals of any literals that are non-equational
    //    e) If the order within any of the equality literals has changed after the rule application as a result of the term ordering, proof the transformation using eqSym_eq
    //    f) If the order within any of the equality literals has changed after the rule application as a result of the term ordering, proof the transformation using eqSym_eq

    // several steps are necessary for the encoding:
    // 1. if some of the literals are not equational, we first need to proof the transition to the equational case
    // 2. in this notation we can proof the equal factoring
    // 3. We proof the transition back to the non-equational case

    // a) If the order of the left -and right -hand sides in either of the literals has to changed in order for the encoded equal factoring rule to associate the sides correctly, apply eqSym_eq
    // todo

    // b) If either of the literals is not equational, transform to the equational form with the correct polarity
    var otherLitAsEq: lpOlTerm = lpOlNothing
    var maxLitAsEq: lpOlTerm = lpOlNothing
    var literalsToTransform: Seq[lpOlTerm] = Seq.empty
    var literalsToTransform2: Seq[lpOlTerm] = Seq.empty
    // We detect the polarity of the max literal to make sure the other Literal shares it
    val polarityOfRule = maxLit.polarity
    if (!otherLit.equational | !maxLit.equational) {
      // We first check weather we need to adjust the polarity of the literals and make them equational
      val transformOtherLit: Boolean = if (!otherLit.equational) {
        literalsToTransform = literalsToTransform :+ otherLitEnc
        true
      }else false
      val transformMaxLit: Boolean = if (!maxLit.equational) {
        literalsToTransform = literalsToTransform :+ maxLitEnc
        true
      }else false
      // Then the actual transformation is encoded
      if (literalsToTransform.nonEmpty) {
        val nameTransfStep = lpConstantTerm("TransformToEqLits")
        val (transformationStep,litMap,_,usedSymbolsNew) = makeLiteralEquational_proofSkript(literalsToTransform,parentEnc,lastStepName,true,polarityOfRule,nameTransfStep)
        allSteps = allSteps :+ transformationStep
        lastStepName = nameTransfStep
        if (transformOtherLit){
          val otherLitTrans = litMap(otherLitEnc)
          otherLitAsEq = otherLitTrans._1
          otherLit_l = otherLitTrans._2
          otherLit_r = otherLitTrans._3
          usedSymbols = usedSymbolsNew
          literalsToTransform2 = literalsToTransform2 :+ otherLitAsEq
        } else{
          otherLitAsEq = otherLitEnc
          otherLit_l = term2LP(otherLit.left,bVarMap,sig)._1
          otherLit_r = term2LP(otherLit.right,bVarMap,sig)._1
        }
        if (transformMaxLit) {
          val maxLitTrans = litMap(maxLitEnc)
          maxLitAsEq = maxLitTrans._1
          maxLit_l = maxLitTrans._2
          maxLit_r = maxLitTrans._3
          usedSymbols = usedSymbolsNew
        } else {
          maxLitAsEq = otherLitEnc
          maxLit_l = term2LP(maxLit.left, bVarMap, sig)._1
          maxLit_r = term2LP(maxLit.right, bVarMap, sig)._1
        }
      }else throw new Exception("In the LP encoding of EqFact, non-equational literlas were detected but no transformation to equality literals could be performed")
    } else {
      otherLitAsEq = otherLitEnc
      otherLit_l = term2LP(otherLit.left, bVarMap, sig)._1
      otherLit_r = term2LP(otherLit.right, bVarMap, sig)._1
      maxLitAsEq = otherLitEnc
      maxLit_l = term2LP(maxLit.left, bVarMap, sig)._1
      maxLit_r = term2LP(maxLit.right, bVarMap, sig)._1
    }

    // c) Apply the appropriate version of equal factoring (EqFact_p or EqFact_n)
    val ty = if (maxLit.equational) maxLit.left.ty else asTerm(maxLit).ty
    val encType = type2LP(ty, sig)._1
    val encEqFact : lpTerm = lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule).instanciate(otherLit_l, otherLit_r, maxLit_l, maxLit_r,encType.lift2Poly)
    lastStepLits = lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule).result(otherLit_l, otherLit_r, maxLit_l, maxLit_r,encType.lift2Poly)
    val afterEqFacAp : lpMlType = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,lastStepLits).prf
    usedSymbols = usedSymbols + lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule)
    val nameEqFactoringStep = lpConstantTerm("EqFact")
    val eqFactStep = lpHave(nameEqFactoringStep.name,afterEqFacAp,lpProofScript(Seq(lpRefine(lpFunctionApp(encEqFact,Seq(lastStepName))))))
    allSteps = allSteps :+ eqFactStep
    lastStepName = nameEqFactoringStep

    // d) Prove the transformation to non-equational literals if applicable
    var uc1: lpOlTerm = lpOlNothing
    var uc1Final: lpOlTerm = lpOlNothing
    var uc2: lpOlTerm = lpOlNothing
    var uc2Eq: lpOlTerm = lpOlNothing

    // e) If the order within any of the equality literals has changed after the rule application as a result of the term ordering, proof the transformation using eqSym_eq
    val otherLitL = if (otherLit.equational) otherLit.left else asTerm(otherLit)
    if (otherLitL == uc1Orig.left) {
      // In this case, the order is already correct
      uc1 = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, otherLit_l, maxLit_r))
      uc1Final = uc1
    } else if ((otherLitL == uc1Orig.right) | (Not(otherLitL) == uc1Orig.right) | (otherLitL == Not(uc1Orig.right))) {
      // In this case, the order was changed
      uc1 = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, otherLit_l, maxLit_l))
      uc1Final = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, maxLit_l, otherLit_l))
      val flipLitsName = lpConstantTerm("EqSymmetry")
      val (flipLitsProofScript, flippedLits, usedSymbolsNew) = flipEqLiteralsProofScript(Seq((uc1,lpOtype)), lpClause(Seq(), lastStepLits), lastStepName, flipLitsName)
      lastStepName = flipLitsName
      lastStepLits = flippedLits
      usedSymbols = usedSymbols ++ usedSymbolsNew
      allSteps = allSteps :+ flipLitsProofScript
    } else throw new Exception(s"In the LP encoding of EqFact, the first unification constraint constructed in LP encoding (${term2LP(otherLitL,bVarMap,sig)._1.pretty}) does not match the one derived by Leo (sides of ${term2LP(asTerm(uc1Orig),bVarMap,sig)._1.pretty}\ntrying to prove ${}")

    //  f) If the order within any of the equality literals has changed after the rule application as a result of the term ordering, proof the transformation using eqSym_eq
    // -> The first one will always be equational since it contains the left sides of otherLit and maxLit
    // -> The second unification constraint is non-equational - and thus requires a backwards encoding - iff the max literals were non equational
    if (maxLit_r == lpOlTop) {
      // todo: if we have a negative left side of other lit, should we encode the backwards translation as double negation here or is it eliminated right away?
      //  define exceptin to test this:
      if (otherLit.equational) {
        otherLit.left match {
          case Not(_) =>
            throw new Exception(s"test what happens with eqFactoring back encoding here")
        }
      }
      uc2Eq = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, otherLit_r, otherLit_r))
      uc2 = lpOlUnaryConnectiveTerm(lpNot, otherLit_r)
      literalsToTransform2 = literalsToTransform2 :+ uc2Eq
    } else if (otherLit_l == lpOlTop) {
      throw new Exception(s"The LP encoding of EqFact non-equational max literal and equational other literal not enocided yet yet")
    } else {
      uc2 = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, otherLit_l, otherLit_r))
      uc2Eq = uc2
    }
    // Combine into one rule for the backwards encoding:
    if (literalsToTransform2.nonEmpty) {
      val nameTransfStep2 = lpConstantTerm("TransformToNonEqLits")
      val (backTransformationStep, backLitMap, litsAfter, usedSymbolsNew) = makeLiteralEquational_proofSkript(literalsToTransform2, lpClause(Seq(), lastStepLits), lastStepName, false, true, nameTransfStep2)
      usedSymbols = usedSymbols ++ usedSymbolsNew
      lastStepName = nameTransfStep2
      lastStepLits = litsAfter
      allSteps = allSteps :+ backTransformationStep
    }
    // Assume step in beginning of this whole proof
    val typeOfWholeProof = lpMlFunctionType(Seq(lpOlUntypedBinaryConnectiveTerm_multi(lpOr, parentEnc.lits).prf, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, lastStepLits).prf))
    val assumeStep = lpAssume(Seq(lpOlConstantTerm("h1")))
    allSteps = Seq(assumeStep) ++ allSteps
    val refineStep = lpRefine(lpFunctionApp(lastStepName, Seq.empty))
    allSteps = allSteps :+ refineStep

    val wholeProof = lpHave(nameStep.pretty, typeOfWholeProof, lpProofScript(allSteps))

    (wholeProof, usedSymbols)
  }

  def encEqFact_proofScript(child: ClauseProxy, parent: ClauseProxy, additionalInfo: (Literal, Literal, Literal, Literal, Boolean, Boolean), parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Set[lpStatement], Option[String]) = {

    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty

    val (otherLit, maxLit, ur1, ur2, wasUnified, wasSimplified) = additionalInfo
    if (wasUnified) {
      //throw new Exception(s"The LP encoding of EqFact including type unification is not implemented yet")
      (lpProofScript(Seq(lpProofScriptAdmit())), Set.empty, Some("The LP encoding of EqFact including type unification is not implemented yet"))
    } else if (wasSimplified) {
      //throw new Exception(s"The LP encoding of EqFact including simplification is not implemented yet")
      (lpProofScript(Seq(lpProofScriptAdmit())), Set.empty, Some("The LP encoding of EqFact including simplification is not implemented yet"))
    } else {

      // The modular proof script can consist of the following steps:
      // 1. Abstract over free variables
      // 2. Identify the two literals to be unified and compose a function proving the rule application including all necessary transformations:
      // 3. If the clause has more than two literals and the order of the literals does not match the one required by the derived function, i.e. if the literals to be unified are not at the last positions of the clause, proof the permuted clause using an instance of permute
      // 4. Apply the rule to the two literals to be unified using the appropriate transform function
      // 5. If the order of literals was changed, change it back with the correct instance of permute
      // 6. Refine with the last proven step

      // 1. Abstract over free variables
      val (clauseQuantification, applySymbolsToParent) = clauseRuleQuantification(parent.cl, bVarMap, sig)
      if (clauseQuantification.nonEmpty) allSteps = allSteps :+ lpAssume(clauseQuantification.map(var0 => var0.untyped))
      var lastStep: lpTerm = lpFunctionApp(parentNameLpEnc, applySymbolsToParent)

      // 2. Identify the two literals to be unified and compose a function proving the rule application including all necessary transformations:
      val factStepName = lpOlConstantTerm("WholeEqFactStep")
      if (parent.cl.lits.length == 2) {
        val (encFactoring, usedSymbolsNew) = encEqFactLiterals(otherLit, maxLit, ur1, ur2, parent.cl, child.cl, bVarMap, lastStep, factStepName, sig)
        allSteps = allSteps :+ encFactoring
        lastStep = factStepName
        usedSymbols = usedSymbols ++ usedSymbolsNew
        // 6. Refine with the last proven step
        allSteps = allSteps :+ lpRefine(lpFunctionApp(lastStep, Seq(lpFunctionApp(parentNameLpEnc, applySymbolsToParent))))
        val wholeProof = lpProofScript(allSteps)

        (wholeProof, usedSymbols, None)
      } else {
        (lpProofScript(Seq(lpProofScriptAdmit())), Set.empty, Some("The LP encoding of EqFact is not implemented for the application to clauses of length more than two yet"))
        //throw new Exception(s"The LP encoding of EqFact is not implemented for the application to clauses of length more than two yet")
        // todo: all the other steps of 2
        // 3. If the clause has more than two literals and the order of the literals does not match the one required by the derived function, i.e. if the literals to be unified are not at the last positions of the clause, proof the permuted clause using an instance of permute
        // todo
        // 4. Apply the rule to the two literals to be unified using the appropriate transform function
        // todo
        // 5. If the order of literals was changed, change it back with the correct instance of permute
        // todo
      }
    }
  }


  ////////////////////////////////////////////////////////////////
  ////////// Extended Calculus
  ////////////////////////////////////////////////////////////////

  def simplificationInfoToSteps(parent: Clause, additionalInfo: Seq[(Seq[Int],String,Term,Term)], sig: Signature):(Seq[lpProofScriptStep],Set[lpStatement])={

    // outdated

    var usedSymbols: Set[lpStatement] = Set.empty
    var rewriteSteps: Seq[lpProofScriptStep] = Seq.empty

    additionalInfo foreach { tuple =>
      val (appliedSimpRule, needsTypeInst) = SimplificationEncoding.SimpRuleMap(tuple._2)
      usedSymbols = usedSymbols + appliedSimpRule
      val (rewritePattern0, termAtRewriteVar) = acessSubterm(Clause.asTerm(parent), tuple._1, sig)
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
      rewriteSteps = rewriteSteps :+ rewriteStep
    }
    (rewriteSteps,usedSymbols)
  }

  def simplificationProofScript(child: Clause, parent: Clause, additionalInfo: Seq[(Seq[Int],String,Term,Term)], symbolsToUnfold: Set[Signature.Key], parentNameLpEnc: lpConstantTerm, quantifiedVars: Seq[lpUntypedVar], bVars: Map[Int, String], sig: Signature):(lpProofScript, Set[lpStatement])={

    // proof the equality between a parent and a child term given a set of rewrite rules and their positions

    val encParent = term2LP(Clause.asTerm(parent), bVars, sig)._1
    val encChild = term2LP(Clause.asTerm(child), bVars, sig)._1
    print(s"Encoding simplification step: ${encParent.pretty} to ${encChild.pretty}\n")

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
    // at the end, only something like x=x should remain of the focussed goal. We add the tactic "reflexivity" to prove this.
    rewriteSteps = rewriteSteps :+ lpReflexivity()

    // we proof that the term before the transformation = the term after the transformation
    val eqSimpTerm = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,encParent,encChild).prf
    val haveStep = lpHave(simplificationStepName,eqSimpTerm,lpProofScript(rewriteSteps))

    allProofStep = allProofStep :+ haveStep


    //// 3. Refine step
    val application = lpFunctionApp(lpConstantTerm(simplificationStepName),Seq(Identity, lpFunctionApp(parentNameLpEnc,quantifiedVars)))
    val applicationStep = lpRefine(application)
    allProofStep = allProofStep :+ applicationStep

    // combine all steps into one proof script
    val proofScript = lpProofScript(allProofStep)

    (proofScript, usedSymbols)
  }

  // encLiftEq(cl, cl.annotation.parents, cl.furtherInfo.addInfoLiftEq, parentInLpEncID, sig)
  def encLiftEq(cl: ClauseProxy, parents: Seq[ClauseProxy], addInfo: Seq[Seq[Int]], parentNameLpEnc: Seq[lpConstantTerm], sig: Signature) = { //: (lpProofScript, Set[lpStatement]) = {

    // encode the lift of equality literals
    // ((x = y) = T)^a to (x = y)^a
    // ((x ≠ y) = T)^tt to (x = y)^ff
    // ((x ≠ y) = T)^ff to (x = y)^tt

    // the complete proof script consists of 3 steps:
    // 1. Assume free variables
    // 2. For each of the literals in the original caluse:
    //    a) in case of negative equality lift, a rewrite tactic has to be applied
    //    b) for the new equality literlas, the order within the equality may have changed, if so: apply rewrite tactic
    // 3. If the order of literals has changed, apply meta theorem and refine with instanciated meta-theorem
    //    Else refine with the last step

    if (parents.length != 1) throw new Exception("trying to encode lift equaltiy step with more than one parent")

    // Extract information about what literals were edited in which way
    // And in which order they will occur in the resulting clause
    val litsPosLift = addInfo(0)
    val litsNegLift = addInfo(1)
    val litsOld = addInfo(2)
    val edIndices = litsPosLift ++ litsNegLift
    val indices = (edIndices ++ litsOld).sorted
    val permutation = litsPosLift ++ litsNegLift ++ litsOld


    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    var usedRules: Set[lpStatement] = Set.empty
    var liftedLits: Seq[lpOlTerm] = Seq.empty

    // 1. Abstract over free variables
    val bVars = clauseVars2LP(parents.head.cl.implicitlyBound, sig, Set.empty)._2
    val (clauseQuantification, applySymbolsToParent) = clauseRuleQuantification(parents.head.cl, bVars, sig)
    if (clauseQuantification.nonEmpty) allSteps = allSteps :+ lpAssume(clauseQuantification.map(var0 => var0.untyped))
    val lastStep: lpTerm = lpFunctionApp(parentNameLpEnc.head, applySymbolsToParent)

    indices foreach {indx =>
      val lit = parents.head.cl.lits(indx)
      if (edIndices.contains(indx)){
        val lhsRhs = ===.unapply(lit.left)
        if (lhsRhs == None) throw new Exception("trying to encode lifting equality on malformed term")
        val (lhs, rhs) = lhsRhs.get
        val encRhs = term2LP(rhs, bVars, sig)._1
        val encLhs = term2LP(lhs, bVars, sig)._1
        val encType = type2LP(lhs.ty, sig)._1
        val rwPattern = generateClausePatternTerm(permutation(indx), indices.length)
        val litPol = lit.polarity
        var finalLit : lpOlTerm = lpOlNothing
        if (litsPosLift.contains(indx)) {
          if (!litPol) {
            finalLit = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, encType, encLhs, encRhs))
          } else {
            finalLit = lpOlTypedBinaryConnectiveTerm(lpEq, encType, encLhs, encRhs)
          }
        } else if (litsNegLift.contains(indx)) {
          //    2 a) in case of negative equality lift, a rewrite tactic has to be applied
          throw new Exception("encoding of inequality lift is unfinished")
          /*
          if (!litPol) {
            print("\nlit is negative")
            allSteps = allSteps :+ lpRewrite(rwPattern, lpInferenceRuleEncoding.liftEq().instanciate(encType, encLhs, encRhs))
            usedRules = usedRules + liftEq()
            print(f"\nadd rule:\n${liftEq().pretty}")
            finalLit = lpOlTypedBinaryConnectiveTerm(lpInEq, encType, encLhs, encRhs)
          } else {
            finalLit = lpOlTypedBinaryConnectiveTerm(lpEq, encType, encLhs, encRhs)
          }
           */
        }
        val lit_cl = cl.cl.lits(permutation.indexOf(indx))
        if (lhs != lit_cl.left) {
          // 2 b) for the new equality literlas, the order within the equality may have changed, if so: apply rewrite tactic
          allSteps = allSteps :+ lpRewrite(rwPattern, flipLiteral(litPol).instanciate(encRhs,encLhs,None))
          finalLit = flipLiteral(litPol).res(encType.lift2Poly,encRhs,encLhs)
          usedRules = usedRules + flipLiteral(true)
        }
        liftedLits = liftedLits :+ finalLit
      }else{
        val lit = parents.head.cl.lits(indx)
        val encLit = term2LP(asTerm(lit), bVars, sig)._1
        liftedLits = liftedLits :+ encLit
      }
    }

    // 3. If the order of literals has changed, apply meta theorem and refine with instanciated meta-theorem
    //    Else refine with the last step
    val needsPermute = permutation != permutation.sorted
    if (needsPermute){
      allSteps = allSteps :+ lpRefine(metaPermutation.instanciate(permutation,liftedLits,lastStep))
      // permutation will not need to be added to the rules assuming that we will add it to stdlib
    } else {
      allSteps = allSteps :+ lpRefine(lpFunctionApp(lastStep,Seq()))
    }

    val finishedProof = lpProofScript(allSteps)

    (finishedProof, usedRules)
  }


  def encRewrite(cl: ClauseProxy, parents: Seq[ClauseProxy], addInfoSimp: Seq[(Seq[Int], String, Term, Term)], parentModoluRw: Option[Clause], parentNameLpEnc: Seq[lpConstantTerm], sig: Signature):(lpProofScript,Set[lpStatement],Option[String]) = {

    // The modular proof script can consist of the following steps:
    // 1. Abstract over free variables
    // For each of the rewrite clauses applied:
    //    2. Use the have tactic to provide a proof-term for the equality used to rewrite the focused goal. The exact form depends on the kind of clause used as a rewrite rule by Leo-III:
    //        a) case I) If the rewrite-clause is a non-equational single literal, proof the transformation to equational form using topPosProp_eq or botNegProp_eq
    //       a) case II) If the rewrite-clause is an equational single literal, use eqSym_eq to prove the reverse rewrite rule
    //       b) Refine with the rewrite-clause and - if a substitution was applied - instanciate it accordingly
    //   For each of the literals that are transformed:
    //       2.5 if the literal in the parent clause is equational, but the literal in the child clause is not, transform to equality
    //       3. If the order within equality literals was changed, apply eqSym
    //       4. Use the (transformed) rewrite-clause to rewrite the focused goal
    // 5. If simplifications were applied, use the encoding of (Simp) to verify the transformations
    // 6. Refine with the (instantiated) parent

    // extract the parents and their names
    assert(parents.length == parentNameLpEnc.length)
    val (parent,rewriteEqCalsues) = (parents(0).cl,parents.tail.map(_.cl))
    val (sourceBeforeParent, sourcesBeforeEq) = (parentNameLpEnc(0), parentNameLpEnc.tail)

    // initialize
    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty

    // temporariy: If versions of the rule are needed that are not encoded yet, return admit
    var allTransformationsEncoded = true
    if (addInfoSimp.nonEmpty) allTransformationsEncoded = false

    // 1. Abstract over free variables
    val (parentImpVars, _, _) = clause2LP_unquantified(parent, Set.empty, sig)
    val (childImpVars, _, _) = clause2LP_unquantified(cl.cl, Set.empty, sig)
    val impBoundParent = parentImpVars.map(var0 => var0.untyped)
    if (impBoundParent.nonEmpty) allSteps = allSteps :+ lpAssume(impBoundParent)

    // encode the parent
    // just temporary: remove this translation, you will not need it.
    val (_, clauseModulo, _) = clause2LP_unquantified(parentModoluRw.get, Set.empty, sig)
    val (_, encParent, _) = clause2LP_unquantified(parent, Set.empty, sig)
    val (_, encChild, _) = clause2LP_unquantified(cl.cl, Set.empty, sig)

    rewriteEqCalsues.zip(sourcesBeforeEq) foreach { case (rewriteEqClause, sourceBeforeEq0) =>
      // encodings of the clauses
      // rewrite Equality Literal
      var sourceBeforeEq = sourceBeforeEq0
      val bVarsRewriteEq = clauseVars2LP(rewriteEqClause.implicitlyBound, sig, Set.empty)._2
      //val (rewriteEqImpVars, encRewriteEq0, _) = clause2LP_unquantified(rewriteEqClause, Set.empty, sig)
      //val encRewriteEq = encRewriteEq0.args.head
      assert(rewriteEqClause.lits.length == 1)
      val rewriteEq = rewriteEqClause.lits.head
      val rwLhs = term2LP(rewriteEq.left, bVarsRewriteEq, sig)._1
      var rwRhs = term2LP(rewriteEq.right, bVarsRewriteEq, sig)._1
      val rwType = type2LP(rewriteEq.right.ty, sig)._1
      val rwPol = rewriteEq.polarity

      Out.lp_debug_info(s"Use ${sourceBeforeEq.name} : ${if (!rwPol) lpNot.pretty} (${rwLhs.pretty} = ${rwRhs.pretty})")
      Out.lp_debug_info(s"To rewrite ${sourceBeforeParent.name} : ${encParent.pretty}")
      Out.lp_debug_info(s"Clause after rewriting: ${clauseModulo.pretty}")

      // check that none of the things not yet encoded occur
      if (rewriteEqClause.implicitlyBound.nonEmpty || rewriteEqClause.typeVars.nonEmpty) allTransformationsEncoded = false

      // begin with the encoding

      // 2. Use the have tactic to provide a proof-term for the equality used to rewrite the focused goal
      // Test if the clause representing the rewrite equation has the right form (only has one literal that is positive and equational)
      // If it is not equational, transform it to an equational one
      if (rewriteEqClause.lits.length != 1) throw new Exception(s"Error while attempting to encode rewrite step in LP: Rewrite-clause with more than one literal")
      if (!rewriteEq.equational) {
        // 2 a) case I) If the rewrite-clause is a non-equational single literal, proof the transformation to equational form using topPosProp_eq or botNegProp_eq
        val transformationStepName = "TransformToEqLits"
        val (haveTransformStep, usedSymbols0) = if (rwPol) {
          val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTop, rwLhs)
          //  2 b) Refine with the rewrite-clause and - if a substitution was applied - instanciate it accordingly
          // todo: sbustitution
          val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, mkTopEqPosProp_script(sourceBeforeEq.pretty).name), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
          (haveTransformStep0, mkTopEqPosProp_script())
        } else {
          // todo: aso use the general skript here
          rwRhs = lpOlBot
          val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlBot, rwLhs)
          val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, mkBotEqNegProp_script(sourceBeforeEq.pretty).name), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
          (haveTransformStep0, mkBotEqNegProp_script())
        }
        allSteps = allSteps :+ haveTransformStep
        usedSymbols = usedSymbols + usedSymbols0
        /*
          val rewriteEqTransformed = encRewriteEq match {
            case lpOlUnaryConnectiveTerm(lpNeg, body) =>
              lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlBot, body)
            case _ =>
              throw new Exception(s"trying to transform term of wrong format to rewriting equality: ${encRewriteEq.pretty}")
          }
           */
        //encRewriteEq = transformedRewriteEq
        sourceBeforeEq = lpConstantTerm(transformationStepName)
      } else if (rewriteEq.polarity) {
        //2 a) case II) If the rewrite-clause is an equational single literal, use eqSym_eq to prove the reverse rewrite rule
        // todo
        // locate the term we are searching in the encoded clause
        val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, rwRhs, rwLhs)
        //print(s"transformedRewriteEq: ${transformedRewriteEq.pretty}\n")
        val transformationStepName = "flip_equality"
        val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, lpFunctionApp(flipLiteral(true).name, Seq.empty, Seq(rwType))), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
        //print(s"haveTransformStep0: ${haveTransformStep0.pretty}\n")
        //throw new Exception("The LP encoding of Rewrite for positive equational rewrite-clauses is not implemented yet")
        val (haveTransformStep, usedSymbols0) = (haveTransformStep0, flipLiteral(true))
        allSteps = allSteps :+ haveTransformStep
        usedSymbols = usedSymbols + usedSymbols0
        sourceBeforeEq = lpConstantTerm(transformationStepName)

      }
      else throw new Exception("Error while attempting to encode rewrite step in LP: Rewrite rule is equational but not positive")

      //val (rewritePattern, rewrittenParent) = findRWTerm(rwLhs, encParent, rwRhs)

      // go over all of the literals and - for each occurrence of the term that has to be rewritten, apply a rewrite rule and if necessary eqSmy
      val clauseLen = parent.lits.length
      val bVarsParentEq = clauseVars2LP(parent.implicitlyBound, sig, Set.empty)._2
      var litCount = 0
      parent.lits.foreach { lit =>
        //val (encLitRhs, _) = term2LP(lit.right, bVarsParentEq, sig)
        //val (encLitLhs, _) = term2LP(lit.left, bVarsParentEq, sig)
        //val rewritePatternEqSym = lpRewritePattern(generateClausePattern(litCount, clauseLen))
        val (encLit, _) = term2LP(asTerm(lit), bVarsParentEq, sig)
        val (encType, _) = type2LP(lit.left.ty, sig)
        //val encLit = if (lit.polarity) lpOlTypedBinaryConnectiveTerm(lpEq,encType,encLitLhs,encLitRhs) else lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,encType,encLitLhs,encLitRhs))
        Out.lp_debug_info(s"encoded literal ${encLit}")
        val (patternTerm, rewrittenLit, counter, rwUnderBinder) = findRWTerm0(rwLhs, encLit, rwRhs)
        if (rwUnderBinder) {
          allTransformationsEncoded = false
        } else if (counter != 0) {
          // generate the rewrite pattern for the rewriting operation itself
          val rewritePattern = lpRewritePattern(generateClausePattern(litCount, clauseLen, true, patternTerm))

          if (!(encChild.args(litCount) == rewrittenLit)) {
            // 2.5 if the literal in the parent clause is equational, but the literal in the child clause is not, transform to equality
            // test if the literal in the parent was equational but the literal in the child is not.
            val correspondingLit = cl.cl.lits(litCount)
            val (encLitChild, _) = term2LP(asTerm(correspondingLit), bVarsParentEq, sig)
            // todo: I should write a unified approach that trasforms any form of literal to any other version of the literal (i.e. switch sides, transform to equality literal, etc.)
            Out.lp_debug_info(s"rewritten Litera: ${rewrittenLit.pretty} ,corresponding literal in child caluse: ${encLitChild.pretty}")
            val (additionalSteps, usedSymbols0, canEncode) = transformLiteral(encLitChild, rewrittenLit, litCount, clauseLen) // todo: acutally, rewerite pattern should be ootional since we do not want it for clauses of length one
            if (canEncode) Out.lp_debug_info(s"proposed Steps: \n${additionalSteps.map(_.pretty).mkString("\n")}")
            else allTransformationsEncoded = false
            usedSymbols = usedSymbols ++ usedSymbols0
            allSteps = allSteps :++ additionalSteps

            /*
            if (lit.equational && !correspondingLit.equational) {
              Out.lp_debug_info("need to transform parent literal to eq!")
              // we need to choose a different transformation based on weather we want to rewrite top or bottom and weather we have a positive or negative literal
              // if we want to rewrite to obtail bottom ...
              val transformation: lpDefinedRules = if (rwRhs == lpOlBot) {
                if (!correspondingLit.polarity) mkPosPropEqBot_script()
                else throw new Exception()
              } else if (rwRhs == lpOlTop) {
                if (!correspondingLit.polarity) mkNegPropNegLit_script()
                else mkPosPropPosLit_script()
              } else throw new Exception(s"Errorn encoding RW application: RHS of RWR is expected to bei Top or Bot but is ${rwRhs.pretty}")
              allSteps = allSteps :+ lpRewrite(Some(lpRewritePattern(generateClausePattern(litCount, clauseLen))), transformation.name)
              usedSymbols = usedSymbols + transformation
            }
            // 3. If the order within equality literals was changed, apply eqSym
            // test if we also need to apply eqSym by comparing the recieved literal with the respective one in "clauseModulo"
            else if (lit.equational) {
              Out.lp_debug_info(s"eqSym necessary: ${rewrittenLit.pretty} is not equal to ${encChild.args(litCount).pretty}. Rewrite pattern is ${rewritePatternEqSym.pretty}")
              allSteps = allSteps :+ lpRewrite(Some(rewritePatternEqSym), lpFunctionApp(flipLiteral(lit.polarity).name, Seq.empty, Seq(encType)))
              usedSymbols = usedSymbols + flipLiteral(lit.polarity)
            }
             */


          }
          // 4. Use the (transformed) rewrite-clause to rewrite the focused goal
          Out.lp_debug_info(s"rewrite pattern is ${rewritePattern.pretty} and the rewritten literal is ${rewrittenLit.pretty}")
          allSteps = allSteps :+ lpRewrite(Some(rewritePattern), lpConstantTerm(sourceBeforeEq.pretty))
        }
        litCount = litCount + 1
      }


      // 3. Use the (transformed) rewrite-clause to rewrite the focused goal
      // todo: will we still find the position if variables have different names? I assume i should prove the rules with quantifications then it should work
      // detect which of the literals the rewrite rule was applied to
      /*
      val rewrittenLits = {
        if (parentModoluRw.isDefined) parentModoluRw.get.lits
        else throw new Exception("Trying to verify application of RW but no rewritten literals were supplied.")
      }
      val changedLitsMap = parent.lits.zip(rewrittenLits)
        .collect {
          case (oldLit, newLit) if oldLit != newLit => oldLit -> newLit
        }.toMap

      parent.lits foreach {oldLit =>
        // test if the literal was modified
        if (changedLitsMap.keySet.contains(oldLit)){

        }
      }

       */
      var rewriteSkript: Seq[lpProofScriptStep] = Seq(lpRewrite(None, sourceBeforeEq))

    }


      // 5. If simplifications were applied, use the encoding of (Simp) to verify the transformations
      /*
      if (addInfoSimp.nonEmpty) {
        val (simplificationSteps, usedSymbolsNew) = simplificationInfoToSteps(parentModoluRw.get, addInfoSimp, sig)
        rewriteSkript = rewriteSkript ++ simplificationSteps
        usedSymbols = usedSymbols ++ usedSymbolsNew
      }
       */

      // 6. Refine with the (instantiated) parent
      //allSteps = allSteps :+ lpRewrite(None, lpConstantTerm(sourceBeforeEq.pretty))
      allSteps = allSteps :+ lpRefine(lpFunctionApp(lpFunctionApp(sourceBeforeParent, impBoundParent), Seq()))
      val finishedProof = lpProofScript(allSteps)

      if (allTransformationsEncoded) (finishedProof, usedSymbols, None)
      else (finishedProof, usedSymbols, Some("When attempting to encode rewrite step, some transformation could not be encoded"))
  }

  ////////////////////////////////////////////////////////////////
  ////////// Unification
  ////////////////////////////////////////////////////////////////

  def substituteVarTerm(t: lpOlTerm, subsMap: Map[String,lpOlTerm]): lpOlTerm = {
    // given a substitution map and a term, substitute all occurrences of given variables in a term

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
        var encArgs: Seq[Either[lpOlTerm,lpOlType]] = Seq.empty
        args foreach {arg =>
          arg match{
            case a : lpOlTerm => encArgs = encArgs :+ Left(substituteVarTerm(a, subsMap))
            // if the argument is e.g. a type we do not need to substitute anything
            case _ => encArgs :+ arg
          }
        }
        lpOlFunctionApp(substituteVarTerm(f, subsMap), encArgs)
      case lpOlQuantifiedTerm(quantifier, variables, body) => lpOlQuantifiedTerm(quantifier, variables.map(var0 => substituteTypedVarsTerm(var0, subsMap)), substituteVarTerm(body, subsMap))
      case lpOlUnaryConnectiveTerm(connective, body) => lpOlUnaryConnectiveTerm(connective,  substituteVarTerm(body, subsMap))
      case lpOlUntypedBinaryConnectiveTerm(connective,lhs,rhs) => lpOlUntypedBinaryConnectiveTerm(connective, substituteVarTerm(lhs, subsMap), substituteVarTerm(rhs, subsMap))
      case lpOlTypedBinaryConnectiveTerm(connective, ty, lhs, rhs) => lpOlTypedBinaryConnectiveTerm(connective, ty,  substituteVarTerm(lhs, subsMap),  substituteVarTerm(rhs, subsMap))
      case lpOlUntypedBinaryConnectiveTerm_multi(connective, args) =>
        lpOlUntypedBinaryConnectiveTerm_multi(connective, args.map(arg => substituteVarTerm(arg, subsMap)))
      case _ => throw new Exception(s"encountered unexptcted term $t when trying to do substitution")
    }
  }

  def removeUnificationConstraint(uniC: Literal, parent: Clause, lastLit0: lpOlTerm, sig: Signature): (Seq[lpProofScriptStep], Set[lpStatement])={
    // prove that unification literal can be removed from a clause when they either have the form ¬⊤ or x≠x (modulo unification)

    var usedSymbols: Set[lpStatement] = Set.empty

    // identify the position of the unification literals in parent clause
    val positionInClause = findLitInClause(uniC,parent)
    val patternVar = lpOlUntypedVar(lpOlConstantTerm("x"))

    var rewriteSteps: Seq[lpProofScriptStep] = Seq.empty

    // in both cases, the second step is the removal of ⊥ from the clause. This can be done using Simp7:
    val rewritePattern_step2 = generateClausePatternTerm(positionInClause - 1, parent.lits.length - 1, None, patternVar)
    val rewriteStep_step2 = lpRewrite(rewritePattern_step2, SimplificationEncoding.Simp7_eq.name)
    rewriteSteps = rewriteSteps :+ rewriteStep_step2
    usedSymbols = usedSymbols + SimplificationEncoding.Simp7_eq

    // proof the first transformation depending on the form of the unification constraint
    val rewritePattern_step1 = generateClausePatternTerm(positionInClause, parent.lits.length, None, patternVar)
    if (uniC.equational){
      if (!uniC.polarity){
        // in this case, we need to first show that both sides are equal modulo simplification and then apply a Simp Rule that postulates that x≠x = ⊥
        // the rewrite rule used here needs to explicitly instanciate the used type, therefore we first need to find that type out:
        var ty = type2LP(uniC.left.ty, sig, Set.empty)._1
        val lastLit = lastLit0 match {
          case lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, ty0, lhs, _)) =>
            ty = ty0
            lhs
          case _ =>
            throw new Exception("attempting to instanciate Simp10 inappropriateley")
        }
        val rewriteStep_step1 = lpRewrite(rewritePattern_step1, lpFunctionApp(SimplificationEncoding.Simp10_eq.name,Seq(ty, lastLit)))
        rewriteSteps = rewriteSteps :+ rewriteStep_step1
        usedSymbols = usedSymbols + SimplificationEncoding.Simp10_eq
      } else throw new Exception(s"Equational positive unification constratint passed on to lambdapi post eqFact encoding?")
    }else{
      // in this case simply we need to prove that 1. ¬⊤ = ⊥
      if (!uniC.polarity){
        val rewriteStep_step1 = lpRewrite(rewritePattern_step1, SimplificationEncoding.Simp16_eq.name)
        rewriteSteps = rewriteSteps :+ rewriteStep_step1
        usedSymbols = usedSymbols + SimplificationEncoding.Simp16_eq
      }else{
        throw new Exception(s"Error: unification constraint passed to LP encoding is non equational and positive")
      }
    }

    (rewriteSteps,usedSymbols)
  }

  def encPreUni(cl: ClauseProxy, parent: ClauseProxy, addInfoUni: (Seq[(Int,Any,Int,Map[Int,String])],Seq[(Int,Any)]), addInfoUniRule: (String, (Literal, Literal)), parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Set[lpStatement], Option[String]) = {
    // encode different versions of unification (after rule applications, ...)

    val bVars = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

    val encModes = Seq("uniAfterFactoring")

    val mode = addInfoUniRule._1

    if (encModes.contains(mode)) {
      Out.lp_debug_info(s"verification of $mode")
      var allSteps: Seq[lpProofScriptStep] = Seq.empty
      var usedSymbols: Set[lpStatement] = Set.empty

      // Abstract over the free variables
      val (unboundVarsChild0, encChild, _) = clause2LP_unquantified(cl.cl, Set.empty, sig)
      var encChildLiterals = encChild.args
      val unboundVarsChild = unboundVarsChild0.map(var0 => lpUntypedVar(var0.name))
      allSteps = if (unboundVarsChild.nonEmpty) allSteps :+ lpAssume(unboundVarsChild) else allSteps

      val (_, encParent, _) = clause2LP_unquantified(parent.cl, Set.empty, sig)
      val encParentLiterals = encParent.args

      // Encode the actual unification and possibly the following simplification
      val typeUnification = addInfoUni._2
      val termUnification = addInfoUni._1

      // Type unification
      if (typeUnification.nonEmpty) {
        throw new Exception(s"LP encoding of type unification not encoded yet")
      }

      else if (termUnification.nonEmpty) {
        // Construct a map for the substitutions
        val subsMap: mutable.HashMap[String, lpOlTerm] = mutable.HashMap.empty
        val varmap = clauseImplicitsToTPTPQuantifierList_map(parent.cl.implicitlyBound)(sig)
        termUnification foreach { termUni =>
          val lpUnboundVar = varmap.apply(termUni._1)
          // Term unifications can either be bindings of variables by terms or by variables...
          // Depending on that, the second element of the tuple is either a term or a String
          termUni._2 match {
            case var0: String =>
              throw new Exception("binding by variables not yet encoded (only terms so far)") //todo: is it really variables? I suppose so, but bound ones, no?
            case t: Term =>
              val encBindTerm = term2LP(t, termUni._4, sig)._1 //todo: dont i need the offset? was it an oversight not to use it in term2lp?
              subsMap += (lpUnboundVar -> encBindTerm)
            case _ => throw new Exception("Encountered unexpected bound object when encoding Unification step in lp")
          }
        }

        // Proof the substitution by applying the terms to be substituted to the parent quanififying over the respective variables
        val encSubstLits = parent.cl.lits.map(lit => substituteVarTerm(term2LP(asTerm(lit), bVars, sig)._1, subsMap.toMap))
        // The application that instanciates the quantified variables with the substituted Terms in lp
        val (unboundVarsParent, _, _) = clause2LP_unquantified(parent.cl, Set.empty, sig)
        val applyToParent = unboundVarsParent.map(var0 => subsMap.getOrElse(var0.name.pretty, var0))
        val substitution = lpProofScript(Seq(lpRefine(lpFunctionApp(parentNameLpEnc, applyToParent))))
        val substitutionStepName = "Substitution"
        val substitutionHaveStep = lpHave(substitutionStepName, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits).prf, substitution)
        allSteps = allSteps :+ substitutionHaveStep

        // Depending on the mode of Unification, additional steps like the removal of unification constraints have to be proven
        // we carry out the substitution todo would there be an advantage to passing on the substitution in its original form after all and doing the actual substitution here instead of doing it as lambda terms?
        if (Seq("uniAfterFactoring").contains(mode)) { // uniAfterFactoring is eqFact
          // in this case the unification constraints were fulfilled and removed, we thus need to prove that they can be removed
          if (termUnification.length != unboundVarsParent.length) {
            throw new Exception(s"trying to encode the unification that does not bind all free variables, this is implemented but untested, make sure this is done correctly") //todo
          }
          // Remove the first unification constraint
          val uniC1 = addInfoUniRule._2._1
          if (parent.cl.lits.last != uniC1) throw new Exception(s"encoding unification following eqFactoring and found unification constraint 1 in unexpected position")
          val nameStep1Removal = "RemoveUC1"
          val (removeUniC1, usedSymbolsUc1) = removeUnificationConstraint(uniC1, parent.cl, encSubstLits.last, sig)
          usedSymbols = usedSymbols ++ usedSymbolsUc1
          val proofStepUc1 = lpHave(nameStep1Removal, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits.init).prf, lpProofScript(removeUniC1 :+ lpRefine(lpFunctionApp(lpConstantTerm(substitutionStepName), Seq()))))
          // Remove the second unification constraint
          val uniC2 = addInfoUniRule._2._2
          if (parent.cl.lits.init.last != uniC2) throw new Exception(s"encoding unification following eqFactoring and found unification constraint 2 in unexpected position")
          val nameStep2Removal = "RemoveUC2"
          val clauseWighoutUC = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits.init.init)
          val (removeUniC2, usedSymbolsUc2) = removeUnificationConstraint(uniC2, Clause(parent.cl.lits.init), encSubstLits.init.last, sig)
          usedSymbols = usedSymbols ++ usedSymbolsUc2
          val proofStepUc2 = lpHave(nameStep2Removal, clauseWighoutUC.prf, lpProofScript(removeUniC2 :+ lpRefine(lpFunctionApp(lpConstantTerm(nameStep1Removal), Seq()))))

          // only add the rewrite steps, this is less complicated but should have the same result
          allSteps = allSteps ++ removeUniC2 ++ removeUniC1

          // Now the last step is refining with the last proven term after removal of the last unification constraint
          val refineStep = lpRefine(lpFunctionApp(lpConstantTerm(substitutionStepName), Seq())) //lpRefine(lpFunctionApp(lpConstantTerm(nameStep2Removal),Seq()))

          allSteps = allSteps :+ refineStep
        }
      }

      // permutation? todo: figure out why this can ecen happen
      if (containsLpLits(encParentLiterals,encChildLiterals)){
        val permutationStep = permutationStepSkript(encParentLiterals,encChildLiterals,lpFunctionApp(parentNameLpEnc,unboundVarsChild))
        Out.lp_debug_info(s"Permutation step: ${permutationStep.pretty}")
        allSteps = allSteps :+ permutationStep
      }

      val proofScript = lpProofScript(allSteps)
      (proofScript, usedSymbols, None)
    }
    else{
      (lpProofScript(Seq.empty),Set.empty,  Option(s"the unification mode $mode is either not set or not encoded yet..."))
    }
  }

  }
