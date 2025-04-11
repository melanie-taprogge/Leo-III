package leo.modules.output.LPoutput
import leo.Out
import leo.datastructures.Literal.{asTerm, isFalse, mkLit}
import leo.modules.output.LPoutput.Encodings._
import leo.datastructures.{Clause, ClauseProxy, Literal, Signature, Term, Type}
import leo.modules.HOLSignature._
import leo.modules.calculus.PolaritySwitch
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.AccessoryRules._
import leo.modules.output.LPoutput.lpInferenceRuleEncoding._
import leo.modules.output.LPoutput.SimplificationEncoding._
import leo.modules.calculus.Simp.normalize

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
    var litCount = 0
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
            val polaritySwitchName = s"PolaritySwitch_lit$litCount"
            val havePolaritySwitchStep = lpHave(polaritySwitchName,equalityToProve.prf,lpProofScript(Seq(polaritySwitchStep)))
            allSteps = allSteps :+ havePolaritySwitchStep
            usedSymbols = usedSymbols + polaritySwitchEqLit

            // ii) Rewrite the Literal
            val posInClause = findLitInClause(transfLit,child.cl)
            val patternVar = lpOlUntypedVar(lpOlConstantTerm("x"))
            assert(posInClause.length == 1, "application to more than once literals not encoded yet, should already work though, remove Seq in position argument and test")
            val rewritePattern = generateClausePatternTerm(Seq(posInClause.head),child.cl.lits.length,None,patternVar)
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
          val polaritySwitchStep = lpRefine(lpFunctionApp(lpStd_eq_sym,Seq(lpSimp_dne.instanciate(encLeft))))
          val polaritySwitchName = s"PolaritySwitch_lit$litCount"
          val havepolaritySwitchStep = lpHave(polaritySwitchName, equalityToProve.prf, lpProofScript(Seq(polaritySwitchStep)))
          allSteps = allSteps :+ havepolaritySwitchStep
          usedSymbols = usedSymbols + lpSimp_dne

          // ii) Rewrite the Literal
          val posInClause = findLitInClause(transfLit, child.cl)
          assert(posInClause.length == 1, "application to more than once literals not encoded yet,, should already work though, remove Seq in position argument and test")
          val rewritePattern = generateClausePatternTerm(Seq(posInClause.head), child.cl.lits.length, None)
          val rewriteStep = lpRewrite(rewritePattern, lpConstantTerm(polaritySwitchName))
          allRewriteSteps = allRewriteSteps :+ rewriteStep

        case _ => // nothing happens in this case
      }
      litCount = litCount + 1
    }
    allSteps = allSteps ++ allRewriteSteps

    // 3. Apply the variables we abstracted over to the parent clause and refine with it
    allSteps = allSteps :+ lpRefine(lpFunctionApp(parentNameLpEnc, freeVarsChild))

    (lpProofScript(allSteps), usedSymbols)
    }

  def initialEncUnclausified(parent: Clause, child: Clause, sig: Signature)={
    val encParent = term2LP(Clause.asTerm(parent),Map.empty,sig)._1
    val encChild = term2LP(Clause.asTerm(child),Map.empty,sig)._1

    val (childUnquantified, childOuterQuantified) = findBeginningVariables(encChild)

    (encParent, encChild, childUnquantified, childOuterQuantified)
  }

  def findBeginningVariables(t: lpOlTerm, accVars: Seq[lpOlTypedVar] = Seq.empty):(lpOlTerm,Seq[lpOlTypedVar])={
    t match {
      case lpOlMonoQuantifiedTerm(`lpOlForAll`,v0,t0,_) =>
        findBeginningVariables(t0, accVars :+ v0)
      case lpOlBoundTerm(`lpOlForAll`,v0,t0) =>
        findBeginningVariables(t0, accVars ++ v0)
      case _ => (t, accVars)
    }
  }

  def EncDefExSimp(child: ClauseProxy, parent: ClauseProxy, defRuleDefined: Boolean, additionalInfoSimp: Boolean, reducedTerm0: Option[Literal], applyAllDefsTacName: String, parentNameLpEnc: lpConstantTerm, sig: Signature):(Seq[lpProofScriptStep],Option[String]) = {//: (lpProofScript, Set[lpStatement], Set[Signature.Key], Option[String]) = {

    // Encoding of the application of the EP rule defexp_and_simp_and_etaexpand (Definition expansion)
    // The modular proof script can consist of the following steps:
    // 1. If definitions are defined, exhausitively apply them using rewrite
    // 2. If simplifications were applies, verify them using the encoding of (SIMP)
    // 3. Refine with the last step

    if(!additionalInfoSimp){

      val reducedTerm = if (reducedTerm0.isDefined) reducedTerm0.get else throw new Exception(s"LP-Encoding: Trying to encode DefExSimp but reduced Term derived by Leo-III is not defined")

      val (encParent,encChild, _, childOuterQuantified) =  initialEncUnclausified(parent.cl, child.cl, sig)
      Out.lp_debug_info(s"Encoding defExSimp of ${encParent.pretty} to ${encChild.pretty}")

      val encExpTerm = term2LP(asTerm(reducedTerm),Map.empty,sig,Set(),false)._1
      Out.lp_debug_info(s"expanded term: ${asTerm(reducedTerm)}")
      Out.lp_debug_info(s"child: ${child.cl}")

      if (childOuterQuantified.length >=  2) Out.lp_debug_info(s"needs to assume vars")

      val (defExpStep, appliedParent) : (Seq[lpProofScriptStep],lpTerm) =
        if (defRuleDefined){
          val haveStepName = "defExpStep"
          val assumptionName = lpConstantTerm("h")
          val applyParentToStep = lpFunctionApp(lpConstantTerm(haveStepName),Seq(parentNameLpEnc))
          val applyDefExp = Seq(lpEval(lpOlConstantTerm(applyAllDefsTacName)))
          val (assumeStep, refineStepHave): (lpAssume, lpRefine) = {
            (lpAssume(Seq(assumptionName)), lpRefine(assumptionName))
          }
          (Seq(lpImpHaveStepConstructor(haveStepName, Seq(), encParent, encExpTerm,(applyDefExp ++ Seq(assumeStep,refineStepHave)))),applyParentToStep)
        }else (Seq(),parentNameLpEnc)

      val (maybeSimpStep, refineName) : (Seq[lpHave],lpTerm) = if (encExpTerm != encChild){
        Out.lp_debug_info(s"reducedTerm:\n${reducedTerm.pretty}\n${Clause.asTerm(child.cl).pretty}")

        // use the encoding of formula simplification to generate the proofs
        val encExpTermClause = lpClauseInst(encExpTerm,Seq(encExpTerm),Seq.empty)
        val encChildClause = lpClauseInst(encChild,Seq(encChild),Seq.empty)
        val childLitLen = if (isFalse(child.cl.lits.head)) 0 else 1
        val (proofScript, _) = encSimpProofScript(Seq(reducedTerm),child.cl.lits,encExpTermClause,encChildClause,childLitLen,Map.empty,appliedParent,sig)

        val simpStepName = "SimpStep"
        val SimpStep = lpHave(simpStepName,encChild.prf,lpProofScript(proofScript))
        (Seq(SimpStep), lpConstantTerm(simpStepName))
      }else (Seq(), appliedParent)

      val refineStep = lpRefine(refineName)

      ((defExpStep ++ maybeSimpStep) :+ refineStep, None)

    }else{
      Out.lp_debug_info("Rweriting under binder required in order to encode Simplification step")
      (Seq(), Some("Rweriting under binder required in order to encode Simplification step"))
    }
  }

  def encRenameCnf(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, unencodedCNF: Boolean, sig: Signature)={
    val (encParent,encChild, childUnquantified, childOuterQuantified) =  initialEncUnclausified(parent.cl, child.cl, sig)

    if (unencodedCNF) Out.lp_debug_info("Can not encode CNF since it requires rewriting under binder")

    Out.lp_debug_info(s"encoding renameCNF with parent ${encParent.pretty}")
  }


  ////////////////////////////////////////////////////////////////
  ////////// Extensionality
  ////////////////////////////////////////////////////////////////

  case class funcExtState(currParentLits: Seq[lpOlTerm],
                          currentUnencParent: Seq[Literal],
                          lastStepName: lpTerm,
                          allSteps: Seq[lpProofScriptStep],
                          usedSymbols: Set[lpStatement],
                          literalsToEqRW: Seq[lpProofScriptStep],
                          cantEncode: Option[String])

  // Recursive helper that follows the chain of edited literal pairs.
  def followChain(edits: Seq[(Literal, Literal)], start: Literal): (Literal, Seq[(Literal, Literal)]) = {
    edits.find {
      case (from, _) => from == start
    } match {
      case Some((_, next)) =>
        // Remove the found tuple and continue following the chain.
        val index = edits.indexWhere(_ == (start, next))
        val updatedEdits = if (index < 0) edits else edits.take(index) ++ edits.drop(index + 1)
        followChain(updatedEdits, next)
      case None =>
        // No further mapping found; return the current literal.
        (start, edits)
    }
  }

  def encFuncExtPos(child: ClauseProxy, parent: ClauseProxy, editedLiterals: Seq[(Literal, Literal)], parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Set[lpStatement], Option[String]) = {
    
    // Encoding of the application of the EP rule FuncExt (Functional Extensionality)
      // The modular proof script can consist of the following steps:
      // 1. Abstract over free variables
      // For each affected literal:
      //    2.   Instantiate PFE and use it to define a new hypothesis
      //    3.   Use the proven hypothesis to apply the changes to the (instantiated) parent formula, using the appropriate transform rule
      //    4 a) If necessary, transform the literal in the parent to equational form
      //    4 b) If the order within the literal was changed, apply eqSym_eq
      // 5. If the order of literals was changed, generate a permute rule and apply it to permute the literals
      // 6. Refine with the last step

    /////////////////////////////////////////////////////
    //// preliminary

    val allFreeVars = editedLiterals.flatMap(pair => pair._2.fv) ++ child.cl.implicitlyBound
    val bVarMap = clauseVars2LP(allFreeVars, sig, Set.empty)._2
    val encParent = clause2LP(parent.cl, Set(), sig)._1
    val impBoundParent = encParent.impBoundVars
    Out.lp_debug_info(s"Amount of edited Literals detected: ${editedLiterals.length}")

    // Check if we will need to do a permutation
      // -> Since FuncExt can be applied in a nested fashion, we first need to construct a mapping of each literal of the
      //    parent to its final transformed stage and then through the comparison of positions we can infer the permutation
    val litsParent = parent.cl.lits.diff(child.cl.lits)
    // Map each final literal to its initial form prior to exhaustive FuncExt application
    val (funcExtMap, _) = litsParent.foldLeft((Map.empty[Literal, Literal], editedLiterals)) {
      case ((acc, edits), parentLit) =>
        val (finalLit, updatedEdits) = followChain(edits, parentLit)
        (acc + (finalLit -> parentLit), updatedEdits)
    }
    // Compute the permutation by mapping each literal in child.cl to its corresponding index in the parent
    val permutation: Seq[Int] = child.cl.lits.map { childLit =>
      val correspondingParentLit = funcExtMap.getOrElse(childLit, childLit)
      parent.cl.lits.indexOf(correspondingParentLit)
    }

    /////////////////////////////////////////////////////
    //// 1. Abstract over free variables

    val freeVarsChild = child.cl.implicitlyBound.map(var0 => lpUntypedVar(lpConstantTerm(bVarMap(var0._1))))
    val initialStep = if (freeVarsChild.nonEmpty) Seq(lpAssume(freeVarsChild)) else Seq()

    // Instantiate the initial state
    val initialState = funcExtState(
      currParentLits = encParent.lits,
      currentUnencParent = parent.cl.lits,
      lastStepName = lpFunctionApp(parentNameLpEnc, liftVarsToMeta(impBoundParent)),
      allSteps = initialStep,
      usedSymbols = Set(),
      literalsToEqRW = Seq(),
      cantEncode = None
    )

    Out.lp_debug_info(s"initial parent:${lpOlUntypedBinaryConnectiveTerm_multi(lpOr, initialState.currParentLits).pretty}")

    /////////////////////////////////////////////////////
    //// Steps 2 to 4

    val postPfeState = editedLiterals.zipWithIndex.foldLeft(initialState) { case (state, (pair, idx)) =>
      val (origLit, edLit) = pair
      if (state.currentUnencParent.contains(origLit)) {
        if (!state.cantEncode.isDefined){
          if (origLit.polarity) {
            val (error, pfeSteps, pfeUsedSymbols, pfeStepName, pfeRwImplicitTrans, updatedParentLits) = posFuncExtStep(origLit, edLit, state.currentUnencParent, state.currParentLits, permutation, state.lastStepName, bVarMap, sig, idx)

            Out.lp_debug_info(s"pfeRwImplicitTrans:\n${pfeRwImplicitTrans.map(_.pretty)}}")
            // Return a new state with the updated values
            state.copy(
              cantEncode = if (state.cantEncode.isDefined) state.cantEncode else error,
              allSteps = state.allSteps ++ pfeSteps,
              usedSymbols = state.usedSymbols ++ pfeUsedSymbols,
              lastStepName = pfeStepName,
              literalsToEqRW = state.literalsToEqRW ++ pfeRwImplicitTrans,
              currParentLits = updatedParentLits,
              currentUnencParent = state.currentUnencParent.updated(state.currentUnencParent.indexOf(origLit), edLit)
            )
          } else state.copy(cantEncode = if (state.cantEncode.isDefined) state.cantEncode else Some("NFE literals unencoded"))
        } else state
      } else {
        Out.lp_debug_info(s"literal ${origLit.pretty} could not be found in parent")
        state
      }
    }

    /////////////////////////////////////////////////////
    //// 5. Apply permutation if necessary

    val postPermStep = if ((permutation != parent.cl.lits.indices) && (!postPfeState.cantEncode.isDefined)) {
      Out.lp_debug_info(s"Permutation required: $permutation")
      val permutationInstance = metaPermutation.instanciate(permutation,postPfeState.currParentLits,postPfeState.lastStepName)
      Out.lp_debug_info(s"proposed permutation: ${permutationInstance.pretty}")
      postPfeState.copy(
        allSteps = (postPfeState.allSteps ++ postPfeState.literalsToEqRW) :+ lpRefine(lpFunctionApp(permutationInstance,Seq())),
        usedSymbols = postPfeState.usedSymbols + metaPermutation
      )
    } else {
      postPfeState.copy(allSteps = (postPfeState.allSteps ++ postPfeState.literalsToEqRW):+ lpRefine(lpFunctionApp(postPfeState.lastStepName, Seq())))
    }

  if (postPermStep.cantEncode.isDefined) (lpProofScript(postPermStep.allSteps),postPermStep.usedSymbols, Some(s"FuncExt can not be encoded: ${postPermStep.cantEncode.get}"))
  else (lpProofScript(postPermStep.allSteps),postPermStep.usedSymbols, None)
}

  private def posFuncExtStep(origLit: Literal, edLit: Literal, currentUnencParent: Seq[Literal], currParentLits: Seq[lpOlTerm], permutation: Seq[Int], lastStepName: lpTerm, bVarMap: Map[Int, String], sig: Signature, editLitCount: Int): (Option[String], Seq[lpProofScriptStep], Set[lpStatement], lpTerm, Seq[lpProofScriptStep], Seq[lpOlTerm]) = {
    // encode the application of an individual step

    /////////////////////////////////////////////////////
    //// Preliminary

    val encOrigLit = lpLiteral(origLit, bVarMap, sig)
    val encEditLit = term2LP(asTerm(edLit), bVarMap, sig)._1
    val indexOfLit = currentUnencParent.indexOf(origLit)
    Out.lp_debug_info(s"Applying FuncExt to literal ${encOrigLit.term.pretty}, resulting in ${encEditLit.pretty}")

    val appliedVar = identifyAppliedTerm(origLit, encOrigLit.term, edLit, bVarMap, sig)
    Out.lp_debug_info(s"applying: ${appliedVar}")

    /////////////////////////////////////////////////////
    //// 2.   Instantiate PFE and use it to define a new hypothesis

    val namefuncExtStep = s"${encPFE().name.pretty}_$editLitCount"
    // Construction of the literal to be proved
    val currentTypeSeq: Seq[lpOlType] = encOrigLit.tyLhs match {
      case lpOlFunctionType(types) => types
      case _ => throw new Exception(s"LP-ENCODING: Expected function type but found ${encOrigLit.tyLhs.pretty}")
    }
    val appliedType = currentTypeSeq.tail
    val appliedLit = lpLiteral(
      betaReduceLpApplication(lpOlFunctionApp(encOrigLit.left, Seq(Left(appliedVar)))),
      betaReduceLpApplication(lpOlFunctionApp(encOrigLit.right, Seq(Left(appliedVar)))),
      if (appliedType.length == 1) appliedType.head else lpOlFunctionType(appliedType),
      true, true)
    // Instanciation of the step
    val impToProve = lpMlFunctionType(Seq(encOrigLit.term.prf, appliedLit.term.prf))
    val funcExtImp = lpRefine(encPFE().instanciate(None, encOrigLit.left, encOrigLit.right, appliedVar))
    val pfeInst = lpHave(namefuncExtStep, impToProve, lpProofScript(Seq(funcExtImp)))
    Out.lp_debug_info(s"Instance of $namefuncExtStep to prove ${impToProve.pretty}")
    Out.lp_debug_info(s"Types of the literal before application: ${currentTypeSeq.map(_.pretty)} after: ${appliedType.map(_.pretty)}")
    Out.lp_debug_info(s"reduced applied lit ${appliedLit.term.pretty}")

    /////////////////////////////////////////////////////
    //// 3.   Use the proven hypothesis to apply the changes to the (instantiated) parent formula, using the appropriate transform rule
    val applicationStepName = lpConstantTerm(s"${namefuncExtStep}_app")
    // if the length of the parent is greater than one, we need to use transform
    val (pfeApp, usedSymbols, newParentLits) = applyInstFuncExtRule(currParentLits, appliedLit, indexOfLit, namefuncExtStep, applicationStepName, lastStepName)
    val allSteps = Seq(pfeInst, pfeApp)

    /////////////////////////////////////////////////////
    //// 4. Apply necessary implicit transformations
    // Compare the derived literal with the literal that it is mapped to and apply any necessary transformations
    val (cantEncode, usedSymbolsTrans, literalsToEqRW) = implicitRwTransFuncEx(encEditLit, appliedLit.term, permutation, indexOfLit, currParentLits.length)
    if (cantEncode) {
      Out.lp_debug_info(s"Implicit RW transformation necessary but can not be applied")
      (Some("unencoded transformation necessary"), Seq(), Set(), lastStepName, Seq(), Seq())
    } else (None, allSteps, usedSymbols ++ usedSymbolsTrans, applicationStepName, literalsToEqRW, newParentLits)
  }

  private def identifyAppliedTerm(origLit: Literal, encOrigLit: lpOlTerm, edLit: Literal, bVarMap: Map[Int, String], sig:Signature): lpOlTerm = {
    // Given two literals, identify a term that we can apply to both sides of the original one to obtain the edited one
    // Usually, this will be variables, but in some cases we need to use witness terms.

    val freshVars = edLit.fv.diff(origLit.fv)
    val allApppliedVars: Seq[lpOlTerm] = freshVars.map(freshVar => lpOlTypedVar(lpOlConstantTerm(bVarMap(freshVar._1)), type2LP(freshVar._2, sig))).toSeq
    // As an individual transformation represents one individual variable application, the list can not be longer than 1
    assert(allApppliedVars.length <= 1)
    // If the applied variables of both sides disappear due to ß-reduction, we use witness terms for the application instead of variables
    // In this case, the sides of the literals must both be lambda terms
    if (allApppliedVars.isEmpty) {
      val encTypes = encOrigLit match {
        case lpOlTypedBinaryConnectiveTerm(_, _, lpOlLambdaTerm(vars, _), _) =>
          vars.head match {
            case Left(termVar) => termVar.ty
            case Right(_) => throw new Exception(s"LP-Encoding: found unexpected type variables")
          }
        case _ =>
          throw new Exception(s"LP-Encoding: Unable to infer applied variable in FuncEx encoding")
      }
      Out.lp_debug_info(s"Witness-Term is needed")
      encTypes match {
        case ty0: lpOlType => lpWitness(ty0)
        case _ => throw new Exception(s"trying to generate witness term for a type that is not an encoded HOL type")
      }
    } else allApppliedVars.head
  }

  private def applyInstFuncExtRule(currParentLits: Seq[lpOlTerm], appliedLit: lpLiteral, indexOfLit: Int, namefuncExtStep:String,  applicationStepName: lpConstantTerm, lastStepName: lpTerm): (lpHave, Set[lpStatement], Seq[lpOlTerm])={
    // use the instiaciated rule for PFE or NFE and apply it to the desired literal in the parent
    val (proofTerm, usedSymbols): (lpTerm, Set[lpStatement]) = if (currParentLits.length > 1)
     ( metaTransform.instanciate(currParentLits, indexOfLit, lpConstantTerm(namefuncExtStep), lastStepName), Set(encPFE(), metaPermutation))
    else
      (lpFunctionApp(lpConstantTerm(namefuncExtStep), Seq(lastStepName)), Set(encPFE()))
    // todo: when encoding NFE, make sure we do not by default add PFE as a needed Rule
    val refineWithFunExt = lpRefine(lpFunctionApp(proofTerm, Seq()))
    val newParentLits = currParentLits.updated(indexOfLit, appliedLit.term)
    val pfeApp = lpHave(applicationStepName.name, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, newParentLits).prf, lpProofScript(Seq(refineWithFunExt)))
    Out.lp_debug_info(s"Successfully applied $namefuncExtStep (in setp $applicationStepName)")
    Out.lp_debug_info(s"updatedParent: ${lpOlUntypedBinaryConnectiveTerm_multi(lpOr, newParentLits).pretty}")
    (pfeApp,usedSymbols,newParentLits)
  }

  private def implicitRwTransFuncEx(encEditLitTerm: lpOlTerm,appliedLitTerm: lpOlTerm, permutation: Seq[Int], indexOfLit: Int, lenParent: Int):(Boolean, Set[lpStatement], Seq[lpProofScriptStep])={
    if (!alphaEquivalent(encEditLitTerm, appliedLitTerm)) {
      Out.lp_debug_info(s"Looking for transformations to get from \n${encEditLitTerm} to \n${appliedLitTerm}}")
      // if we had a permutation, we need to infer the index in the clause modulo application
      val indexModuloPerm = permutation.indexOf(indexOfLit)
      val (literalsToEqRW, usedSymbolsTrans, canEncode0) = transformLiteral(encEditLitTerm, appliedLitTerm, indexModuloPerm, lenParent)
      if (canEncode0) {
        Out.lp_debug_info(s"Transformation to equational form is applied: ${literalsToEqRW.map(_.pretty)}")
        (false, usedSymbolsTrans, literalsToEqRW)
      } else {
        Out.lp_debug_info(s"Transformation to equational form necessary but can not be applied")
        (true, Set(), Seq())
      }
    } else (false, Set(), Seq())
  }



  def encBoolExt(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, addInfo: Set[(Literal,Seq[Literal])], sig: Signature): (lpProofScript, Set[lpStatement], Option[String]) = {

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

    if (parent.cl.lits.length > 1) {
      (lpProofScript(Seq.empty),usedSymbols,Some(s"Encoding of boolExt in LP for clauses with more than one literal not encoded yet"))
    }
    else {
      allSteps = allSteps :+ lpRefine(lpFunctionApp(transitions.head, Seq(lpFunctionApp(parentNameLpEnc, freeVarsChild))))
      val proof = lpProofScript(allSteps)

      // 6. Refine with the last proven step
      (proof, usedSymbols, None)
    }
  }


  ////////////////////////////////////////////////////////////////
  ////////// Primary Inference Rules
  ////////////////////////////////////////////////////////////////

  def encEqFactLiterals(otherLit: Literal, maxLit: Literal, uc1Orig: Literal, uc2Orig: Literal, parent: Clause, child: Clause, bVarMap: Map[Int, String], sourceBefore: lpTerm, nameStep: lpOlTerm, sig: Signature): (lpProofScriptStep, Set[lpStatement], Boolean) = {
    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty
    val nameAssumption = lpOlConstantTerm("h1")
    var lastStepName: lpTerm = nameAssumption
    var canEncode: Boolean = true


    var otherLit_l0: lpOlTerm = term2LP(otherLit.left, bVarMap, sig)._1
    var otherLit_r0: lpOlTerm = term2LP(otherLit.right, bVarMap, sig)._1
    var maxLit_l0: lpOlTerm = term2LP(maxLit.left, bVarMap, sig)._1
    var maxLit_r0: lpOlTerm = term2LP(maxLit.right, bVarMap, sig)._1
    val ty = if (maxLit.equational) maxLit.left.ty else asTerm(maxLit).ty
    val encType = type2LP(ty, sig)
    val (posOtherLit0, posMaxLit0) = (findLitInClause(otherLit, parent),findLitInClause(maxLit, parent))
    assert(posMaxLit0.length == 1 && posOtherLit0.length == 1, "multiple occurences of max or alternative literal found in lpEncoidng") //todo: what does Leo do here?
    var (posMaxLit, posOtherLit) = (posMaxLit0.head, posOtherLit0.head)
    var lenParent = parent.lits.length
    val polarityOfRule = maxLit.polarity

    val otherLitEnc = if (otherLit.equational) {
      val otherLitEq = lpOlTypedBinaryConnectiveTerm(lpEq,encType,otherLit_l0,otherLit_r0)
      if (otherLit.polarity) otherLitEq else lpOlUnaryConnectiveTerm(lpNot,otherLitEq)
    }else{
      if (otherLit.polarity) otherLit_l0 else lpOlUnaryConnectiveTerm(lpNot,otherLit_l0)
    }
    val maxLitEnc = if (maxLit.equational) {
      val maxLitEq = lpOlTypedBinaryConnectiveTerm(lpEq, encType, maxLit_l0, maxLit_r0)
      if (maxLit.polarity) maxLitEq else lpOlUnaryConnectiveTerm(lpNot, maxLitEq)
    } else {
      if (maxLit.polarity) maxLit_l0 else lpOlUnaryConnectiveTerm(lpNot, maxLit_l0)
    }
    //val maxLitEq = lpOlTypedBinaryConnectiveTerm(lpEq, encType, maxLit_l, maxLit_r)
    //val maxLitEnc = if (maxLit.polarity) otherLitEq else lpOlUnaryConnectiveTerm(lpNot, maxLitEq)
    val parentEnc = clause2LP(parent, Set.empty, sig)._1
    val parentLits = parentEnc.lits
    var currentLits = parentLits
    assert(otherLit.right.ty == maxLit.right.ty)
    Out.lp_debug_info(s"Applying to parent ${parentEnc.pretty}")
    Out.lp_debug_info(s"MaxLit is ${maxLitEnc.pretty}, OtherLit is ${otherLitEnc.pretty}")

    // infer the other lit and the unification constraint in the child
    val childOtherLitEnc = term2LP(asTerm(child.lits(lenParent - 2)),bVarMap,sig)._1
    val childUc1Enc = term2LP(asTerm(uc1Orig),bVarMap,sig)._1
    val childUc2Enc = term2LP(asTerm(uc2Orig),bVarMap,sig)._1

    // Identify the two literals to be unified and compose a function proving the rule application including all necessary transformations:
    //    a) If either of the literals is not equational, transform to the equational form with the correct polarity
    //    b) If the order of the left- and right-hand sides in either of the literals has to changed in order for the encoded equal factoring rule to associate the sides correctly, apply eqSym_eq
    //    b.5) apply permutation if necessary
    //    c) Apply the appropriate version of equal factoring (EqFact_p or EqFact_n)
    //    d) Prove the transformation to non-equational literals of any literals that are non-equational
    //    e) If the order within any of the equality literals has changed after the rule application as a result of the term ordering, proof the transformation using eqSym_eq
    //    f) If the order within any of the equality literals has changed after the rule application as a result of the term ordering, proof the transformation using eqSym_eq

    //    a) If either of the literals is not equational, transform to the equational form with the correct polarity
    // infer how the literals need to be transformed in order for the rule to be applied:
    // check which of the sides of the other literal is paired with which of the sides of the max literal

    // do all of the necessary trnasformations and construct the transformed literals
    // - check weather you need to transform the other and max lit to equality
    // - check weather you need to change polarity of the other or max lit
    // - check weather you need to swap sides of the other lit
    // -> all in one big transform-step
    // based on the transformed literals, do the EqFact transformation
    // based on the associated stuff in the literals in parent...
    // ... transform back
    // ... and decide weather you need a permutation

    // infer weather a permutation will be needed
    // construct the permutation necessary to move the max and other lit to the end in the right order
    val indices = parent.lits.indices.toList
    val permutaion = indices.filterNot(n => n == posMaxLit || n == posOtherLit) ++ Seq(posOtherLit, posMaxLit)
    if (indices != permutaion) {
      Out.lp_debug_info(s"need to apply permutatin: $permutaion")
      val permStepName = "Permutation"
      val permutedLits = permutaion.map(currentLits(_))
      val permutationApp = permutationStepSkript(currentLits, permutedLits, lastStepName)
      val permutationStep = lpHave("Permutation", lpOlUntypedBinaryConnectiveTerm_multi(lpOr, permutedLits).prf, lpProofScript(Seq(lpRefine(permutationApp))))
      allSteps = allSteps :+ permutationStep
      usedSymbols = usedSymbols + metaPermutation
      lastStepName = lpConstantTerm(permStepName)
      Out.lp_debug_info(s"permutation applied")
      currentLits = permutedLits
    }

    var allTransformSteps : Seq[lpProofScriptStep] = Seq.empty

    val otherLitBeforeEqFact : (lpOlTerm, lpOlTerm, lpOlTerm) = {
      if (!otherLit.equational){
        val transformOtherLit0 = equationalForm(otherLitEnc,polarityOfRule)
        val (newSteps, newUsedSymbols, newCanEncode) = transformLiteral(transformOtherLit0._1,otherLitEnc,permutaion(posOtherLit),lenParent)
        allTransformSteps =  allTransformSteps ++ newSteps
        usedSymbols = usedSymbols ++ newUsedSymbols
        if (!newCanEncode) {
          canEncode = false
          Out.lp_debug_info(s"unable to do eqFactoring transformation for other lit")
        }
        Out.lp_debug_info(s"transformed other literal to ${transformOtherLit0._1.pretty}")
        transformOtherLit0
      }else{
        if (otherLit.polarity != polarityOfRule){
          throw new Exception(s"when encoding equal factoring, wrong polarity of rule was encountered")
        } else {
          //    b) If the order of the left- and right-hand sides in either of the literals has to changed in order for the encoded equal factoring rule to associate the sides correctly, apply eqSym_eq
          if ((otherLit.right == uc1Orig.left || otherLit.right == uc1Orig.right) && (otherLit.left == uc2Orig.left || otherLit.left == uc2Orig.right)) {
            // flip the other literal
            val flippedOtherLitEq = lpOlTypedBinaryConnectiveTerm(lpEq, encType, otherLit_r0, otherLit_l0)
            val flippedOtherLit = if (polarityOfRule) flippedOtherLitEq else lpOlUnaryConnectiveTerm(lpNot,flippedOtherLitEq)
            val rewriteStep = flipStep(posOtherLit, parent.lits.length, polarityOfRule, encType)
            allTransformSteps = allTransformSteps :+ rewriteStep
            usedSymbols = usedSymbols + flipLiteral()
            Out.lp_debug_info(s"flipped other literal to ${flippedOtherLit.pretty}")
            (flippedOtherLit,otherLit_r0,otherLit_l0)
          } else (otherLitEnc,otherLit_l0,otherLit_r0)
        }
      }
    }
    val maxLitBeforeEqFact = {
      if (!maxLit.equational) {
        val transformMaxLit0 = equationalForm(maxLitEnc, polarityOfRule)
        val (newSteps, newUsedSymbols, newCanEncode) = transformLiteral(transformMaxLit0._1,maxLitEnc, permutaion(posMaxLit), lenParent)
        allTransformSteps = allTransformSteps ++ newSteps
        usedSymbols = usedSymbols ++ newUsedSymbols
        if (!newCanEncode) {
          canEncode = false
          Out.lp_debug_info(s"unable to do eqFactoring transformation for maxLit")
        }
        Out.lp_debug_info(s"transformed max literal to ${transformMaxLit0._1.pretty}")
        transformMaxLit0
      } else {
        assert(maxLit.polarity == polarityOfRule)
        (maxLitEnc,maxLit_l0,maxLit_r0)
      }
    }

    // apply all of the transfomration
    if (allTransformSteps.nonEmpty){
      allTransformSteps = allTransformSteps :+ lpRefine(lpFunctionApp(lastStepName,Seq()))
      currentLits = Seq(otherLitBeforeEqFact._1,maxLitBeforeEqFact._1)
      val transformStepName = "pre_eqFac_transform"
      allSteps = allSteps :+ lpHave(transformStepName,lpOlUntypedBinaryConnectiveTerm_multi(lpOr,currentLits).prf,lpProofScript(allTransformSteps))
      lastStepName = lpConstantTerm(transformStepName)
    }


    // apply equal factoring
    val encEqFact: lpTerm = lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule).instanciate(otherLitBeforeEqFact._2, otherLitBeforeEqFact._3, maxLitBeforeEqFact._2, maxLitBeforeEqFact._3, encType.lift2Poly)
    currentLits = lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule).result(otherLitBeforeEqFact._2, otherLitBeforeEqFact._3, maxLitBeforeEqFact._2, maxLitBeforeEqFact._3, encType.lift2Poly)
    // now we can instanciate and apply equal factoring
    val afterEqFacAp: lpMlType = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, currentLits).prf
    usedSymbols = usedSymbols + lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule)
    val nameEqFactoringStep = lpConstantTerm("EqFact")
    val eqFactStep = lpProofScript(Seq(lpRefine(lpFunctionApp(encEqFact, Seq(lastStepName)))))
    allSteps = allSteps :+ lpHave(nameEqFactoringStep.name, afterEqFacAp, eqFactStep)
    Out.lp_debug_info(s"generated equal factoring step:\n${eqFactStep.pretty}")
    lastStepName = nameEqFactoringStep

    // if we need more transformations, carry them out
    var allBackTransformSteps : Seq[lpProofScriptStep] = Seq.empty
    Out.lp_debug_info(s"derived other lit = ${otherLitBeforeEqFact._1.pretty}, found other lit = ${childOtherLitEnc.pretty}")
    if (otherLitBeforeEqFact._1 != childOtherLitEnc){
      val (newSteps, newUsedSymbols, newCanEncode) = transformLiteral(childOtherLitEnc,otherLitBeforeEqFact._1,0,currentLits.length)
      allBackTransformSteps = allBackTransformSteps ++ newSteps
      usedSymbols = usedSymbols ++ newUsedSymbols
      currentLits = currentLits.updated(0,childOtherLitEnc)
      if (!newCanEncode) {
        canEncode = false
        Out.lp_debug_info(s"unable to do back transformation for other lit")
      }
      Out.lp_debug_info(s"transformed other literal to ${childOtherLitEnc.pretty}")
    }
    if (currentLits(1) != childUc1Enc){
      val (newSteps, newUsedSymbols, newCanEncode) = transformLiteral(childUc1Enc, currentLits(1), 1, currentLits.length)
      allBackTransformSteps = allBackTransformSteps ++ newSteps
      usedSymbols = usedSymbols ++ newUsedSymbols
      currentLits = currentLits.updated(1,childUc1Enc)
      if (!newCanEncode) {
        canEncode = false
        Out.lp_debug_info(s"unable to do back transformation for UC1")
      }
      Out.lp_debug_info(s"transformed UC1 to ${childUc1Enc.pretty}")
    }
    if (currentLits(2) != childUc2Enc) {
      val (newSteps, newUsedSymbols, newCanEncode) = transformLiteral(childUc2Enc, currentLits(2), 2, currentLits.length)
      allBackTransformSteps = allBackTransformSteps ++ newSteps
      usedSymbols = usedSymbols ++ newUsedSymbols
      currentLits = currentLits.updated(2,childUc2Enc)
      if (!newCanEncode) {
        canEncode = false
        Out.lp_debug_info(s"unable to do back transformation for UC2")
      }
      Out.lp_debug_info(s"transformed UC2 to ${childUc2Enc.pretty}")
    }

    // apply all of the transfomration
    if (allBackTransformSteps.nonEmpty) {
      val transformStepName = "post_eqFac_transform"
      allBackTransformSteps = allBackTransformSteps :+ lpRefine(lpFunctionApp(lastStepName,Seq()))
      allSteps = allSteps :+ lpHave(transformStepName, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, currentLits).prf, lpProofScript(allBackTransformSteps))
      lastStepName = lpConstantTerm(transformStepName)
    }

    // now we can construct the whole proof
    val typeOfWholeProof = lpMlFunctionType(Seq(lpOlUntypedBinaryConnectiveTerm_multi(lpOr, parentLits).prf, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, currentLits).prf))
    val assumeStep = lpAssume(Seq(nameAssumption))
    allSteps = Seq(assumeStep) ++ allSteps
    allSteps = allSteps :+ lpRefine(lpFunctionApp(lastStepName,Seq()))

    val completeHaveStep = lpHave(nameStep.pretty,typeOfWholeProof,lpProofScript(allSteps))

    (completeHaveStep,usedSymbols, canEncode)

  }
  def encEqFactLiteralsOld(otherLit: Literal, maxLit: Literal, uc1Orig: Literal, cc2Orig: Literal, parent: Clause, child: Clause, bVarMap: Map[Int, String], sourceBefore: lpTerm, nameStep: lpOlTerm, sig: Signature): (lpProofScriptStep, Set[lpStatement]) = {

    var lastStepName: lpTerm = sourceBefore
    var lastStepLits: Seq[lpOlTerm] = Seq.empty
    var usedSymbols: Set[lpStatement] = Set.empty
    var allSteps: Seq[lpProofScriptStep] = Seq.empty

    // todo: all this should happen when processing the clause! change before generalizing to longer clauses
    val otherLitEnc = term2LP(asTerm(otherLit),bVarMap,sig)._1
    val maxLitEnc = term2LP(asTerm(maxLit),bVarMap,sig)._1
    val parentEnc = clause2LP(parent,Set.empty,sig)._1


    // infer weather a permutation will be needed
    val posMaxLit0 = findLitInClause(maxLit,parent)
    val posOtherLit0 = findLitInClause(otherLit,parent)
    assert(posMaxLit0.length == 1 && posOtherLit0.length == 1, "multiple occurences of max or alternative literal found in lpEncoidng") //todo: what does Leo do here?
    var (posMaxLit, posOtherLit) = (posMaxLit0.head, posOtherLit0.head)
    Out.lp_debug_info(s"index of max lit: $posMaxLit, index of other Lit: $posOtherLit")
    // construct the permutation necessary to move the max and other lit to the end in the right order
    val indices = parent.lits.indices.toList
    val permutaion = indices.filterNot(n => n == posMaxLit || n == posOtherLit) ++ Seq(posOtherLit,posMaxLit)
    posOtherLit = permutaion.length - 2
    var parentLits = parentEnc.lits

    assert(otherLit.right.ty == maxLit.right.ty)
    val eqTypeEnc = type2LP(otherLit.right.ty,sig)
    Out.lp_debug_info(s"Applying to parent ${parentEnc.pretty}")
    Out.lp_debug_info(s"MaxLit is ${maxLitEnc.pretty}, OtherLit is ${otherLitEnc.pretty}")

    // the values that we will pass on to the instantiation of the actual rule will be defined during this step and only need to be instantiated here
    var otherLit_l0: lpOlTerm = lpOlNothing
    var otherLit_r0: lpOlTerm = lpOlNothing
    var maxLit_l: lpOlTerm = lpOlNothing
    var maxLit_r: lpOlTerm = lpOlNothing
    val ty = if (maxLit.equational) maxLit.left.ty else asTerm(maxLit).ty
    val encType = type2LP(ty, sig)

    // Identify the two literals to be unified and compose a function proving the rule application including all necessary transformations:
    //    a) If the order of the left- and right-hand sides in either of the literals has to changed in order for the encoded equal factoring rule to associate the sides correctly, apply eqSym_eq
    //    b) If either of the literals is not equational, transform to the equational form with the correct polarity
    //    b.5) apply permutation if necessary
    //    b.8) flip the other lither if necessary
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
    Out.lp_debug_info(s"polarity of the rule: $polarityOfRule")
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
      Out.lp_debug_info(s"Transform other lit? $transformOtherLit, transform max lit? $transformMaxLit")
      // Then the actual transformation is encoded
      if (literalsToTransform.nonEmpty) {
        val nameTransfStep = lpConstantTerm("TransformToEqLits")
        val (transformationStep,litMap,_,usedSymbolsNew) = makeLiteralEquational_proofSkript(literalsToTransform,parentEnc,lastStepName,true,polarityOfRule,nameTransfStep)
        parentLits = parentLits.map(lit => if (litMap.keySet.contains(lit)) litMap(lit)._1 else lit)
        allSteps = allSteps :+ transformationStep
        Out.lp_debug_info(s"Transformation steps generated successfully: \n${transformationStep.pretty}")
        lastStepName = nameTransfStep
        if (transformOtherLit){
          val otherLitTrans = litMap(otherLitEnc)
          otherLitAsEq = otherLitTrans._1
          otherLit_l0 = otherLitTrans._2
          otherLit_r0 = otherLitTrans._3
          usedSymbols = usedSymbolsNew
          literalsToTransform2 = literalsToTransform2 :+ otherLitAsEq
          Out.lp_debug_info(s"transformed other lit to ${otherLitAsEq.pretty}")
        } else{
          otherLitAsEq = otherLitEnc
          otherLit_l0 = term2LP(otherLit.left,bVarMap,sig)._1
          otherLit_r0 = term2LP(otherLit.right,bVarMap,sig)._1
        }
        if (transformMaxLit) {
          val maxLitTrans = litMap(maxLitEnc)
          maxLitAsEq = maxLitTrans._1
          maxLit_l = maxLitTrans._2
          maxLit_r = maxLitTrans._3
          usedSymbols = usedSymbolsNew
          Out.lp_debug_info(s"transformed max lit to ${maxLitAsEq.pretty}")
        } else {
          maxLitAsEq = otherLitEnc
          maxLit_l = term2LP(maxLit.left, bVarMap, sig)._1
          maxLit_r = term2LP(maxLit.right, bVarMap, sig)._1
        }
      }else throw new Exception("In the LP encoding of EqFact, non-equational literlas were detected but no transformation to equality literals could be performed")
    } else {
      otherLitAsEq = otherLitEnc
      otherLit_l0 = term2LP(otherLit.left, bVarMap, sig)._1
      otherLit_r0 = term2LP(otherLit.right, bVarMap, sig)._1
      maxLitAsEq = otherLitEnc
      maxLit_l = term2LP(maxLit.left, bVarMap, sig)._1
      maxLit_r = term2LP(maxLit.right, bVarMap, sig)._1
      Out.lp_debug_info(s"no transformation to equational form necessary")
    }

    // b.5) apply permutation if necessary
    if (indices != permutaion){
      Out.lp_debug_info(s"need to apply permutatin: $permutaion")
      val permStepName = "Permutation"
      val permutedParents = permutaion.map(parentLits(_))
      val permutationApp = permutationStepSkript(parentLits,permutedParents, lastStepName)
      val permutationStep = lpHave("Permutation",lpOlUntypedBinaryConnectiveTerm_multi(lpOr,permutedParents).prf,lpProofScript(Seq(lpRefine(permutationApp))))
      allSteps = allSteps :+ permutationStep
      usedSymbols = usedSymbols + metaPermutation
      lastStepName = lpConstantTerm(permStepName)
      Out.lp_debug_info(s"permutation applied")
      parentLits = permutedParents
    }

    // b.8)
    // test which sides of the other lit and the max lit were combined to form the unification constraints
    // if the lhs of the other lit ends up in the second unification constraint and the rhs in the first one, the other lit needs to be flipped
    // todo: update for case where other lit is negative in negative EqFactor
    var haveEqFactSteps: Seq[lpProofScriptStep] = Seq.empty
    val (otherLit_l, otherLit_r) = if ((otherLit.right == uc1Orig.left||otherLit.right == uc1Orig.right)&&(otherLit.left == cc2Orig.left||otherLit.left == cc2Orig.right)){
      val rewriteStep = flipStep(posOtherLit,parent.lits.length,otherLit.polarity,eqTypeEnc)
      val otherLitFlipStepName = "OtherLitSym"
      val flippedOtherLit = lpOlTypedBinaryConnectiveTerm(lpEq,encType,otherLit_r0,otherLit_l0)
      val otherLitFlipStep = lpHave(otherLitFlipStepName,lpOlUntypedBinaryConnectiveTerm_multi(lpOr,parentLits.updated(posOtherLit,flippedOtherLit)).prf,lpProofScript(Seq(rewriteStep)))
      haveEqFactSteps = haveEqFactSteps :+ rewriteStep
      lastStepName = lpConstantTerm(otherLitFlipStepName)
      usedSymbols = usedSymbols + flipLiteral()
      Out.lp_debug_info(s"flipped other literal to ${flippedOtherLit.pretty}")
      (otherLit_r0,otherLit_l0)
    }else (otherLit_l0,otherLit_r0)

    // c) Apply the appropriate version of equal factoring (EqFact_p or EqFact_n)
    val encEqFact : lpTerm = lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule).instanciate(otherLit_l, otherLit_r, maxLit_l, maxLit_r,encType.lift2Poly)
    lastStepLits = lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule).result(otherLit_l, otherLit_r, maxLit_l, maxLit_r,encType.lift2Poly)
    // if we flipped the sides of the other lit to associate them correctly, we need to apply the operation here
    if (otherLit_l0 != otherLit_l) lastStepLits = lastStepLits.updated(0,lpOlTypedBinaryConnectiveTerm(lpEq,encType,otherLit_l0,otherLit_r0))
    // now we can instanciate and apply equal factoring
    val afterEqFacAp : lpMlType = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,lastStepLits).prf
    usedSymbols = usedSymbols + lpInferenceRuleEncoding.eqFactoring_script(polarityOfRule)
    val nameEqFactoringStep = lpConstantTerm("EqFact")
    haveEqFactSteps = haveEqFactSteps :+ lpRefine(lpFunctionApp(encEqFact,Seq(lastStepName)))
    val eqFactStep = lpHave(nameEqFactoringStep.name,afterEqFacAp,lpProofScript(haveEqFactSteps))
    Out.lp_debug_info(s"generated equal factoring step:\n${eqFactStep.pretty}")
    allSteps = allSteps :+ eqFactStep
    lastStepName = nameEqFactoringStep

    // d) Prove the transformation to non-equational literals if applicable
    var uc1: lpOlTerm = lpOlNothing
    var uc1Final: lpOlTerm = lpOlNothing
    var uc2: lpOlTerm = lpOlNothing
    var uc2Eq: lpOlTerm = lpOlNothing

    // if necessary, flip back the other lit


    // e) and f) If the order within any of the equality literals has changed after the rule application as a result of the term ordering, proof the transformation using eqSym_eq
    var needsFlipping:  Seq[(lpOlTerm, lpOlType)] = Seq.empty
    val otherLitL = if (otherLit_l0 == otherLit_l){
      if (otherLit.equational) otherLit.left else asTerm(otherLit)
    }  else  otherLit.right
    if (otherLitL == uc1Orig.left) {
      // In this case, the order is already correct
      uc1 = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, eqTypeEnc.lift2Poly, otherLit_l, maxLit_r))
      uc1Final = uc1
    } else if ((otherLitL == uc1Orig.right) | (Not(otherLitL) == uc1Orig.right) | (otherLitL == Not(uc1Orig.right))) {
      // In this case, the order was changed
      val encUniConst = term2LP(uc1Orig.right,bVarMap,sig)._1
      //Out.lp_debug_info(s"flipping of other lit necessary, encoded unification constraint: ${encUniConst.pretty}")
      Out.lp_debug_info(s"flipping of UC1 necessary, encoded unification constraint : ${encUniConst.pretty}")
      uc1 = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, eqTypeEnc.lift2Poly, otherLit_l, maxLit_l))
      uc1Final = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, eqTypeEnc, maxLit_l, otherLit_l))
      needsFlipping = needsFlipping :+ (uc1,eqTypeEnc)
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
      uc2Eq = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, eqTypeEnc.lift2Poly, otherLit_r, otherLit_r))
      uc2 = lpOlUnaryConnectiveTerm(lpNot, otherLit_r)
      literalsToTransform2 = literalsToTransform2 :+ uc2Eq
    } else if (otherLit_l == lpOlTop) {
      throw new Exception(s"The LP encoding of EqFact non-equational max literal and equational other literal not enocided yet yet")
    } else if (otherLit.equational && ((otherLit.right == cc2Orig.right) | (Not(otherLit.right) == cc2Orig.right) | (otherLit.right == Not(cc2Orig.right)))){
      val otherLitR = otherLit.right
      // In this case, the order was changed
      val encUniConst = term2LP(cc2Orig.right, bVarMap, sig)._1
      //Out.lp_debug_info(s"flipping of other lit necessary, encoded unification constraint: ${encUniConst.pretty}")
      Out.lp_debug_info(s"flipping of UC2 necessary, encoded unification constraint : ${encUniConst.pretty}")
      uc2 = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, eqTypeEnc.lift2Poly, otherLit_r, maxLit_r))
      uc2Eq = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, eqTypeEnc, maxLit_r, otherLit_r))
      needsFlipping = needsFlipping :+ (uc2, eqTypeEnc)
    } else {
      uc2 = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, eqTypeEnc, otherLit_l, otherLit_r))
      uc2Eq = uc2
    }

    if (needsFlipping.nonEmpty){
      val flipLitsName = lpConstantTerm("EqSymmetry")
      val (flipLitsProofScript, flippedLits, usedSymbolsNew) = flipEqLiteralsProofScript(needsFlipping, lpClause(Seq(), lastStepLits), lastStepName, flipLitsName)
      lastStepName = flipLitsName
      lastStepLits = flippedLits
      usedSymbols = usedSymbols ++ usedSymbolsNew
      allSteps = allSteps :+ flipLitsProofScript
      Out.lp_debug_info(s"proving flip of equality literals:\n${flipLitsProofScript.pretty}")
    }

    // Combine into one rule for the backwards encoding:
    if (literalsToTransform2.nonEmpty) {
      Out.lp_debug_info(s"Encoding transformation back to non-equational literals for literals ${literalsToTransform2.map(_.pretty).mkString(", ")}")
      Out.lp_debug_info(s"for the clause ${lpClause(Seq(), lastStepLits).pretty}")
      val nameTransfStep2 = lpConstantTerm("TransformToNonEqLits")
      val (backTransformationStep, backLitMap, litsAfter, usedSymbolsNew) = makeLiteralEquational_proofSkript(literalsToTransform2, lpClause(Seq(), lastStepLits), lastStepName, false, true, nameTransfStep2)
      Out.lp_debug_info(s"successful")
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
        val (encFactoring, usedSymbolsNew, canEncode) = encEqFactLiterals(otherLit, maxLit, ur1, ur2, parent.cl, child.cl, bVarMap, lastStep, factStepName, sig)
        allSteps = allSteps :+ encFactoring
        lastStep = factStepName
        usedSymbols = usedSymbols ++ usedSymbolsNew
        // 6. Refine with the last proven step
        allSteps = allSteps :+ lpRefine(lpFunctionApp(lastStep, Seq(lpFunctionApp(parentNameLpEnc, applySymbolsToParent))))
        val wholeProof = lpProofScript(allSteps)

        if (canEncode) (wholeProof, usedSymbols, None)
        else (lpProofScript(Seq(lpProofScriptAdmit())), Set.empty, Some("The LP encoding of EqFact requires some unencoded transformation"))
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

  def simplificationInfoToSteps(parent: Clause, additionalInfo: Seq[(Seq[Int],Int)], sig: Signature):(Seq[lpProofScriptStep],Set[lpStatement])={

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
            type2LP(tl.ty, sig)
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

  def simplificationProofScript(child: Clause, parent: Clause, additionalInfo: Seq[(Seq[Int],Int)], symbolsToUnfold: Set[Signature.Key], parentNameLpEnc: lpConstantTerm, quantifiedVars: Seq[lpUntypedVar], bVars: Map[Int, String], sig: Signature):(lpProofScript, Set[lpStatement])={

    // proof the equality between a parent and a child term given a set of rewrite rules and their positions

    val encParent = term2LP(Clause.asTerm(parent), bVars, sig)._1
    val encChild = term2LP(Clause.asTerm(child), bVars, sig)._1
    //print(s"Encoding simplification step: ${encParent.pretty} to ${encChild.pretty}\n")

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

  def inferImplicitTransformationsSimp(parentLits: Seq[Literal], ChildLits: Seq[Literal], childLen: Int, bVarMap: Map[Int, String], sig: Signature): (Seq[Literal], Seq[Int], Seq[lpProofScriptStep], Seq[lpStatement]) = {

    // Applies simplification to the given literals and then applies the operations carried out by Leo-III that can potentialy lead to the literal
    // being flipped or transformed in any other way. Then forms a new sequence omitting any literals that reduce to F or have already been
    // derived and - in the process - keeps track of this information in order to apply the necessary implicit transformations

    var simpLits = Seq.empty[Literal]
    var doubleLiterals = Seq.empty[Int]
    var implicitRwTransf = Seq.empty[lpProofScriptStep]
    var usedSymbolsTransf = Seq.empty[lpStatement]

    // Helper function that updates doubleLiterals and simpLits if the literal is not false.
    def addLiteral(lit: Literal): Unit = {
      if (!Literal.isFalse(lit)) {
        val idx = if (simpLits.contains(lit)) simpLits.indexOf(lit) else doubleLiterals.distinct.length
        doubleLiterals = doubleLiterals :+ idx
        if (!simpLits.contains(lit)) simpLits = simpLits :+ lit
      }
    }

    // Process each literal from the parent.
    parentLits.foreach { parentLit =>
      if (!parentLit.equational) {
        val lit = PolaritySwitch(Literal(normalize(parentLit.left), parentLit.polarity))
        addLiteral(lit)
      } else {
        val normLeft = normalize(parentLit.left)
        val normRight = normalize(parentLit.right)
        if (normLeft == normRight) {
          val lit = PolaritySwitch(Literal(LitTrue(), parentLit.polarity))
          addLiteral(lit)
        } else {
          val maybeOrderedLit = PolaritySwitch(Literal.mkLit(normLeft, normRight, parentLit.polarity, parentLit.oriented))
          val unorderedLit = PolaritySwitch(Literal.mkLit(normLeft, normRight, parentLit.polarity, false))
          addLiteral(unorderedLit)
          // Update doubleLiterals for the unordered literal.
          //doubleLiterals = doubleLiterals :+ (
          //  if (simpLits.contains(unorderedLit)) simpLits.indexOf(unorderedLit)
          //  else doubleLiterals.distinct.length
          //  )
          if (!simpLits.contains(unorderedLit) && !Literal.isFalse(unorderedLit)) {
          //  simpLits = simpLits :+ unorderedLit

            // Test if a transformation is required
            if (maybeOrderedLit != unorderedLit) {
              val encOrigLit = lpLiteral(maybeOrderedLit, bVarMap, sig)
              val encDesiredLit = lpLiteral(unorderedLit, bVarMap, sig)
              throw new Exception(s"Required implicit transformation in SIMP encoding from ${encOrigLit.term.pretty} to ${encDesiredLit.term.pretty}!")
              // todo: the following implments implicit transformations, but it is not yet tested.
              //  Comment the exception and test carefully.
              val (transformSteps, usedSymbols0, canEncode) = transformLiteral(encOrigLit.term, encDesiredLit.term, simpLits.length, childLen)
              if (!canEncode) throw new Exception(s"LP-Encoding SIMP: could not transform ${encOrigLit.term.pretty} to ${encDesiredLit.term.pretty}")
              implicitRwTransf = implicitRwTransf ++ transformSteps
              usedSymbolsTransf = usedSymbolsTransf ++ usedSymbols0
            }
          }
        }
      }
    }

    assert(simpLits.length == childLen, s"LP-Encoding: Lengths of derived and given simplifications differ. Derived clause: ${simpLits.length} literals, given Clause: ${childLen} literals.")
    // If no literals were added, default to false.
    if (simpLits.isEmpty) {
      simpLits = if (ChildLits.isEmpty) Seq(Literal(LitFalse(), true)) else ChildLits
    }
    if (doubleLiterals.isEmpty)
      doubleLiterals = Seq(0)

    (simpLits, doubleLiterals, implicitRwTransf, usedSymbolsTransf)
  }

  def lpEncodingPrelim(child: Clause, parents: Seq[Clause], allVariables: Seq[(Int, Type)], sig: Signature):(lpClauseInst, Seq[ lpClauseInst], Map[Int, String], Seq[lpAssume])={
    val encParents = parents.map(parent => lpClauseInst(parent, sig))
    val encChild = lpClauseInst(child, sig)
    val bVarMap = clauseVars2LP(allVariables, sig, Set.empty)._2
    // Instanciate the initial step abstracting over the free variables of the child
    val initialStep = if (encChild.metaVars.nonEmpty) Seq(lpAssume(encChild.metaVars)) else Seq()
    (encChild, encParents, bVarMap, initialStep)
  }

  def lpImpHaveStepConstructor(stepName: String, quantifiedVars: Seq[lpTypedVar], termBefore: lpOlTerm, termAfter: lpOlTerm, proofScriptSteps: Seq[lpProofScriptStep]): lpHave = {
    // Function constructing subproofs for one clause implying another using the have-tactic with potential...
    // - Abstraction over variables

    val impToProve = lpOlUntypedBinaryConnectiveTerm(lpImp, termBefore, termAfter)
    // Quantify over variables if necessary
    val (maybeQuanrifiedImpToProve, fullProofScript) =
      if (quantifiedVars.isEmpty) (impToProve.prf, lpProofScript(proofScriptSteps))
      else (lpMlDependType(quantifiedVars, impToProve.prf), lpProofScript(Seq(lpAssume(quantifiedVars)) ++ proofScriptSteps))
    // Complete substep using have-tactic
    val haveSimpAppStep = lpHave(stepName, maybeQuanrifiedImpToProve, fullProofScript)
    haveSimpAppStep
  }

  /** Carry out the construction of a proof script for applications of (SIMP)*/
  def encSimpProofScript(pLits: Seq[Literal], cLits: Seq[Literal], encParent: lpClauseInst, encChild: lpClauseInst, childLen: Int, bVarMap: Map[Int, String], parentNameLpEnc: lpTerm, sig:Signature)= {


    // Identify any implicit transformations that may need to be encoded
    val (simpLits, doubleLiterals, implicitRwTransf, usedSymbolsTransf) = inferImplicitTransformationsSimp(pLits, cLits, childLen, bVarMap, sig)
    val encSimpLits = simpLits.map(simpLit => lpLiteral(simpLit, bVarMap, sig).term)


    Out.lp_debug_info("huhu")
    /////////////////////////////////////////////////////
    //// 2. Instaniate a subproof (SimpApp) using have to proof that the parent implies the child
    ////    by applying all of the simplification rules to the parent

    // If we need to account for the deletion of double literals, we include the duplicates in the implication we construct
    //    and remove them in an additional step
    Out.lp_debug_info(s"huhu ${doubleLiterals.map(indx => encSimpLits(indx))}")
    val clauseToProve = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, doubleLiterals.map(indx => encSimpLits(indx)))
    // Identify any variables that were implicitly quantified in the parent but not in the child
    val disappearingVars = encParent.metaVars.diff(encChild.metaVars)
    // Step applying all of the RW-rules encoding the simplifications
    val simpAppStepName = "SimpApp"
    val haveSimpAppStep = lpImpHaveStepConstructor(simpAppStepName, disappearingVars, encParent.term, clauseToProve, Seq(allSimpRuleApplicationStep))
    Out.lp_debug_info("Substep applying the boolean identities generated")



    /////////////////////////////////////////////////////
    //// 3. Apply Implicit transformations: Deletion of double literals, eqSym and permutation

    val witnessTermsToApply = disappearingVars.map(var0 => lpWitness.fromAnyType(var0.ty))
    val allTermsToApplyToParent = encParent.metaVars.map(var0 => if (disappearingVars.contains(var0)) lpWitness.fromAnyType(var0.ty) else var0)
    val appliedSimpAppStepName = lpFunctionApp.toDefName(simpAppStepName, witnessTermsToApply)
    val simpStepName = lpFunctionApp(appliedSimpAppStepName, Seq(lpFunctionApp(parentNameLpEnc, allTermsToApplyToParent)))
    val (maybePerm, maybePermStepName): (Set[lpStatement], lpFunctionApp) = if (doubleLiterals != doubleLiterals.indices) {
      // Application of delete literal is necessary
      // todo: exclude cases where the rewrite rule applied by LP would also handle it. (should only happen if the relevant literals are at the two most left ones right?)
      Out.lp_debug_info(s"need to prove ${doubleLiterals.map(indx => encChild.lits(indx).pretty)}")
      val instMetaDelTheorem = metaDeletion.instanciate(encChild.lits, doubleLiterals, simpStepName)
      (Set(metaPermutation), instMetaDelTheorem)
    } else (Set(), simpStepName)


    /////////////////////////////////////////////////////
    //// 4. Refine with the parent applied to SimpApp

    val refineStep = lpRefine(maybePermStepName)
    val allSteps: Seq[lpProofScriptStep] = (Seq(haveSimpAppStep) ++ implicitRwTransf) :+ refineStep

    (allSteps, maybePerm ++ usedSymbolsTransf)}

  def newSimpEncoding(child: Clause, parent: Clause, parentNameLpEnc: lpConstantTerm, sig: Signature):(Seq[lpProofScriptStep],Set[lpStatement])={

    // Encoding of the simplification via exhaustive application of the encoded boolean equalities via the rewrite tactic
    // The modular proof script can consist of the following steps:
    // 1. Abstract over free variables
    // 2. Instaniate a subproof (SimpApp) using the "have"-tactic to proof that the parent implies the child by applying
    //    all of the simplification rules as well as the rule for polarity switch to the parent
    //    -> If the parent has implicitly quantified variables that disappear as an effect of the simplification,
    //       we include them in the have-step, assume them and apply their corresponding witness terms in the Refine-step
    // 3. Apply Implicit transformations: Deletion of double literals and eqSym
    // 4. Refine with the parent applied to SimpApp (and apply witness terms in case the parent has disappearing vars as a
    //    consequence of simplification)

    // todo: No example needed implicit eq-sym or other literal transformations so far
    //  Even though thi is implemented, it is therefore not yet tested -> test implementation

    /////////////////////////////////////////////////////
    //// preliminary and 1. Abstract over free variables

    val (encChild,encParent0,bVarMap,initialStep) = lpEncodingPrelim(child,Seq(parent),parent.implicitlyBound,sig)
    assert(encParent0.length == 1)
    val encParent = encParent0.head
    Out.lp_debug_info(s"Encoding simplification of ${encParent.term.pretty} to ${encChild.term.pretty}")

    /////////////////////////////////////////////////////
    //// 2 - 4
    val (allSteps0, usedSymbols) = encSimpProofScript(parent.lits, child.lits, encParent, encChild, child.lits.length, bVarMap, parentNameLpEnc, sig)

    val allSteps = initialStep ++ allSteps0

    (allSteps, usedSymbols)
  }

  def encLiftEq(cl: ClauseProxy, parents: Seq[ClauseProxy], addInfo: Seq[Seq[Int]], parentNameLpEnc: Seq[lpConstantTerm], sig: Signature):(lpProofScript,Set[lpStatement],Option[String]) = { //: (lpProofScript, Set[lpStatement]) = {

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

    assert(parents.length == 1, "trying to encode lift equaltiy step with more than one parent")

    // Extract information about what literals were edited in which way
    // And in which order they will occur in the resulting clause
    if (addInfo.isEmpty) {
      Out.lp_debug_info(s"no additional inforamtion provided, can not encode") //todo: would be better to infer atuomtically anyays
      (lpProofScript(Seq.empty), Set.empty, Some("missing the additional information for the encoding"))
    } else {


      val litsPosLift = addInfo(0)
      val litsNegLift = addInfo(1)
      val litsOld = addInfo(2)
      val edIndices = litsPosLift ++ litsNegLift
      val indices = (edIndices ++ litsOld).sorted
      val permutation = litsPosLift ++ litsNegLift ++ litsOld

      Out.lp_debug_info(s"edited literals at indices ${edIndices.mkString(", ")}, unchanged literals: ${litsOld.mkString(", ")}")

      var allSteps: Seq[lpProofScriptStep] = Seq.empty
      var usedRules: Set[lpStatement] = Set.empty
      var liftedLits: Seq[lpOlTerm] = Seq.empty
      var canEncode: Option[String] = None

      // 1. Abstract over free variables
      val bVars = clauseVars2LP(parents.head.cl.implicitlyBound, sig, Set.empty)._2
      val (clauseQuantification, applySymbolsToParent) = clauseRuleQuantification(parents.head.cl, bVars, sig)
      if (clauseQuantification.nonEmpty) allSteps = allSteps :+ lpAssume(clauseQuantification.map(var0 => var0.untyped))
      val lastStep: lpTerm = lpFunctionApp(parentNameLpEnc.head, applySymbolsToParent)

      indices foreach { indx =>
        val lit = parents.head.cl.lits(indx)
        if (edIndices.contains(indx)) {
          val lhsRhs = ===.unapply(lit.left)
          if (lhsRhs == None) throw new Exception("trying to encode lifting equality on malformed term")
          val (lhs, rhs) = lhsRhs.get
          val encRhs = term2LP(rhs, bVars, sig)._1
          val encLhs = term2LP(lhs, bVars, sig)._1
          val encType = type2LP(lhs.ty, sig)
          val litPol = lit.polarity
          val rwPattern = generateClausePatternTerm(Seq(permutation.indexOf(indx)), indices.length, None, lpOlUntypedVar(lpOlConstantTerm("x")), litPol)
          if (rwPattern.isDefined) Out.lp_debug_info(s"generated pattern for rewrite operation: ${rwPattern.get.pretty}")
          var finalLit: lpOlTerm = lpOlNothing
          if (litsPosLift.contains(indx)) {
            if (!litPol) {
              finalLit = lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, encType, encLhs, encRhs))
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
          Out.lp_debug_info(s"constructed Literal ${finalLit.pretty}")
          val lit_cl = cl.cl.lits(permutation.indexOf(indx))
          val encCorrespondingLit = term2LP(asTerm(lit_cl),bVars,sig)._1
          if (finalLit != encCorrespondingLit){
            // transformation to or from bottom or order has changed
            Out.lp_debug_info(s"corresponding lit in child: ${encCorrespondingLit.pretty}, transformation necessary")
            val (transformationSteps, usedSymbols0, canEncode0) = transformLiteral(encCorrespondingLit,finalLit,permutation.indexOf(indx), indices.length)
            if (canEncode0){
              allSteps = allSteps ++ transformationSteps
              usedRules = usedRules ++ usedSymbols0
              Out.lp_debug_info(s"transformation successful")
              //finalLit = encCorrespondingLit
            }
            else canEncode = {
              Out.lp_debug_info(s"transformation unsuccessful")
              Some("unencoded transformation necessary")
            }
          }
          /*
          if (lhs != lit_cl.left) {
            // 2 b) for the new equality literlas, the order within the equality may have changed, if so: apply rewrite tactic
            allSteps = allSteps :+ lpRewrite(rwPattern, flipLiteral().instanciate(encRhs, encLhs, None))
            finalLit = flipLiteral().res(litPol, encType.lift2Poly, encRhs, encLhs)
            usedRules = usedRules + flipLiteral()
          }
           */
          liftedLits = liftedLits :+ finalLit
        } else {
          val lit = parents.head.cl.lits(indx)
          val encLit = term2LP(asTerm(lit), bVars, sig)._1
          liftedLits = liftedLits :+ encLit
        }
      }

      // 3. If the order of literals has changed, apply meta theorem and refine with instanciated meta-theorem
      //    Else refine with the last step
      val needsPermute = permutation != permutation.sorted
      if (needsPermute) {
        Out.lp_debug_info(s"applying the following permutation: $permutation")
        allSteps = allSteps :+ lpRefine(metaPermutation.instanciate(permutation, liftedLits, lastStep))
        usedRules = usedRules + metaPermutation
        // permutation will not need to be added to the rules assuming that we will add it to stdlib
      } else {
        allSteps = allSteps :+ lpRefine(lpFunctionApp(lastStep, Seq()))
      }

      val finishedProof = lpProofScript(allSteps)

      (finishedProof, usedRules, canEncode)
    }
  }


  def encRewrite(cl: ClauseProxy, parents: Seq[ClauseProxy], addInfoSimp: Seq[(Seq[Int], Int)], parentModoluRw: Option[Clause], parentNameLpEnc: Seq[lpConstantTerm], sig: Signature):(lpProofScript,Set[lpStatement],Option[String]) = {

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
    if (addInfoSimp.nonEmpty) {
      Out.lp_debug_info("Simplification steps not yet encoded")
      allTransformationsEncoded = false
    }

    // 1. Abstract over free variables
    val (parentImpVars, _, _) = clause2LP_unquantified(parent, Set.empty, sig)
    val impBoundParent = liftVarsToMeta(parentImpVars).map(var0 => var0.untyped)
    if (impBoundParent.nonEmpty) allSteps = allSteps :+ lpAssume(impBoundParent)

    // encode the relevant clauses
    //val (_, clauseModulo, _) = clause2LP_unquantified(parentModoluRw.get, Set.empty, sig)
    val (_, encParent, _) = clause2LP_unquantified(parent, Set.empty, sig)
    val (_, encChild, _) = clause2LP_unquantified(cl.cl, Set.empty, sig)
    Out.lp_debug_info(s"Encoding application or RW-rule on ${sourceBeforeParent.name} : ${encParent.pretty}")
    Out.lp_debug_info(s"The derived child is ${encChild.pretty}")

    var rewriteenLits = encParent.args
    val clauseLen = rewriteenLits.length
    var transformationsRwCounter = 0
    var eqFlipCounter = 0
    var rwRuleApplicationSteps: Seq[lpProofScriptStep] = Seq.empty
    rewriteEqCalsues.zip(sourcesBeforeEq) foreach { case (rewriteEqClause, sourceBeforeEq0) =>
      var sourceBeforeEq = sourceBeforeEq0
      val bVarsRewriteEq = clauseVars2LP(rewriteEqClause.implicitlyBound, sig, Set.empty)._2
      assert(rewriteEqClause.lits.length == 1)

      // encode the equality clause used as a rewrite rule
      val rewriteEq = rewriteEqClause.lits.head
      val rwLhs = term2LP(rewriteEq.left, bVarsRewriteEq, sig)._1
      var rwRhs = term2LP(rewriteEq.right, bVarsRewriteEq, sig)._1
      val rwType = type2LP(rewriteEq.right.ty, sig)
      val rwPol = rewriteEq.polarity

      // check that none of the things not yet encoded occur
      if (rewriteEqClause.implicitlyBound.nonEmpty || rewriteEqClause.typeVars.nonEmpty) {
        allTransformationsEncoded = false
        Out.lp_debug_info(s"Rewriting with ${sourceBeforeEq.name} : ${if (!rwPol) lpNot.pretty} (${rwLhs.pretty} = ${rwRhs.pretty}) is non-ground and therefore not yet encoded")
      } else {
        Out.lp_debug_info(s"Rewriting with ${sourceBeforeEq.name} : ${if (!rwPol) lpNot.pretty} (${rwLhs.pretty} = ${rwRhs.pretty})")
        // 2. Use the have tactic to provide a proof-term for the equality used to rewrite the focused goal

        assert(rewriteEqClause.lits.length == 1, s"trying to encode RW rule application with RW clause of length ${rewriteEqClause.lits.length}")
        if (!rewriteEq.equational) {
          // 2 a) case I) If the rewrite-clause is a non-equational single literal, proof the transformation to equational form using topPosProp_eq or botNegProp_eq
          val transformationStepName = s"TransformToEqLits_${transformationsRwCounter}"
          transformationsRwCounter = transformationsRwCounter + 1
          // Choose the fitting rule for the transformation todo: aso use the general skript here
          val (haveTransformStep, usedSymbols0) = if (rwPol) {
            val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTop, rwLhs)
            val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, mkTopEqPosProp.term), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
            (haveTransformStep0, mkTopEqPosProp)
          } else {
            rwRhs = lpOlBot
            val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlBot, rwLhs)
            val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, mkBotEqNegProp.term), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
            (haveTransformStep0, mkBotEqNegProp)
          }
          Out.lp_debug_info(s"Transforming rewrite rule to equality...")
          //  2 b) Refine with the rewrite-clause and - if a substitution was applied - instanciate it accordingly todo: sbustitution
          allSteps = allSteps :+ haveTransformStep
          usedSymbols = usedSymbols + usedSymbols0
          sourceBeforeEq = lpConstantTerm(transformationStepName)
        } else if (rewriteEq.polarity) {
          //2 a) case II) If the rewrite-clause is an equational single literal, use eqSym_eq to prove the reverse rewrite rule
          val transformationStepName = s"flip_equality_$eqFlipCounter"
          eqFlipCounter = eqFlipCounter + 1
          val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, rwRhs, rwLhs)
          Out.lp_debug_info(s"transforming rewirte clause to ${transformedRewriteEq.pretty}")
          val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, lpFunctionApp(flipLiteral().name, Seq.empty, Seq(rwType))), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
          val (haveTransformStep, usedSymbols0) = (haveTransformStep0, flipLiteral())
          //  2 b) Refine with the rewrite-clause and - if a substitution was applied - instanciate it accordingly todo: sbustitution
          allSteps = allSteps :+ haveTransformStep
          usedSymbols = usedSymbols + usedSymbols0
          sourceBeforeEq = lpConstantTerm(transformationStepName)
        } else throw new Exception("Error while attempting to encode rewrite step in LP: Rewrite rule is equational but not positive")

        // go over all of the literals and - for each occurrence of the term that has to be rewritten, apply a rewrite rule and if necessary eqSmy
        val bVarsParentEq = clauseVars2LP(parent.implicitlyBound, sig, Set.empty)._2
        var litCount = 0
        rewriteenLits.foreach {encLit =>
          val (patternTerm, rewrittenLit, counter, rwUnderBinder) = findRWTerm0(Seq((rwLhs, rwRhs)).toMap, encLit)
          if (rwUnderBinder) {
            allTransformationsEncoded = false
            Out.lp_debug_info(s"Rewriting-Tactic can not be used on literal of the parent clause: ${encLit.pretty} since term is under binder")
          } else if (counter != 0) {
            rewriteenLits = rewriteenLits.updated(litCount,rewrittenLit)
            Out.lp_debug_info(s"Trying to apply to literal of the parent clause: ${encLit.pretty}")
            val rewritePattern = lpRewritePattern(generateClausePattern(Seq(litCount), clauseLen, true, patternTerm))

            // 4. Use the (transformed) rewrite-clause to rewrite the focused goal
            Out.lp_debug_info(s"rewrite pattern is ${rewritePattern.pretty} and the rewritten literal is ${rewrittenLit.pretty}")
            rwRuleApplicationSteps = rwRuleApplicationSteps :+ lpRewrite(Some(rewritePattern), lpConstantTerm(sourceBeforeEq.pretty))
          }
          litCount = litCount + 1
        }
      }
    }

    var litCount = 0
    if (allTransformationsEncoded){
      rewriteenLits foreach { rewrittenLit =>
        // 2.5 if the literal in the parent clause is equational, but the literal in the child clause is not, transform to equality
        val encLitChild = encChild.args(litCount)
        if (!(encLitChild == rewrittenLit)) {
          Out.lp_debug_info(s"rewritten Literal: ${rewrittenLit.pretty} ,corresponding literal in child caluse: ${encLitChild.pretty}")
          val (additionalSteps, usedSymbols0, canEncode) = transformLiteral(encLitChild, rewrittenLit, litCount, clauseLen) // todo: acutally, rewerite pattern should be ootional since we do not want it for clauses of length one
          if (canEncode) Out.lp_debug_info(s"proposed Steps: \n${additionalSteps.map(_.pretty).mkString("\n")}")
          else {
            Out.lp_debug_info(s"unable to encode the transformation of ${encLitChild.pretty} to ${rewrittenLit.pretty}}")
            allTransformationsEncoded = false
          }
          usedSymbols = usedSymbols ++ usedSymbols0
          allSteps = allSteps :++ additionalSteps
        }
        litCount = litCount + 1
      }
    }


    // 5. If simplifications were applied, use the encoding of (Simp) to verify the transformations todo
    /*
    if (addInfoSimp.nonEmpty) {
      val (simplificationSteps, usedSymbolsNew) = simplificationInfoToSteps(parentModoluRw.get, addInfoSimp, sig)
      rewriteSkript = rewriteSkript ++ simplificationSteps
      usedSymbols = usedSymbols ++ usedSymbolsNew
    }
     */

    allSteps = allSteps ++ rwRuleApplicationSteps

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
    // todo: instead of matchin on names, actually give the subst map using variables
    // given a substitution map and a term, substitute all occurrences of given variables in a term

    def substituteTypedVarsTerm(var0: Either[lpOlTypedVar, lpOlTyVar], subsMap: Map[String, lpOlTerm]): Either[lpOlTypedVar, lpOlTyVar] = {
      // apply substitution to a typed variable
      var0 match {
        case Left(termVar) =>
          if (subsMap.contains(termVar.name.pretty)) {
            subsMap(termVar.name.pretty) match {
              case lpOlTypedVar(name1, ty1) => Left(lpOlTypedVar(name1, ty1))
              //case lpOlTyVar(name1) => lpOlTyVar(name1)
              case lpOlUntypedVar(lpOlConstantTerm(name1)) =>
                termVar.ty match {
                  case ty0: lpOlType => Left(lpOlTypedVar(lpOlConstantTerm(name1), ty0))
                  case _ => throw new Exception(s"LP encoding: trying to substitute expected OL variable ${termVar.pretty}, but type is ${termVar.ty.pretty}")
                }
              case lpOlConstantTerm(name1) => //todo: this actually should not happen
                termVar.ty match {
                  case ty0: lpOlType => Left(lpOlTypedVar(lpOlConstantTerm(name1), ty0))
                  case _ => throw new Exception(s"LP encoding: trying to substitute expected OL variable ${termVar.pretty}, but type is ${termVar.ty.pretty}")
                }
              case _ => throw new Exception(s"Error in lp Encoding: trying to substitute variable ${termVar.pretty} with ${subsMap(termVar.name.pretty)}")
            }
          } else var0
        case Right(tyVar) =>
          throw new Exception(s"Error in lp Encoding: trying to substitute variable ${tyVar.pretty} with ${subsMap(tyVar.name)}")
          /*
          todo: once the variables can be either term or type vars, we can use this:
          if (subsMap.contains(tyVar.name)) {
            subsMap(tyVar.name) match {
              case lpOlTyVar(name1) => Right(lpOlTyVar(name1))
              case _ => throw new Exception(s"Error in lp Encoding: trying to substitute variable ${tyVar.pretty} with ${subsMap(tyVar.name)}")
            }
          } else var0
           */
      }
    }

      t match {
        case `lpOlTop` => lpOlTop
        case `lpOlBot` => lpOlBot
        case lpOlConstantTerm(name) =>
          subsMap.getOrElse(name, lpOlConstantTerm(name))
        case lpOlTypedVar(name, ty) =>
          // when we encounter the typed var that was quantified in the body, we want to replace it!
          subsMap.getOrElse(name.a, t)
        //case lpOlTyVar(name) =>
          // when we encounter the typed var that was quantified in the body, we want to replace it!
          //subsMap.getOrElse(name, t)
        case lpOlUntypedVar(lpConstantTerm(name)) =>
          if (subsMap.contains(name)) {
            subsMap(name) match {
              case lpOlTypedVar(name1, _) => lpOlUntypedVar(name1)
              //case lpOlTyVar(name1) => lpOlUntypedVar(lpConstantTerm(name1))
              case lpOlUntypedVar(name1) => lpOlUntypedVar(lpOlConstantTerm(name1.pretty))
              case lpOlConstantTerm(name1) => lpOlUntypedVar(lpOlConstantTerm(name1))
              case _ => throw new Exception(s"Error in lp Encoding: trying to substitute variable ${t.pretty} with ${subsMap(name).pretty}")
            }
          } else t
        case lpOlLambdaTerm(vars, body) => lpOlLambdaTerm(vars.map(var0 => substituteTypedVarsTerm(var0, subsMap)), substituteVarTerm(body, subsMap))
        case lpOlFunctionApp(f, args) =>
          var encArgs: Seq[Either[lpOlTerm, lpOlType]] = Seq.empty
          args foreach { arg =>
            arg match {
              case Left(term) => encArgs = encArgs :+ Left(substituteVarTerm(term, subsMap))
              // if the argument is e.g. a type we do not need to substitute anything
              case Right(ty) => encArgs :+ arg
              //case a : Left[lpOlTerm, lpOlType] => encArgs = encArgs :+ Left(substituteVarTerm(a, subsMap))
              //case _ => encArgs :+ arg
            }
          }
          lpOlFunctionApp(substituteVarTerm(f, subsMap), encArgs)
        case lpOlBoundTerm(quantifier, variables, body) => lpOlBoundTerm(quantifier, variables.map(var0 => isTermVar(substituteTypedVarsTerm(Left(var0), subsMap))), substituteVarTerm(body, subsMap))
        case lpOlUnaryConnectiveTerm(connective, body) => lpOlUnaryConnectiveTerm(connective, substituteVarTerm(body, subsMap))
        case lpOlUntypedBinaryConnectiveTerm(connective, lhs, rhs) => lpOlUntypedBinaryConnectiveTerm(connective, substituteVarTerm(lhs, subsMap), substituteVarTerm(rhs, subsMap))
        case lpOlTypedBinaryConnectiveTerm(connective, ty, lhs, rhs) => lpOlTypedBinaryConnectiveTerm(connective, ty, substituteVarTerm(lhs, subsMap), substituteVarTerm(rhs, subsMap))
        case lpOlUntypedBinaryConnectiveTerm_multi(connective, args) =>
          lpOlUntypedBinaryConnectiveTerm_multi(connective, args.map(arg => substituteVarTerm(arg, subsMap)))
        case _ => throw new Exception(s"encountered unexptcted term $t when trying to do substitution")
      }
  }

  def removeUnificationConstraint(uniC: Literal, parent: Clause, lastLit0: lpOlTerm, sig: Signature): (Seq[lpProofScriptStep], Set[lpStatement])={
    // prove that unification literal can be removed from a clause when they either have the form ¬⊤ or x≠x (modulo unification)

    var usedSymbols: Set[lpStatement] = Set.empty

    // identify the position of the unification literals in parent clause
    val positionsInClause = findLitInClause(uniC,parent)
    val position = if (positionsInClause.length != 1){
      positionsInClause.last //todo: this is justified since the unification constraints get added at the end ... right?
    } else positionsInClause.head

    val patternVar = lpOlUntypedVar(lpOlConstantTerm("x"))

    var rewriteSteps: Seq[lpProofScriptStep] = Seq.empty

    // in both cases, the second step is the removal of ⊥ from the clause. This can be done using Simp7:
    val rewritePattern_step2 = generateClausePatternTerm(Seq(position - 1), parent.lits.length - 1, None, patternVar)
    val rewriteStep_step2 = lpRewrite(rewritePattern_step2, SimplificationEncoding.lpSimp_orBot.name,true)
    rewriteSteps = rewriteSteps :+ rewriteStep_step2
    usedSymbols = usedSymbols + SimplificationEncoding.lpSimp_orBot

    // proof the first transformation depending on the form of the unification constraint
    val rewritePattern_step1 = generateClausePatternTerm(Seq(position), parent.lits.length, None, patternVar)
    if (uniC.equational){
      if (!uniC.polarity){
        // in this case, we need to first show that both sides are equal modulo simplification and then apply a Simp Rule that postulates that x≠x = ⊥
        // the rewrite rule used here needs to explicitly instanciate the used type, therefore we first need to find that type out:
        var ty = type2LP(uniC.left.ty, sig)
        val lastLit = lastLit0 match {
          case lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, ty0, lhs, _)) =>
            ty = ty0
            lhs
          case _ =>
            throw new Exception("attempting to instanciate Simp10 inappropriateley")
        }
        val rewriteStep_step1 = lpRewrite(rewritePattern_step1, lpFunctionApp(SimplificationEncoding.lpSimp_negEq_idem.name,Seq(ty, lastLit)),true)
        rewriteSteps = rewriteSteps :+ rewriteStep_step1
        usedSymbols = usedSymbols + SimplificationEncoding.lpSimp_negEq_idem
      } else throw new Exception(s"Equational positive unification constratint passed on to lambdapi post eqFact encoding?")
    }else{
      // in this case simply we need to prove that 1. ¬⊤ = ⊥
      if (!uniC.polarity){
        val rewriteStep_step1 = lpRewrite(rewritePattern_step1, SimplificationEncoding.lpSimp_negTop.name,true)
        rewriteSteps = rewriteSteps :+ rewriteStep_step1
        usedSymbols = usedSymbols + SimplificationEncoding.lpSimp_negTop
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

    var canEncode = true

    if (encModes.contains(mode)) {
      Out.lp_debug_info(s"verification of $mode")
      var allSteps: Seq[lpProofScriptStep] = Seq.empty
      var usedSymbols: Set[lpStatement] = Set.empty

      // Abstract over the free variables
      val (unboundVarsChild0, encChild, _) = clause2LP_unquantified(cl.cl, Set.empty, sig)
      val (unboundVarsParent, _, _) = clause2LP_unquantified(parent.cl, Set.empty, sig)
      var encChildLiterals = encChild.args
      val unboundVarsChild = liftVarsToMeta(unboundVarsChild0)
      allSteps = if (unboundVarsChild.nonEmpty) allSteps :+ lpAssume(unboundVarsChild) else allSteps

      val (_, encParent, _) = clause2LP_unquantified(parent.cl, Set.empty, sig)
      val encParentLiterals = encParent.args

      // Encode the actual unification and possibly the following simplification
      val typeUnification = addInfoUni._2
      val termUnification = addInfoUni._1

      if (termUnification.length != unboundVarsParent.length) {
        //throw new Exception(s"trying to encode the unification that does not bind all free variables, this is implemented but untested, make sure this is done correctly") //todo
        Out.lp_debug_info(s"unification that does not bind all free variables not yet encoded")
        (lpProofScript(Seq.empty),usedSymbols,Some("unification that does not bind all free variables not yet encoded"))
      } else {
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
                canEncode = false
              //throw new Exception(s"binding by variables not yet encoded (only terms so far) $var0") //todo: is it really variables? I suppose so, but bound ones, no?
              case t: Term =>
                val encBindTerm = term2LP(t, termUni._4, sig)._1 //todo: dont i need the offset? was it an oversight not to use it in term2lp?
                subsMap += (lpUnboundVar -> encBindTerm)
              case _ => throw new Exception("Encountered unexpected bound object when encoding Unification step in lp")
            }
          }

          if (canEncode) {

            // Proof the substitution by applying the terms to be substituted to the parent quanififying over the respective variables
            val encLits = parent.cl.lits.map(lit => term2LP(asTerm(lit), bVars, sig)._1)
            Out.lp_debug_info(s"substituting variables in terms: ${encLits.map(_.pretty)}")
            Out.lp_debug_info(s"substitution: $subsMap")
            val encSubstLits = encLits.map(encLit => substituteVarTerm(encLit, subsMap.toMap))
            Out.lp_debug_info(s"substitution result: ${encSubstLits.map(_.pretty)}")
            // The application that instanciates the quantified variables with the substituted Terms in lp
            val applyToParent: Seq[lpTerm] = unboundVarsParent.map(var0 => subsMap.getOrElse(liftVarsToMeta(var0).name.pretty, liftVarsToMeta(var0)))
            val substitution = lpProofScript(Seq(lpRefine(lpFunctionApp(parentNameLpEnc, applyToParent))))
            val substitutionStepName = "Substitution"
            val substitutionHaveStep = lpHave(substitutionStepName, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits).prf, substitution)
            allSteps = allSteps :+ substitutionHaveStep

            // Depending on the mode of Unification, additional steps like the removal of unification constraints have to be proven
            // we carry out the substitution todo would there be an advantage to passing on the substitution in its original form after all and doing the actual substitution here instead of doing it as lambda terms?
            var allRemovalSteps: Seq[lpProofScriptStep] = Seq.empty
            val finalLits = if (Seq("uniAfterFactoring").contains(mode)) { // uniAfterFactoring is eqFact
              // in this case the unification constraints were fulfilled and removed, we thus need to prove that they can be removed
              // Remove the first unification constraint
              val uniC1 = addInfoUniRule._2._1
              val encUniC1 = term2LP(asTerm(uniC1),bVars,sig)._1
              val nameStep1Removal = "RemoveUC1"
              val removeUniC1: Seq[lpProofScriptStep] = if (parent.cl.lits.last != uniC1) {
                canEncode = false
                Seq.empty
              } //throw new Exception(s"encoding unification following eqFactoring and found unification constraint 1 in unexpected position, unic1 and last lit are....:\n${encUniC1.pretty}\n${parent.cl.lits.last}")
              else {
                val (removeUniC1_0, usedSymbolsUc1) = removeUnificationConstraint(uniC1, parent.cl, encSubstLits.last, sig)
                usedSymbols = usedSymbols ++ usedSymbolsUc1
                val proofStepUc1 = lpHave(nameStep1Removal, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits.init).prf, lpProofScript(removeUniC1_0 :+ lpRefine(lpFunctionApp(lpConstantTerm(substitutionStepName), Seq()))))
                removeUniC1_0
              }
              // Remove the second unification constraint
              val uniC2 = addInfoUniRule._2._2
              val nameStep2Removal = "RemoveUC2"
              val removeUniC2: Seq[lpProofScriptStep] = if (parent.cl.lits.init.last != uniC2) {
                canEncode = false
                Seq.empty
              } //throw new Exception(s"encoding unification following eqFactoring and found unification constraint 2 in unexpected position")
              else {
                val clauseWighoutUC = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, encSubstLits.init.init)
                val (removeUniC2_0, usedSymbolsUc2) = removeUnificationConstraint(uniC2, Clause(parent.cl.lits.init), encSubstLits.init.last, sig)
                usedSymbols = usedSymbols ++ usedSymbolsUc2
                val proofStepUc2 = lpHave(nameStep2Removal, clauseWighoutUC.prf, lpProofScript(removeUniC2_0 :+ lpRefine(lpFunctionApp(lpConstantTerm(nameStep1Removal), Seq()))))
                removeUniC2_0
              }
              // only add the rewrite steps, this is less complicated but should have the same result
              allRemovalSteps = allRemovalSteps ++ removeUniC2 ++ removeUniC1

              // it is necessary to potentially flip literals


              // Now the last step is refining with the last proven term after removal of the last unification constraint
              val refineStep = lpRefine(lpFunctionApp(lpConstantTerm(substitutionStepName), Seq())) //lpRefine(lpFunctionApp(lpConstantTerm(nameStep2Removal),Seq()))

              allRemovalSteps = allRemovalSteps :+ refineStep

              encSubstLits.init.init
            } else encSubstLits

            // compare the literals to see if we need to change any sides
            finalLits.foreach{ lit =>
              // find associated literal in parent
              val indexInChild = finalLits.indexOf(lit)
              val associatedChildLit = encChildLiterals(indexInChild)
              val reducedLit = betaReduceLpApplication(lit)
              // if they are not equal, the sides must have switchen.
              val flipRewriteStep = isFlippedVersion(reducedLit,associatedChildLit,indexInChild,finalLits.length)
              if (flipRewriteStep.isDefined){
                Out.lp_debug_info(s"need to flip sides of ${reducedLit.pretty}")
                allSteps = allSteps :+ flipRewriteStep.get
              }
            }

            allSteps = allSteps ++ allRemovalSteps


            // permutation? todo: figure out why this can even happen
            // sometimes all that happens is a permutation and nothing else
            if (containsLpLits(encParentLiterals, encChildLiterals)) {
              val permutationStep = permutationStepSkript(encParentLiterals, encChildLiterals, lpFunctionApp(parentNameLpEnc, unboundVarsChild))
              usedSymbols = usedSymbols + metaPermutation

              Out.lp_debug_info(s"Permutation step: ${permutationStep.pretty}")
              allSteps = allSteps :+ lpRefine(permutationStep)
            }

            // if necessary, we apply transformations to flip sides of literals etc.

            val proofScript = lpProofScript(allSteps)
            if (canEncode) (proofScript, usedSymbols, None)
            else (lpProofScript(Seq.empty),Set.empty,  Option(s"permutation necessary for the encodng")) // (See problem lpProof_SYO885^1_033_003)
          } else (lpProofScript(Seq.empty),Set.empty,  Option(s"instanciation with variables not encoded yet"))
        } else (lpProofScript(Seq.empty),Set.empty,  Option(s"no term unifications to encode"))
      }
    }
    else{
      (lpProofScript(Seq.empty),Set.empty,  Option(s"the unification mode $mode is either not set or not encoded yet..."))
    }
  }

  }
