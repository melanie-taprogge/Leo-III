package leo.modules.output.LPoutput
import leo.Out
import leo.datastructures.Literal.asTerm
import leo.modules.output.LPoutput.OldLpDatastructures.Encodings._
import leo.datastructures.{AddInfoCnf, AddInfoCnfConj, AddInfoPara, AddInfoUni, Clause, ClauseProxy, Literal, MoveQuantStep, QuantExists, QuantStep, QuantUniv, Signature, SkolemStep, Term, Type, UniTermByBoundVar, UniTermByTerm}
import leo.modules.HOLSignature._
import leo.modules.calculus.PolaritySwitch
import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures._
import leo.modules.output.LPoutput.AccessoryRules._
import leo.modules.output.LPoutput.lpInferenceRuleEncoding._
import leo.modules.output.LPoutput.SimplificationEncoding._
import leo.modules.calculus.Simp.normalize
import leo.modules.output.LPoutput.CNFEncoding.{cnfTacQuantifiers, lpMoveExists, lpMoveUniv, lpSkolemizeExists, lpSkolemizeUniv, onlyBoolRulesTermName}
import leo.modules.output.LPoutput.CommonProofSteps.ScriptBuilders.assumeClauseVars
import leo.modules.output.LPoutput.OldLpDatastructures.LPSignature.{eqImp, lpEm, lpLorElimMulti, lpLorIntro2, lpLorIntroMulti, lpLorelim}
import leo.modules.output.LPoutput.LPoutput.{ParentInfo, abbreviationFormulaeFile}
import leo.modules.saturatedUserSignature

import scala.collection.mutable

/** Modular encoding of proofs
  *
  * @author Melanie Taprogge
  */

object ModularProofEncoding {

  ////////////////////////////////////////////////////////////////
  ////////// Additional Leo-III Inferences
  ////////////////////////////////////////////////////////////////

  def encPolaritySwitch(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript) = {

    val bVarMap = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

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
          val polaritySwitchStep = lpRefine(lpFunctionApp(lpStd_eq_sym.name,Seq(lpSimp_dne.instanciate(encLeft))))
          val polaritySwitchName = s"PolaritySwitch_lit$litCount"
          val havepolaritySwitchStep = lpHave(polaritySwitchName, equalityToProve.prf, lpProofScript(Seq(polaritySwitchStep)))
          allSteps = allSteps :+ havepolaritySwitchStep

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

    (lpProofScript(allSteps))
    }

  def initialEncUnclausified(parent: Clause, child: Clause, sig: Signature)={
    val bVars = clauseVars2LP(child.implicitlyBound ++ parent.implicitlyBound, sig, Set.empty)._2
    val encParent = term2LP(Clause.asTerm(parent),Map.empty,sig)._1
    val encChild = term2LP(Clause.asTerm(child),bVars,sig)._1
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

  def EncDefExSimp(child: ClauseProxy, parent: ClauseProxy, defRuleDefined: Boolean, additionalInfoSimp: Boolean, reducedTerm0: Option[Literal], applyAllDefsTacName: String, parentNameLpEnc: lpConstantTerm, sig: Signature):(Seq[lpProofScriptStep],Option[String]) = {

    // Encoding of the application of the EP rule defexp_and_simp_and_etaexpand (Definition expansion)
    // The modular proof script can consist of the following steps:
    // 1. If definitions are defined, exhausitively apply them using rewrite
    // 2. If simplifications were applies, verify them using the encoding of (SIMP)
    // 3. Refine with the last step

    // todo: test if we also need to handle <=> and <~> specifically

    // cosntruct the tactic applying all the occuring definitions val sName = lpEscapeName(symbol.name, sig, false)
    val allSymbols = saturatedUserSignature(Clause.symbols(parent.cl).distinct)(sig)
    val keysWithDefn = allSymbols.filter(k => sig(k).hasDefn).toList
    val allDefs = keysWithDefn.map(key => s"${lpEscapeName(sig.apply(key).name, sig, false)}_def") //todo: have a unified name generation method for def file generation and this


    if(!additionalInfoSimp){

      val (encParent,encChild, _, _) =  initialEncUnclausified(parent.cl, child.cl, sig)
      Out.lp_debug_info(s"Encoding defExSimp of ${encParent.pretty} to ${encChild.pretty}")
      val reducedTerm = if (reducedTerm0.isDefined) reducedTerm0.get else throw new Exception(s"LP-Encoding: Trying to encode DefExSimp but reduced Term derived by Leo-III is not defined")
      val encExpTerm = term2LP(asTerm(reducedTerm),Map.empty,sig,Set(),false)._1
      Out.lp_debug_info(s"parent: ${Clause.asTerm(parent.cl)}")
      Out.lp_debug_info(s"expanded term: ${asTerm(reducedTerm)}")
      Out.lp_debug_info(s"child: ${child.cl}")

      //Out.lp_debug_info(s"Contains <= ? ${parent.cl.lits.flatMap(symbols(_)).contains(sig("<=").key)}")

      val (defExpStep, appliedParent) : (Seq[lpProofScriptStep],lpTerm) =
        if (allDefs.nonEmpty){
          val haveStepName = "defExpStep"
          val assumptionName = lpConstantTerm("h")
          val applyParentToStep = lpFunctionApp(lpConstantTerm(haveStepName),Seq(parentNameLpEnc))
          //val applyDefExp = Seq(lpEval(lpOlConstantTerm(applyAllDefsTacName)))
          val allDefsInRW = allDefs.map(defName => lpRewrite(None, lpOlConstantTerm(s"${abbreviationFormulaeFile}" + defName)).olUsrTac)
          val applyAllDefsTact: lpProofScriptStep = lpRepeat(allDefsInRW.reduceRight((r1: lpProofScriptStep, r2: lpProofScriptStep) => lpTacBinaryConnectiveTerm(lpOrElseTac, r1, r2))).asUserTac
          val applyDefExp = Seq(lpEval(applyAllDefsTact))
          val (assumeStep, refineStepHave): (lpAssume, lpRefine) = {
            (lpAssume(Seq(assumptionName)), lpRefine(assumptionName))
          }
          (Seq(lpImpHaveStepConstructor(haveStepName, Seq(), encParent, encExpTerm,(applyDefExp ++ Seq(assumeStep,refineStepHave)))),applyParentToStep)
        }else (Seq(),parentNameLpEnc)

      val (maybeSimpStep, refineName) : (Seq[lpHave],lpTerm) = if (encExpTerm != encChild){
        // Use the encoding of formula simplification to generate the proofs
        // We only need the exhaustive simplification step, as the implicit transformations will only occur when operating on literals
        val (simpStep, simpStepName) = encSimpProofSubstep(Seq.empty, encExpTerm, encChild)
        (Seq(simpStep), lpFunctionApp(lpConstantTerm(simpStepName),Seq(appliedParent)))
      }else (Seq(), appliedParent)

      val refineStep = lpRefine(refineName)

      ((defExpStep ++ maybeSimpStep) :+ refineStep, None)

    }else{
      Out.lp_debug_info("Rweriting under binder required in order to encode Simplification step")
      (Seq(), Some("Rweriting under binder required in order to encode Simplification step"))
    }
  }

  object RwCnfEncoding {

    /**
      * RWCnf — Outline of the encoded proof
      *
      *
      * Steps:
      * 0) Assume any free variables
      * 1) Prove that the original formula = the clausified one in a sub-step using the appropriate user-defined Lambdapi tactic
      * 2) refine with the sub-step of (1) and the parent
      *
      */

    private final case class RwCnfVarContext(allBvars: Seq[(Int, Type)], bV: Map[Int, String], allMetaVars: Seq[lpTypedVar])
    private final case class RwCnfContext(varCtxt: RwCnfVarContext, encParent: lpClauseInst, conj: lpOlTerm, maybeQuantifiedConj: lpMlType, allSymbols: Set[Signature.Key])


    /** Orchestrator of the RW-CNF proof:
      * 0) Build the encoding context and preflight checks
      * 1) Plan/assume clause variables (avoid name clashes via offsetting)
      * 2) Build the clausification sub-step using user tactics (quantifiers + bool ids)
      * 3) Refine with the instantiated parent
      *
      * @return (script, skipReason, quantified goal type, potentially defined symbols)
      *         - If not encodable, returns an empty script and a reason.
      *         - The `lpMlType` is the (possibly ∀-quantified) goal.
      */
    def encRenameCnf_conj(parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, cnfInfo: AddInfoCnf, sig: Signature): (lpProofScript, Option[String], lpMlType, Set[Signature.Key]) = {
      //todo: You should be able to safeley remove the "allsymbols" as the step is added to the standard leo output now anyways...
      ///////////////////////////////////////////////////////////////////////////////////////
      //// 0. Set up: encode everything and test if the step can be encoded
      // encodings
      val ctxt = buildRwCnfContext(parent, cnfInfo, sig)
      val RwCnfContext(varCtxt, encParent, conj, maybeQuantifiedMlConj, allSymbols) = ctxt
      Out.lp_debug_info(s"Attempting to verify clausification of ${parentNameLpEnc.name}: ${encParent.term.pretty} resulting in ${conj.pretty}")
      // check if we can encode
      val cantEncode = checkRwCNFEncodable(parent, cnfInfo, varCtxt.allBvars)

      checkRwCNFEncodable(parent, cnfInfo, varCtxt.allBvars) match {
        case Some(cantEncode) => (lpProofScript(Seq.empty), Some(cantEncode), maybeQuantifiedMlConj, allSymbols)
        case None =>

        ///////////////////////////////////////////////////////////////////////////////////////
        //// 1. Assume any free variables
        // change names of the meta-vars to avoid overlap with variables in the sub-steps
        val (assumeStep, apply2parent, apply2step): (Seq[lpProofScriptStep], Seq[lpTypedVar], Seq[lpTypedVar]) = handleClauseVars(cnfInfo,varCtxt,sig)

        ///////////////////////////////////////////////////////////////////////////////////////
        //// 2. Proof the conjunction in a sub-step using a Lambdapi tactic
        // generate the necessary instances of user-defined tactics for the sub-step
        val (allSubProofSteps, maybeQuantifiedConj) = rwCNFTacticGen(cnfInfo,varCtxt,sig,conj)
        // construct the sub-step and the proof
        val clauseStepName = s"Clausification"
        val clausStep: lpHave = lpEqHaveStepConstructor(clauseStepName, Seq.empty, encParent.term, maybeQuantifiedConj, lpOtype, allSubProofSteps)

        ///////////////////////////////////////////////////////////////////////////////////////
        //// 3. Refine with the (instantiated) parent
        val refineStep = assembleRefinement(apply2parent, parentNameLpEnc, clauseStepName, apply2step)
        // compose the entire proof script
        val resscript = (assumeStep ++ Seq(clausStep) :+ refineStep)
        // todo: we now either have vars in the initial assume or in the maybeAssumeStep, as we do not handle cases where we add vars and also
        //  already had clause-variables. Once we start encoding this, we need to handle them uniformly.

        (lpProofScript(resscript), None, maybeQuantifiedMlConj, allSymbols)
      }
    }

    /** Build the full RW-CNF context for a parent clause and its CNF transformation. */
    private def buildRwCnfContext(parent: ClauseProxy, cnfInfo: AddInfoCnf, sig: Signature): RwCnfContext = {
      val encParent = lpClauseInst(parent.cl, sig)
      val (bV, encChildClauses) = lpClauseInst.apply_to_set(cnfInfo.derivedClauses, sig)
      val allBvars = cnfInfo.derivedClauses.flatMap(_.implicitlyBound).distinct.sortBy(_._1).reverse
      val allMetaVars = var2Lp(allBvars, bV, sig).map(_.asMlVar)
      val conj = lpOlUntypedBinaryConnectiveTerm_multi.conjunction(encChildClauses.map(_.term))
      val maybeQuantifiedConj: lpMlType = if (allMetaVars.isEmpty) conj.prf else lpMlDependType(allMetaVars, conj.prf)
      val allSymbols = cnfInfo.derivedClauses.flatMap(Clause.symbols(_)).toSet

      RwCnfContext(RwCnfVarContext(allBvars, bV, allMetaVars), encParent, conj, maybeQuantifiedConj, allSymbols)
    }

    /** Determine whether this CNF step can be encoded with the current backend */
    private def checkRwCNFEncodable(parent: ClauseProxy, cnfInfo: AddInfoCnf, allBvars: Seq[(Int, Type)]): Option[String] = {
      if (cnfInfo.renameHappend) Some("Renaming not encoded yet")
      else if (cnfInfo.rewriteUnderBinder) Some("Clausification involving Binders not encoded")
      else if (parent.cl.implicitlyBound.nonEmpty && (parent.cl.implicitlyBound.length != allBvars.length)) Some("Fresh variables in re-clausification")
      else if (parent.cl.lits.length > 1) Some("Re-clausification of clause longer than one currently not encoded")
      else if (cnfInfo.addInfoQuants.exists { case SkolemStep(_, _, ftVs, _) => ftVs.nonEmpty; case _ => false}) Some("Free type-variables in Skolems")
      else None
    }

    /** Construct the `assume` tactic call and the lists of variables used to instantiate
      * the parent term and the clausification sub-step application.
      *
      * Convention:
      * - “Old” variables = variables already present in the parent clause.
      * - “New” variables = variables introduced by generalization (`MoveQuantStep`) during clausification.
      *
      * Behavior:
      * - Old variables are applied to the parent step to instantiate it.
      * - New variables are applied to the application of the parent to the sub-step.
      * - All variables handled here are used in `assume` or `refine` calls in the main proof script.
      * To ensure variable names remain unique between the main body and the sub-step,
      * all variables are offset by the number of “new” variables.
      */
    private def handleClauseVars(cnfInfo: AddInfoCnf, ctxt: RwCnfVarContext, sig: Signature): (Seq[lpProofScriptStep], Seq[lpTypedVar], Seq[lpTypedVar]) = {
      val RwCnfVarContext(allBvars, bV, allMetaVars) = ctxt
      // If there are no meta variables -> noting to do
      if (allMetaVars.isEmpty) return (Seq.empty, Seq.empty, Seq.empty)

      // Else:
      // 1) partition into "new" and "old" variables
      val newBVars = cnfInfo.addInfoQuants.collect { case MoveQuantStep(v, _) => v }
      // ensure that all newly added vars are amongst the boundVars of the step
      val allIds = allBvars.map(_._1).toSet
      val newIds = newBVars.map(_._1).toSet
      assert(newIds.subsetOf(allIds), s"Error in LP-Encoding: MoveQuantStep variables not all in allBvars. moved=${newIds.diff(allIds)}; all=$allIds")
      val (_, oldBVars) = allBvars.partition(v => newIds.contains(v._1))

      // 2) offset the names
      val nameOffset = newBVars.length
      val extendedBvars = extendBvarMap(bV, nameOffset)
      def offsetBVar(n: Int) = n + nameOffset
      val shiftedMetaVars = var2Lp(allBvars.map(bVar => (offsetBVar(bVar._1), bVar._2)), extendedBvars, sig).map(_.asMlVar)
      val shiftedOldMetaVars = var2Lp(oldBVars.map(bVar => (offsetBVar(bVar._1), bVar._2)), extendedBvars, sig).map(_.asMlVar)
      val shiftedNewMetaVars = var2Lp(newBVars.map(bVar => (offsetBVar(bVar._1), bVar._2)), extendedBvars, sig).map(_.asMlVar)

      Out.lp_debug_info(s"meta vars to assume: ${shiftedMetaVars.map(_.pretty)}")

      // todo : This will have to be revised once we handle inner universal quantifiers
      (Seq(lpAssume(shiftedMetaVars)), shiftedOldMetaVars, shiftedNewMetaVars)
    }

    /** Synthesize the proof-script steps for handling quantifiers in RWCnf,
      * and (if needed) wrap the clausified conjunction under a ∀-prefix.
      *
      * Currently, only universal quantifiers at the prenex position are handled.
      * These are handled by individual tactics calls that assume the necessary variables and
      * instanciate all the following Skolem Defs as needed.
      * Therefore, we split:
      *  - Prenex part = all leading generalizations (MoveQuantStep) up to the last such step.
      *   (instantiated one-by-one)
      *  - Remaining   = (inner) Skolemizations (SkolemStep) and any later steps.
      *   (passed to the quantifier tactic in one batch)
      */
    private def rwCNFTacticGen(cnfInfo: AddInfoCnf, ctxt: RwCnfVarContext, sig: Signature, conj: lpOlTerm): (Seq[lpProofScriptStep], lpOlTerm) = {
      val RwCnfVarContext(allBvars, bV, _) = ctxt
      // 1. Split the list of steps into the part that contains any prenex (universal) quantifiers and the rest (only skolem steps)
      // the terms to skolemize more deeply lested terms
      val lastUQIdx = cnfInfo.addInfoQuants.lastIndexWhere {
        case MoveQuantStep(_, _) => true
        case _ => false
      }
      val (prenexQuants, remainingSk) =
        if (lastUQIdx < 0) (Seq.empty[QuantStep], cnfInfo.addInfoQuants)
        else cnfInfo.addInfoQuants.splitAt(lastUQIdx + 1)

      // Instantiate prenex generalizations individually
      val (leadingQuants, orderedVars): (Seq[lpProofScriptStep], Seq[lpOlTypedVar]) = if (prenexQuants.nonEmpty) {
        val (ruleInstances, orderedVars0) = generateRuleInst(prenexQuants, allBvars, bV, sig)
        (ruleInstances.map(lpEval(_)), orderedVars0)
      } else (Seq(), Seq())

      // Batch the remaining Skolem steps, or fall back to Boolean identities if none
      val nestedSkolems: Seq[lpProofScriptStep] = if (remainingSk.nonEmpty) {
        val (ruleInstances, orderedVars0) = generateRuleInst(remainingSk, allBvars, bV, sig)
        assert(orderedVars0.isEmpty, "Error in LP encoding: expected instances of Skolemization but found quantifier generalisazion")
        Seq(lpEval(lpFunctionApp(cnfTacQuantifiers, Seq(lpList(ruleInstances)))))
      } else Seq(lpEval(onlyBoolRulesTermName))

      // Quantify the goal if prenex produced ordered variables
      val maybeQuantifiedConj = if (orderedVars.nonEmpty) lpOlBoundTerm(lpOlForAll, orderedVars, conj) else conj

      (leadingQuants ++ nestedSkolems, maybeQuantifiedConj)
    }

    /** Generate a rewrite tactic with appropriate application of quantified variables for a given Skolem term */
    private def SkolemRwTac(skInto: SkolemStep, bV: Map[Int, String], sig: Signature, quantified: Boolean = true): lpOlFunctionApp = {
      val skName = lpOlConstantTerm(nameSkDef(skInto.sko,sig).local.value) // todo: naming function uniform wih LPOutput module
      val varsToApply = var2Lp(skInto.fVs, bV, sig, true).map(Left(_))
      val appliedName = if (quantified && varsToApply.nonEmpty) lpOlFunctionApp(skName, varsToApply) else skName
      lpRewrite(None, appliedName, true).olTermApp
    }

    /** Generate user-defined tactic instances for the quantifier steps, collect the ordered variables introduced by generalization.
      *
      * Behavior:
      * For each SkolemStep, choose the appropriate user tactic (lpSkolemizeUniv / lpSkolemizeExists) and instantiate it with
      * the rewrite rule of the Skolem definition.
      * For each MoveQuantStep, choose lpMoveUniv / lpMoveExists, assume the corresponding variable, and add that variable to
      * orderedVars (order matters).
      *
      * */
    private def generateRuleInst(quantifierInfo: Seq[QuantStep], allBvars: Seq[(Int, Type)], bV: Map[Int, String], sig: Signature): (Seq[lpOlFunctionApp], Seq[lpOlTypedVar]) = {
      quantifierInfo.foldLeft((Vector.empty[lpOlFunctionApp],Vector.empty[lpOlTypedVar])){
        case ((insts, ordVars), step) => step match {
          // Choose the correct user-defined tactic and instantiate it with the rewrite rule of the Skolem definition
          case sko: SkolemStep =>
            val neededProcedure = sko.polarity match {
              case QuantUniv => lpSkolemizeUniv;
              case QuantExists => lpSkolemizeExists
            }
            val skoRW = Left(SkolemRwTac(sko, bV, sig, true))
            val app = lpOlFunctionApp(neededProcedure, Seq(skoRW))
            (insts :+ app, ordVars)

          case uq: MoveQuantStep =>
            val neededProcedure = uq.polarity match {
              case QuantUniv => lpMoveUniv;
              case QuantExists => lpMoveExists
            }
            assert(allBvars.contains(uq.corrChildVar), "Error in LP encoding: Generalized universal quantifier but used variable is not in child")
            val corVar = var2Lp(uq.corrChildVar._1, uq.corrChildVar._2, bV, sig, true)
            val univTactic = Left(lpAssume(Seq(corVar)).olTermApp)
            (insts :+ lpOlFunctionApp(neededProcedure, Seq(univTactic)), ordVars :+ corVar)
        }
      }
    }

    /** assemble the final `refine` step with aproperiate instanciation */
    private def assembleRefinement(apply2parent: Seq[lpTypedVar], parentNameLpEnc: lpConstantTerm, clauseStepName: String, apply2step: Seq[lpTypedVar]): lpRefine = {
      val appliedParent = lpFunctionApp.mk(parentNameLpEnc, apply2parent)
      val instClausStep = lpFunctionApp(lpFunctionApp(lpFunctionApp(eqImp.name, Seq(lpConstantTerm(clauseStepName))), Seq(appliedParent)), apply2step)
      lpRefine(instClausStep)
    }

  }

  object CnfConjEncoding {
    // cnfConj-only data holders

    final case class cnfConjCtxt(encChild: lpClauseInst, encParent: lpClauseInst, clauseIdx: Int, clauseCount: Int)

    /**
      * cnfConj — Outline of the encoded proof
      *
      *
      * Steps:
      * 0) Assume all free variables of the child.
      * 1) Refine with the instanciated meta-theorem "select"
      *
      */
    def encCnfConj(child: ClauseProxy, parent: ParentInfo, cnfInfo: AddInfoCnfConj, sig: Signature): lpProofScript = {

      // todo: possibly add a defined term reflecting the whole conjunction as a list after deriving the clause and then simply reference
      //  it here rather than constructing the sequence of wildcards?
      
      val ctxt = cnfConjEncoding(child, parent, cnfInfo, sig) match {
        case Left(error) => throw new Exception(error)
        case Right(value) => value
      }

      val cnfConjCtxt(encChild, encParent, indxInConj, numOfClauses) = ctxt

      // preliminaries
      val allMetaVars = encParent.metaVars


      ///////////////////////////////////////////////////////////////////////////////////////
      //// 0) Assume any free variables
      val varsToAssume = encChild.metaVars
      val assumeStep = if (varsToAssume.nonEmpty) Seq(lpAssume(varsToAssume)) else Seq()

      ///////////////////////////////////////////////////////////////////////////////////////
      //// 1) Refine with the instanciated meta-theorem "select"
      // We need to instanciate those variables in the assume step that are not also free in the derived clause with witness terms
      val applyToSelectSteps = allMetaVars.map(metVar => if (varsToAssume.contains(metVar)) metVar
        else {
        val witness = lpWitness.fromAnyType(metVar.ty)
        Out.lp_debug_info(s"Instantiating ${metVar.pretty} with witness ${witness.pretty}")
        witness
      })
      val seqWithWildcards = Seq.fill(numOfClauses)(lpOlWildcard).updated(indxInConj, encChild.term)

      // Instanciate the meta theorem
      val selectStep = metaSelect.instanciate(seqWithWildcards, indxInConj, lpFunctionApp(parent.lpName, applyToSelectSteps))

      (lpProofScript(assumeStep :+ (lpRefine(selectStep))))
    }

    private def cnfConjEncoding(child: ClauseProxy, parent: ParentInfo, cnfInfo: AddInfoCnfConj, sig: Signature): Either[String, cnfConjCtxt] = {

      // do the necessary encodings and checks to ensure admissable input data

      // todo: pipe the encoded parent form the cnf steps through and get the clause count from there, possibly also just extract the index of the clause

      val AddInfoCnfConj(indxInConj, numOfClauses) = cnfInfo
      if (indxInConj > (numOfClauses - 1)) return Left(s"Error in Lambdapi encoding: Trying to pick clause $indxInConj but the conjunction only has $numOfClauses clauses")

      // ensure that parent is indeed a conjunction with more than one conjunct
      val (_, encClauses) = lpClauseInst.apply_to_set(Seq(parent.clPr.cl,child.cl),sig)
      val encParent = encClauses(0)
      val encChild = encClauses(1)

      encParent.lits match {
        case Seq(lpOlUntypedBinaryConnectiveTerm(`lpAnd`, _, _)) => ()
        case Seq(lpOlUntypedBinaryConnectiveTerm_multi(`lpAnd`, _)) => ()
        case _ => return Left(s"Error in Lambdapi encoding: Trying to encode application of cnfConj but parent has wrong shape : ${encParent.term.pretty}")
      }

      Out.lp_debug_info(s"Conjunction of $numOfClauses clauses under consideration: ${encParent.term.pretty}")
      Out.lp_debug_info(s"Extracting clause with index $indxInConj (${encChild.term.pretty})")

      Right(cnfConjCtxt(encChild, encParent, indxInConj, numOfClauses))
    }
  }





  ////////////////////////////////////////////////////////////////
  ////////// Extensionality
  ////////////////////////////////////////////////////////////////

  case class funcExtState(currParentLits: Seq[lpOlTerm],
                          currentUnencParent: Seq[Literal],
                          lastStepName: lpTerm,
                          allSteps: Seq[lpProofScriptStep],
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

  def encFuncExtPos(child: ClauseProxy, parent: ClauseProxy, editedLiterals: Seq[(Literal, Literal)], parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Option[String]) = {
    
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
            val (error, pfeSteps, pfeStepName, pfeRwImplicitTrans, updatedParentLits) = posFuncExtStep(origLit, edLit, state.currentUnencParent, state.currParentLits, permutation, state.lastStepName, bVarMap, sig, idx)

            Out.lp_debug_info(s"pfeRwImplicitTrans:\n${pfeRwImplicitTrans.map(_.pretty)}}")
            // Return a new state with the updated values
            state.copy(
              cantEncode = if (state.cantEncode.isDefined) state.cantEncode else error,
              allSteps = state.allSteps ++ pfeSteps,
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
      )
    } else {
      postPfeState.copy(allSteps = (postPfeState.allSteps ++ postPfeState.literalsToEqRW):+ lpRefine(lpFunctionApp(postPfeState.lastStepName, Seq())))
    }

  if (postPermStep.cantEncode.isDefined) (lpProofScript(postPermStep.allSteps), Some(s"FuncExt can not be encoded: ${postPermStep.cantEncode.get}"))
  else (lpProofScript(postPermStep.allSteps), None)
}

  private def posFuncExtStep(origLit: Literal, edLit: Literal, currentUnencParent: Seq[Literal], currParentLits: Seq[lpOlTerm], permutation: Seq[Int], lastStepName: lpTerm, bVarMap: Map[Int, String], sig: Signature, editLitCount: Int): (Option[String], Seq[lpProofScriptStep], lpTerm, Seq[lpProofScriptStep], Seq[lpOlTerm]) = {
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
    val (pfeApp, newParentLits) = applyInstFuncExtRule(currParentLits, appliedLit, indexOfLit, namefuncExtStep, applicationStepName, lastStepName)
    val allSteps = Seq(pfeInst, pfeApp)

    /////////////////////////////////////////////////////
    //// 4. Apply necessary implicit transformations
    // Compare the derived literal with the literal that it is mapped to and apply any necessary transformations
    val (cantEncode, literalsToEqRW) = implicitRwTransFuncEx(encEditLit, appliedLit.term, permutation, indexOfLit, currParentLits.length)
    if (cantEncode) {
      Out.lp_debug_info(s"Implicit RW transformation necessary but can not be applied")
      (Some("unencoded transformation necessary"), Seq(), lastStepName, Seq(), Seq())
    } else (None, allSteps, applicationStepName, literalsToEqRW, newParentLits)
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

  private def applyInstFuncExtRule(currParentLits: Seq[lpOlTerm], appliedLit: lpLiteral, indexOfLit: Int, namefuncExtStep:String,  applicationStepName: lpConstantTerm, lastStepName: lpTerm): (lpHave, Seq[lpOlTerm])={
    // use the instiaciated rule for PFE or NFE and apply it to the desired literal in the parent
    val proofTerm: lpTerm = if (currParentLits.length > 1)
     metaTransform.instanciate(currParentLits, indexOfLit, lpConstantTerm(namefuncExtStep), lastStepName)
    else
      lpFunctionApp(lpConstantTerm(namefuncExtStep), Seq(lastStepName))
    // todo: when encoding NFE, make sure we do not by default add PFE as a needed Rule
    val refineWithFunExt = lpRefine(lpFunctionApp(proofTerm, Seq()))
    val newParentLits = currParentLits.updated(indexOfLit, appliedLit.term)
    val pfeApp = lpHave(applicationStepName.name, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, newParentLits).prf, lpProofScript(Seq(refineWithFunExt)))
    Out.lp_debug_info(s"Successfully applied $namefuncExtStep (in setp $applicationStepName)")
    Out.lp_debug_info(s"updatedParent: ${lpOlUntypedBinaryConnectiveTerm_multi(lpOr, newParentLits).pretty}")
    (pfeApp,newParentLits)
  }

  private def implicitRwTransFuncEx(encEditLitTerm: lpOlTerm,appliedLitTerm: lpOlTerm, permutation: Seq[Int], indexOfLit: Int, lenParent: Int):(Boolean, Seq[lpProofScriptStep])={
    if (!alphaEquivalent(encEditLitTerm, appliedLitTerm)) {
      Out.lp_debug_info(s"Looking for transformations to get from \n${encEditLitTerm} to \n${appliedLitTerm}}")
      // if we had a permutation, we need to infer the index in the clause modulo application
      val indexModuloPerm = permutation.indexOf(indexOfLit)
      val (literalsToEqRW, canEncode0) = transformLiteral(encEditLitTerm, appliedLitTerm, indexModuloPerm, lenParent)
      if (canEncode0) {
        Out.lp_debug_info(s"Transformation to equational form is applied: ${literalsToEqRW.map(_.pretty)}")
        (false, literalsToEqRW)
      } else {
        Out.lp_debug_info(s"Transformation to equational form necessary but can not be applied")
        (true, Seq())
      }
    } else (false, Seq())
  }



  def encBoolExt(child: ClauseProxy, parent: ClauseProxy, parentNameLpEnc: lpConstantTerm, addInfo: Set[(Literal,Seq[Literal])], sig: Signature): (lpProofScript, Option[String]) = {

    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

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
      transitions = transitions :+ lpInferenceRuleEncoding.boolExt(lhs,pol).instanciate(beforeLhsEnc,beforeRhsEnc)
    }

    // 3. Prove the application of the rules using the necessary accessory transform rule
    // todo

    // 4. If the rules resulted in double occurrences of literals, proof the removal using the necessary delete rule
    // todo

    // 5. If the order of literals was changed, generate a transform rule and apply it to permute the literals
    // todo

    if (parent.cl.lits.length > 1) {
      (lpProofScript(Seq.empty),Some(s"Encoding of boolExt in LP for clauses with more than one literal not encoded yet"))
    }
    else {
      allSteps = allSteps :+ lpRefine(lpFunctionApp(transitions.head, Seq(lpFunctionApp(parentNameLpEnc, freeVarsChild))))
      val proof = lpProofScript(allSteps)

      // 6. Refine with the last proven step
      (proof, None)
    }
  }


  ////////////////////////////////////////////////////////////////
  ////////// Primary Inference Rules
  ////////////////////////////////////////////////////////////////

  /*
  def encPara(child: ClauseProxy, parents: Seq[ClauseProxy], parentNames:  Seq[lpConstantTerm], info0: Option[AddInfoPara], sig: Signature): (lpProofScript, Option[String]) = {
    val info = info0.getOrElse(throw new Exception(s"no additional infomration for the encoding of paramodulation was provided"))

    ////////////////////////////
    // 0. Find out if the resulting clause was simplified -> if so, we split into two steps
    if (info.preSimpClause.lits != child.cl.lits){
      // first encode paramodulation itself to derive the non-simplified clause
      val paraRes = encPara0(info.preSimpClause,parents,parentNames,info,sig)
      val paraStep = lpConstantTerm(s"...")
      // then prove the simplified clause based on the non-simplified one
      val simpRes = newSimpEncoding(child.cl,info.preSimpClause,paraStep,sig)
      throw new Exception(s"unfinished")
    }else{
      // straight forward to prove the clause...
      encPara0(child.cl,parents,parentNames,info,sig)
      throw new Exception(s"unfinished")
    }
  }

   */

  object ParamodEncoding {
    // paramod-only data holders
    final case class ParaWithClause(withLit: Literal, otherLits: Seq[lpOlTerm], enc: lpClauseInst, encWithLit: lpLiteral, name: lpConstantTerm, currentRef: lpTerm, withLitIdx: Int, len: Int)
    final case class ParaIntoClause(intoLit: Literal, enc: lpClauseInst, encIntoLit: lpLiteral, name: lpConstantTerm, currentRef: lpTerm)
    final case class ParaChildClause(uni: Literal, intoLit: Literal, enc: lpClauseInst, encUniLit: lpOlTerm, encIntoLit: lpLiteral, encPosUniLit: lpOlTerm, intoLitIdx: Int, len: Int)
    final case class EncParaCtx(withC: ParaWithClause, intoC: ParaIntoClause, childC: ParaChildClause, bvars: Map[Int, String])
    final case class EncParaProofSteps(transformIntoLitSteps: Seq[lpProofScriptStep], maybeFlipIntoLitStep: Seq[lpProofScriptStep], rewriteWithUniLit: lpRewrite, childIntoTermPattern: lpRewritePattern, vIntro1_intoClause_uniLit: lpFunctionApp, assumeUniConsT: lpAssume)

    /**
      * encPara — Outline of the encoded proof
      *
      * Notation:
      *   - withClause / withLit: clause and literal used for rewriting.
      *   - intoClause / intoLit: clause and literal that is rewritten.
      *   - UF: the (positive) equality u = v that becomes the new unification constraint;
      *     in the child clause it appears as ¬(u = v).
      *
      * Steps:
      * 0) Assume all free variables of the child.
      *
      * 1) Ensure the rewrite literal is equational:
      * If withLit is positive and non-equational, transform it into an equality in a separate sub-step.
      *
      * 2) Case split on UF (the equality u = v underlying the new constraint):
      * A) Case UF is TRUE (u = v holds):
      *       - If withClause has one literal:
      *         Assume withLit; perform (i)–(ii); in (iii) refine using disjunction introduction from intoClause ∨ UF.
      *       - If withClause has multiple literals, perform an inner case split on withLit:
      *         A1) withLit TRUE:
      *         Assume withLit; perform (i)–(ii); then introduce using the remaining withClause literals
      *         together with (intoClause ∨ UF).
      *         A2) “withClause without withLit” TRUE:
      *         Assume the remaining withClause literals and introduce directly to match the goal’s prefix.
      *         (i) Prepare the target (the intoLit in the child):
      *         - If the intoLit in the child is non-equational, expand it to an equality.
      *         - If the orientation differs from what we need, flip the equality.
      *           (ii) Rewrite the targeted subterm of intoLit:
      *         - First using the (equational) withLit.
      *         - Then using UF (u = v).
      *           (iii) Close by disjunction introduction
      *  B) Case UF is FALSE (¬(u = v) holds):
      *           Assume ¬(u = v) and close the goal by disjunction introduction with the assumed negated constraint.
      *
      * Notes:
      *   - Rewriting under binders is not encoded; if the target position lies under a binder, we return a “can’t encode” result.
      */
    def encPara(child: Clause, parentWithClause: ParentInfo, parentIntoClause: ParentInfo, info: AddInfoPara, sig: Signature): (lpProofScript, Option[String]) = {

      // todo: review the saved inforamation and weather we need all of it

      ////////////////////////////
      // Encodings and prelim
      // todo: prelim cheks: child has at least two literals, UC is equational, check the indices here too

      val ctxt = encParaClauses(child, parentWithClause, parentIntoClause, info, sig) match {
        case Left(error) => throw new Exception(error)
        case Right(value) => value
      }

      // Create a pattern for the target sub-term of the intoLit in the child
      val childIntoTermPattern = generateParaIntoSubTermPattern(ctxt, info, sig) match {
        case Left(error) => return (lpProofScript(Seq.empty), Some(error))
        case Right(value) => value
      }


      ////////////////////////////
      // 0) Assume free variables
      val assumeVarsStep = assumeClauseVars(ctxt.childC.enc)

      ////////////////////////////
      // 1) Ensure the rewrite literal is equational
      val (updatedWithCl, stepWithLit2Eq) = withCl2eq(ctxt.withC) match {
        case Left(error) => throw new Exception(error)
        case Right(value) => value
      }
      val newCtxt = ctxt.copy(withC = updatedWithCl)

      ////////////////////////////
      // 2) Case split on UF (the equality u = v underlying the new constraint):
      //    A) Assume that the UF holds

      // generate some proof snippets concerning the UF
      val (assumeUniConsT, rewriteWithUniLit, vIntro1_intoClause_uniLit) = branchUniLitTrue_prelim(newCtxt, info, childIntoTermPattern)

      // Prepare the intoLit in the child (if necessary, carry out transform and flip steps)
      val transformIntoLitSteps = transformIntoLit(newCtxt)
      val maybeFlipIntoLitStep = flipIntoLit(newCtxt, info)

      // Combine the proof snippets that do not depend on the length of the with Literal:
      val proofBricks = EncParaProofSteps(transformIntoLitSteps, maybeFlipIntoLitStep, rewriteWithUniLit, childIntoTermPattern, vIntro1_intoClause_uniLit, assumeUniConsT)

      // construct the proof-branch for UF holding depending on the length of the withClause
      val caseUniLitTrue = if (newCtxt.withC.len > 1) {
        branchUniLitTrue_longerWithClause(newCtxt, info, proofBricks)
      } else {
        branchUniLitTrue_unaryWithClause(newCtxt, info, proofBricks)
      }

      ////////////////////////////
      // 2 B) Case UF is FALSE (¬(u = v) holds)
      val caseUniLitFalse: lpProofScript = branchUniLitFalse(newCtxt.childC)

      // Finish 2 by combining the proof scripts for the case split
      val ufTrueOrFalse = lpFunctionApp(lpLorelim.name, Seq(lpFunctionApp(lpEm.name, Seq(newCtxt.childC.encPosUniLit)), lpWildcard, lpWildcard))
      val caseSplitUniLit = lpRefine(ufTrueOrFalse, Seq(caseUniLitTrue, caseUniLitFalse))

      val proof = lpProofScript(assumeVarsStep ++ stepWithLit2Eq :+ caseSplitUniLit)
      (proof, None)
    }

    // helpers
    private def encParaClauses(child: Clause, parentWithClause: ParentInfo, parentIntoClause: ParentInfo, info: AddInfoPara, sig: Signature):
    Either[String, EncParaCtx] = {

      // extract clauses and names
      val withClause = parentWithClause.clPr.cl
      val withClauseName = parentWithClause.lpName
      // The variable names in the into clause are consistent with the ones used in the child, the one in the parent may not be
      val intoClause = info.intoClause
      val intoClauseName = parentIntoClause.lpName

      // extract specific literals
      // check that the provided indices are in range
      val childIndexIntoLit = (withClause.lits.length - 1) + info.intoIndex

      def inRange(who: String, idx: Int, size: Int): Either[String, Unit] = if (0 <= idx && idx < size) Right(()) else Left(s"$who index $idx out of range (${size - 1})")

      val validation = for {
        _ <- inRange("withLit", info.withIndex, withClause.lits.length)
        _ <- inRange("intoLit", info.intoIndex, intoClause.lits.length)
        _ <- inRange("intoLit in child", childIndexIntoLit, child.lits.length)
        _ <- Either.cond(child.lits.nonEmpty, (), "child has no literals")}
      yield ()
      validation match {
        case Left(err) => return Left(err)
        case Right(_) => ()
      }
      val withLit = withClause.lits(info.withIndex)
      val intoLit = intoClause.lits(info.intoIndex)
      val intoLitChild = child.lits(childIndexIntoLit)
      val uniLit = child.lits.last

      // encodings
      val (bVarsMap, clauses) = lpClauseInst.apply_to_set(Seq(intoClause, withClause), sig)
      val encWithClause = clauses(1)
      val encIntoClause = clauses(0)
      val encWithLit = lpLiteral(encWithClause.lits(info.withIndex))
      val encOtherLitsWithClause = encWithClause.lits.patch(info.withIndex, Nil, 1)
      val encChildClause = lpClauseInst(child, sig)
      val encUniLit = encChildClause.lits.last
      val encPosUniLit = encUniLit match {
        case lpOlUnaryConnectiveTerm(`lpNot`, nonNegLit) => nonNegLit
        case _ => return Left(s"uni lit ${encUniLit.pretty} should be negated but is not")
      }
      // use fresh encoding rather than just pattern matching the encoded lits in order to avoid implicit lifitng via the
      // translation (this can falsify comparisons needed to detect literal flips later)
      val encIntoLitIntoClause = lpLiteral(intoClause.lits(info.intoIndex),bVarsMap,sig)
      val encIntoLitChild = lpLiteral(child.lits(childIndexIntoLit),bVarsMap,sig)

      // get the lengths
      val withClauseLen = withClause.lits.length
      val childLen = child.lits.length

      // instanciation of RW clause
      val instWithClause = lpFunctionApp(withClauseName, encWithClause.metaVars)
      val instIntoClause = lpFunctionApp(intoClauseName, encIntoClause.metaVars)

      val withClauseObject = ParaWithClause(withLit, encOtherLitsWithClause, encWithClause, encWithLit, withClauseName, instWithClause, info.withIndex, withClauseLen)
      val intoClauseObject = ParaIntoClause(intoLit, encIntoClause, encIntoLitIntoClause, intoClauseName, instIntoClause)
      val childClauseObject = ParaChildClause(uniLit, intoLitChild, encChildClause, encUniLit, encIntoLitChild, encPosUniLit, childIndexIntoLit, childLen)

      Out.lp_debug_info(s"Rewriting ${intoClauseObject.enc.lits(info.intoIndex).pretty} in ${intoClauseObject.enc.term.pretty}")
      Out.lp_debug_info(s"With ${withClauseObject.encWithLit.term.pretty} in ${withClauseObject.enc.term.pretty}")
      Out.lp_debug_info(s"Resulting in ${childClauseObject.enc.term.pretty} (with uni const ${childClauseObject.encUniLit.pretty})")

      Right(EncParaCtx(withClauseObject, intoClauseObject, childClauseObject, bVarsMap))
    }

    // implicit transformations

    private def withCl2eq(withCl: ParaWithClause): Either[String, (ParaWithClause, Seq[lpProofScriptStep])] = {

      if (withCl.withLit.equational) Right((withCl, Seq.empty))
      else {
        Out.lp_debug_info(s"withLit needs to be transformed to equational form ...")
        if (!withCl.withLit.polarity) Left("Error in Lambdapi encoding: trying to encode paramodulation with negative non-equational RW-lit")
        else {
          // Construct equational withLit and new clause
          //val encEqWithLit = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, withCl.encWithLit.term, lpOlTop)
          val encEqWithLit = lpLiteral(withCl.encWithLit.left, lpOlTop, lpOtype, true, true)
          val newEncWithLits = withCl.enc.lits.updated(withCl.withLitIdx, encEqWithLit.term)
          val newWithClause = lpClauseInst(lpOlUntypedBinaryConnectiveTerm_multi(lpOr, newEncWithLits), newEncWithLits, withCl.enc.vars)

          // Carry out transformation in a sub-step
          val nameHaveEqWithClause = "equationalWithClause"
          val withClausePattern = generateClausePatternTerm(Seq(withCl.withLitIdx), withCl.len)
          val rwWithLit2eq = lpRewrite(withClausePattern, lpSimp_eqTop.name)
          val refWithLit2Eq = lpRefine(withCl.currentRef)
          val haveEqRwLit = lpHave(nameHaveEqWithClause, newWithClause.term.prf, lpProofScript(Seq(rwWithLit2eq, refWithLit2Eq)))
          val commentStep = lpProofScriptCommentLine(s"Transform withLiteral to an equation")

          Out.lp_debug_info(s"Transformed to new withLit: ${encEqWithLit.term.pretty} (in subStep $nameHaveEqWithClause)")
          val updatedWithCl = ParaWithClause(withCl.withLit, withCl.otherLits, newWithClause, encEqWithLit, withCl.name, lpConstantTerm(nameHaveEqWithClause), withCl.withLitIdx, withCl.len)
          Right((updatedWithCl, Seq(commentStep, haveEqRwLit)))
        }
      }
    }

    private def transformIntoLit(ctxt: EncParaCtx): Seq[lpProofScriptStep] = {
      val childCl = ctxt.childC
      if (ctxt.intoC.intoLit.equational && !childCl.intoLit.equational) {
        Out.lp_debug_info(s"intoLit in child needs to be transformed to equational form ...")
        val expandPattern = generateClausePattern(Seq(childCl.intoLitIdx), childCl.len, childCl.intoLit.polarity)
        val expandStep = lpRewrite(Some(lpRewritePattern(expandPattern)), lpSimp_eqTop.name, true)
        val addComment = lpProofScriptCommentLine("Target literal needs expansion to equational form")

        Seq(addComment, expandStep)
      } else {
        Seq.empty
      }
    }

    private def flipIntoLit(ctxt: EncParaCtx, info: AddInfoPara): Seq[lpProofScriptStep] = {

      val writeIntoLhs = if (info.intoSide) true else false
      val intoLitInChildNeedsflip = if (writeIntoLhs) !alphaEquivalent(ctxt.intoC.encIntoLit.right, ctxt.childC.encIntoLit.right) else !alphaEquivalent(ctxt.intoC.encIntoLit.left, ctxt.childC.encIntoLit.left)
      if (intoLitInChildNeedsflip) {
        Out.lp_debug_info(s"intoLit in child needs to be flipped")
        val flipPattern = generateClausePattern(Seq(ctxt.childC.intoLitIdx), ctxt.childC.len, ctxt.childC.intoLit.polarity)
        val flipStep = lpRewrite(Some(lpRewritePattern(flipPattern)), flipLiteral.instanciate(ctxt.intoC.encIntoLit.tyLhs))
        Seq(lpProofScriptCommentLine("Target literal needs to be flipped"), flipStep)
      } else Seq.empty
    }

    // encode branches of the cases

    private def branchUniLitFalse(childCl: ParaChildClause) = {
      val nameUniLit = lpConstantTerm("uniLitInEq")
      val assumeUniLit = lpAssume(Seq(nameUniLit))
      val orIntro: lpTerm = if (childCl.enc.lits.length > 2) lpLorIntroMulti.instanciate(childCl.enc.lits.init, Seq(childCl.encUniLit), Seq.empty) else lpLorIntro2.name
      lpProofScript(Seq(assumeUniLit, lpRefine(lpFunctionApp(orIntro, Seq(nameUniLit)))))
    }

    private def branchUniLitTrue_prelim(ctxt: EncParaCtx, info: AddInfoPara, childIntoTermPattern: lpRewritePattern): (lpAssume, lpRewrite, lpFunctionApp) = {
      val EncParaCtx(withCl, intoCl, childCl, bVarsMap) = ctxt
      // assume the UC
      val nameUniConsT = lpConstantTerm("uniConsEq")
      val assumeUniConsT = lpAssume(Seq(nameUniConsT))

      // rewrite with uni lit
      val rewriteTarget = if (info.withSide) withCl.encWithLit.left else withCl.encWithLit.right
      val uniLitLhs = lpLiteral(childCl.encUniLit).left
      val flipUniLit = (!alphaEquivalent(rewriteTarget, uniLitLhs))
      if (flipUniLit) Out.lp_debug_info(s"Unification Constraint needs to be used in reversed (Lambdapi keyword left)!")
      val rewriteWithUniLit = lpRewrite(Some(childIntoTermPattern), nameUniConsT, flipUniLit)

      // regardless of the length of the withClause, we need to instanciate disjunction introduction to combine the intoClause literals and the uniLit
      val vIntro1_intoClause_uniLit = lpFunctionApp(lpLorIntroMulti.instanciate(Seq.empty,intoCl.enc.lits, Seq(childCl.encUniLit)), Seq(intoCl.currentRef))
      (assumeUniConsT, rewriteWithUniLit, vIntro1_intoClause_uniLit)
    }

    private def branchUniLitTrue_longerWithClause(ctxt: EncParaCtx, info: AddInfoPara, proofBricks: EncParaProofSteps): lpProofScript = {

      Out.lp_debug_info(s"The With clause is not unary")

      // extract the necessary proof snippets
      val EncParaProofSteps(transformIntoLitSteps, maybeFlipIntoLitStep, rewriteWithUniLit, childIntoTermPattern, vIntro1_intoClause_uniLit, assumeUniConsT) = proofBricks

      // case withLit
      val nameWithLit = lpConstantTerm("withLit")
      val assumeWithLit = lpAssume(Seq(nameWithLit))
      // like in the base case, we can not rewrite with the with-Lit
      val rewriteWithWithLit = lpRewrite(Some(childIntoTermPattern), nameWithLit, info.withSide)
      // use disjunction introduction to account for the other lits in the withClause
      val vIntroWithClause = lpLorIntroMulti.instanciate(ctxt.withC.otherLits, ctxt.intoC.enc.lits :+ ctxt.childC.encUniLit, Seq.empty)
      val refineStepCaseWithLit = lpRefine(lpFunctionApp(vIntroWithClause, Seq(vIntro1_intoClause_uniLit)))
      // combine all of these steps into one step
      val caseWithLit = lpProofScript((assumeWithLit +: transformIntoLitSteps) ++ maybeFlipIntoLitStep ++ Seq(lpProofScriptCommentLine("Rewrite parent with with-literal"), rewriteWithWithLit, lpProofScriptCommentLine("Rewrite parent with unification constraint"), rewriteWithUniLit, refineStepCaseWithLit))

      // case rest of with clause
      val nameWithClauseWithoutLit = lpConstantTerm("otherLitsWithClause")
      val assumeWithClauseWithoutLit = Seq(lpAssume(Seq(nameWithClauseWithoutLit)))
      // refine with disjunction introduction based on the literals
      val vIntro_withClauseWithoutLit = lpLorIntroMulti.instanciate(Seq.empty,ctxt.withC.otherLits, ctxt.childC.enc.lits.drop(ctxt.withC.otherLits.length))
      val refineStepCaseWithClauseWithoutLit = lpRefine(lpFunctionApp(vIntro_withClauseWithoutLit, Seq(nameWithClauseWithoutLit)))
      val caseWithClauseWithoutLit = lpProofScript(assumeWithClauseWithoutLit :+ refineStepCaseWithClauseWithoutLit)

      // combining the branches
      val caseSplitWithClause = lpFunctionApp(lpLorElimMulti.instanciate(info.withIndex, ctxt.withC.enc.lits, None), Seq(ctxt.withC.currentRef, lpWildcard, lpWildcard))
      val proofCaseSplitWithClause = lpRefine(caseSplitWithClause, Seq(caseWithLit, caseWithClauseWithoutLit))
      lpProofScript(Seq(assumeUniConsT) ++ Seq(proofCaseSplitWithClause))
    }

    def branchUniLitTrue_unaryWithClause(ctxt: EncParaCtx, info: AddInfoPara, proofBricks: EncParaProofSteps): lpProofScript = {

      Out.lp_debug_info(s"The With clause is unary")

      val refineStep = lpRefine(proofBricks.vIntro1_intoClause_uniLit)
      // We can directly rewrite with the instantiated RW clause
      val rewriteWithWithClause = lpRewrite(Some(proofBricks.childIntoTermPattern), ctxt.withC.currentRef, info.withSide)
      lpProofScript(Seq(proofBricks.assumeUniConsT) ++ proofBricks.transformIntoLitSteps ++ proofBricks.maybeFlipIntoLitStep ++ Seq(lpProofScriptCommentLine("Rewrite parent with with-literal"), rewriteWithWithClause, lpProofScriptCommentLine("Rewrite parent with unification constraint"), proofBricks.rewriteWithUniLit, refineStep))
    }

    // misc

    def generateParaIntoSubTermPattern(ctxt: EncParaCtx, info: AddInfoPara, sig: Signature): Either[String, lpRewritePattern] = {
      val intoCl = ctxt.intoC

      // extract the meta-information about the intoLit needed to generate the pattern
      // todo: maybe use the lpLit encoding of intoLit instead?
      val (intoLitSide, intoLitLhsTy) = if (intoCl.intoLit.equational) {
        val encType = ctxt.intoC.encIntoLit.tyLhs
        (Some(info.intoSide), encType)
      } else (None, lpOtype)
      val intoLitSideTerm = if (info.intoSide) intoCl.intoLit.left else intoCl.intoLit.right
      // construct the pattern for the subterm we are rewriting
      val (encPattern, _, cantEncodeRwPattern) = leoPosition2LpPattern(intoLitSideTerm, info.intoPosition, sig)
      cantEncodeRwPattern match {
        case Some(error) =>
          Out.lp_debug_info(s"unable to encode rewrite pattern as it attempts to rewrite under binder")
          Left(error)
        case None =>
          val childIntoTermPattern = generateWrapperPattern(ctxt.childC.intoLitIdx, ctxt.childC.len, intoCl.intoLit.polarity, intoLitSide, Some(intoLitLhsTy), encPattern)
          Out.lp_debug_info(s"Pattern of targeted sub-term of intoLit in child: ${childIntoTermPattern.pretty}")
          Right(lpRewritePattern(childIntoTermPattern))
      }
    }
  }


  def encEqFactLiterals(otherLit: Literal, maxLit: Literal, uc1Orig: Literal, uc2Orig: Literal, parent: Clause, child: Clause, bVarMap: Map[Int, String], sourceBefore: lpTerm, nameStep: lpOlTerm, sig: Signature): (lpProofScriptStep, Boolean) = {
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
      lastStepName = lpConstantTerm(permStepName)
      Out.lp_debug_info(s"permutation applied")
      currentLits = permutedLits
    }

    var allTransformSteps : Seq[lpProofScriptStep] = Seq.empty

    val otherLitBeforeEqFact : (lpOlTerm, lpOlTerm, lpOlTerm) = {
      if (!otherLit.equational){
        val transformOtherLit0 = equationalForm(otherLitEnc,polarityOfRule)
        val (newSteps, newCanEncode) = transformLiteral(transformOtherLit0._1,otherLitEnc,permutaion(posOtherLit),lenParent)
        allTransformSteps =  allTransformSteps ++ newSteps
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
            Out.lp_debug_info(s"flipped other literal to ${flippedOtherLit.pretty}")
            (flippedOtherLit,otherLit_r0,otherLit_l0)
          } else (otherLitEnc,otherLit_l0,otherLit_r0)
        }
      }
    }
    val maxLitBeforeEqFact = {
      if (!maxLit.equational) {
        val transformMaxLit0 = equationalForm(maxLitEnc, polarityOfRule)
        val (newSteps, newCanEncode) = transformLiteral(transformMaxLit0._1,maxLitEnc, permutaion(posMaxLit), lenParent)
        allTransformSteps = allTransformSteps ++ newSteps
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
    val nameEqFactoringStep = lpConstantTerm("EqFact")
    val eqFactStep = lpProofScript(Seq(lpRefine(lpFunctionApp(encEqFact, Seq(lastStepName)))))
    allSteps = allSteps :+ lpHave(nameEqFactoringStep.name, afterEqFacAp, eqFactStep)
    Out.lp_debug_info(s"generated equal factoring step:\n${eqFactStep.pretty}")
    lastStepName = nameEqFactoringStep

    // if we need more transformations, carry them out
    var allBackTransformSteps : Seq[lpProofScriptStep] = Seq.empty
    Out.lp_debug_info(s"derived other lit = ${otherLitBeforeEqFact._1.pretty}, found other lit = ${childOtherLitEnc.pretty}")
    if (otherLitBeforeEqFact._1 != childOtherLitEnc){
      val (newSteps, newCanEncode) = transformLiteral(childOtherLitEnc,otherLitBeforeEqFact._1,0,currentLits.length)
      allBackTransformSteps = allBackTransformSteps ++ newSteps
      currentLits = currentLits.updated(0,childOtherLitEnc)
      if (!newCanEncode) {
        canEncode = false
        Out.lp_debug_info(s"unable to do back transformation for other lit")
      }
      Out.lp_debug_info(s"transformed other literal to ${childOtherLitEnc.pretty}")
    }
    if (currentLits(1) != childUc1Enc){
      val (newSteps, newCanEncode) = transformLiteral(childUc1Enc, currentLits(1), 1, currentLits.length)
      allBackTransformSteps = allBackTransformSteps ++ newSteps
      currentLits = currentLits.updated(1,childUc1Enc)
      if (!newCanEncode) {
        canEncode = false
        Out.lp_debug_info(s"unable to do back transformation for UC1")
      }
      Out.lp_debug_info(s"transformed UC1 to ${childUc1Enc.pretty}")
    }
    if (currentLits(2) != childUc2Enc) {
      val (newSteps, newCanEncode) = transformLiteral(childUc2Enc, currentLits(2), 2, currentLits.length)
      allBackTransformSteps = allBackTransformSteps ++ newSteps
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

    (completeHaveStep, canEncode)

  }

  def encEqFact_proofScript(child: ClauseProxy, parent: ClauseProxy, additionalInfo: (Literal, Literal, Literal, Literal, Boolean, Boolean), parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Option[String]) = {

    val bVarMap = clauseVars2LP(child.cl.implicitlyBound, sig, Set.empty)._2

    var allSteps: Seq[lpProofScriptStep] = Seq.empty

    val (otherLit, maxLit, ur1, ur2, wasUnified, wasSimplified) = additionalInfo
    if (wasUnified) {
      //throw new Exception(s"The LP encoding of EqFact including type unification is not implemented yet")
      (lpProofScript(Seq(lpProofScriptAdmit())), Some("The LP encoding of EqFact including type unification is not implemented yet"))
    } else if (wasSimplified) {
      //throw new Exception(s"The LP encoding of EqFact including simplification is not implemented yet")
      (lpProofScript(Seq(lpProofScriptAdmit())), Some("The LP encoding of EqFact including simplification is not implemented yet"))
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
        val (encFactoring, canEncode) = encEqFactLiterals(otherLit, maxLit, ur1, ur2, parent.cl, child.cl, bVarMap, lastStep, factStepName, sig)
        allSteps = allSteps :+ encFactoring
        lastStep = factStepName
        // 6. Refine with the last proven step
        allSteps = allSteps :+ lpRefine(lpFunctionApp(lastStep, Seq(lpFunctionApp(parentNameLpEnc, applySymbolsToParent))))
        val wholeProof = lpProofScript(allSteps)

        if (canEncode) (wholeProof, None)
        else (lpProofScript(Seq(lpProofScriptAdmit())), Some("The LP encoding of EqFact requires some unencoded transformation"))
      } else {
        (lpProofScript(Seq(lpProofScriptAdmit())), Some("The LP encoding of EqFact is not implemented for the application to clauses of length more than two yet"))
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

  def inferImplicitTransformationsSimp(parentLits: Seq[Literal], ChildLits: Seq[Literal], childLen: Int, bVarMap: Map[Int, String], ignoreIndices: Seq[Int], sig: Signature): (Seq[Literal], Seq[Int], Seq[lpProofScriptStep]) = {

    // Applies simplification to the given literals and then applies the operations carried out by Leo-III that can potentialy lead to the literal
    // being flipped or transformed in any other way. Then forms a new sequence omitting any literals that reduce to F or have already been
    // derived and - in the process - keeps track of this information in order to apply the necessary implicit transformations

    var simpLits = Seq.empty[Literal]
    var doubleLiterals = Seq.empty[Int]
    var implicitRwTransf = Seq.empty[lpProofScriptStep]

    // Helper function that updates doubleLiterals and simpLits if the literal is not false.
    def addLiteral(lit: Literal): Unit = {
      if (!Literal.isFalse(lit)) {
        val idx = if (simpLits.contains(lit)) {
          val idx0 = simpLits.indexOf(lit)
          needsTransformation(simpLits(idx0),lit)
          idx0
        } else doubleLiterals.distinct.length
        doubleLiterals = doubleLiterals :+ idx
        if (!simpLits.contains(lit)) simpLits = simpLits :+ lit
      }
    }

    def addIgnoredLiteral(lit: Literal): Unit = {
        val idx = doubleLiterals.distinct.length
        doubleLiterals = doubleLiterals :+ idx
        simpLits = simpLits :+ lit
    }

    def needsTransformation(lit0: Literal, lit1: Literal): Unit = {
      // There are two scenarios that can necessitate us to apply additinal implicit transfomrations to a literal:
      // 1. If the flipped version of the literal is already in the list of simplified literals. Then Leo-III will identify them and delete one occurance
      //    -> We produce a proof of the non simplified clause implying the simplified one with the literal already flipped. That way we need only to
      //       apply the rewrite step flipping the literal within the substep proving the implication
      // 2. The actual term ordering flips the literal before adding it to the new clause.
      //    -> We need to flip the literal in the
      if (lit0.pretty != lit1.pretty){
        val encOrigLit = lpLiteral(lit0, bVarMap, sig)
        val encDesiredLit = lpLiteral(lit1, bVarMap, sig)
        Out.lp_debug_info(s"needs Transformation for simplification: from ${encOrigLit.term.pretty} to ${encDesiredLit.term.pretty}")
        val impPattern: lpOlTerm => lpOlTerm = x => lpOlUntypedBinaryConnectiveTerm(lpImp, lpOlWildcard, x)
        val (transformSteps, canEncode) = transformLiteral(encDesiredLit.term, encOrigLit.term, simpLits.length, parentLits.length, Some(impPattern))
        if (!canEncode) throw new Exception(s"LP-Encoding SIMP: could not transform ${encOrigLit.term.pretty} to ${encDesiredLit.term.pretty}")
        implicitRwTransf = implicitRwTransf ++ transformSteps
      }
    }

    // Process each literal from the parent.
    val litIndex = parentLits.zipWithIndex
    litIndex.foreach {pair =>
      val (parentLit, litIdx) = pair
      if (ignoreIndices.contains(litIdx)){
        addIgnoredLiteral(parentLit)
      }else {
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
            //val maybeOrderedLit = PolaritySwitch(Literal.mkOrdered(normLeft, normRight, parentLit.polarity)(sig))
            val unorderedLit = PolaritySwitch(Literal.mkLit(normLeft, normRight, parentLit.polarity, parentLit.oriented))
            // Update doubleLiterals for the unordered literal.
            //doubleLiterals = doubleLiterals :+ (
            //  if (simpLits.contains(unorderedLit)) simpLits.indexOf(unorderedLit)
            //  else doubleLiterals.distinct.length
            //  )
            addLiteral(unorderedLit)
            /*
            if (!Literal.isFalse(unorderedLit) && (maybeOrderedLit.left != unorderedLit.left)) {
              val encOrigLit = lpLiteral(maybeOrderedLit, bVarMap, sig)
              val encDesiredLit = lpLiteral(unorderedLit, bVarMap, sig)
              needsTransformation(unorderedLit,maybeOrderedLit)
              addLiteral(maybeOrderedLit)
              //throw new Exception(s"Required implicit transformation in SIMP encoding from ${encOrigLit.term.pretty} to ${encDesiredLit.term.pretty}!")
              // should be possible to use needsTransformation from above
            } else addLiteral(unorderedLit)

             */
          }
        }
      }
    }

    assert(simpLits.length == childLen, s"LP-Encoding: Lengths of derived and given simplifications differ. Derived clause: ${simpLits.length} literals, given Clause: ${childLen} literals. Derived lits: ")
    // If no literals were added, default to false.
    if (simpLits.isEmpty) {
      simpLits = if (ChildLits.isEmpty) Seq(Literal(LitFalse(), true)) else ChildLits
    }
    if (doubleLiterals.isEmpty)
      doubleLiterals = Seq(0)

    (simpLits, doubleLiterals, implicitRwTransf)
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

  def lpEqHaveStepConstructor(stepName: String, quantifiedVars: Seq[lpTypedVar], termLhs: lpOlTerm, termRhs: lpOlTerm, ty: lpOlType, proofScriptSteps: Seq[lpProofScriptStep]): lpHave = {
    // Function constructing subproofs for one clause implying another using the have-tactic with potential...
    // - Abstraction over variables

    val eqToProve = lpOlTypedBinaryConnectiveTerm(lpEq, ty, termLhs, termRhs)
    // Quantify over variables if necessary
    val (maybeQuanrifiedImpToProve, fullProofScript) =
      if (quantifiedVars.isEmpty) (eqToProve.prf, lpProofScript(proofScriptSteps))
      else (lpMlDependType(quantifiedVars, eqToProve.prf), lpProofScript(Seq(lpAssume(quantifiedVars)) ++ proofScriptSteps))
    // Complete substep using have-tactic
    val haveSimpAppStep = lpHave(stepName, maybeQuanrifiedImpToProve, fullProofScript)
    haveSimpAppStep
  }

  def encSimpProofSubstep(disappearingVars: Seq[lpTypedVar], termBefore: lpOlTerm, termAfter: lpOlTerm, addSteps: Seq[lpProofScriptStep] = Seq())={
    // Step applying all of the RW-rules encoding the simplifications
    val simpAppStepName = "SimpApp"
    val haveSimpAppStep = lpImpHaveStepConstructor(simpAppStepName, disappearingVars, termBefore, termAfter, addSteps ++ Seq(allSimpRuleApplicationStep))
    Out.lp_debug_info("Substep applying the boolean identities generated")

    (haveSimpAppStep, simpAppStepName)
  }

  /** Carry out the construction of a proof script for applications of (SIMP)*/
  def encSimpProofScript(pLits: Seq[Literal], cLits: Seq[Literal], encParent: lpClauseInst, encChild: lpClauseInst, childLen: Int, bVarMap: Map[Int, String], parentNameLpEnc: lpTerm, ignoreIndices: Seq[Int], sig:Signature):Seq[lpProofScriptStep]= {


    // Identify any implicit transformations that may need to be encoded
    val (simpLits, doubleLiterals, implicitRwTransf) = inferImplicitTransformationsSimp(pLits, cLits, childLen, bVarMap, ignoreIndices, sig)
    val encSimpLits = simpLits.map(simpLit => lpLiteral(simpLit, bVarMap, sig).term)
    Out.lp_debug_info(s"simplified literals: ${encSimpLits.map(_.pretty)}")

    // Identify the variables remaining after simplification and assume them
    val remainingVars = simpLits.flatMap(_.fv).distinct.sortBy(_._1).reverse
    val encRemainingVars = var2Lp(remainingVars, bVarMap, sig).map(_.asMlVar)
    val assumeStep : Seq[lpProofScriptStep] = if (encRemainingVars.nonEmpty) Seq(lpAssume(encRemainingVars)) else Seq()

    /////////////////////////////////////////////////////
    //// 2. Instantiate a subproof (SimpApp) using have to proof that the parent implies the child
    ////    by applying all of the simplification rules to the parent

    // If we need to account for the deletion of double literals, we include the duplicates in the implication we construct
    //    and remove them in an additional step
    val clauseToProve = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, doubleLiterals.map(indx => encSimpLits(indx)))
    // Identify any variables that were implicitly quantified in the parent but not in the child
    val disappearingVars = encParent.metaVars.diff(encRemainingVars)
    Out.lp_debug_info(s"Vars in parent: ${encParent.metaVars.map(_.pretty)}, Vars after Simp: ${encRemainingVars.map(_.pretty)} => Disappearing implicitly quantified variables: ${disappearingVars.map(_.pretty)}")

    val (haveSimpAppStep, simpAppStepName) = encSimpProofSubstep(disappearingVars, encParent.term, clauseToProve, implicitRwTransf)



    /////////////////////////////////////////////////////
    //// 3. Apply Implicit transformations: Deletion of double literals, eqSym and permutation

    val witnessTermsToApply = disappearingVars.map(var0 => lpWitness.fromAnyType(var0.ty))
    val allTermsToApplyToParent = encParent.metaVars.map(var0 => if (disappearingVars.contains(var0)) lpWitness.fromAnyType(var0.ty) else var0)
    val appliedSimpAppStepName = lpFunctionApp.toDefName(simpAppStepName, witnessTermsToApply)
    val simpStepName = lpFunctionApp(appliedSimpAppStepName, Seq(lpFunctionApp(parentNameLpEnc, allTermsToApplyToParent)))
    val maybePermStepName: lpFunctionApp = if (doubleLiterals != doubleLiterals.indices) {
      // Application of delete literal is necessary
      // todo: exclude cases where the rewrite rule applied by LP would also handle it. (should only happen if the relevant literals are at the two most left ones right?)
      Out.lp_debug_info(s"need to prove ${doubleLiterals.map(indx => encChild.lits(indx).pretty)}")
      val instMetaDelTheorem = metaDeletion.instanciate(encChild.lits, doubleLiterals, simpStepName)
      instMetaDelTheorem
    } else simpStepName


    /////////////////////////////////////////////////////
    //// 4. Refine with the parent applied to SimpApp

    val refineStep = lpRefine(maybePermStepName)
    val allSteps: Seq[lpProofScriptStep] = assumeStep ++ (Seq(haveSimpAppStep)) :+ refineStep

    allSteps}

  def newSimpEncoding(child: Clause, parent: Clause, parentNameLpEnc: lpConstantTerm, sig: Signature, ignoreIndices: Seq[Int] = Seq()):Seq[lpProofScriptStep]={

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

    assert((ignoreIndices.isEmpty || ignoreIndices.max <= parent.lits.length),"Error in Lambdapi encoding: Indices to ignore in Simplification out of bounds")

    val (encChild,encParent0,bVarMap,_) = lpEncodingPrelim(child,Seq(parent),parent.implicitlyBound,sig)
    assert(encParent0.length == 1)
    val encParent = encParent0.head
    Out.lp_debug_info(s"Encoding simplification of ${encParent.term.pretty} to ${encChild.term.pretty}")

    /////////////////////////////////////////////////////
    //// 2 - 4
    val allSteps0 = encSimpProofScript(parent.lits, child.lits, encParent, encChild, child.lits.length, bVarMap, parentNameLpEnc, ignoreIndices, sig)

    allSteps0
  }

  def encLiftEq(cl: ClauseProxy, parents: Seq[ClauseProxy], addInfo: Seq[Seq[Int]], parentNameLpEnc: Seq[lpConstantTerm], sig: Signature):(lpProofScript,Option[String]) = {

    // encode the lift of equality literals
    // ((x = y) = T)^a to (x = y)^a
    // ((x ≠ y) = T)^tt to (x = y)^ff
    // ((x ≠ y) = T)^ff to (x = y)^tt

    // the complete proof script consists of 3 steps:
    // 1. Assume free variables
    // 2. For each of the literals in the original caluse:
    //    a) in case of negative equality lift, a rewrite tactic has to be applied
    //    b) for the new equality literlas, the order within the equality may have changed, if so: apply rewrite tactic
    // 3. If the order of literals has changed, apply meta theorem and refine with instantiated meta-theorem
    //    Else refine with the last step

    assert(parents.length == 1, "trying to encode lift equaltiy step with more than one parent")

    // Extract information about what literals were edited in which way
    // And in which order they will occur in the resulting clause
    if (addInfo.isEmpty) {
      Out.lp_debug_info(s"no additional inforamtion provided, can not encode") //todo: would be better to infer atuomtically anyays
      (lpProofScript(Seq.empty), Some("missing the additional information for the encoding"))
    } else {


      val litsPosLift = addInfo(0)
      val litsNegLift = addInfo(1)
      val litsOld = addInfo(2)
      val edIndices = litsPosLift ++ litsNegLift
      val indices = (edIndices ++ litsOld).sorted
      val permutation = litsPosLift ++ litsNegLift ++ litsOld

      Out.lp_debug_info(s"edited literals at indices ${edIndices.mkString(", ")}, unchanged literals: ${litsOld.mkString(", ")}")

      var allSteps: Seq[lpProofScriptStep] = Seq.empty
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
            val (transformationSteps, canEncode0) = transformLiteral(encCorrespondingLit,finalLit,permutation.indexOf(indx), indices.length)
            if (canEncode0){
              allSteps = allSteps ++ transformationSteps
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
            allSteps = allSteps :+ lpRewrite(rwPattern, flipLiteral.instanciate(encRhs, encLhs, None))
            finalLit = flipLiteral.res(litPol, encType.lift2Poly, encRhs, encLhs)
            usedRules = usedRules + flipLiteral
          }
           */
          liftedLits = liftedLits :+ finalLit
        } else {
          val lit = parents.head.cl.lits(indx)
          val encLit = term2LP(asTerm(lit), bVars, sig)._1
          liftedLits = liftedLits :+ encLit
        }
      }

      // 3. If the order of literals has changed, apply meta theorem and refine with instantiated meta-theorem
      //    Else refine with the last step
      val needsPermute = permutation != permutation.sorted
      if (needsPermute) {
        Out.lp_debug_info(s"applying the following permutation: $permutation")
        allSteps = allSteps :+ lpRefine(metaPermutation.instanciate(permutation, liftedLits, lastStep))
        // permutation will not need to be added to the rules assuming that we will add it to stdlib
      } else {
        allSteps = allSteps :+ lpRefine(lpFunctionApp(lastStep, Seq()))
      }

      val finishedProof = lpProofScript(allSteps)

      (finishedProof, canEncode)
    }
  }


  def encRewrite(cl: ClauseProxy, parents: Seq[ClauseProxy], addInfoSimp: Seq[(Seq[Int], Int)], parentModoluRw: Option[Clause], parentNameLpEnc: Seq[lpConstantTerm], sig: Signature):(lpProofScript,Option[String]) = {

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
          val haveTransformStep = if (rwPol) {
            val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTop, rwLhs)
            val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, lpSimp_topEq.name), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
            haveTransformStep0
          } else {
            rwRhs = lpOlBot
            val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlBot, rwLhs)
            val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, lpSimp_botEq.name), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
            haveTransformStep0
          }
          Out.lp_debug_info(s"Transforming rewrite rule to equality...")
          //  2 b) Refine with the rewrite-clause and - if a substitution was applied - instanciate it accordingly todo: sbustitution
          allSteps = allSteps :+ haveTransformStep
          sourceBeforeEq = lpConstantTerm(transformationStepName)
        } else if (rewriteEq.polarity) {
          //2 a) case II) If the rewrite-clause is an equational single literal, use eqSym_eq to prove the reverse rewrite rule
          val transformationStepName = s"flip_equality_$eqFlipCounter"
          eqFlipCounter = eqFlipCounter + 1
          val transformedRewriteEq = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, rwRhs, rwLhs)
          Out.lp_debug_info(s"transforming rewirte clause to ${transformedRewriteEq.pretty}")
          val haveTransformStep0 = lpHave(transformationStepName, transformedRewriteEq.prf, lpProofScript(Seq(lpRewrite(None, lpFunctionApp(flipLiteral.name, Seq.empty, Seq(rwType))), lpRefine(lpFunctionApp(sourceBeforeEq, Seq())))))
          val haveTransformStep = haveTransformStep0
          //  2 b) Refine with the rewrite-clause and - if a substitution was applied - instanciate it accordingly todo: sbustitution
          allSteps = allSteps :+ haveTransformStep
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
          val (additionalSteps, canEncode) = transformLiteral(encLitChild, rewrittenLit, litCount, clauseLen) // todo: acutally, rewerite pattern should be ootional since we do not want it for clauses of length one
          if (canEncode) Out.lp_debug_info(s"proposed Steps: \n${additionalSteps.map(_.pretty).mkString("\n")}")
          else {
            Out.lp_debug_info(s"unable to encode the transformation of ${encLitChild.pretty} to ${rewrittenLit.pretty}}")
            allTransformationsEncoded = false
          }
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

    if (allTransformationsEncoded) (finishedProof, None)
    else (finishedProof, Some("RW: Non-ground rewrite step or missing transformation"))
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
          subsMap.getOrElse(name.name, t)
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
        case lpOlFunctionApp(f, args, _) =>
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

  def removeUnificationConstraint(uniC: Literal, parent: Clause, lastLit0: lpOlTerm, sig: Signature): (Seq[lpProofScriptStep])={
    // prove that unification literal can be removed from a clause when they either have the form ¬⊤ or x≠x (modulo unification)

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

    // proof the first transformation depending on the form of the unification constraint
    val rewritePattern_step1 = generateClausePatternTerm(Seq(position), parent.lits.length, None, patternVar)
    if (uniC.equational){
      if (!uniC.polarity){
        // in this case, we need to first show that both sides are equal modulo simplification and then apply a Simp Rule that postulates that x≠x = ⊥
        // the rewrite rule used here needs to explicitly instanciate the used type, therefore we first need to find that type out:
        var ty = type2LP(uniC.left.ty, sig)
        val lastLit = lastLit0 match {
          case lpOlUnaryConnectiveTerm(`lpNot`,lpOlTypedBinaryConnectiveTerm(lpEq, ty0, lhs, _)) =>
            ty = ty0
            lhs
          case _ =>
            throw new Exception("attempting to instanciate Simp10 inappropriateley")
        }
        val rewriteStep_step1 = lpRewrite(rewritePattern_step1, lpFunctionApp(SimplificationEncoding.lpSimp_negEq_idem.name,Seq(ty, lastLit)),true)
        rewriteSteps = rewriteSteps :+ rewriteStep_step1
      } else throw new Exception(s"Equational positive unification constratint passed on to lambdapi post eqFact encoding?")
    }else{
      // in this case simply we need to prove that 1. ¬⊤ = ⊥
      if (!uniC.polarity){
        val rewriteStep_step1 = lpRewrite(rewritePattern_step1, SimplificationEncoding.lpSimp_negTop.name,true)
        rewriteSteps = rewriteSteps :+ rewriteStep_step1
      }else{
        throw new Exception(s"Error: unification constraint passed to LP encoding is non equational and positive")
      }
    }

    rewriteSteps
  }

  def encPreUni(cl: ClauseProxy, parent: ClauseProxy, addInfoUni: AddInfoUni, addInfoUniRule: (String, (Literal, Literal)), parentNameLpEnc: lpConstantTerm, sig: Signature): (lpProofScript, Option[String]) = {
    // encode different versions of unification (after rule applications, ...)

    val bVars = clauseVars2LP(parent.cl.implicitlyBound, sig, Set.empty)._2

    val encModes = Seq("uniAfterFactoring")

    val mode = addInfoUniRule._1

    var canEncode = true

    if (encModes.contains(mode)) {
      Out.lp_debug_info(s"verification of $mode")
      var allSteps: Seq[lpProofScriptStep] = Seq.empty

      // Abstract over the free variables
      val (unboundVarsChild0, encChild, _) = clause2LP_unquantified(cl.cl, Set.empty, sig)
      val (unboundVarsParent, _, _) = clause2LP_unquantified(parent.cl, Set.empty, sig)
      var encChildLiterals = encChild.args
      val unboundVarsChild = liftVarsToMeta(unboundVarsChild0)
      allSteps = if (unboundVarsChild.nonEmpty) allSteps :+ lpAssume(unboundVarsChild) else allSteps

      val (_, encParent, _) = clause2LP_unquantified(parent.cl, Set.empty, sig)
      val encParentLiterals = encParent.args

      // Encode the actual unification and possibly the following simplification
      val typeUnification = addInfoUni.subst.typeSubsts
      val termUnification = addInfoUni.subst.termSubsts

      if (termUnification.length != unboundVarsParent.length) {
        //throw new Exception(s"trying to encode the unification that does not bind all free variables, this is implemented but untested, make sure this is done correctly") //todo
        Out.lp_debug_info(s"unification that does not bind all free variables not yet encoded")
        (lpProofScript(Seq.empty),Some("unification that does not bind all free variables not yet encoded"))
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
            val lpUnboundVar = varmap.apply(termUni.sourceIndex)
            // Term unifications can either be bindings of variables by terms or by variables...
            // Depending on that, the second element of the tuple is either a term or a String
            termUni.rhs match {
              case UniTermByBoundVar(targetIndex) =>
                canEncode = false
              case UniTermByTerm(term, _, varmap) =>
                val encBindTerm = term2LP(term, varmap, sig)._1 //todo: dont i need the offset? was it an oversight not to use it in term2lp?
                subsMap += (lpUnboundVar -> encBindTerm)
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
                val removeUniC1_0 = removeUnificationConstraint(uniC1, parent.cl, encSubstLits.last, sig)
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
                val removeUniC2_0 = removeUnificationConstraint(uniC2, Clause(parent.cl.lits.init), encSubstLits.init.last, sig)
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

              Out.lp_debug_info(s"Permutation step: ${permutationStep.pretty}")
              allSteps = allSteps :+ lpRefine(permutationStep)
            }

            // if necessary, we apply transformations to flip sides of literals etc.

            val proofScript = lpProofScript(allSteps)
            if (canEncode) (proofScript, None)
            else (lpProofScript(Seq.empty), Option(s"permutation necessary for the encodng")) // (See problem lpProof_SYO885^1_033_003)
          } else (lpProofScript(Seq.empty), Option(s"instanciation with variables not encoded yet"))
        } else (lpProofScript(Seq.empty), Option(s"no term unifications to encode"))
      }
    }
    else{
      (lpProofScript(Seq.empty),  Option(s"the unification mode $mode is either not set or not encoded yet..."))
    }
  }

  }
