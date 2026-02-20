package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Clause.{effectivelyEmpty, vars}
import leo.datastructures.Type.{ComposedType, ProductType, ∀}
import leo.datastructures._
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.ImplicitTransformationUtil.{LiteralInfo2LiteralTransforamtion, verifySubstitutionLiteralNormalisazion}
import leo.modules.output.LPoutput.LpLibs.EqRules.AsTerms._
import leo.modules.output.LPoutput.LpLibs.FunRules.AsTerms.{DecompSingleResult, DecompStepRes, mkDecompSingleObj, mkDecompStepObj}
import leo.modules.output.LPoutput.LpLibs.LeoTactics.EvalApp.removeBot
import leo.modules.output.LPoutput.LpLibs.MetaTheorems.Inst.{deleteBots, transform_n}
import leo.modules.output.LPoutput.LpLibs.ND.Terms._
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.Arguments.extractTermArgs
import leo.modules.output.LPoutput.NewLpDatastructures.ClauseEncoding.lit2Lp
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript._
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Obj, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.Prf
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures._

object Util {
  private def assumeVars(encChild: lpClauseInst): Seq[Name] = {
    encChild.vars.map {
      case Left(olVar) => olVar.name
      case Right(_) => throw new Exception(s"Error in Lambdapi Encoding: Encountered unexpected TyVar, Poymorphism not yet encoded")
    }
  }

  def encPatternUniAssume(encChild: lpClauseInst): (Seq[LpProofScript], Seq[Name]) = {
    if (encChild.vars.nonEmpty) {
      val varNames = assumeVars(encChild)
      (Seq(Assume(varNames)), varNames)
    } else (Seq.empty, Seq.empty)
  }

  final case class EncUniCtx(encChild: lpClauseInst, encParent: lpClauseInst, sharedVarMap: Map[Int, String], childVarMap: Map[Int, String], parentNameLpEnc: LpTerm[Level.Obj], substClauseLen: Int)

  def initCtxt(childCl: Clause, parentCl: Clause, parentNameLpEnc0: Name): EncUniCtx = {

    //todo: do any checks here?

    // translation of the clauses
    val (sharedVarMap, encClauses) = lpClauseInst.apply_to_set(Seq(childCl, parentCl))

    // compute names and clause length
    val parentNameLpEnc: LpTerm[Level.Obj] = Const(SymRef.LP(QName.local(parentNameLpEnc0.value)))
    val substClauseLen = parentCl.lits.length

    // filter out only the vars relevant to the child
    val childVarMap = sharedVarMap.view.filterKeys(vars(childCl).distinct).toMap

    EncUniCtx(encClauses.head, encClauses(1), sharedVarMap, childVarMap, parentNameLpEnc, substClauseLen)
  }

}

object UnificationEncoding {

  import Util._

  /**
    * encode PatternUni — Outline of the encoded proof (pattern unification)
    *
    * Intuition:
    * Pattern unification produces (i) a substitution (term/type) and (ii) a set of
    * unification-constraint literals that become trivially false after applying the substitution.
    * The child clause is obtained from the parent by applying the substitution (if any)
    * and then deleting those trivially-false constraint literals.
    *
    * Notation:
    *   - parent / child: the Leo clauses before / after the inference.
    *   - implicitlyBound: list of free variables represented as de Bruijn indices.
    *   - termSubst / typeSubst: substitutions produced by unification.
    *   - deletedUniLits: indices of unification-constraint literals removed in the child.
    *   - litTransf: bookkeeping for literal normalization (e.g. flipping equalities).
    *
    * Steps:
    * 0) Assume all free variables of the child clause.
    *
    * 1) Substitution subproof (optional):
    * If unification produced a non-empty term substitution:
    *      - Instantiate the encoded parent clause by applying the substitution
    *        arguments to its free variables.
    *      - If some literals must be normalized before substitution
    *        (e.g. equality orientation differs), insert rewrite steps using eqsym
    *        to justify the normalization.
    *        Otherwise:
    *      - Use the encoded parent instantiated with the child’s variables directly.
    *
    * 2) Constraint-elimination subproof:
    * The unification constraints are trivially false after substitution.
    * Show that the (substituted) parent implies the child by:
    * (i)   Turning each deleted unification literal into ⊥
    * using a dedicated tactic.
    * (ii)  Removing these ⊥-literals with deleteBots (or an equivalent theorem),
    * yielding exactly the child clause.
    *
    * 3) Composition in final refine step:
    * Combine the substitution subproof (or the original parent, if no substitution
    * was applied) with the constraint-elimination subproof via eqImp to obtain
    * a proof of the child clause from the parent.
    *
    * Limitations / Notes:
    *   - Type unification is currently not encoded
    *   - If deletedUniLits is empty or inconsistent, we currently throw; this should ideally
    *     be a structured “can’t encode” result.
    *
    * @return (proof script, optional error message)
    */
  def encodePatternUni(parent: ClauseProxy, child: ClauseProxy, parentNameLpEnc0: Name, sig: LpSig): EncodeResult = {
    Out.lp_debug_info(s"Encoding instance of Pattern Unification")
    //todo only do substitution step if we actually have subst, sometimes we can also have trivial stuff
    val ro = RenderOptions()

    ////////////////////////////
    // Encodings and prelim

    // encoding of parents, generation of var maps etc.
    val ctxt = initCtxt(child.cl, parent.cl, parentNameLpEnc0)
    val EncUniCtx(encChild, encParent, sharedVarMap, childVarMap, parentNameLpEnc, substClauseLen) = ctxt
    Out.lp_debug_info(s"proving ${Renderer.ty(encChild.asMl, ro, sig)}")
    Out.lp_debug_info(s"parent: ${Renderer.ty(encParent.asMl, ro, sig)}")

    // encoding of additional information regarding the unification rule application
    val UniCtx(termSubst, typeSubst, deletedUniLits, litTransf) = initUniCtxt(child)

    // construct the parent post-substitution (but prior to the deletion of the literals) and a mapping of the child literal indices to the ones in this parent
    val (encSubstParent, old2NewIdx) = reconstructSubstUniParent(deletedUniLits, encChild, childVarMap)


    ////////////////////////////
    // 0) Assume free variables
    val (assumeStep, childVarNames) = encPatternUniAssume(encChild)

    // construct the actual proof
    if (typeSubst.nonEmpty) {
      NotEncodable("Type unification not encoded yet")
    } else {

      ////////////////////////////
      // 1) Substitution subproof (optional)
      val (maybeSubstStepName, maybeSubstStep) = encodeSubstitutionSubstep(ctxt, termSubst, litTransf, old2NewIdx, childVarNames, encSubstParent, child.cl, parent.cl.implicitlyBound)

      ////////////////////////////
      // 2) Constraint-elimination subproof
      val nameHaveRemoveStep = Name("RemoveUniConst")
      val haveRemoveStep = constructRemoveStep(nameHaveRemoveStep, encSubstParent, encChild.lits, deletedUniLits, substClauseLen, child.cl)

      ////////////////////////////
      // 3) Composition in final refine step
      val lastStep = LpTerm.App(Obj(eqImp), Seq(Arg.Explicit[Level.Meta](Const(SymRef.LP(QName.local(nameHaveRemoveStep.value)))), Arg.Explicit[Level.Meta](Obj(maybeSubstStepName))))

      Encoded(((assumeStep ++ maybeSubstStep) :+ haveRemoveStep) :+ Refine(lastStep))
    }
  }

  /**
    * encodeUniInfo — Encode one RHS entry of a term substitution as an LP argument.
    *
    * The produced argument is intended to be applied to the encoded parent clause in
    * unification/ substitution steps
    *
    * Cases:
    *  - UniTermByBoundVar(j):
    *    -> If j refers to a variable that is available in the child’s context, return that variable.
    *    -> Otherwise, j denotes an out-of-scope bound index;
    *       in this case we generate a witness term of the appropriate HOL type using lpWitnessCon.
    *  - UniTermByTerm(t, ...):
    *    Encode the concrete term t directly and return it as an explicit argument.
    *
    * @param termUni      The RHS of a unification substitution entry.
    * @param childBoundIndices    Bound indices that are in scope for the child clause.
    * @param sharedVarMap Mapping from bound indices to LP variable names (for in-scope vars).
    * @param bndIdxToType      Mapping from bound indices to HOL types (used to build witness terms).
    * @return An explicit LP argument to be applied to the encoded parent.
    */
  private def encodeUniInfo(termUni: UniTermRhs, childBoundIndices: Seq[Int], sharedVarMap: Map[Int, String], bndIdxToType: Map[Int, leo.datastructures.Type]): Arg[Level.Obj] = {
    termUni match {
      case UniTermByBoundVar(targetIndex) =>
        if (childBoundIndices.contains(targetIndex)) {
          Out.lp_debug_info(s"bind by variable with index $targetIndex")
          //val encVar = Const[Level.Obj](SymRef.LP(QName.local(sharedVarMap(targetIndex)))) //todo: this is not nice
          val encVar = LpTerm.Var[Level.Obj](Name(sharedVarMap(targetIndex)),None)
          Arg.Explicit(encVar)
        } else {
          Out.lp_debug_info(s"creating a witness term for variable of scope $targetIndex")
          val ty = bndIdxToType(targetIndex)
          val freshWitness = LpTerm.App[Level.Obj](lpWitnessCon, Seq(Arg.ExplicitTypeArg(type2LP(ty))))
          Arg.Explicit(freshWitness)
        }

      case UniTermByTerm(term, _, _) =>
        val encTargetTerm = term2LP(term, sharedVarMap, suppressReduction = false, replaceUnknownVars = true)
        Out.lp_debug_info(s"bind by term $encTargetTerm}")
        Arg.Explicit(encTargetTerm)
    }
  }

  private final case class UniCtx(termSubst: Seq[UniTermSubst], typeSubst: Seq[UniTypeSubst], deletedUniLits: Seq[UniLitInfo], litTransf: LiteralTransformation)

  private def initUniCtxt(child:ClauseProxy)={
    // extract the addInfo
    val addInfo = child.furtherInfo.addInfoUni

    //extract the substitutions
    val termSubst = addInfo.subst.termSubsts
    val typeSubst = addInfo.subst.typeSubsts
    val deletedUniLits = addInfo.uniLits

    Out.lp_debug_info(s"subst non empty? ${addInfo.subst.termSubsts.nonEmpty || addInfo.subst.typeSubsts.nonEmpty}")

    val litTransf = addInfo.literalTransformations

    UniCtx(termSubst,typeSubst,deletedUniLits,litTransf)
  }

  private def reconstructSubstUniParent(deletedUniLits: Seq[UniLitInfo], encChild: lpClauseInst, childVarMap: Map[Int, String])={
    assert(deletedUniLits.nonEmpty, "Trying to verify unification but no unification literals to delete were given")
    Out.lp_debug_info(s"found ${deletedUniLits.length} unification literal(s):")
    val sortedInsertLits = deletedUniLits.sortBy(_.position)
    val newLits = sortedInsertLits.foldLeft(encChild.lits) {
      case (acc, newUniLit) =>
        val encNewLit = lit2Lp(newUniLit.literal, childVarMap, surpressReduction = true, replaceUnknownVars = true)
        Out.lp_debug_info(s"- at position ${newUniLit.position}: ($encNewLit)")
        acc.patch(newUniLit.position, Seq(encNewLit), 0)
    }

    // positions at which we insert new literals (sorted)
    val insertPositions: Seq[Int] = sortedInsertLits.map(_.position)
    // map from old index -> new index after all insertions
    val old2NewIdx: Map[Int, Int] = {
      val n = encChild.lits.length

      (0 until n).map { oldIdx =>
        // how many insertions were at or before this old index?
        val shift = insertPositions.count(_ <= oldIdx)
        oldIdx -> (oldIdx + shift)
      }.toMap
    }

    (newLits, old2NewIdx)
  }

  private def constructSubstStep(parentVars: Seq[(Int, Type)], childVars: Seq[(Int, Type)], termToApply: Map[Int, Arg[Level.Obj]], sharedVarMap: Map[Int, String], parentNameLpEnc: LpTerm[Level.Obj]): Refine = {
    assert(termToApply.nonEmpty)
    // todo: should i not instead test for the non-emptiness of parent.cl.implicitlyBound ?

    val orderedTerms: Seq[Arg[Level.Obj]] = parentVars.map(id =>
      // case var instanciated by some term
      if (termToApply.keySet.contains(id._1)) termToApply(id._1)
      // case var instanciated by a var of the parent
      else if (childVars.contains(id)) Arg.Explicit(var2Lp(id._1, id._2, sharedVarMap))
      // case var instanciated by a witness term
      else Arg.Explicit(LpTerm.App(lpWitnessCon, Seq(Arg.ExplicitTypeArg(type2LP(id._2))))))

    val appliedParentName = if (orderedTerms.nonEmpty) LpTerm.App(parentNameLpEnc, orderedTerms) else parentNameLpEnc

    Refine(Obj(appliedParentName))
  }

  // prove the parent after the substitution and the normalisazion of non-uf literals as a result of the substitution,
  // but prior to the deletion of the now trivially false unification constraints produce a have step proving this
  private def encodeSubstitutionSubstep(ctxt: EncUniCtx, termSubst: Seq[UniTermSubst], litTransf: LiteralTransformation, old2NewIdx: Map[Int, Int], childVarNames: Seq[Name], encSubstParent: Seq[LpTerm[Level.Obj]], childCl: Clause, parentImpB : Seq[(Int, Type)]):(LpTerm[Level.Obj], Seq[Have]) = {
    // based on the additional information, construct the terms in the lambdapi encoidng that need to be applied to the parent to verify the substitution
    // this is a mapping of the id of the free variable to the encoded term that it is instanciated with
    val termToApply: Map[Int, Arg[Level.Obj]] =
    termSubst.foldLeft(Map.empty[Int, Arg[Level.Obj]]) { (acc, termUni) =>
      val lpUnboundVar = termUni.sourceIndex
      val encSubstTerm = encodeUniInfo(termUni.rhs, childCl.implicitlyBound.map(_._1), ctxt.sharedVarMap.view.filterKeys(childCl.implicitlyBound.map(_._1).contains(_)).toMap, parentImpB.toMap)
      acc + (lpUnboundVar -> encSubstTerm)
    }

    // construct the application
    Out.lp_debug_info(s"vars of parent: ${parentImpB.map(_._1)}")
    Out.lp_debug_info(s"vars of child: ${childCl.implicitlyBound.map(_._1)}")
    if (termToApply.nonEmpty) {
      // todo: should i not instead test for the non-emptiness of parent.cl.implicitlyBound ?

      // detect potential flipping or normalisazion of literals that may be necessary in this step
      val idxFun = old2NewIdx.withDefault(identity)
      val maybeFlipStep: Seq[Rewrite] = verifySubstitutionLiteralNormalisazion(litTransf, childCl.lits, ctxt.substClauseLen, idxFun)
      // construct the refine step carrying out the substitution
      val refineStep = constructSubstStep(parentImpB, childCl.implicitlyBound, termToApply, ctxt.sharedVarMap, ctxt.parentNameLpEnc)

      // have substitution step
      val nameSubst = Name("Subst") // todo: add to names to keep safe, maybe make them parameters of the class
      val haveSubstStep = Have(nameSubst, Prf(nAry.disjunction(encSubstParent)), (maybeFlipStep :+ refineStep).map(Left(_)))

      (Const[Level.Obj](SymRef.LP(QName.local(nameSubst.value))), Seq(haveSubstStep))

    } else (LpTerm.App(ctxt.parentNameLpEnc, childVarNames.map(varName => Arg.Explicit(LpTerm.Var(varName, None)))), Seq.empty)
  }

  private def constructRemoveStep(nameHaveRemoveStep: Name, encSubstParent: Seq[LpTerm[Level.Obj]], encChildLits: Seq[LpTerm[Level.Obj]], deletedUniLits: Seq[UniLitInfo],  substClauseLen: Int, childCl: Clause) = {
    val impToProve = Prf(LogicConst.Eq(HolBaseTypes.O, nAry.disjunction(encSubstParent), nAry.disjunction(encChildLits)))
    val proofScript: Seq[LpProofScript] = deletedUniLits.map(litInfo => {
      Out.lp_debug_info(s"orig pos is ${litInfo.position}")
      val posInSubs = litInfo.position
      val patternLitInfo = PatternBuilder.PatternInfo(posInSubs, None, polarity = true)
      val pattern = PatternBuilder.generateClausePattern(Seq(patternLitInfo), substClauseLen)
      val embeddedPattern = PatternBuilder.embedPatternInEq(pattern, Side.Left)
      removeBot(embeddedPattern)
    })
    val finalStep = if (effectivelyEmpty(childCl) && childCl.lits.length == 1) Reflexivity else Refine(deleteBots(encChildLits, deletedUniLits.map(_.position).sorted))
    Have(nameHaveRemoveStep, impToProve, (proofScript :+ finalStep).map(step => Left(step)))
  }

}

object DetUniSimpEncoding {

  import Util._

  // defined Datatypes etc.

  final case class DetUniStage(curName: LpTerm[Level.Obj], // current proof term to refine at the end
                                scripts: Vector[LpProofScript], // accumulated scripts
                                clauseLits: Seq[LpTerm[Level.Obj]]) // current clause literal encoding after steps
                              {
                                def add(more: Seq[LpProofScript]): DetUniStage = copy(scripts = scripts ++ more)
                              }
  sealed trait StageResult
  private object StageResult {
    final case class Ok(stage: DetUniStage) extends StageResult
    final case class Fail(reason: String) extends StageResult
  }

  case class DetUniReconstruction(deleteIdx: Vector[Int],
                                  permutation: Vector[Int]
                                  //decomposed: Map[Int, Vector[Literal]]
                                 )

  // Orchestrator

  /**
    * encodeDetUniSimp — Outline of the encoded proof
    *
    * The DetUniSimp rule in Leo-III combines several logical transformations:
    *   - Decomposition (Decomp):
    *     Negated equational literals with identical rigid heads are decomposed
    *     into inequalities between corresponding arguments.
    *         Example:
    *         ¬(f s₁ … sₙ = f t₁ … tₙ) ⇒ ¬(s₁ = t₁) ∨ … ∨ ¬(sₙ = tₙ)
    *
    *   - Deterministic unification (Bind):
    *     Unification constraints of the form x = t (with x flexible)
    *     generate substitutions that instantiate variables.
    *
    *   - Deletion:
    *     Trivially false literals and resolved unification constraints
    *     are removed from the clause.
    *
    * Proof structure in the Lambdapi encoding:
    *
    * 0) Assume free variables
    *    Introduce all free variables of the child clause.
    *
    *
    * 1) Substitution subproof (optional)
    *    If deterministic unification produced a non-empty substitution:
    *      - Instantiate the encoded parent clause by applying the substitution.
    *      - If literal normalization is required prior to substitution
    *        (e.g. flipped equality orientation), insert rewrite steps
    *        justified via eqsym or related normalization theorems.
    *      - Otherwise, directly use the instantiated parent clause.
    *
    * 2) Clause permutation subproof (optional)
    *    If DetUniSimp reordered literals:
    *      - Apply the `permute` theorem in a dedicated substep to align
    *        the parent clause with the child clause ordering.
    * 3) Removal of trivially false literals (optional)
    *    Required when literals were deleted due to:
    *      - Deterministic unification constraints, or
    *      - Pre-existing trivial contradictions.
    *    Procedure:
    *   (i)   Convert each deleted literal into ⊥ using a dedicated tactic.
    *   (ii)  Remove ⊥-literals via deleteBots (or an equivalent theorem),
    *         yielding the child clause.
    *
    * 4) Decomposition subproof (optional)
    *    For each decomposed literal:
    *      - Apply Decomp_step repeatedly to peel off arguments.
    *      - Close using Decomp_single for the final argument.
    *      - If normalization altered literal structure (e.g. eta-expansion,
    *        orientation changes), justify via the corresponding equality theorems.
    *
    * 5) Composition
    *     Combine the constructed subproofs using eqImp (or equivalent)
    *     to derive the child clause from the original parent clause.
    *
    * Limitations / Notes:
    *   - Type unification is currently not encoded.
    *   - Unencoded procedures are treated as assumptions.
    *   - Decomposition operates on βη-normalized literals;
    *     normalization effects may introduce abstractions.
    *
    * @return (proof scripts, optional failure reason)
    */
  def encodeDetUniSimp(parent: ClauseProxy, child: ClauseProxy, parentNameLpEnc0: Name, sig: LpSig): EncodeResult = {
    Out.lp_debug_info(s"Encoding instance of DetUniSimp")
    val ro = RenderOptions()

    // todo: probably will need to also pass on a mapping of indices after encoding of delete and permute

    ////////////////////////////
    // Encodings and prelim
    val ctxt = initCtxt(child.cl, parent.cl, parentNameLpEnc0)
    val EncUniCtx(encChild, encParent, sharedVarMap, childVarMap, parentNameLpEnc, substClauseLen) = ctxt
    Out.lp_debug_info(s"parent: ${Renderer.ty(encParent.asMl, ro, sig)}")
    Out.lp_debug_info(s"proving ${Renderer.ty(encChild.asMl, ro, sig)}")

    // extract tracked additional information
    val subst = child.furtherInfo.addInfoDetUni.uniSubst
    val taggedLits = child.furtherInfo.addInfoDetUni.branchState.lits
    val decompInfo = child.furtherInfo.addInfoDetUni.branchState.decomp

    // reconstruct the necessary additional info based on the tagged literals:
    val DetUniReconstruction(deleteIdx,permutation) = reconstruct(taggedLits,parent.cl.lits.length)

    if (subst.typeSubsts.nonEmpty) return NotEncodable(s"type substitution not encoded")

    ////////////////////////////
    // 0) Assume free variables
    val (assumeStep, childVarNames) = encPatternUniAssume(encChild)

    // initial state
    val appliedParent = LpTerm.App(parentNameLpEnc, childVarNames.map(varName => Arg.Explicit[Level.Obj](LpTerm.Var(varName, None))))
    val parntLits = encParent.lits
    val initState = DetUniStage(appliedParent,assumeStep.toVector,parntLits)

    ////////////////////////////
    // 1) Substitution subproof (optional)
    val substStage: DetUniStage = verifyDetUniSubstStep(initState, subst) match {
      case StageResult.Ok(stage) => stage
      case StageResult.Fail(reason) => return NotEncodable(reason)
    }

    ////////////////////////////
    // 2) Clause permutation subproof (optional)
    val permStage: DetUniStage = verifyDetUniPermuteStep(permutation, parent.cl.lits.indices.toVector, substStage) match {
      case StageResult.Ok(stage) => stage
      case StageResult.Fail(reason) => return NotEncodable(reason)
    }

    ////////////////////////////
    // 3) Removal of trivially false literals (optional)
    val deleteStage: DetUniStage = verifyDetUniDeleteStep(deleteIdx, permStage) match {
      case StageResult.Ok(stage) => stage
      case StageResult.Fail(reason) => return NotEncodable(reason)
    }

    ////////////////////////////
    // 4) Decomposition subproof (optional)
    val decompStage: DetUniStage = verifyDecomp(decompInfo, deleteStage, child.cl.lits) match {
      case StageResult.Ok(stage) => stage
      case StageResult.Fail(reason) => return NotEncodable(reason)
    }

    ////////////////////////////
    // 5) Composition
    val finalRefine = Refine(Obj(decompStage.curName))

    Encoded(decompStage.scripts :+ finalRefine)
  }

  // Helpers for Substitution steps

  /**
    * encode the substitution steps, WIP
    */
  private def verifyDetUniSubstStep(previousStage: DetUniStage, subst: UniSubst): StageResult = {
    if (subst.termSubsts.nonEmpty) {
      Out.lp_debug_info(s"needs to apply substitution(s)")
      // todo
      //val termSubst = subst.termSubsts
      StageResult.Fail("DetUniSimp with substitution")
    } else {
      StageResult.Ok(previousStage)
    }
  }

  // Helpers for Permutation steps

  /**
    * encode the permutation steps, WIP
    */
  private def verifyDetUniPermuteStep(permutation: Vector[Int], parentIds: Vector[Int], previousStage: DetUniStage): StageResult = {
    val needsPermutation = permutation != parentIds
    if (needsPermutation) {
      Out.lp_debug_info(s"needs to apply permutation")
      // todo
      StageResult.Fail("DetUniSimp with permutation")
    } else {
      StageResult.Ok(previousStage)
    }
  }

  // Helpers for Deletion steps

  /**
    * encode the deletion steps, WIP
    */
  private def verifyDetUniDeleteStep(deleteIdx: Vector[Int], previousStage: DetUniStage): StageResult = {
    if (deleteIdx.nonEmpty) {
      Out.lp_debug_info(s"needs to verify deletion")
      // todo
      StageResult.Fail("DetUniSimp with Deletion")
    } else {
      StageResult.Ok(previousStage)
    }
  }

  // Helpers for Decomp steps

  /**
    * verifyDecomp — Verification of DetUniSimp decomposition steps
    *
    * Purpose:
    * Construct the Lambdapi proof subscript that justifies decomposition
    * steps produced by DetUniSimp.
    * Conceptually, decomposition replaces a negated equational literal
    * with the disjunction of negated equalities between corresponding arguments:
    * ¬(f t1 … tn = f s1 … sn)  ===>  ¬(t1 = s1) ∨ … ∨ ¬(tn = sn)
    *
    * The generated proof shows that this transformation is logically valid by
    * iterated applications of the encoded decomposition rules (Decomp_step /
    * Decomp_single), using transform theorem if necessary.
    *
    * Current limitations:
    *   - At most one literal is decomposed.
    *   - No implicit literal transformations are pending
    *     (no flips, no normalization steps).
    *   - Polymorphic types are not handled
    *   - Eta expansions are not handled
    *
    * Preconditions / Encoding Invariants:
    *   - The decomposed literal must have the shape ¬(f(args…) = f(args…))
    */
  private def verifyDecomp(decompInfo: Vector[DecompInfo], currentStage: DetUniStage, goalLits: Seq[Literal]): StageResult = {
    if (decompInfo.length > 1) return StageResult.Fail("DetUniSimp: Decomp on mulitple literals!")

    // go over the individual tracked decompositions and apply the necessary steps to encode them
    // todo: maybe encforce computation in the order of the literals in the current goal by sorting according to DecompInfo.idx modulo mapping
    val scriptsRes: StageResult = decompInfo.foldLeft[Either[String, (Vector[LpProofScript],Int)]](Right(Vector.empty, 0)) {
      // if the accumulator already inlcudes an error, abort
      case (Left(err), _) => Left(err)
      // else, continue
      case (Right((acc,alreadyAddedLitCount)), mapping) =>
        val idxInParent = mapping.OrigIdx

        if (!currentStage.clauseLits.isDefinedAt(idxInParent))
          Left(s"DetUniSimp: decomp index $idxInParent out of bounds (len=${currentStage.clauseLits.length})")
        else {
          val litInParent = currentStage.clauseLits(idxInParent)
          Out.lp_debug_info(s"handling literal at pos $idxInParent: $litInParent")

          // generate the new proof steps necessary to encode the given decomposition
          val newScriptsE_numAddedSteps: Either[String, (Vector[LpProofScript], Int)] = litInParent match {
            // expected case: Equation enclosed by negation
            case LogicConst.Not(LogicConst.Eq(_, LpTerm.App(f0, args0), LpTerm.App(f1, args1))) if f0 == f1 =>
              // ensure that the number of arguemtns is appropriate
              val n = args0.length
              if (n != args1.length) Left("Error in encoding of DetUniSimp: decomp but different number of arguments")
              else if (n < 1) Left("Error in encoding of DetUniSimp: decomp but no arguments found")
              else {
                // extract types of the arguments
                if (!(n <= mapping.hdTy.funParamTypes.length)) Left(s"Error in DetUniSimp Encoding: too many arguments in decomp")
                else {
                  val (_, residualTy) = mapping.hdTy.splitFunParamTypesAt(n)
                  if (residualTy.isFunType) Left(s"DetUniSimp: needs Eta expansion")
                  else {
                    safeEncTypes(mapping.hdTy.funParamTypesWithResultType) match {
                      case Left(NotEncodable(err)) => Left(err)
                      case Right(fullTypeSpine) =>
                        // Iterative construction of the necessary rule instances
                        (extractTermArgs(args0), extractTermArgs(args1)) match {
                          case (Left(NotEncodable(r)), _) => Left(r)
                          case (_, Left(NotEncodable(r))) => Left(r)
                          case (Right(lhsArgs), Right(rhsArgs)) =>
                            val instanciatedRules = stepwiseInstDecompRule(f0, lhsArgs, rhsArgs, fullTypeSpine, currentStage.clauseLits, idxInParent)
                            // reverse application of the rule makes up the proof script
                            val decompSteps = instanciatedRules.reverse.map(transfRule => Refine(Obj(transfRule)))
                            
                            val verifyInitialTransformationSteps = decompLitNormalisazion(mapping,alreadyAddedLitCount,goalLits)

                            Right(verifyInitialTransformationSteps ++ decompSteps, n)
                        }
                    }
                  }
                }
              }

            case LogicConst.Not(LogicConst.Eq(ty, LpTerm.Lam(lAbst, lBody), LpTerm.Lam(rAbst, rBody))) =>
              Left("DetUniSimp: Equations with Lambbdas not handled yet")

            case _ => Left(s"Error in encoding of DetUniSimp: trying to encode decomp, could not match")
          }
          (newScriptsE_numAddedSteps.map(pair => (acc ++ pair._1, alreadyAddedLitCount + pair._2)))
        }
    } match {
      case Left(err) => StageResult.Fail(err)
      case Right(scripts) => StageResult.Ok(currentStage.add(Comment("Verification of Decomp steps") +: scripts._1))
    }
    scriptsRes
  }

  /** Helper for Decomp steps: todo: move this to more general file
    * safe encoder of types that does not throw on poly types but just regurns a Not encodable mesage
    */
  private def safeEncTy(ty: Type): Either[NotEncodable, OlType] = {
    ty match {
      case ComposedType(_, _) =>
        Left(NotEncodable("Error: trying to encode ComposedType"))
      case ProductType(_) =>
        Left(NotEncodable("Error: trying to encode ProductType"))
      case ∀(_) =>
        Left(NotEncodable("Error: trying to encode quantified Type"))
      case _ => Right(type2LP(ty))
    }
  }

  // todo: move this to more general file
  private def safeEncTypes(tys: Seq[Type]): Either[NotEncodable, Vector[OlType]] = {
    tys.foldLeft[Either[NotEncodable, Vector[OlType]]](Right(Vector.empty)){
      case (Left(err), _) => Left(err)
      // else, continue
      case (Right(acc), nextTy) =>
        safeEncTy(nextTy) match {
          case Left(error) => Left(error)
          case Right(encTy) => Right(acc :+ encTy)
        }
    }
  }


  /**
    * stepwiseInstDecompRule
    *
    * Construct the sequence of instantiated Lambdapi decomposition rules required to verify
    * a Leo-III Decomp step on a negated equation
    *
    * The function works from the *last* argument inward:
    * - If more than one argument remains, it instantiates `Decomp_step` and produces a clause
    *   transformation (via `transform_n`) that replaces the current literal at `curPos`.
    * - When exactly one argument remains, it instantiates `Decomp_single` and finishes.
    *
    * @param hd         head symbol term (the common head)
    * @param lArgs      term arguments on LHS application (must match rArgs length)
    * @param rArgs      term arguments on RHS application
    * @param typeEls    types of the arguments applied
    * @param currClause current encoded clause literals (as Lp terms)
    * @param curPos     index of the literal to decompose; remains constant by invariant
    * @return Vector of instantiated clause-transformation applications (each one is a proof step),
    *         ordered from outermost to innermost (i.e. the order you would usually reverse for refine).
    */
  private def stepwiseInstDecompRule(hd: LpTerm[Level.Obj], lArgs: Seq[LpTerm[Level.Obj]], rArgs: Seq[LpTerm[Level.Obj]], typeEls: Seq[OlType], currClause: Seq[LpTerm[Level.Obj]], curPos: Int): Vector[LpTerm.App[Level.Obj]] = {
    val nArgs = lArgs.length
    val curArgTy = typeEls(nArgs - 1)

    // compute the type of the applied head
    val appliedHdTy0 = typeEls.takeRight(typeEls.length - nArgs)
    val appliedHdTy = if (appliedHdTy0.length == 1) appliedHdTy0.head else OlType.Fun(appliedHdTy0)

    val lArg = lArgs.last
    val rArg = rArgs.last

    val l = currClause(curPos)
    val c0 = currClause.take(curPos)
    val c2 = currClause.takeRight(currClause.length - (curPos + 1))

    if (lArgs.length == 1) {
      // needs to apply rule for last step (or single occurrence)
      val instRule = mkDecompSingleObj(curArgTy, appliedHdTy, lArg, rArg, hd, None)
      val res = DecompSingleResult(curArgTy, lArg, rArg)

      Vector(transform_n(l, c0, c2, Seq(res), instRule, Wildcard[Level.Obj]()))

    } else {
      // needs to apply rule for step
      val lLeadingArgs = lArgs.init
      val rLeadingArgs = rArgs.init
      val lFun = LpTerm.App(hd, lLeadingArgs.map(arg => Arg.Explicit(arg)))
      val rFun = LpTerm.App(hd, rLeadingArgs.map(arg => Arg.Explicit(arg)))

      val instRule = mkDecompStepObj(curArgTy, appliedHdTy, lArg, rArg, lFun, rFun, None)
      val res = DecompStepRes(curArgTy, appliedHdTy, lArg, rArg, lFun, rFun)

      transform_n(l, c0, c2, Seq(res._1, res._2), instRule, Wildcard[Level.Obj]()) +: stepwiseInstDecompRule(hd, lLeadingArgs, rLeadingArgs, typeEls, c0 ++ Seq(res._1, res._2) ++ c2, curPos) // idx does not change because the hd stays on the lhs
    }
  }

  /**
    * decompLitNormalisazion — Generate rewrite steps for implicit transformations invoked by  Decomp
    *
    * During decomposition, Leo may implicitly:
    * • Flip equational literals
    * • Normalise equalities (polarity adjustments/ changing equalities with $false or $true to non-eq literals)
    *
    * decompLitNormalisazion constructs the clause-level rewrite rules required to justify these implicit
    * literal transformations.
    *
    * Behaviour:
    * • Detects whether any transformations are required.
    * • Translates decomposition-local transformation metadata into global
    *   clause indices via LiteralInfo2LiteralTransformation.
    * • Delegates rewrite construction to
    *   verifySubstitutionLiteralNormalisazion.
    *
    * @param decompInfo           Tracked decomposition metadata
    * @param alreadyAddedLitCount Number of literals inserted before this step
    * @param goalLits             Clause literals after reconstruction
    * @return Rewrite steps justifying transformations
    */
  private def decompLitNormalisazion(decompInfo: DecompInfo, alreadyAddedLitCount: Int, goalLits: Seq[Literal]): Vector[Rewrite] = {
    // first check if we need any additional transformations
    val impTransf = decompInfo.LitTransf.exists(t => t.flip || t.normalize.isDefined)
    if (impTransf) {
      Out.lp_debug_info(s"needed transformations: ${decompInfo.LitTransf}")
      val idxInGoal = decompInfo.OrigIdx // todo: once we also do other steps, this will need to be mapped
      // transform the currently handled additional information
      val addInfoAsLiteralTransformation = LiteralInfo2LiteralTransforamtion(decompInfo.LitTransf, idxInGoal + alreadyAddedLitCount)
      verifySubstitutionLiteralNormalisazion(addInfoAsLiteralTransformation, goalLits, goalLits.length).toVector
    } else {
      Vector.empty
    }
  }

  /** Reconstruct deletion/permutation/decomposition info from the tagged literals of one branch.
    *
    * @param tagged    Final branch literals (after det-uni processing), still tagged.
    * @param clauseLen Original clause length (so indices are 0..clauseLen-1).
    */
  private def reconstruct(tagged: Seq[TaggedLit], clauseLen: Int): DetUniReconstruction = {

    // 1) permutation of surviving originals, in the order they appear in `tagged`
    val permutation: Vector[Int] = {
      val seen = scala.collection.mutable.LinkedHashSet.empty[Int]
      tagged.foreach {
        case TaggedLit(Orig(idx), _) =>
          seen += idx
        case TaggedLit(DecompOf(idx, _), _) =>
          seen += idx
      }
      seen.toVector
    }

    // 2) decomposition map: original index -> produced literals (in k-order)
//    val decomposed: Map[Int, Vector[Literal]] = {
//      val groups: Map[Int, Seq[(Int, Literal)]] =
//        tagged.collect { case TaggedLit(DecompOf(i, k), lit) => (i, (k, lit)) }
//          .groupBy(_._1)
//          .view.mapValues(_.map(_._2)).toMap
//
//      groups.view.mapValues { ks =>
//        ks.sortBy(_._1).map(_._2).toVector
//      }.toMap
//    }

    // 3) deletion indices:
    val deleteIdx = (0 until clauseLen).iterator.filter(i => !permutation.contains(i)).toVector

    DetUniReconstruction(
      deleteIdx = deleteIdx,
      permutation = permutation
      //decomposed = decomposed
    )
  }

}
