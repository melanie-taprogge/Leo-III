package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Clause.vars
import leo.datastructures._
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.ImplicitTransformationUtil.{LiteralInfo2LiteralTransforamtion, litNorm2lpRule, verifySubstitutionLiteralNormalisazion}
import leo.modules.output.LPoutput.LpLibs.EqRules.AsTerms.mkExpandLit
import leo.modules.output.LPoutput.LpLibs.FunRules.AsTerms.{DecompSingleResult, DecompStepRes, LiftedDecompSingleResult, LiftedDecompStepResult, mkDecompSingleObj, mkDecompStepObj, mkLiftDecompSingleBinderObj, mkLiftDecompStepBinderObj}
import leo.modules.output.LPoutput.LpLibs.MetaTheorems
import leo.modules.output.LPoutput.LpLibs.MetaTheorems.Inst.transform_n
import leo.modules.output.LPoutput.LpLibs.ND.Terms._
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.Arguments.extractTermArgs
import leo.modules.output.LPoutput.NewLpDatastructures.ClauseEncoding.{lit2Lp, lits2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript._
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Obj, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{El, Prf}
import leo.modules.output.LPoutput.NewLpDatastructures.Substitution.removeLeadingTypeArgs
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{args2LP, term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.{polyType2LP, safeEncTy, safeEncTypes, type2LP}
import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewModularEncoding.AssumeStep.{encAssumeStep, extractVarNames}
import leo.modules.output.LPoutput.NewModularEncoding.InstMetaTheorems.{applyRemoveStep, constructRemoveStep}

object Util {

  // Set up Context for encodings

  final case class EncUniCtx(encChild: lpClauseInst, encParent: lpClauseInst, sharedVarMap: Map[Int, String], childVarMap: Map[Int, String], childVarNames: Seq[Name], parentNameLpEnc: LpTerm[Level.Obj], substClauseLen: Int)

  def initUniRuleCtxt(childCl: Clause, parentCl: Clause, parentNameLpEnc0: Name): EncUniCtx = {

    //todo: do any checks here?

    // translation of the clauses
    val (sharedVarMap, encChild, encParent) = lpClauseInst.apply_to_pair(childCl, parentCl)

    // compute names and clause length
    val parentNameLpEnc: LpTerm[Level.Obj] = Const(SymRef.LP(QName.local(parentNameLpEnc0.value)))
    val substClauseLen = parentCl.lits.length

    // filter out only the vars relevant to the child
    val childVarMap = sharedVarMap.view.filterKeys(vars(childCl).distinct).toMap
    val childVarNames = extractVarNames(encChild)

    EncUniCtx(encChild, encParent, sharedVarMap, childVarMap, childVarNames, parentNameLpEnc, substClauseLen)
  }

  // Encode the Substitution steps

  /**
    * encodeUniInfo — Encode the RHS entry of a term substitution as an LP argument.
    *
    * The produced argument is intended to be used to instantiate the parent clause in
    * unification/ substitution steps.
    *
    * Cases:
    *  - UniTermByBoundVar(j):
    *    -> If j refers to a variable that is available in the child’s context, return that variable.
    *    -> Otherwise, j denotes an out-of-scope bound index;
    *    in this case we generate a witness term of the appropriate HOL type using lpWitnessCon.
    *  - UniTermByTerm(t, ...):
    *    Encode the concrete term t directly and return it as an explicit argument.
    *
    * @param termUni           The RHS of a unification substitution entry.
    * @param childBoundIndices Bound indices that are in scope for the child clause.
    * @param sharedVarMap      Mapping from bound indices to LP variable names (for in-scope vars).
    * @param bndIdxToType      Mapping from bound indices to HOL types (used to build witness terms).
    * @return An explicit LP argument to be applied to the encoded parent.
    */
  private def encodeUniInfo(termUni: UniTermRhs, childBoundIndices: Seq[Int], sharedVarMap: Map[Int, String], bndIdxToType: Map[Int, leo.datastructures.Type]): Arg[Level.Obj] = {
    termUni match {
      case UniTermByBoundVar(targetIndex) =>
        if (childBoundIndices.contains(targetIndex)) {
          Out.lp_debug_info(s"bind by variable with index $targetIndex")
          val encVar = LpTerm.Var[Level.Obj](Name(sharedVarMap(targetIndex)), None)
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

  /**
    * Encode the refine step encoding instantiation of the parent during a substitution step
    *
    * @param parentVars The free variables of the parent to be instantiated
    * @param childVars The free variables of the child to be proved
    * @param termToApply A mapping of the Integers encoding the variable to be instantiated to the encoded LP Term
    * @param sharedVarMap The mapping assigning unambiguous variables to the free variables of the parent and child clause
    * @param parentNameLpEnc The Term in the LP encoding representing the proved step of the parent
    * @return LP refine tactic with the applied parent
    */
  private def constructSubstStep(parentVars: Seq[(Int, Type)], childVars: Seq[(Int, Type)], termToApply: Map[Int, Arg[Level.Obj]], sharedVarMap: Map[Int, String], parentNameLpEnc: LpTerm[Level.Obj]): Refine = {
    assert(termToApply.nonEmpty)
    // todo: should i not instead test for the non-emptiness of parent.cl.implicitlyBound ?

    val orderedTerms: Seq[Arg[Level.Obj]] = parentVars.map(id =>
      // case var instantiated by some term
      if (termToApply.keySet.contains(id._1)) termToApply(id._1)
      // case var instantiated by a var of the parent
      else if (childVars.contains(id)) Arg.Explicit(var2Lp(id._1, id._2, sharedVarMap))
      // case var instantiated by a witness term
      else Arg.Explicit(LpTerm.App(lpWitnessCon, Seq(Arg.ExplicitTypeArg(type2LP(id._2))))))

    val appliedParentName = if (orderedTerms.nonEmpty) LpTerm.App(parentNameLpEnc, orderedTerms) else parentNameLpEnc

    Refine(Obj(appliedParentName))
  }

  /**
    * Orchestrator for the construction of a proof step encoding the substitution and any potential implicit transformations entailed by it.
    *
    * @param ctxt The encoding context
    * @param termSubst Additional information about the substitution tracked during proof search
    * @param litTransf Additional information about the implicit literal transformation entailed by substitution tracked during proof search
    * @param encSubstParent A sequence of literals encoding the parent that is to result from the substitution step
    * @param childImpBound A mapping of the implicitly bound variable indices of the child to its types
    * @param parentImpB A mapping of the implicitly bound variable indices of the parent to its types
    * @param idxMap If the indices given in the additional information refer to indices in the original child clause, we need a mapping to associate
    *               them with the correct indices in the clause at hand.
    * @return if no substitution is needed, return the previous step and an empty sequence, else, return the LP term encoding the substet and a
    *         sequence containing the LP have tactic encoding the substep
    */
  def encodeSubstitutionSubstep(nameStep: Name, ctxt: EncUniCtx, termSubst: Seq[UniTermSubst], litTransf: LiteralTransformation, encSubstParent: Seq[lpLiteralInst], childImpBound: Seq[(Int, Type)], parentImpB: Seq[(Int, Type)], idxMap: Int => Int = identity): (LpTerm[Level.Obj], Seq[Have]) = {

    // a mapping of the id of the free variable to the encoded term that it is instanciated with
    val termToApply: Map[Int, Arg[Level.Obj]] =
    termSubst.foldLeft(Map.empty[Int, Arg[Level.Obj]]) { (acc, termUni) =>
      val lpUnboundVar = termUni.sourceIndex
      val encSubstTerm = encodeUniInfo(termUni.rhs, childImpBound.map(_._1), ctxt.sharedVarMap.view.filterKeys(childImpBound.map(_._1).contains(_)).toMap, parentImpB.toMap)
      acc + (lpUnboundVar -> encSubstTerm)
    }

    // construct the application
    Out.lp_debug_info(s"vars of parent: ${parentImpB.map(_._1)}")
    Out.lp_debug_info(s"vars of child: ${childImpBound.map(_._1)}")
    if (termToApply.nonEmpty) {
      // detect potential flipping or normalisazion of literals that may be necessary in this step
      val maybeFlipAndNormalize: Seq[Rewrite] = verifySubstitutionLiteralNormalisazion(litTransf, encSubstParent.map(_.polarity), ctxt.substClauseLen, idxMap)
      // construct the refine step carrying out the substitution
      val refineStep = constructSubstStep(parentImpB, childImpBound, termToApply, ctxt.sharedVarMap, ctxt.parentNameLpEnc)

      // have substitution step
      val haveSubstStep = Have(nameStep, Prf(nAry.disjunction(encSubstParent.map(_.term))), (maybeFlipAndNormalize :+ refineStep).map(Left(_)))

      (Const[Level.Obj](SymRef.LP(QName.local(nameStep.value))), Seq(haveSubstStep))

    } else (LpTerm.App(ctxt.parentNameLpEnc, ctxt.childVarNames.map(varName => Arg.Explicit(LpTerm.Var(varName, None)))), Seq.empty)
  }

  /**
    * Reindex literal-transformation metadata through a clause-position map.
    *
    * Literal transformations are usually tracked in the clause produced by the
    * calculus rule. If proof reconstruction temporarily reinserts deleted
    * literals, the same transformations must be applied at the corresponding
    * positions in the reconstructed parent.
    */
  def reindexLiteralTransformation(litTransf: LiteralTransformation, idxMap: Int => Int): LiteralTransformation = {
    LiteralTransformation(
      litTransf.flippedLits.map(idxMap),
      litTransf.normalizedEq.map { case (idx, mode) => (idxMap(idx), mode) }
    )
  }

  /**
    * Reconstruct a parent clause after applying an original Leo substitution,
    * including any recorded literal-level transformations.
    *
    * This is shared by DetUniSimp and PreUni: both need an explicit encoded
    * clause as target type for the substitution subproof, and both can obtain
    * it most robustly by applying the original substitution to the parent clause.
    */
  def reconstructSubstParent(origTermSubst: Subst, origTypeSubst: Subst, litTransf: LiteralTransformation, ctxt: EncUniCtx, parentCl: Clause): Option[Seq[lpLiteralInst]]= {
    val substParent = parentCl.substitute(origTermSubst, origTypeSubst)
    val encSubstParent = lits2Lp(substParent.lits, ctxt.childVarMap, replaceUnknownVars = true)
    applyLiteralTransformations(encSubstParent, litTransf)
  }

  /**
    * Apply recorded literal transformations to an encoded clause.
    *
    * The returned literals represent the post-substitution clause shape expected
    * by the later proof target, while the rewrite proof for these transformations
    * is still generated separately by `verifySubstitutionLiteralNormalisazion`.
    */
  def applyLiteralTransformations(encLits: Seq[lpLiteralInst], litTransf: LiteralTransformation): Option[Seq[lpLiteralInst]] = {
    val normalisazionMap = litTransf.normalizedEq.toMap
    if (litTransf.transforamtionsHappened) {
      Some(encLits.zipWithIndex.map { taggedLit =>
        val (lit, idx) = taggedLit
        if (litTransf.flippedLits.contains(idx)) {
          lit.flipIfEq
        } else if (normalisazionMap.contains(idx)) {
          val appliedRule = litNorm2lpRule(normalisazionMap(idx))
          Out.lp_debug_info(s"trying to apply normalisazion $appliedRule to ${lit.term}")
          val transformedLit = appliedRule.applyTo(lit)
          Out.lp_debug_info(s"resulting in $transformedLit ")
          transformedLit match {
            case Some(res) => res
            case None => return None
          }
        } else {
          lit
        }
      })
    } else Some(encLits)
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
    val ctxt = initUniRuleCtxt(child.cl, parent.cl, parentNameLpEnc0)
    val EncUniCtx(encChild, encParent, sharedVarMap, childVarMap, childVarNames, parentNameLpEnc, substClauseLen) = ctxt
    Out.lp_debug_info(s"proving ${Renderer.ty(encChild.asMl, ro, sig)}")
    Out.lp_debug_info(s"parent: ${Renderer.ty(encParent.asMl, ro, sig)}")

    // encoding of additional information regarding the unification rule application
    val UniCtx(termSubst, typeSubst, deletedUniLits, litTransf) = initUniCtxt(child.furtherInfo.addInfoUni)

    // construct the parent post-substitution (but prior to the deletion of the literals) and a mapping of the child literal indices to the ones in this parent
    val (encSubstParent, old2NewIdx) = reconstructSubstUniParent(deletedUniLits, encChild.lits, childVarMap)


    ////////////////////////////
    // 0) Assume free variables
    val (assumeStep) = encAssumeStep(childVarNames)

    // construct the actual proof
    if (typeSubst.nonEmpty) {
      NotEncodable("Type unification not encoded yet")
    } else {

      ////////////////////////////
      // 1) Substitution subproof (optional)
      val nameHaveSubstStep = Name("Subst")
      val (maybeSubstStepName, maybeSubstStep) = encodeSubstitutionSubstep(nameHaveSubstStep,ctxt, termSubst, litTransf, encSubstParent, child.cl.implicitlyBound, parent.cl.implicitlyBound, old2NewIdx.withDefault(identity))

      ////////////////////////////
      // 2) Constraint-elimination subproof
      val nameHaveRemoveStep = Name("RemoveUniConst")
      val haveRemoveStep = constructRemoveStep(nameHaveRemoveStep, encSubstParent, encChild.lits, deletedUniLits.map(_.position)) // , child.cl

      ////////////////////////////
      // 3) Composition in final refine step
      val appliedHaveRemoveStep = applyRemoveStep(nameHaveRemoveStep, maybeSubstStepName)

      Encoded(((assumeStep ++ maybeSubstStep) :+ haveRemoveStep) :+ Refine(Obj(appliedHaveRemoveStep)))
    }
  }

  final case class UniCtx(termSubst: Seq[UniTermSubst], typeSubst: Seq[UniTypeSubst], deletedUniLits: Seq[UniLitInfo], litTransf: LiteralTransformation)

  def initUniCtxt(addInfo: AddInfoUni) = {
    // extract the addInfo

    //extract the substitutions
    val termSubst = addInfo.subst.termSubsts
    val typeSubst = addInfo.subst.typeSubsts
    val deletedUniLits = addInfo.uniLits

    Out.lp_debug_info(s"subst non empty? ${addInfo.subst.termSubsts.nonEmpty || addInfo.subst.typeSubsts.nonEmpty}")

    val litTransf = addInfo.literalTransformations

    UniCtx(termSubst, typeSubst, deletedUniLits, litTransf)
  }

  /**
    * reconstructSubstUniParent - reconstruct a clause after substitution but prior to the deletion of unification literals
    *
    * In the process of unification, Leo-III carries out the substitution and deletes the unification constraints
    * that have become trivially false as a result of the substitution. In proof verification, the substitution step
    * prior to this deletion needs to be verified in a substep in order to justify this removal.
    * reconstructSubstUniParent carries out this reconstruction based on a lits of deleted literals, and the encoded
    * literals of the last proven step.
    *
    * We track the literals produced by unification throughtout the reasoning process of Leo-III, and this function expects
    * the already substituted literal as an arguemnt.
    *
    * @param deletedUniLits Seq of UniLitInfo, detailing the deleted literals and their indices
    * @param encUniClause   List of encoded literals of the clause after substitution
    * @param childVarMap    Mapping of the bound variables, necessary for encoding of the new literals
    * @return A Seq of literals representing the last proven step with the deleted literals inserted, and mapping linking the
    *         original index of the literals in encLastStep to those in the new Seq.
    */
  def reconstructSubstUniParent(deletedUniLits: Seq[UniLitInfo], encUniClause: Seq[lpLiteralInst], childVarMap: Map[Int, String]): (Seq[lpLiteralInst], Map[Int, Int]) = {
    assert(deletedUniLits.nonEmpty, "Trying to verify unification but no unification literals to delete were given")
    Out.lp_debug_info(s"found ${deletedUniLits.length} unification literal(s):")
    val sortedInsertLits = deletedUniLits.sortBy(_.position)
    // reinsert the deleted literals
    // first, encode the new literals
    val newLits = sortedInsertLits.foldLeft(encUniClause) {
      case (acc, newUniLit) =>
        val encNewLit = lit2Lp(newUniLit.literal, childVarMap, surpressReduction = true, replaceUnknownVars = true)
        Out.lp_debug_info(s"- at position ${newUniLit.position}: ($encNewLit)")
        // we assume that the sequence of literals passed here do not contain the
        acc.patch(newUniLit.position, Seq(encNewLit), 0)
    }
    // positions at which we insert new literals (sorted)
    val insertPositions: Seq[Int] = sortedInsertLits.map(_.position)
    // map from old index -> new index after all insertions
    val old2NewIdx: Map[Int, Int] = {
      val n = encUniClause.length

      (0 until n).map { oldIdx =>
        // how many insertions were at or before this old index?
        val shift = insertPositions.count(_ <= oldIdx)
        oldIdx -> (oldIdx + shift)
      }.toMap
    }

    (newLits, old2NewIdx)
  }

}

object DetUniSimpEncoding {

  import Util._

  // defined Datatypes etc.

  final case class DetUniStage(curName: LpTerm[Level.Obj], // current proof term to refine at the end
                                scripts: Vector[LpProofScript], // accumulated scripts
                                clauseLits: Seq[lpLiteralInst],
                                parent2currentIdx: Map[Int,Int]) // current clause literal encoding after steps
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
    *
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
    val ctxt = initUniRuleCtxt(child.cl, parent.cl, parentNameLpEnc0)
    val EncUniCtx(encChild, encParent, sharedVarMap, childVarMap, childVarNames, parentNameLpEnc, substClauseLen) = ctxt
    Out.lp_debug_info(s"parent: ${Renderer.ty(encParent.asMl, ro, sig)}")
    Out.lp_debug_info(s"proving ${Renderer.ty(encChild.asMl, ro, sig)}")

    // extract tracked additional information
    val subst = child.furtherInfo.addInfoDetUni.uniSubst
    val taggedLits = child.furtherInfo.addInfoDetUni.branchState.lits
    val decompInfo = child.furtherInfo.addInfoDetUni.branchState.decomp

    // reconstruct the necessary additional info based on the tagged literals:
    val DetUniReconstruction(deleteIdx,permutation) = reconstruct(taggedLits,parent.cl.lits.length)

    if (subst.encSubst.typeSubsts.nonEmpty) return NotEncodable(s"type substitution not encoded")

    ////////////////////////////
    // 0) Assume free variables
    val (assumeStep) = encAssumeStep(childVarNames)

    // initial state
    val appliedParent = LpTerm.App(parentNameLpEnc, childVarNames.map(varName => Arg.Explicit[Level.Obj](LpTerm.Var(varName, None))))
    val parntLits = encParent.lits
    val initState = DetUniStage(appliedParent,assumeStep.toVector,parntLits, (0 until (encParent.lits.length)).map(i => i -> i).toMap)

    Out.lp_debug_info(s"initial state")
    Out.lp_debug_info(s"proof so far: ${initState.scripts.map(scr => Renderer.proof(scr, ro, sig))}")
    Out.lp_debug_info(s"current step: ${initState.clauseLits.map(lit => Renderer.termP(lit.term, ro, 0, sig))}")

    ////////////////////////////
    // 1) Substitution subproof (optional)
    val substStage: DetUniStage = verifyDetUniSubstStep(initState, subst, ctxt, child.cl, parent.cl) match {
      case StageResult.Ok(stage) => stage
      case StageResult.Fail(reason) => return NotEncodable(reason)
    }

    Out.lp_debug_info(s"substStage state")
    Out.lp_debug_info(s"proof so far: ${substStage.scripts.map(scr => Renderer.proof(scr, ro, sig))}")
    Out.lp_debug_info(s"current step: ${substStage.clauseLits.map(lit => Renderer.termP(lit.term, ro, 0, sig))}")

    ////////////////////////////
    // 3) Removal of trivially false literals (optional)
    val deleteStage: DetUniStage = verifyDetUniDeleteStep(deleteIdx, substStage) match { // todo: throw untested exception in case of non uni literals to delete
      case StageResult.Ok(stage) => stage
      case StageResult.Fail(reason) => return NotEncodable(reason)
    }

    Out.lp_debug_info(s"permutation: $permutation, current map values: ${deleteStage.parent2currentIdx.values.toVector}")
    // permutation needs to be updated
    //val updatedPermutation = permutation.map(deleteStage.parent2currentIdx)
    //if (subst.encSubst.termSubsts.nonEmpty && (updatedPermutation != deleteStage.parent2currentIdx.values.toVector)) throw new Exception(s"BOOOOOTH")

    Out.lp_debug_info(s"deleteStage state")
    Out.lp_debug_info(s"proof so far: ${deleteStage.scripts.map(scr => Renderer.proof(scr, ro, sig))}")
    Out.lp_debug_info(s"current step: ${deleteStage.clauseLits.map(lit => Renderer.termP(lit.term, ro, 0, sig))}")

    ////////////////////////////
    // 2) Clause permutation subproof (optional) //todo: handle cases with permuation and substitution
    val permStage: DetUniStage = verifyDetUniPermuteStep(permutation, deleteStage) match {
      case StageResult.Ok(stage) => stage
      case StageResult.Fail(reason) => return NotEncodable(reason)
    }

    Out.lp_debug_info(s"permStage state")
    Out.lp_debug_info(s"proof so far: ${permStage.scripts.map(scr => Renderer.proof(scr,ro,sig))}")
    Out.lp_debug_info(s"current step: ${permStage.clauseLits.map(lit => Renderer.termP(lit.term,ro,0,sig))}")

    ////////////////////////////
    // 4) Decomposition subproof (optional)
    val etaExpandedStage: DetUniStage = etaExpandDecompParents(decompInfo, permStage) match {
      case StageResult.Ok(stage) => stage
      case StageResult.Fail(reason) => return NotEncodable(reason)
    }

    val decompStage: DetUniStage = verifyDecomp(decompInfo, etaExpandedStage, child.cl.lits, sig) match {
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
    * Reconstruct the parent of a DetUniSimp step prior to implicit transformations. This process is more involved than in
    * other unification instances, as DetUniSubst applies substitution interlaced with other operations (like decomposition). In order to separate
    * the processes cleanly and verify them sequentially, the result of the substitution step needs to be reconstructed carefully.
    *
    * @param subst Additional information on substitution tracked during proof search
    * @param ctxt The encoding context
    * @param parentCl The unencoded parent clause
    * @return
    */
  def reconstructSubstParentUniDetSubst(subst: AddInfoUniWithSubst, ctxt: EncUniCtx, parentCl: Clause): Option[Seq[lpLiteralInst]]= {
    reconstructSubstParent(subst.origTermSubst, subst.origTypeSubst, subst.literalTransformations, ctxt, parentCl)
  }

  private def verifyDetUniSubstStep(previousStage: DetUniStage, subst: AddInfoUniWithSubst, ctxt: EncUniCtx, childCl: Clause, parentCl: Clause): StageResult = {
    if (subst.encSubst.termSubsts.nonEmpty) {
      Out.lp_debug_info(s"needs to apply substitution(s)")

      // encoding of additional information regarding the unification rule application
      val (termSubst, litTransf) = (subst.encSubst.termSubsts,subst.literalTransformations)

      val normalSubstParent: Seq[lpLiteralInst] = reconstructSubstParentUniDetSubst(subst, ctxt, parentCl) match {
        case Some(res) => res
        case None => return StageResult.Fail(s"Trying to encode substitution substep, error when reconstructing substituted parent")
      }

      val nameHaveSubstStep = Name("Subst")
      val (newStepName, substSubstep) = encodeSubstitutionSubstep(nameHaveSubstStep,ctxt,termSubst,litTransf,normalSubstParent,childCl.implicitlyBound,parentCl.implicitlyBound,previousStage.parent2currentIdx.withDefault(identity))

      StageResult.Ok(DetUniStage(newStepName,previousStage.scripts ++ substSubstep,normalSubstParent,previousStage.parent2currentIdx))
    } else {
      StageResult.Ok(previousStage)
    }
  }

  // Helpers for Permutation steps

  /**
    * encode the permutation steps
    */
  private def verifyDetUniPermuteStep(permutation: Vector[Int], previousStage: DetUniStage): StageResult = {
    val currentIds = previousStage.parent2currentIdx.values.toVector
    val updatedPermutation = permutation.map(previousStage.parent2currentIdx(_))
    val needsPermutation = updatedPermutation != currentIds
    if (needsPermutation) {
      Out.lp_debug_info(s"needs to apply permutation: $permutation")
      Out.lp_debug_info(s"all good")
      val instPermTheorem = MetaTheorems.Inst.permute(updatedPermutation,previousStage.clauseLits,previousStage.curName)
      Out.lp_debug_info(s"inst theorem: $instPermTheorem")
      // todo
      val haveStepName = Name("DetUniLit_permutation") // todo: safe and source from one central place that can ensure no conflict with names occurs
      val permutedClause = updatedPermutation.map(previousStage.clauseLits)
      val refineStep = Refine(Obj(instPermTheorem))
      val haveStep = Have(haveStepName,Prf(nAry.disjunction(permutedClause.map(_.term))),Seq(Left(refineStep)))

      // update the map todo: can probably make this a general (safe) method in package
      val updatedMap = previousStage.parent2currentIdx.map{case (i, j) => (i, updatedPermutation(j))}

      StageResult.Ok(previousStage.copy(scripts = previousStage.scripts :+ haveStep, clauseLits = permutedClause, curName = Const(SymRef.LP(QName.local(haveStepName.value))),parent2currentIdx = updatedMap))
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
      Out.lp_debug_info(s"needs to verify deletion (of indices $deleteIdx)")

      // This is currently just the identity, but order of steps may be rearranged leading to change in orders
      val deleteIdxCurrent = deleteIdx.map(i => previousStage.parent2currentIdx(i))

      val fdsfsd = deleteIdxCurrent.map(i => i >= 0 && i < previousStage.clauseLits.length)

      // ensure all indices are in scope
      if (!fdsfsd.contains(false)){
        // reconstruct the clause after the removal of the substituted literals
        val postDeleteClause = previousStage.clauseLits.zipWithIndex.filterNot { case (_, i) => deleteIdxCurrent.toSet(i) }.map(_._1)

        val nameHaveRemoveStep = Name("RemoveTrivFalse")
        val haveRemoveStep = constructRemoveStep(nameHaveRemoveStep, previousStage.clauseLits, postDeleteClause, deleteIdxCurrent)
        val appliedRemoveStep = applyRemoveStep(nameHaveRemoveStep,previousStage.curName)

        // create a mapping that (for all remaining literals) links the indices that literals had in the parent clause to the index of the literal in the current goal
        // to this end, we need to delete elements from the mapping that lead to indices that were remoced, and we need to shift the remaining indices
        //val updatedMapping = previousStage.parent2currentIdx.filterNot{case (_, v) => deleteIdxCurrent.contains(v)}
        val delsSorted = deleteIdxCurrent.distinct.sorted

        def shiftAfterDeletes(i: Int): Int = i - delsSorted.count(_ < i)

        val updatedMapping =
          previousStage.parent2currentIdx
            .filterNot { case (_, v) => deleteIdxCurrent.contains(v) }
            .map { case (k, v) => k -> shiftAfterDeletes(v) }
        // todo: I may want to handle these updates differently/ ensure that the operation is admissible in all cases etc. I may need this across operations _> safe method in package?

        StageResult.Ok(DetUniStage(appliedRemoveStep, previousStage.scripts :+ haveRemoveStep,postDeleteClause,updatedMapping))
      } else{
        StageResult.Fail(s"Error encoding DetUniSimp: Attempting to verify deletion of literals but indices ${deleteIdxCurrent.filter(fdsfsd)} are out of scope")
      }
    } else {
      StageResult.Ok(previousStage)
    }
  }

  // Helpers for Decomp steps

  private final case class EtaExpansion(lit: lpLiteralInst, rewrite: Option[Rewrite])

  private def etaExpandDecompLiteral(info: DecompInfo, lit: lpLiteralInst, idxInClause: Int, clauseLen: Int): Either[String,EtaExpansion] = lit.term match {
    case LogicConst.Not(LogicConst.Eq(ty, left, right)) =>
      val (expandedLeft, expandedRight) = etaExpandTermPair(ty,left,right,s"Eta${info.OrigIdx}")
      val expandedLit = lpLiteralInst(LogicConst.Not(LogicConst.Eq(ty,expandedLeft,expandedRight)),polarity = false,eq = true)
      if (expandedLit == lit) Right(EtaExpansion(lit,None))
      else splitOlFun(ty) match {
        case Some((argTy, resultTy)) =>
          val pattern = PatternBuilder.generateClausePattern(Seq(PatternBuilder.PatternInfo(idxInClause,None,polarity = true)), clauseLen)
          Right(EtaExpansion(expandedLit,Some(Rewrite(Some(pattern),mkExpandLit(argTy,resultTy,left,right),Side.Left))))
        case None =>
          Left("DetUniSimp: eta expansion changed a non-functional decomp literal")
      }
    case _ =>
      Right(EtaExpansion(lit,None))
  }

  private def etaExpandDecompParents(decompInfo: Vector[DecompInfo], previousStage: DetUniStage): StageResult = {
    if (decompInfo.isEmpty) return StageResult.Ok(previousStage)

    val clauseLen = previousStage.clauseLits.length
    var updatedLits = previousStage.clauseLits
    var rewrites = Vector.empty[Rewrite]

    decompInfo.foreach { info =>
      previousStage.parent2currentIdx.get(info.OrigIdx) match {
        case Some(idxInClause) if updatedLits.isDefinedAt(idxInClause) =>
          etaExpandDecompLiteral(info, updatedLits(idxInClause), idxInClause, clauseLen) match {
            case Right(EtaExpansion(newLit, maybeRewrite)) =>
              updatedLits = updatedLits.updated(idxInClause,newLit)
              rewrites = rewrites ++ maybeRewrite.toVector
            case Left(err) =>
              return StageResult.Fail(err)
          }
        case Some(idxInClause) =>
          return StageResult.Fail(s"DetUniSimp: eta expansion requested for decomp literal at out-of-bounds index $idxInClause")
        case None =>
          return StageResult.Fail(s"DetUniSimp: eta expansion requested for missing original literal ${info.OrigIdx}")
      }
    }

    if (rewrites.isEmpty) StageResult.Ok(previousStage)
    else {
      val haveStepName = Name("DetUniEtaExpandedParent")
      val haveStep = Have(haveStepName,Prf(nAry.disjunction(updatedLits.map(_.term))),(rewrites :+ Refine(Obj(previousStage.curName))).map(Left(_)))
      StageResult.Ok(previousStage.copy(curName = lpTermBuilder.localObj(haveStepName), scripts = previousStage.scripts :+ haveStep, clauseLits = updatedLits))
    }
  }

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
    *   - Polymorphic types are not handled
    *   - Eta expansions are not handled
    *
    * Preconditions / Encoding Invariants:
    *   - The decomposed literal must have the shape ¬(f(args…) = f(args…))
    */
  private def verifyDecomp(decompInfo: Vector[DecompInfo], currentStage: DetUniStage, goalLits: Seq[Literal], sig: LpSig): StageResult = {

    Out.lp_debug_info(s"Needs verification of decomposition")

    if (decompInfo.isEmpty) return StageResult.Ok(currentStage)

    // Store all data needed for one decomposed original literal.  We first
    // collect these tasks from the unchanged stage, then use them twice: once to
    // compute the fully decomposed target clause, and once to build the proof
    // backwards from that target.
    final case class DecompTask(info: DecompInfo,
                                originalIdx: Int,
                                originalLit: lpLiteralInst,
                                replacementLits: Seq[lpLiteralInst],
                                binders: Seq[LpTerm.Var[Level.Obj]],
                                hd: LpTerm[Level.Obj],
                                lhsArgs: Seq[LpTerm[Level.Obj]],
                                rhsArgs: Seq[LpTerm[Level.Obj]],
                                fullTypeSpine: Seq[OlMonoType])

    // Decode the tracked Leo decomposition information into LP literals and arguments.
    def buildTask(mapping: DecompInfo): Either[String, DecompTask] = {
      val maybeIdxInParent = currentStage.parent2currentIdx.get(mapping.OrigIdx)

      if (maybeIdxInParent.isEmpty) {
        Left(s"DetUniSimp: decomp original index ${mapping.OrigIdx} is not present in the current clause")
      } else if (!currentStage.clauseLits.isDefinedAt(maybeIdxInParent.get)) {
        Left(s"DetUniSimp: decomp index ${maybeIdxInParent.get} out of bounds (len=${currentStage.clauseLits.length})")
      } else {
        val idxInParent = maybeIdxInParent.get
        val litInParent = currentStage.clauseLits(idxInParent)
        Out.lp_debug_info(s"handling literal at pos $idxInParent: $litInParent")

        def buildApplicationTask(binders: Seq[LpTerm.Var[Level.Obj]], leftBody: LpTerm[Level.Obj], rightBody: LpTerm[Level.Obj]): Either[String, DecompTask] = {
          val (f0, args0) = flattenAppSpine(leftBody)
          val (f1, args1) = flattenAppSpine(rightBody)
          if (args0.nonEmpty && args1.nonEmpty && f0 == f1) {
            val (hdTy, relevantArgs0, relevantArgs1) = (mapping.hdTy, removeLeadingTypeArgs(args0), removeLeadingTypeArgs(args1))
            // ensure that the number of arguemtns is appropriate
            val n = relevantArgs0.length
            if (n != relevantArgs1.length) Left("Error in encoding of DetUniSimp: decomp but different number of arguments")
            else if (n < 1) Left("Error in encoding of DetUniSimp: decomp but no arguments found")
            else {
              // extract types of the arguments
              if (!(n <= hdTy.funParamTypes.length)) {
                val encHdTySafe = hdTy.funParamTypesWithResultType.map(polyType2LP)
                Out.lp_debug_info(s"type of the head symbol: ${mapping.hdTy}, encoded: ${encHdTySafe}")
                Out.lp_debug_info(s"args: $relevantArgs0")
                Left(s"Error in DetUniSimp Encoding: too many arguments ($n) in decomp (funParamTypes gives ${hdTy.funParamTypes.length})")
              }
              else {
                val (_, residualTy) = hdTy.splitFunParamTypesAt(n)
                if (residualTy.isFunType)
                  Left(s"DetUniSimp: needs Eta expansion")
                else {
                  safeEncTypes(hdTy.funParamTypesWithResultType) match {
                    case Left(NotEncodable(err)) => Left(err)
                    case Right(fullTypeSpine) =>
                      // Iterative construction of the necessary rule instances
                      (extractTermArgs(relevantArgs0), extractTermArgs(relevantArgs1)) match {
                        case (Left(NotEncodable(r)), _) => Left(r)
                        case (_, Left(NotEncodable(r))) => Left(r)
                        case (Right(lhsArgs), Right(rhsArgs)) =>
                          // The final replacement for f a1 ... an = f b1 ... bn is
                          // the block a1=b1, ..., an=bn.  Literal-level cleanup
                          // recorded by DetUniSimp is applied to this block here,
                          // while the proof of those cleanups is emitted later.
                          val rawReplacement = lhsArgs.zip(rhsArgs).zip(fullTypeSpine.take(n)).map {
                            case ((lhsArg, rhsArg), argTy) =>
                              if (binders.isEmpty) DecompSingleResult(argTy, lhsArg, rhsArg)
                              else lpTermBuilder.negEq(lpTermBuilder.funTy(binders,argTy), lpTermBuilder.lam(binders,lhsArg), lpTermBuilder.lam(binders,rhsArg))
                          }
                          Out.lp_debug_info(s"callsite 1")
                          val localLitTransf = LiteralInfo2LiteralTransforamtion(mapping.LitTransf, 0)
                          Out.lp_debug_info(s"generated transfomration: $localLitTransf")
                          Out.lp_debug_info(s"applying to: \n${rawReplacement.map(l => Renderer.termP(l.term,RenderOptions(),0,sig)).mkString("\n")}")
                          applyLiteralTransformations(rawReplacement, localLitTransf) match {
                            case Some(replacement) =>
                              Right(DecompTask(mapping, idxInParent, litInParent, replacement, binders, f0, lhsArgs, rhsArgs, fullTypeSpine))
                            case None =>
                              Left("Error in DetUniSimp Encoding: could not apply literal transformations after decomp")
                          }
                      }
                  }
                }
              }
            }

          } else {
            Out.lp_debug_info(s"unsuccessfully tried to match ${Renderer.termP(litInParent.term,RenderOptions(),0,sig)}")
            Left(s"Error in encoding of DetUniSimp: trying to encode decomp, could not match")
          }
        }

        litInParent.term match {
          case LogicConst.Not(LogicConst.Eq(_, left, right)) =>
            val (lBinders, lBody) = collectLeadingLambdas(left)
            val (rBinders, rBody) = collectLeadingLambdas(right)
            assert(lBinders == rBinders, s"DetUniSimp: decomp under binders requires matching leading lambdas, got $lBinders and $rBinders")
            buildApplicationTask(lBinders, lBody, rBody)
          case _ =>
            Out.lp_debug_info(s"unsuccessfully tried to match ${Renderer.termP(litInParent.term,RenderOptions(),0,sig)}")
            Left(s"Error in encoding of DetUniSimp: trying to encode decomp, could not match")
        }
      }
    }

    // Forward model of the DetUniSimp result: replace one original literal by
    // its decomposed block and shift all later tracked original-literal
    // positions.  Applying this to every task yields the clause we ultimately
    // have to prove.
    def replaceForward(stage: DetUniStage, task: DecompTask): DetUniStage = {
      Out.lp_debug_info(s"replacing ${Renderer.termP(task.originalLit.term,RenderOptions(),0,sig)} with ${task.replacementLits.map(l => Renderer.termP(l.term,RenderOptions(),0,sig))}")
      val idx = stage.parent2currentIdx(task.info.OrigIdx)
      val updatedClause = stage.clauseLits.patch(idx, task.replacementLits, 1)
      val shift = task.replacementLits.length - 1
      val updatedMapping = stage.parent2currentIdx.map {
        case (origIdx, _) if origIdx == task.info.OrigIdx => origIdx -> idx
        case (origIdx, pos) if pos > idx => origIdx -> (pos + shift)
        case other => other
      }
      stage.copy(clauseLits = updatedClause, parent2currentIdx = updatedMapping)
    }

    // Proof scripts are generated by refinement, hence backwards.  Starting
    // from a goal in which all decompositions have already happened, one
    // transform_n step proves the current goal from a subgoal where exactly the
    // selected decomposed block is reverted to its original literal.  Other
    // decomposition blocks must stay in their current goal form.
    def revertForBackwardProof(stage: DetUniStage, task: DecompTask): DetUniStage = {
      val idx = stage.parent2currentIdx(task.info.OrigIdx)
      val updatedClause = stage.clauseLits.patch(idx, Seq(task.originalLit), task.replacementLits.length)
      val shift = task.replacementLits.length - 1
      val updatedMapping = stage.parent2currentIdx.map {
        case (origIdx, _) if origIdx == task.info.OrigIdx => origIdx -> idx
        case (origIdx, pos) if pos > idx => origIdx -> (pos - shift)
        case other => other
      }
      stage.copy(clauseLits = updatedClause, parent2currentIdx = updatedMapping)
    }

    val orderedDecomps = decompInfo.sortBy(info => currentStage.parent2currentIdx.getOrElse(info.OrigIdx, Int.MaxValue))

    val tasksE = orderedDecomps.foldLeft[Either[String, Vector[DecompTask]]](Right(Vector.empty)) {
      case (Left(err), _) => Left(err)
      case (Right(acc), info) => buildTask(info).map(task => acc :+ task)
    }

    tasksE match {
      case Left(err) => StageResult.Fail(err)
      case Right(tasks) =>
        // Construct the actual DetUniSimp child shape after all decomposition
        val targetStage = tasks.foldLeft(currentStage)(replaceForward)
        val scripts0 = targetStage.scripts :+ Comment("Verification of Decomp steps")

        // Build the proof in the reversed direction, i.e. each emitted transform_n step
        // consumes the current goal and leaves the next, less-decomposed subgoal.
        val proofResult = tasks.zipWithIndex.foldLeft[Either[String, (DetUniStage, Vector[LpProofScript])]](Right(targetStage, scripts0)) {
          case (Left(err), _) => Left(err)
          case (Right((proofGoalStage, scripts)), (task, taskIdx)) =>
            val idxInGoal = proofGoalStage.parent2currentIdx(task.info.OrigIdx)
            val sourceStage = revertForBackwardProof(proofGoalStage, task)
            // Instantiate Decomp_step/Decomp_single against the source clause:
            val instanciatedRules = stepwiseInstDecompRule(task.hd, task.lhsArgs, task.rhsArgs, task.fullTypeSpine, sourceStage.clauseLits, idxInGoal, task.binders, Name(s"Decomp_inst_${task.info.OrigIdx}"))
            val decompSteps = instanciatedRules.reverse.flatMap(rule => rule.setupScripts :+ Refine(Obj(rule.transformRule)))
            // Rewrites for implicit flips/normalisations
            val verifyInitialTransformationSteps = decompLitNormalisazion(task.info, 0, proofGoalStage.clauseLits.map(_.polarity), proofGoalStage.parent2currentIdx)
            // After one decomposition proof has fired, Lambdapi may expose list
            // constructors in the surrounding disjunction.  Normalize those away
            // before targeting another literal with a rewrite pattern.
            val simplifyDisj =
              if (taskIdx > 0 && verifyInitialTransformationSteps.nonEmpty) Vector(Repeat(Simplify(Seq(Name("disj")))))
              else Vector.empty
            Right((sourceStage, scripts ++ simplifyDisj ++ verifyInitialTransformationSteps ++ decompSteps))
        }

        proofResult match {
          case Left(err) => StageResult.Fail(err)
          case Right((_, scripts)) => StageResult.Ok(targetStage.copy(scripts = scripts))
        }
    }
  }

  /**
    * Result of generating local Lambdapi subproofs for a lifted decomp rule.
    *
    * `proofs` must be emitted before the transform_n step.
    * `finalRule` is the proof term that can be used as transform_n's rule proof.
    * `initialLit` and `derivedLits` describe the fully lifted rule:
    * π initialLit -> π (disj derivedLits)
    */
  final case class LiftedDecompRuleProofs(proofs: Vector[Have],
                                          finalRule: LpTerm[Level.Obj],
                                          initialLit: lpLiteralInst,
                                          derivedLits: Vector[lpLiteralInst])

  private final case class DecompRuleApplication(setupScripts: Vector[LpProofScript],
                                                 transformRule: LpTerm[Level.Obj])

  private def liftName(baseName: Name, liftedBinders: Seq[LpTerm.Var[Level.Obj]]): Name =
    Name(s"${baseName.value}_lift_${liftedBinders.map(_.name.value).mkString("_")}")

  /**
    * Generate local subproofs for a Decomp_step instance under leading binders.
    *
    * The first `have` removes all leading lambdas and replaces them by Π-bound variables.
    * Each following `have` reintroduces one lambda with `lift_decomp_step_binder`, from the
    * innermost binder outwards. The final proof term is suitable as the rule argument of
    * `transform_n`.
    *
    * @param resultTy The result type `b` of the body-level decomposition rule
    *                 `Decomp_step [a] [b] s t f g`.
    */
  def decompStepSubproofs(baseName: Name,
                          binders: Seq[LpTerm.Var[Level.Obj]],
                          argTy: OlMonoType,
                          resultTy: OlMonoType,
                          lhsArg: LpTerm[Level.Obj],
                          rhsArg: LpTerm[Level.Obj],
                          lhsFun: LpTerm[Level.Obj],
                          rhsFun: LpTerm[Level.Obj]): LiftedDecompRuleProofs = {
    val (basePremise, baseDerived) = LiftedDecompStepResult(Seq.empty, argTy, resultTy, lhsArg, rhsArg, lhsFun, rhsFun)
    val baseProofSteps =
      (if (binders.nonEmpty) Seq(Left(Assume(binders.map(_.name)))) else Seq.empty) :+
        Left(Refine(Obj(mkDecompStepObj(argTy, resultTy, lhsArg, rhsArg, lhsFun, rhsFun, None))))
    val baseHave = Have(baseName, lpTermBuilder.ruleType(binders, basePremise, baseDerived), baseProofSteps)

    val liftHaves = binders.indices.reverse.map { idx =>
      val currentBinder = binders(idx)
      val prefix = binders.take(idx)
      val alreadyLifted = binders.drop(idx + 1)
      val nowLifted = binders.drop(idx)
      val prevName = if (idx == binders.length - 1) baseName else liftName(baseName, alreadyLifted)
      val curName = liftName(baseName, nowLifted)

      val (premise, derived) = LiftedDecompStepResult(nowLifted, argTy, resultTy, lhsArg, rhsArg, lhsFun, rhsFun)

      val residualTy = lpTermBuilder.funTy(alreadyLifted, OlMonoType.Fun(Seq(argTy, resultTy)))
      val liftBinders = currentBinder +: alreadyLifted
      val liftRule = mkLiftDecompStepBinderObj(lpTermBuilder.olTy(currentBinder), lpTermBuilder.funTy(alreadyLifted, resultTy), residualTy, lpTermBuilder.funTy(alreadyLifted, argTy), lpTermBuilder.lam(liftBinders, lpTermBuilder.app(lhsFun, Seq(lhsArg))), lpTermBuilder.lam(liftBinders, lpTermBuilder.app(rhsFun, Seq(rhsArg))), lpTermBuilder.lam(liftBinders, lhsFun), lpTermBuilder.lam(liftBinders, rhsFun), lpTermBuilder.lam(liftBinders, lhsArg), lpTermBuilder.lam(liftBinders, rhsArg), Some(Wildcard[Level.Obj]()))

      val proofSteps =
        (if (prefix.nonEmpty) Seq(Left(Assume(prefix.map(_.name)))) else Seq.empty) :+
          Left(Refine(Obj(liftRule))) :+
          Left(Refine(Obj(lpTermBuilder.app(lpTermBuilder.localObj(prevName), prefix))))

      Have(curName, lpTermBuilder.ruleType(prefix, premise, derived), proofSteps)
    }.toVector

    val allProofs = baseHave +: liftHaves
    val finalName = if (binders.isEmpty) baseName else liftName(baseName, binders)
    val (finalPremise, finalDerived) = LiftedDecompStepResult(binders, argTy, resultTy, lhsArg, rhsArg, lhsFun, rhsFun)

    LiftedDecompRuleProofs(allProofs, lpTermBuilder.localObj(finalName), finalPremise, finalDerived)
  }

  /**
    * Generate local subproofs for a Decomp_single instance under leading binders.
    *
    * This mirrors `decompStepSubproofs`, but the generated rule has one derived
    * literal instead of the residual-function-literal plus argument-literal pair.
    *
    * @param resultTy The result type `b` of the body-level decomposition rule
    *                 `Decomp_single [a] [b] s t f`.
    */
  def decompSingleSubproofs(baseName: Name,
                            binders: Seq[LpTerm.Var[Level.Obj]],
                            argTy: OlMonoType,
                            resultTy: OlMonoType,
                            lhsArg: LpTerm[Level.Obj],
                            rhsArg: LpTerm[Level.Obj],
                            hd: LpTerm[Level.Obj]): LiftedDecompRuleProofs = {
    val (basePremise, baseDerived) = LiftedDecompSingleResult(Seq.empty, argTy, resultTy, lhsArg, rhsArg, hd)
    val baseProofSteps =
      (if (binders.nonEmpty) Seq(Left(Assume(binders.map(_.name)))) else Seq.empty) :+
        Left(Refine(Obj(mkDecompSingleObj(argTy, resultTy, lhsArg, rhsArg, hd, None))))
    val baseHave = Have(baseName, lpTermBuilder.ruleType(binders, basePremise, baseDerived), baseProofSteps)

    val liftHaves = binders.indices.reverse.map { idx =>
      val currentBinder = binders(idx)
      val prefix = binders.take(idx)
      val alreadyLifted = binders.drop(idx + 1)
      val nowLifted = binders.drop(idx)
      val prevName = if (idx == binders.length - 1) baseName else liftName(baseName, alreadyLifted)
      val curName = liftName(baseName, nowLifted)

      val (premise, derived) = LiftedDecompSingleResult(nowLifted, argTy, resultTy, lhsArg, rhsArg, hd)

      val liftBinders = currentBinder +: alreadyLifted
      val liftRule = mkLiftDecompSingleBinderObj(lpTermBuilder.olTy(currentBinder), lpTermBuilder.funTy(alreadyLifted, resultTy), lpTermBuilder.funTy(alreadyLifted, argTy), lpTermBuilder.lam(liftBinders, lpTermBuilder.app(hd, Seq(lhsArg))), lpTermBuilder.lam(liftBinders, lpTermBuilder.app(hd, Seq(rhsArg))), lpTermBuilder.lam(liftBinders, lhsArg), lpTermBuilder.lam(liftBinders, rhsArg), Some(Wildcard[Level.Obj]()))

      val proofSteps =
        (if (prefix.nonEmpty) Seq(Left(Assume(prefix.map(_.name)))) else Seq.empty) :+
          Left(Refine(Obj(liftRule))) :+
          Left(Refine(Obj(lpTermBuilder.app(lpTermBuilder.localObj(prevName), prefix))))

      Have(curName, lpTermBuilder.ruleType(prefix, premise, derived), proofSteps)
    }.toVector

    val allProofs = baseHave +: liftHaves
    val finalName = if (binders.isEmpty) baseName else liftName(baseName, binders)
    val (finalPremise, finalDerived) = LiftedDecompSingleResult(binders, argTy, resultTy, lhsArg, rhsArg, hd)

    LiftedDecompRuleProofs(allProofs, lpTermBuilder.localObj(finalName), finalPremise, finalDerived)
  }

  /**
    * Apply the Decomp rules for instances where only one single arguemnt is applied (i.e. litrals of the shape f x = f y)
    * This applies the Decomp literal and applies the transform literal to embed it in a bigger clause.
    *
    * @param curArgTy The type of the arguments (i.e. the type of x and y)
    * @param appliedHdTy The type of the head applied with the current argument (i.e. the type of f)
    * @param lArg The argument of the lhs (i.e. x)
    * @param rArg The argument of the lhs (i.e. y)
    * @param hd The head symbol (i.e. f)
    * @param initialLit The literal in the previous step to be replaced
    * @param clauseLhs A list of literals on the lhs of the literal to be changed
    * @param clauseRhs A list of literals on the rhs of the literal to be changed
    * @return The instanciated version of the decomp rule, applied to the transform rule if necessary
    */
  private def singleInstDecompRule(curArgTy: OlMonoType, appliedHdTy: OlMonoType, lArg: LpTerm[Level.Obj], rArg: LpTerm[Level.Obj], hd: LpTerm[Level.Obj], initialLit: lpLiteralInst, clauseLhs: Seq[lpLiteralInst], clauseRhs: Seq[lpLiteralInst], binders: Seq[LpTerm.Var[Level.Obj]], baseName: Name): DecompRuleApplication = {
    if (binders.isEmpty) {
      val instRule = mkDecompSingleObj(curArgTy, appliedHdTy, lArg, rArg, hd, None)
      val res = DecompSingleResult(curArgTy, lArg, rArg)
      DecompRuleApplication(Vector.empty, transform_n(initialLit, clauseLhs, clauseRhs, Seq(res), instRule, Wildcard[Level.Obj]()))
    } else {
      val liftedRule = decompSingleSubproofs(baseName, binders, curArgTy, appliedHdTy, lArg, rArg, hd)
      DecompRuleApplication(liftedRule.proofs, transform_n(initialLit, clauseLhs, clauseRhs, liftedRule.derivedLits, liftedRule.finalRule, Wildcard[Level.Obj]()))
    }
  }

  /**
    * Given a clause, isolate one literal and provide the literals before and after as lists
    *
    * @param currClause The literals of a given clause as a list
    * @param curPos The position of the literal in question
    * @return A tuple of the literal, a sequence of the literal on its lhs and another sequence of the literals on the rhs
    */
  def splitParentClause(currClause: Seq[lpLiteralInst], curPos: Int) = {
    assert(currClause.indices.contains(curPos), "Error in LP-Encoding: attemtpint to isolate literal but given index out of bounds")
    val l = currClause(curPos)
    val c0 = currClause.take(curPos)
    val c2 = currClause.takeRight(currClause.length - (curPos + 1))
    (l, c0, c2)
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
  private def stepwiseInstDecompRule(hd: LpTerm[Level.Obj], lArgs: Seq[LpTerm[Level.Obj]], rArgs: Seq[LpTerm[Level.Obj]], typeEls: Seq[OlMonoType], currClause: Seq[lpLiteralInst], curPos: Int, binders: Seq[LpTerm.Var[Level.Obj]], ruleNamePrefix: Name): Vector[DecompRuleApplication] = {
    val nArgs = lArgs.length
    val curArgTy = typeEls(nArgs - 1)

    // compute the type of the applied head
    val appliedHdTy0 = typeEls.takeRight(typeEls.length - nArgs)
    val appliedHdTy = if (appliedHdTy0.length == 1) appliedHdTy0.head else OlMonoType.Fun(appliedHdTy0)

    val lArg = lArgs.last
    val rArg = rArgs.last

    val (l, c0, c2) = splitParentClause(currClause, curPos)

    if (lArgs.length == 1) {
      // needs to apply rule for last step (or single occurrence)
      val instSingleDecompRule = singleInstDecompRule(curArgTy,appliedHdTy, lArg, rArg, hd, l, c0, c2, binders, Name(s"${ruleNamePrefix.value}_single"))

      Vector(instSingleDecompRule)

    } else {
      // needs to apply rule for step
      val lLeadingArgs = lArgs.init
      val rLeadingArgs = rArgs.init
      val lFun = LpTerm.App(hd, lLeadingArgs.map(arg => Arg.Explicit(arg)))
      val rFun = LpTerm.App(hd, rLeadingArgs.map(arg => Arg.Explicit(arg)))

      val (setupScripts, derivedLits, instRule) =
        if (binders.isEmpty) {
          val res = DecompStepRes(curArgTy, appliedHdTy, lArg, rArg, lFun, rFun)
          (Vector.empty, Vector(res._1,res._2), mkDecompStepObj(curArgTy, appliedHdTy, lArg, rArg, lFun, rFun, None))
        } else {
          val liftedRule = decompStepSubproofs(Name(s"${ruleNamePrefix.value}_step_$nArgs"), binders, curArgTy, appliedHdTy, lArg, rArg, lFun, rFun)
          (liftedRule.proofs, liftedRule.derivedLits, liftedRule.finalRule)
        }
      val instDecompRule = DecompRuleApplication(setupScripts, transform_n(l, c0, c2, derivedLits, instRule, Wildcard[Level.Obj]()))

      instDecompRule +: stepwiseInstDecompRule(hd, lLeadingArgs, rLeadingArgs, typeEls, c0 ++ derivedLits ++ c2, curPos, binders, ruleNamePrefix) // idx does not change because the hd stays on the lhs
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
    * @param goalLitPolarities    Clause literal polarities at the point where the rewrite is applied
    * @return Rewrite steps justifying transformations
    */
  private def decompLitNormalisazion(decompInfo: DecompInfo, alreadyAddedLitCount: Int, goalLitPolarities: Seq[Boolean], mapUpdatedPos: Map[Int,Int]): Vector[Rewrite] = {
    // first check if we need any additional transformations
    val impTransf = decompInfo.LitTransf.exists(t => t.flip || t.normalize.isDefined)
    if (impTransf) {
      Out.lp_debug_info(s"needed transformations: ${decompInfo.LitTransf}")
      val idxInGoal = mapUpdatedPos(decompInfo.OrigIdx)

      // transform the currently handled additional information
      Out.lp_debug_info(s"callsite 2")
      val addInfoAsLiteralTransformation = LiteralInfo2LiteralTransforamtion(decompInfo.LitTransf, idxInGoal + alreadyAddedLitCount)
      verifySubstitutionLiteralNormalisazion(addInfoAsLiteralTransformation, goalLitPolarities, goalLitPolarities.length).toVector
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

object PreUniVerification {

  import Util._

  // Orchestrator

  /**
    * encodePreUni — Outline of the encoded proof
    *
    * Proof structure in the Lambdapi encoding:
    *
    * 0) Assume free variables
    *    Introduce all free variables of the child clause.
    *
    * 1) Reconstruct the substituted parent
    *    Rebuild the parent clause with the shared reconstruction helper by
    *    applying the original PreUni substitution and the recorded literal
    *    transformations. This yields the clause before removing the tracked
    *    unification constraints and is used as the target type of the
    *    substitution subproof.
    *
    * 2) Substitution subproof
    *    Instantiate the encoded parent proof with the substitution terms.
    *    Any recorded implicit literal transformations are delegated to the
    *    shared substitution encoder, which emits the corresponding rewrite
    *    steps before refining with the instantiated parent proof.
    *
    * 3) Constraint-elimination subproof
    *    The tracked deleted constraints are expected to be trivially false
    *    after substitution. Turn them into ⊥ using the shared remove-trivial-
    *    false tactic, then remove them from the disjunction via deleteBots.
    *
    * 4) Composition
    *    Compose the removal proof with the substitution proof using eqImp,
    *    yielding a proof of the child clause from the original parent.
    *
    * Limitations / Notes:
    *   - The encoding is structural: unsupported PreUni modes should fail
    *     through the reconstruction and deletion-shape checks rather than
    *     through a mode-name whitelist.
    *   - Type unification is not encoded.
    *   - Residual flex-flex literals are not encoded here; if PreUni produces
    *     new flex-flex constraints, the reconstructed post-deletion parent may
    *     not have the same literal shape as the child.
    *     
    * This is the new-datastructure counterpart of `ModularProofEncoding.encPreUni`.
    *
    * @return encoded proof script or an explanatory NotEncodable result
    */
  def encodePreUni(parent: ClauseProxy, child: ClauseProxy, parentNameLpEnc0: Name, sig: LpSig): EncodeResult = {
    val ro = RenderOptions()

    ////////////////////////////
    // Encodings and prelim

    val addInfoUni = child.furtherInfo.addInfoUni
    val addInfoUniRule = child.furtherInfo.addInfoUniRule
    val mode = addInfoUniRule._1
    Out.lp_debug_info(s"Encoding instance of PreUni, mode: ${if (mode.nonEmpty) mode else "<unset>"}")

    val UnificationEncoding.UniCtx(termSubst, typeSubst, deletedUniLits, litTransf) = UnificationEncoding.initUniCtxt(addInfoUni)

    if (typeSubst.nonEmpty) {
      return NotEncodable("LP encoding of type unification not encoded yet")
    }
//    if (termSubst.isEmpty) {
//      return NotEncodable("no term unifications to encode")
//    }

    val ctxt = initUniRuleCtxt(child.cl, parent.cl, parentNameLpEnc0)
    val EncUniCtx(encChild, encParent, _, _, childVarNames, _, _) = ctxt
    Out.lp_debug_info(s"parent: ${Renderer.ty(encParent.asMl, ro, sig)}")
    Out.lp_debug_info(s"proving ${Renderer.ty(encChild.asMl, ro, sig)}")

    if (deletedUniLits.isEmpty) {
      return NotEncodable("PreUni did not track any deleted unification constraints")
    }

    val deletePositions = deletedUniLits.map(_.position)

    Out.lp_debug_info(s"Unification literal positions in original clause: $deletePositions")

    val childToParentIdx = childToSubstitutedParentIdx(parent.cl.lits.length, deletePositions, encChild.lits.length) match {
      case Left(reason) => return NotEncodable(reason)
      case Right(idxMap) => idxMap
    }
    val childToParentIdxDefault = childToParentIdx.withDefault(identity)

    // Literal transformations are tracked relative to the child clause.
    // Reindex them to reconstruct the substituted parent before deletion.
    val substParentLitTransf = reindexLiteralTransformation(litTransf, childToParentIdxDefault)

    // Reconstruct the parent after PreUni substitution, but before deleting constraints.
    val normalizedSubstParent = reconstructSubstParent(addInfoUni.origTermSubst, addInfoUni.origTypeSubst, substParentLitTransf, ctxt, parent.cl) match {
      case Some(lits) => lits
      case None => return NotEncodable("Trying to encode PreUni substitution substep, error when reconstructing substituted parent")
    }

    ////////////////////////////
    // 0) Assume free variables
    val assumeStep = encAssumeStep(childVarNames)

    ////////////////////////////
    // 1) Substitution subproof
    val nameHaveSubstStep = Name("Substitution")
    val (substStepName, substStep) =
      encodeSubstitutionSubstep(nameHaveSubstStep, ctxt, termSubst, litTransf, normalizedSubstParent, child.cl.implicitlyBound, parent.cl.implicitlyBound, childToParentIdxDefault)

    ////////////////////////////
    // 2) Constraint-elimination subproof
    val nameHaveRemoveStep = Name("RemoveUniConst")
    val haveRemoveStep = constructRemoveStep(nameHaveRemoveStep, normalizedSubstParent, encChild.lits, deletePositions)

    ////////////////////////////
    // 3) Composition in final refine step
    val appliedRemoveStep = applyRemoveStep(nameHaveRemoveStep, substStepName)

    Encoded((assumeStep ++ substStep) :+ haveRemoveStep :+ Refine(Obj(appliedRemoveStep)))
  }

  // Helpers for tracked unification-constraint deletion

  /**
    * Compute how child-clause literal positions embed into the substituted parent.
    *
    * PreUni tracks deleted unification constraints as `UniLitInfo`, with
    * positions in the parent before deletion. The substitution proof, however,
    * receives literal-transformation metadata in child positions. This helper
    * builds the required child-position to parent-position map.
    *
    * Limitation: If the remaining parent positions do not match the child length, PreUni
    * produced a different literal shape, for example by adding residual
    * flex-flex constraints. That case is not currently encoded.
    *
    * @param parentLen       Number of literals in the parent clause
    * @param deletePositions Parent positions deleted by PreUni
    * @param childLen        Number of literals in the child clause
    * @return map from child literal positions to reconstructed-parent positions
    */
  private def childToSubstitutedParentIdx(parentLen: Int, deletePositions: Seq[Int], childLen: Int): Either[String, Map[Int, Int]] = {
    val deleteSet = deletePositions.toSet
    val remainingParentPositions = (0 until parentLen).filterNot(deleteSet)

    if (deletePositions.exists(pos => pos < 0 || pos >= parentLen)) {
      Left(s"PreUni tracked deleted literal positions out of bounds: $deletePositions")
    } else if (remainingParentPositions.length != childLen) {
      Left("PreUni with residual flex-flex literals is not encoded yet")
    } else {
      Right(remainingParentPositions.zipWithIndex.map { case (parentIdx, childIdx) => childIdx -> parentIdx }.toMap)
    }
  }
}
