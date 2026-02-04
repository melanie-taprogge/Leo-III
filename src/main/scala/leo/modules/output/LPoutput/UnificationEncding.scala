package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Clause.{effectivelyEmpty, vars}
import leo.datastructures.{Clause, ClauseProxy, LitNorm, Literal, LiteralTransformation, Multiset, Type, UniLitInfo, UniTermRhs, UniTermSubst, UniTypeSubst}
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.LpLibs.EqRules.AsTerms._
import leo.modules.output.LPoutput.LpLibs.LeoTactics.EvalApp.removeBot
import leo.modules.output.LPoutput.LpLibs.MetaTheorems.Inst.deleteBots
import leo.modules.output.LPoutput.LpLibs.ND.Terms._
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.ClauseEncoding.lit2Lp
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Assume, Have, Refine, Reflexivity, Rewrite, RewritePattern, Side}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Obj, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.Prf
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, HolBaseTypes, Level, LogicConst, LpProofScript, LpSig, LpTerm, LpType, Name, OlType, QName, RenderOptions, Renderer, SymRef, lpClauseInst, nAry}
import leo.datastructures.{UniTermByBoundVar, UniTermByTerm}

object UnificationEncding {

  final case class EncUniCtx(encChild: lpClauseInst, encParent: lpClauseInst, sharedVarMap: Map[Int, String], childVarMap: Map[Int, String], parentNameLpEnc: LpTerm[Level.Obj],substClauseLen: Int)

  /**
    * encodePatternUni — Outline of the encoded proof (pattern unification)
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

    // construct the parent post-substitution (but prior to the deletion of the literals) and a mapping of the child literal indeces to the ones in this parent
    val (encSubstParent, old2NewIdx): (LpTerm[Level.Obj], Map[Int, Int]) = reconstructSubstUniParent(deletedUniLits, encChild, childVarMap)


    ////////////////////////////
    // 0) Assume free variables
    val (assumeStep, childVarNames) = encPatternUniAssume(encChild, sharedVarMap, vars(child.cl).distinct)

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
  def encodeUniInfo(termUni: UniTermRhs, childBoundIndices: Seq[Int], sharedVarMap: Map[Int, String], bndIdxToType: Map[Int, leo.datastructures.Type]): Arg[Level.Obj] = {
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
        val encTargetTerm = term2LP(term, sharedVarMap, false, true)
        Out.lp_debug_info(s"bind by term $encTargetTerm}")
        Arg.Explicit(encTargetTerm)
    }
  }

  // generate the rewrite rules necessary to verify normalisazion by reverse-engineering
  // goalLits = child.cl.lits
  def verifyLiteralNormalisazion(addInfo: LiteralTransformation, old2NewIdx: Map[Int, Int], goalLits: Seq[Literal], clauseLen: Int) = {

    def generatePatternInfo(id: Int) = PatternBuilder.PatternInfo(old2NewIdx.getOrElse(id, id), None, goalLits(id).polarity)

    var newFlipSteps: Seq[Int] = Seq.empty
    val maybeNormalizeSteps: Seq[Rewrite] = if (addInfo.normalizedEq.nonEmpty) {
      Out.lp_debug_info(s"need to normalize: ${addInfo.normalizedEq}")
      addInfo.normalizedEq.map { pair =>
        val (pos, normMode) = pair
        val rule: LpTerm[Level.Meta] = normMode match {
          case LitNorm.TopL => newFlipSteps = newFlipSteps :+ pos; lpSimp_eqTop
          case LitNorm.TopR => lpSimp_eqTop
          case LitNorm.BotL => newFlipSteps = newFlipSteps :+ pos; lpSimp_eqBot
          case LitNorm.BotR => lpSimp_eqBot
        }
        val patternInfo = generatePatternInfo(pos)
        val pattern = PatternBuilder.generateClausePattern(Seq(patternInfo), clauseLen)
        Rewrite(Some(pattern),rule,Side.Left)
      }
    } else Seq.empty

    // sanity check: we ony need to flip literals that are equational and we only need to rewrite literals to an euational form if they are non-equational. Therefore, there can never be an overlap between the two
    assert(addInfo.flippedLits.intersect(newFlipSteps).isEmpty, s"Error in Lambdapi Encoding: Trying to verify literal-normalisazion, but found contradicroty input (${addInfo.flippedLits.intersect(newFlipSteps)})")

    val allFlipSteps = (addInfo.flippedLits ++ newFlipSteps).sorted

    val maybeFlipStep: Seq[Rewrite] = if (allFlipSteps.nonEmpty) {
      Out.lp_debug_info(s"the following literals need to be flipped: ${allFlipSteps}") //todo: kann es sein, dass auch das abgespeicherte uni lit geflippt wurde? in dem fall muss ich die Operation umkehren
      // the indices refer to the positions of the literals in the child, as we re-inserted the uni Lits, we may need to shift them
      val flipInfo = allFlipSteps.map(generatePatternInfo)
      val flipPattern = PatternBuilder.generateClausePattern(flipInfo, clauseLen)

      Seq(Rewrite(Some(flipPattern), eqSym))
    } else Seq.empty

    (maybeNormalizeSteps ++ maybeFlipStep)
  }
  
  // general mode of encoding: apply substitution, show that unification literal is now trivially false, remove it

  private def assumeVars(encChild: lpClauseInst): Seq[Name] = {
    encChild.vars.map(var0 => var0 match {
      case Left(olVar) => olVar.name
      case Right(tyVar) => throw new Exception(s"Error in Lambdapi Encoding: Encountered unexpected TyVar, Poymorphism not yet encoded")
    })
  }
  private def encPatternUniAssume(encChild: lpClauseInst, varMap: Map[Int, String], childVars: Set[Int]): (Seq[LpProofScript], Seq[Name]) = {
    if (encChild.vars.nonEmpty) {
      val varNames = assumeVars(encChild)
      (Seq(Assume(varNames)), varNames)
    } else (Seq.empty, Seq.empty)
  }

  def initCtxt(childCl: Clause, parentCl: Clause, parentNameLpEnc0: Name): EncUniCtx = {

    //todo: do any checks here?

    // translation of the clauses
    val (sharedVarMap, encClauses) = lpClauseInst.apply_to_set(Seq(childCl, parentCl))

    // compute names and clause length
    val parentNameLpEnc: LpTerm[Level.Obj] = Const(SymRef.LP(QName.local(parentNameLpEnc0.value)))
    val substClauseLen = parentCl.lits.length

    // filter out only the vars relevant to the child
    val childVarMap = sharedVarMap.view.filterKeys(vars(childCl).distinct).toMap

    EncUniCtx(encClauses(0), encClauses(1), sharedVarMap, childVarMap, parentNameLpEnc, substClauseLen)
  }

  final case class UniCtx(termSubst: Seq[UniTermSubst],typeSubst: Seq[UniTypeSubst],deletedUniLits: Seq[UniLitInfo], litTransf: LiteralTransformation)

  def initUniCtxt(child:ClauseProxy)={
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
        val encNewLit = lit2Lp(newUniLit.literal, childVarMap, true, true)
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

    (nAry.disjunction(newLits), old2NewIdx)
  }


  private def constructSubstStep(parentVars: Seq[(Int, Type)], childVars: Seq[(Int, Type)], termToApply: Map[Int, Arg[Level.Obj]], maybeFlipStep: Seq[Rewrite], sharedVarMap: Map[Int, String], parentNameLpEnc: LpTerm[Level.Obj]): Refine = {
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

  private def encodeSubstitutionSubstep(ctxt: EncUniCtx, termSubst: Seq[UniTermSubst], litTransf: LiteralTransformation, old2NewIdx: Map[Int, Int], childVarNames: Seq[Name], encSubstParent: LpTerm[Level.Obj], childCl: Clause, parentImpB : Seq[(Int, Type)]):(LpTerm[Level.Obj], Seq[Have]) = {
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

      // detect potential flipping of literals that may be necessary in this step
      val maybeFlipStep: Seq[Rewrite] = verifyLiteralNormalisazion(litTransf, old2NewIdx, childCl.lits, ctxt.substClauseLen)
      // construct the refine step carrying out the substitution
      val refineStep = constructSubstStep(parentImpB, childCl.implicitlyBound, termToApply, maybeFlipStep, ctxt.sharedVarMap, ctxt.parentNameLpEnc)

      // have substitution step
      val nameSubst = Name("Subst") // todo: add to names to keep safe, maybe make them parameters of the class
      val haveSubstStep = Have(nameSubst, Prf(encSubstParent), (maybeFlipStep :+ refineStep).map(Left(_)))

      (Const[Level.Obj](SymRef.LP(QName.local(nameSubst.value))), Seq(haveSubstStep))

    } else (LpTerm.App(ctxt.parentNameLpEnc, childVarNames.map(varName => Arg.Explicit(LpTerm.Var(varName, None)))), Seq.empty)
  }

  private def constructRemoveStep(nameHaveRemoveStep: Name, encSubstParent: LpTerm[Level.Obj], encChildLits: Seq[LpTerm[Level.Obj]], deletedUniLits: Seq[UniLitInfo],  substClauseLen: Int, childCl: Clause
                                 ) = {
    val impToProve = Prf(LogicConst.Eq(HolBaseTypes.O, encSubstParent, nAry.disjunction(encChildLits)))
    val proofScript: Seq[LpProofScript] = deletedUniLits.map(litInfo => {
      Out.lp_debug_info(s"orig pos is ${litInfo.position}")
      val posInSubs = litInfo.position
      val patternLitInfo = PatternBuilder.PatternInfo(posInSubs, None, true)
      val pattern = PatternBuilder.generateClausePattern(Seq(patternLitInfo), substClauseLen)
      val embeddedPattern = PatternBuilder.embedPatternInEq(pattern, Side.Left)
      removeBot(embeddedPattern)
    })
    val finalStep = if ((effectivelyEmpty(childCl)) && childCl.lits.length == 1) Reflexivity else Refine(deleteBots(encChildLits, deletedUniLits.map(_.position).sorted))
    Have(nameHaveRemoveStep, impToProve, (proofScript :+ finalStep).map(step => Left(step)))
  }

}
