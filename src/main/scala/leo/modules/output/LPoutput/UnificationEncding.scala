package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Clause.{effectivelyEmpty, vars}
import leo.datastructures.{Clause, ClauseProxy, LitNorm, Literal, LiteralTransformation, Multiset, Type, UniLitInfo, UniTermRhs, UniTermSubst, UniTypeSubst}
import leo.modules.output.LPoutput.LpLibs.EqRules.AsTerms._
import leo.modules.output.LPoutput.LpLibs.LeoTactics.EvalApp.removeBot
import leo.modules.output.LPoutput.LpLibs.MetaTheorems.Inst.deleteBots
import leo.modules.output.LPoutput.LpLibs.ND.Terms._
import leo.modules.output.LPoutput.NewLpDatastructures.ClauseEncoding.lit2Lp
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Assume, Have, Refine, Reflexivity, Rewrite, RewritePattern, Side}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Obj, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.Prf
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, HolBaseTypes, Level, LogicConst, LpProofScript, LpSig, LpTerm, LpType, Name, OlType, QName, RenderOptions, Renderer, SymRef, lpClauseInst, nAry}

object UnificationEncding {

  import leo.datastructures.{UniTermByBoundVar, UniTermByTerm}

  /**
    * Wrapper for additional information concerning the properties of the literal necessary to generate rewrite pattern for entire clauses
    * @param position The index of the literal in the clause
    * @param sideIfEq Indicates if the pattern is supposed to only target one side of an equational literal.
    *                 None => Literal is targeted as a whole
    *                 Some(Side.Left) / Some(Side.Right) => The pattern will target the specific side
    * @param polarity Indicates if the pattern is supposed to only target the body of a literal with negative polarity
    *                 True: Polarity is positive or entire (potentially negated) literal should be targeted
    *                 False: Literal is negative and pattern should target the body only.
    */
  case class PatternInfo(position: Int,
                         sideIfEq: Option[(Side, OlType)],
                         polarity: Boolean)

  /**
    * Generator for pattern-terms targeting specific sub-structures of Literals.
    *
    * @param info Wrapped information regarding the sub-structures to be targeted
    * @param hole Shape of the term to be used as a whole, typically a pattern variable like "x"
    * @return A term to be used to construct a rewrite pattern for the Lambdapi rewrite-tactic
    */
  def generatePatternLit(info: PatternInfo, hole: LpTerm[Level.Obj]): LpTerm[Level.Obj] = {
    val maybeEqLit = if (info.sideIfEq.isDefined) info.sideIfEq.get match {
      case (Side.Left, ty) => LogicConst.Eq(ty, Wildcard[Level.Obj], hole)
      case (Side.Right, ty) => LogicConst.Eq(ty, hole, Wildcard[Level.Obj])
    } else hole
    if (info.polarity) maybeEqLit else LogicConst.Not(maybeEqLit)
  }

  /**
    * Generator for patterns to be used for the Lambdapi rewrite-tactic to target specific literals or sub-structures thereof in a clause.
    *
    * @param termPosSeq Sequence of wrapped information for each literal to be targeted (defining the index and the the sub-structures of interest)
    * @param clauseLen Number of literals in the clause the pattern is generated for
    * @return A rewrite pattern to be used to instansiate the Lambdapi rewrite-tactic
    */
  def generateClausePattern(termPosSeq: Seq[PatternInfo], clauseLen: Int): RewritePattern = {
    val patternVar = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("x")))
    val maxTermPos = termPosSeq.map(_.position).max
    assert(maxTermPos < clauseLen, s"Error in Lambdapi encoidng when generating a pattern: Literal index (${maxTermPos} out of bounds for clause of length $clauseLen)")
    var args: Seq[LpTerm[Level.Obj]] = Seq.fill(clauseLen)(Wildcard[Level.Obj])
    termPosSeq foreach { pos =>
      args = args.updated(pos.position, generatePatternLit(pos,patternVar))
    }
    RewritePattern(nAry.disjunction(args), patternVar)
  }

  /** Enclose the pattern given in a Lambdapi-Rewrite-Pattern in an equality, useful when proving steps like "clause A = Clause B" */
  def embedPatternInEq(pat: RewritePattern, side: Side): RewritePattern = {
    val term = pat.LpTerm
    val embTerm = side match {
      case Side.Left => LogicConst.Eq(HolBaseTypes.O, term, Wildcard[Level.Obj])
      case Side.Right => LogicConst.Eq(HolBaseTypes.O, Wildcard[Level.Obj], term)
    }
    RewritePattern(embTerm, pat.hole)
  }

  // go over the additional information provided for the substitutions applied and - based on it - construct terms to be applied to the parent clause in the LP encoding
  def encodeUniInfo(termUni: UniTermRhs, childVars: Seq[Int], sharedVarMap: Map[Int, String], mapping: Map[Int, leo.datastructures.Type]): Arg[Level.Obj] = {
    termUni match {
      case UniTermByBoundVar(targetIndex) =>
        // confusingly, this only references pre-existing variables, fresh ones are also counted as terms here...
        if (childVars.contains(targetIndex)) {
          Out.lp_debug_info(s"bind by variable with index $targetIndex")
          val encVar = Const[Level.Obj](SymRef.LP(QName.local(sharedVarMap(targetIndex)))) //todo: this is not nice
          Arg.Explicit(encVar)
        } else {
          Out.lp_debug_info(s"creating a witness term for variable of scope $targetIndex")
          val ty = mapping(targetIndex)
          val freshWitness = LpTerm.App[Level.Obj](lpWitnessCon, Seq(Arg.ExplicitTypeArg(type2LP(ty))))
          Arg.Explicit(freshWitness)
        }

      case UniTermByTerm(term, b, c) =>
        Out.lp_debug_info(s"using var map: $sharedVarMap, proposed map: $c")
        val encTargetTerm = term2LP(term, sharedVarMap, false, true)
        Out.lp_debug_info(s"bind by term $encTargetTerm} (aka ${term.pretty})")
        Arg.Explicit(encTargetTerm)
    }
  }

  // generate the rewrite rules necessary to verify normalisazion by reverse-engineering
  // goalLits = child.cl.lits
  def verifyLiteralNormalisazion(addInfo: LiteralTransformation, old2NewIdx: Map[Int, Int], goalLits: Seq[Literal], clauseLen: Int) = {

    def generatePatternInfo(id: Int) = PatternInfo(old2NewIdx.getOrElse(id, id), None, goalLits(id).polarity)

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
        val pattern = generateClausePattern(Seq(patternInfo), clauseLen)
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
      val flipPattern = generateClausePattern(flipInfo, clauseLen)

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

  final case class EncParaCtx(encChild: lpClauseInst, encParent: lpClauseInst, sharedVarMap: Map[Int, String], childVarMap: Map[Int, String], parentNameLpEnc: LpTerm[Level.Obj],substClauseLen: Int)

  def initCtxt(childCl: Clause, parentCl: Clause, parentNameLpEnc0: Name): EncParaCtx = {

    //todo: do any checks here?

    // translation of the clauses
    val (sharedVarMap, encClauses) = lpClauseInst.apply_to_set(Seq(childCl, parentCl))

    // compute names and clause length
    val parentNameLpEnc: LpTerm[Level.Obj] = Const(SymRef.LP(QName.local(parentNameLpEnc0.value)))
    val substClauseLen = parentCl.lits.length

    // filter out only the vars relevant to the child
    val childVarMap = sharedVarMap.view.filterKeys(vars(childCl).distinct).toMap

    EncParaCtx(encClauses(0), encClauses(1), sharedVarMap, childVarMap, parentNameLpEnc, substClauseLen)
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

  def encodePatternUni(parent: ClauseProxy,child: ClauseProxy, parentNameLpEnc0: Name, sig:LpSig): Seq[LpProofScript] = {
    Out.lp_debug_info(s"Encoding instance of Pattern Unification")
    //todo only do substitution step if we actually have subst, sometimes we can also have trivial stuff
    val ro = RenderOptions()

    // set up context
    val ctxt = initCtxt(child.cl,parent.cl,parentNameLpEnc0)
    val EncParaCtx(encChild, encParent, sharedVarMap, childVarMap, parentNameLpEnc, substClauseLen) = ctxt
    Out.lp_debug_info(s"proving ${Renderer.ty(encChild.asMl, ro, sig)}")
    Out.lp_debug_info(s"parent: ${Renderer.ty(encParent.asMl, ro, sig)}")

    val uniCtxt = initUniCtxt(child)
    val UniCtx(termSubst,typeSubst,deletedUniLits,litTransf) = uniCtxt

    // frist assume the variables
    val (assumeStep, childVarNames) = encPatternUniAssume(encChild, sharedVarMap, vars(child.cl).distinct)

    // construct the parent post substitution but prior to the deletion of the literals
    // and a mapping of the child literal indeces to the ones in this parent
    val (encSubstParent, old2NewIdx) : (LpTerm[Level.Obj], Map[Int,Int]) = if (deletedUniLits.nonEmpty){
      reconstructSubstUniParent(deletedUniLits,encChild,childVarMap)
    } else throw new Exception(s"wrong unmber of unification literals: ${deletedUniLits.length}.")

    Out.lp_debug_info(s"old2newMap = $old2NewIdx")

    // construct the actual proof
    if (typeSubst.nonEmpty){
      // todo: explicitly return an unencoded step here
      // cant encode type subst yet
      Seq()

    }else{
      // based on the additional information, construct the terms in the lambdapi encoidng that need to be applied to the parent to verify the substitution
      // this is a mapping of the id of the free variable to the encoded term that it is instanciated with
      val termToApply: Map[Int, Arg[Level.Obj]] =
        termSubst.foldLeft(Map.empty[Int, Arg[Level.Obj]]) {(acc, termUni) =>
          val lpUnboundVar = termUni.sourceIndex
          val encSubstTerm = encodeUniInfo(termUni.rhs, child.cl.implicitlyBound.map(_._1), sharedVarMap.view.filterKeys(child.cl.implicitlyBound.map(_._1).contains(_)).toMap, parent.cl.implicitlyBound.toMap)
          acc + (lpUnboundVar -> encSubstTerm)
        }

      // construct the application
      Out.lp_debug_info(s"vars of parent: ${parent.cl.implicitlyBound.map(_._1)}")
      Out.lp_debug_info(s"vars of child: ${child.cl.implicitlyBound.map(_._1)}")
      val (maybeSubstStepName, maybeSubstStep): (LpTerm[Level.Obj], Seq[Have]) = if (termToApply.nonEmpty) {
        // todo: should i not instead test for the non-emptiness of parent.cl.implicitlyBound ?

        // detect potential flipping of literals that may be necessary in this step
        val maybeFlipStep: Seq[Rewrite] = verifyLiteralNormalisazion(litTransf,old2NewIdx,child.cl.lits,substClauseLen)
        // construct the refine step carrying out the substitution
        val refineStep = constructSubstStep(parent.cl.implicitlyBound, child.cl.implicitlyBound, termToApply, maybeFlipStep, sharedVarMap, parentNameLpEnc)

        // have substitution step
        val nameSubst = Name("Subst") // todo: add to names to keep safe, maybe make them parameters of the class
        val haveSubstStep = Have(nameSubst, Prf(encSubstParent), (maybeFlipStep :+ refineStep).map(Left(_)))

        (Const[Level.Obj](SymRef.LP(QName.local(nameSubst.value))), Seq(haveSubstStep))

      } else (LpTerm.App(parentNameLpEnc,childVarNames.map(varName => Arg.Explicit(LpTerm.Var(varName,None)))), Seq.empty)

      // construct step proving the removal

      // as Leo never applies the substitution to the actual unification lit - but we need to do so in order to justify its removal - we need to apply it and reconstruct
      // the clause at this point of the proof explicitly

      // prove that the substituted clause implies the one with the litearal removed
      val nameHaveRemoveStep = Name("RemoveUniConst")

      val haveRemoveStep = constructRemoveStep(nameHaveRemoveStep, encSubstParent, encChild.lits, deletedUniLits, substClauseLen, child.cl)

      val lastStep = LpTerm.App(Obj(eqImp),Seq(Arg.Explicit[Level.Meta](Const(SymRef.LP(QName.local(nameHaveRemoveStep.value)))),Arg.Explicit[Level.Meta](Obj(maybeSubstStepName))))

      ((assumeStep ++ maybeSubstStep) :+ haveRemoveStep) :+ Refine(lastStep)
    }
  }

  private def constructRemoveStep(nameHaveRemoveStep: Name, encSubstParent: LpTerm[Level.Obj], encChildLits: Seq[LpTerm[Level.Obj]], deletedUniLits: Seq[UniLitInfo],  substClauseLen: Int, childCl: Clause
                                 ) = {
    val impToProve = Prf(LogicConst.Eq(HolBaseTypes.O, encSubstParent, nAry.disjunction(encChildLits)))
    val proofScript: Seq[LpProofScript] = deletedUniLits.map(litInfo => {
      Out.lp_debug_info(s"orig pos is ${litInfo.position}")
      val posInSubs = litInfo.position
      val patternLitInfo = PatternInfo(posInSubs, None, true)
      val pattern = generateClausePattern(Seq(patternLitInfo), substClauseLen)
      val embeddedPattern = embedPatternInEq(pattern, Side.Left)
      removeBot(embeddedPattern)
    })
    val finalStep = if ((effectivelyEmpty(childCl)) && childCl.lits.length == 1) Reflexivity else Refine(deleteBots(encChildLits, deletedUniLits.map(_.position).sorted))
    Have(nameHaveRemoveStep, impToProve, (proofScript :+ finalStep).map(step => Left(step)))
  }

}
