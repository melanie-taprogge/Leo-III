package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Clause.{effectivelyEmpty, vars}
import leo.datastructures.Literal.asTerm
import leo.datastructures.{Clause, ClauseProxy, LitNorm, Literal, LiteralInfo, LiteralTransformation, UniTermRhs}
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
  def encodePatternUni(parent: ClauseProxy,child: ClauseProxy, parentNameLpEnc0: Name, sig:LpSig)={
    Out.lp_debug_info(s"Encoding instance of Pattern Unification")
    //todo only do substitution step if we actually have subst, sometimes we can also have trivial stuff
    val ro = RenderOptions()
    val parentNameLpEnc: LpTerm[Level.Obj] = Const(SymRef.LP(QName.local(parentNameLpEnc0.value)))

    // encode the parents
    val (sharedVarMap, encClauses) = lpClauseInst.apply_to_set(Seq(child.cl,parent.cl))
    val encChild = encClauses(0)
    val encParent = encClauses(1)

    val substClauseLen = parent.cl.lits.length

    var allProofSteps: Seq[LpProofScript] = Seq.empty

    // frist assume the variables
    val (assumeStep, childBvars, childVarNames): (Seq[LpProofScript], Map[Int,String], Seq[Name]) = if (encChild.vars.nonEmpty){
      val varNames = encChild.vars.map(var0 => var0 match {
        case Left(olVar) => olVar.name
        case Right(tyVar) => throw new Exception(s"Error in Lambdapi Encoding: Encountered unexpected TyVar, Poymorphism not yet encoded")
      })
      (Seq(Assume(varNames)), sharedVarMap.view.filterKeys(vars(child.cl).distinct).toMap, varNames)
    }else (Seq.empty, Map.empty, Seq.empty)

    allProofSteps = allProofSteps ++ assumeStep

    Out.lp_debug_info(s"proving ${Renderer.ty(encChild.asMl,ro,sig)}")
    Out.lp_debug_info(s"parent: ${Renderer.ty(encParent.asMl,ro,sig)}")

    val addInfo = child.furtherInfo.addInfoUni
    Out.lp_debug_info(s"subst non empty? ${addInfo.subst.termSubsts.nonEmpty || addInfo.subst.typeSubsts.nonEmpty}")

    //extract the substitutions
    val termSubst = addInfo.subst.termSubsts
    val typeSubst = addInfo.subst.typeSubsts
    val deletedUniLits = addInfo.uniLits

    val uniRle = child.furtherInfo.addInfoUniRule

    Out.lp_debug_info(s"set mode? ${uniRle._1}")


    val (encSubstParent, old2NewIdx) : (LpTerm[Level.Obj], Map[Int,Int]) = if (deletedUniLits.nonEmpty){
      Out.lp_debug_info(s"found ${deletedUniLits.length} unification literal(s):")
      val sortedInsertLits = deletedUniLits.sortBy(_.position)
      val newLits = sortedInsertLits.foldLeft(encChild.lits) {
        case (acc, newUniLit) =>
          val encNewLit = lit2Lp(newUniLit.literal,childBvars,true,true)
          Out.lp_debug_info(s"- at position ${newUniLit.position}: (${Renderer.termP(encNewLit,ro,0,sig)})")
          acc.patch(newUniLit.position, Seq(encNewLit), 0)
      }

      val needEta = (Clause.asTerm(child.cl).etaContract != Clause.asTerm(child.cl))

      Out.lp_debug_info(s"needsEta? $needEta")

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
    } else throw new Exception(s"wrong unmber of unification literals: ${deletedUniLits.length}.")//nAry.disjunction(encChild.lits)

    Out.lp_debug_info(s"old2newMap = $old2NewIdx")

    // construct the actual proof


    if (typeSubst.nonEmpty){
      // cant encode type subst yet

    }else{
      // based on the additional information, construct the terms in the lambdapi encoidng that need to be applied to the parent to verify the substitution
      val termToApply: Map[Int, Arg[Level.Obj]] =
        termSubst.foldLeft(Map.empty[Int, Arg[Level.Obj]]) {(acc, termUni) =>
          val lpUnboundVar = termUni.sourceIndex
          val encSubstTerm = encodeUniInfo(termUni.rhs, child.cl.implicitlyBound.map(_._1), sharedVarMap.view.filterKeys(child.cl.implicitlyBound.map(_._1).contains(_)).toMap, parent.cl.implicitlyBound.toMap)
          acc + (lpUnboundVar -> encSubstTerm)
        }

      // construct the application
      Out.lp_debug_info(s"vars of parent: ${parent.cl.implicitlyBound.map(_._1)}")
      Out.lp_debug_info(s"vars of child: ${child.cl.implicitlyBound.map(_._1)}")
      val maybeSubstStepName: LpTerm[Level.Obj] = if (termToApply.nonEmpty) {
        val orderedTerms: Seq[Arg[Level.Obj]] = parent.cl.implicitlyBound.map(id =>
          if (termToApply.keySet.contains(id._1)) termToApply(id._1)
          else if (child.cl.implicitlyBound.contains(id)) Arg.Explicit(var2Lp(id._1, id._2, sharedVarMap))
          else Arg.Explicit(LpTerm.App(lpWitnessCon, Seq(Arg.ExplicitTypeArg(type2LP(id._2))))))
        val appliedParentName = if (termToApply.nonEmpty) LpTerm.App(parentNameLpEnc, orderedTerms) else parentNameLpEnc

        // have substitution step
        val nameSubst = Name("Subst") // todo: add to names to keep safe, maybe make them parameters of the class
        // detect potential flipping of literals that may be necessary in this step

        Out.lp_debug_info(s"need to normalize: ${addInfo.literalTransformations.normalizedEq}")

        /*
        val maybeFlipStep: Seq[Rewrite] = if (addInfo.literalTransformations.flippedLits.nonEmpty) {
          Out.lp_debug_info(s"the following literals need to be flipped: ${addInfo.literalTransformations}") //todo: kann es sein, dass auch das abgespeicherte uni lit geflippt wurde? in dem fall muss ich die Operation umkehren
          // the indices refer to the positions of the literals in the child, as we re-inserted the uni Lits, we may need to shift them

          val flipInfo = addInfo.literalTransformations.flippedLits.map(id => PatternInfo(old2NewIdx.getOrElse(id,id), None, child.cl.lits(id).polarity))
          val flipPattern = generateClausePattern(flipInfo, substClauseLen)


          Seq(Rewrite(Some(flipPattern), eqSym))
        } else Seq.empty
         */
        val maybeFlipStep: Seq[Rewrite] = verifyLiteralNormalisazion(addInfo.literalTransformations,old2NewIdx,child.cl.lits,substClauseLen)
        val haveSubstStep = Have(nameSubst, Prf(encSubstParent), (maybeFlipStep :+ Refine(Obj(appliedParentName))).map(Left(_)))

        allProofSteps = allProofSteps :+ haveSubstStep
        Const[Level.Obj](SymRef.LP(QName.local(nameSubst.value)))
      } else LpTerm.App(parentNameLpEnc,childVarNames.map(varName => Arg.Explicit(LpTerm.Var(varName,None))))
      // construct step proving the removal

      // as Leo never applies the substitution to the actual unification lit - but we need to do so in order to justify its removal - we need to apply it and reconstruct
      // the clause at this point of the proof explicitly

      // prove that the substituted clause implies the one with the litearal removed
      val nameHaveRemoveStep = Name("RemoveUniConst")
      val impToProve = Prf(LogicConst.Eq(HolBaseTypes.O,encSubstParent, nAry.disjunction(encChild.lits)))
      val proofScript:  Seq[LpProofScript] = deletedUniLits.map(litInfo => {
        Out.lp_debug_info(s"orig pos is ${litInfo.position}")
        val posInSubs = litInfo.position
        val patternLitInfo = PatternInfo(posInSubs, None, true)
        val pattern = generateClausePattern(Seq(patternLitInfo),substClauseLen)
        val embeddedPattern = embedPatternInEq(pattern,Side.Left)
        removeBot(embeddedPattern)
      })
      val finalStep = if ((effectivelyEmpty(child.cl)) && child.cl.lits.length == 1) Reflexivity else Refine(deleteBots(encChild.lits,deletedUniLits.map(_.position).sorted))
      val haveRemoveStep = Have(nameHaveRemoveStep,impToProve,(proofScript :+ finalStep).map(step => Left(step)))

      allProofSteps = allProofSteps :+ haveRemoveStep

      val lastStep = LpTerm.App(Obj(eqImp),Seq(Arg.Explicit[Level.Meta](Const(SymRef.LP(QName.local(nameHaveRemoveStep.value)))),Arg.Explicit[Level.Meta](Obj(maybeSubstStepName))))

      allProofSteps = allProofSteps :+ Refine(lastStep)
    }
    allProofSteps
  }

}
