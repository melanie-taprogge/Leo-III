package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.{Clause, ClauseAnnotation, ClausePosition, ClauseProxy, GeneralizationOccurrence, Literal, MoveQuantStep, Position, QuantExists, QuantUniv, Role_Definition, Signature, SkolemStep, Term, Type, isPropSet}
import leo.datastructures.Term.:::>
import leo.modules.HOLSignature.{&, Exists, Forall, Not, |||}
import leo.modules.calculus.{CnfConj, CnfSkolem, FullCNF, RenameCNF}
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.LpLibs.{Clausification, EqRules, LeoTactics, MetaTheorems}
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Assume, Have, Refine, Repeat, Rewrite, RewritePattern, Side, Simplify, Try}
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, vars2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, HolBaseTypes, Level, LogicConst, LpProofScript, LpSig, LpTerm, LpType, Name, OlMonoType, QName, RenderOptions, Renderer, SymRef, lpClauseInst, lpTermBuilder}
import leo.modules.output.LPoutput.NewModularEncoding.AssumeStep.{encAssumeStep, encClauseVariableIntroduction}
import leo.modules.output.LPoutput.NewModularEncoding.ProofTermUtil.proofTermAsTacticArg

/** Reconstruction entry points for standalone clausification steps.
  *
  * Each entry point receives resolved parent proof terms in source-parent order.
  * Proof bodies use NewLpDatastructures; LPoutput owns their declaration wrappers.
  */
object ClausificationEncoding {
  private object Shared {
    // Add helpers here when they are shared by the clausification encoders.
  }

  /** Validated inputs and translations shared by the Skolemization helpers.
    * The definition proof is the declared pointwise equality, not a proof of
    * the whole-function equality in the source definition node.
    */
  private final case class SkolemContext(step: ClauseProxy,
                                         parent: Clause,
                                         parentProof: LpTerm[Level.Obj],
                                         definitionProof: LpTerm[Level.Obj],
                                         encParent: lpClauseInst,
                                         encChild: lpClauseInst,
                                         variableMap: Map[Int, String],
                                         skolemInfo: SkolemStep,
                                         position: ClausePosition,
                                         variableIntroduction: Seq[LpProofScript])

  /** Inputs to the inverse Skolemization lemma, recovered from the parent.
    * The pattern selects the surrounding subformula; for a negative universal
    * it must include the negation as well as the quantifier.
    */
  private final case class SkolemSite(quantifiedType: OlMonoType,
                                      predicate: LpTerm[Level.Obj],
                                      pattern: RewritePattern)

  /** Validated conjunction selection and the variable context needed by its proof. */
  private final case class CnfConjContext(parentVars: Seq[(Int, Type)],
                                          childVars: Seq[(Int, Type)],
                                          parentProof: LpTerm[Level.Obj],
                                          encChild: lpClauseInst,
                                          variableMap: Map[Int, String],
                                          clauseIndex: Int,
                                          clauseCount: Int,
                                          variableIntroduction: Seq[LpProofScript])

  /** A generalization with mandatory occurrence evidence and shared translations.
    * Vacuity refers to the immediate after-clause, not the final CNF child.
    */
  private final case class CnfGeneralization(info: MoveQuantStep,
                                            occurrence: GeneralizationOccurrence,
                                            before: lpClauseInst,
                                            after: lpClauseInst,
                                            vacuous: Boolean)

  /** One forward quantifier rewrite, with a selector relative to the formula body.
    * The bridge emitter adds the remaining pending prefix and antecedent context.
    */
  private final case class CnfQuantifierMove(rule: LpTerm[Level.Meta],
                                            pattern: RewritePattern)

  /** Stable source inputs and translations for one residual CNF segment.
    * Generalizations remain in source order; reconstruction visits them backwards.
    */
  private final case class CnfContext(step: ClauseProxy,
                                      parentProof: LpTerm[Level.Obj],
                                      variableMap: Map[Int, String],
                                      encParent: lpClauseInst,
                                      encChild: lpClauseInst,
                                      generalizations: Seq[CnfGeneralization])

  /** The current obligation is body quantified over pendingVars, in that order.
    * Introduced ordinary variables are in scope; pending variables stay bound.
    */
  private final case class CnfStage(body: LpTerm[Level.Obj],
                                    introducedVars: Seq[(Int, Type)],
                                    pendingVars: Seq[(Int, Type)],
                                    scripts: Seq[LpProofScript])

  /** Validate the selected source path and translate parent, child, and recorded
    * immediate states once, using a shared variable map. Missing occurrence
    * evidence is unsupported and must not be classified as a vacuous binder.
    */
  private def initCnfContext(step: ClauseProxy,
                             parentProofs: Seq[LpTerm[Level.Obj]],
                             sig: LpSig): Either[String, CnfContext] = {
    val parents = step.annotation.parents
    if ((step.annotation.fromRule != FullCNF && step.annotation.fromRule != RenameCNF) ||
        parents.size != 1 || parentProofs.size != 1)
      return Left(s"CNF step ${step.id}: expected a FullCNF or RenameCNF segment with one parent and one resolved proof")

    val info = step.furtherInfo.cnfInfo

    // checks ensuring that step can be encoded
    if (info.renameHappend)
      return Left(s"CNF step ${step.id}: formula renaming is not encoded")
    val moves = info.addInfoQuants.collect { case move: MoveQuantStep => move }
    if (moves.size != info.addInfoQuants.size)
      return Left(s"CNF step ${step.id}: residual segment contains a non-generalization quantifier record")
    if (moves.exists(_.occurrence.isEmpty))
      return Left(s"CNF step ${step.id}: missing generalization occurrence metadata")

    // Flatten before/after pairs in source order. Their literal indices refer
    // to these reconstructed clauses, not to the original parent's literals.
    val occurrences = moves.flatMap(_.occurrence)
    val clauses = Vector(parents.head.cl, step.cl) ++ occurrences.flatMap { occurrence =>
      Vector(occurrence.position.cl, occurrence.after)
    }
    val variables = moves.map(_.corrChildVar)

    // further checks
    if (clauses.exists(_.typeVars.nonEmpty) || variables.exists(_._2.isPolyType))
      return Left(s"CNF step ${step.id}: polymorphic clausification is not encoded")
    if (variables.exists(_._1 <= 0) || variables.map(_._1).distinct.size != variables.size)
      return Left(s"CNF step ${step.id}: expected distinct positive generalized-variable identifiers")
    val allVariables = clauses.flatMap(_.implicitlyBound) ++ variables
    if (allVariables.groupBy(_._1).exists { case (_, entries) => entries.map(_._2).distinct.size != 1 })
      return Left(s"CNF step ${step.id}: inconsistent types for a shared clause variable")
    if (occurrences.exists { occurrence =>
      val position = occurrence.position
      !position.cl.lits.isDefinedAt(position.litIdx) ||
        (!position.cl.lits(position.litIdx).equational && position.side == Literal.rightSide)
    })
      return Left(s"CNF step ${step.id}: generalization position does not address a literal side of its before-clause")
    if (moves.zip(occurrences).exists { case (move, occurrence) =>
      occurrence.position.cl.implicitlyBound.exists(_._1 == move.corrChildVar._1)
    })
      return Left(s"CNF step ${step.id}: generalized variable already occurs in its before-clause")

    // Actual encodings
    // Include recorded variables even when vacuous, so every retained identity
    // has one name. Translation does not turn them into outer proof binders.
    val (variableMap, encoded) = lpClauseInst.apply_to_set(clauses, variables)
    // split the encoded clauses into the original parent and child, and all the intermediate steps
    val (encParent, encChild) = (encoded.head, encoded(1))
    val encSteps = encoded.tail.tail
    val generalizations = moves.zip(occurrences).zipWithIndex.map { case ((move, occurrence), index) =>
      CnfGeneralization(move, occurrence, encSteps(2 * index), encSteps(1 + 2 * index),
        vacuous = !occurrence.after.implicitlyBound.contains(move.corrChildVar))
    }
    val ctx = CnfContext(step, parentProofs.head, variableMap, encParent, encChild, generalizations)
    Out.lp_debug_info(s"CNF step ${step.id}: parent ${parents.head.id} as ${ctx.parentProof}, ${generalizations.size} generalization(s)")
    Out.lp_debug_info(s"CNF shared variable map: ${ctx.variableMap.toSeq.sortBy(_._1)}")
    Out.lp_debug_info(s"CNF translated parent: ${ctx.encParent.term}")
    Out.lp_debug_info(s"CNF translated child: ${ctx.encChild.term}")
    /*
    generalizations.foreach { generalization =>
      Out.lp_debug_info(s"CNF generalization variable ${generalization.info.corrChildVar._1}: position ${generalization.occurrence.position.pretty}, vacuous=${generalization.vacuous}")
      Out.lp_debug_info(s"CNF translated before-state: ${generalization.before.term}")
      Out.lp_debug_info(s"CNF translated after-state: ${generalization.after.term}")
    }
     */
    Right(ctx)
  }

  /** encCnf — Outline of the encoded proof
    *
    * Let Q(V, F) universally quantify F over the pending variables V.
    * A residual source segment alternates Boolean blocks L -> R with recorded
    * generalizations Before -> After(v). Reconstruct its child backwards:
    *
    * 1. Reorder the child parameters, then introduce only ordinary parameters.
    * 2. For each recorded generalization, in reverse source order:
    *    a. Prove H : π (Q(V, After) ⇒ Q(V, current)) by normalizing both bodies
    *       under their pending prefixes; refine H _ restores the after-state.
    *    b. For a vacuous binder, restore it by a targeted constant-quantifier
    *       rewrite. Otherwise prove one gen : π (Q(W, Before) ⇒ Q(W, ∀v. After))
    *       by forward movement in the antecedent, then refine gen _.
    * 3. Undo the remaining Boolean block to recover the parent formula.
    * 4. Refine with the resolved parent proof applied to available parameters.
    */
  def encCnf(step: ClauseProxy,
             parentProofs: Seq[LpTerm[Level.Obj]],
             sig: LpSig): EncodeResult = {
    // Validate and translate the segment, retaining the recorded endpoints.
    val ctx = initCnfContext(step, parentProofs, sig) match {
      case Right(value) => value
      case Left(reason) =>
        Out.lp_debug_info(reason)
        return NotEncodable(reason)
    }

    // Introduce ordinary parameters while keeping generalized variables bound.
    var stage = encCnfVariablePrefix(ctx, sig) match {
      case Right(value) => value
      case Left(reason) =>
        Out.lp_debug_info(reason)
        return NotEncodable(reason)
    }

    // Undo each trailing Boolean block and its preceding generalization.
    val generalizations = ctx.generalizations.reverseIterator
    while (generalizations.hasNext) {
      val generalization = generalizations.next()
      val afterBoolean = encCnfBooleanBlock(ctx, stage, generalization.after.term, sig) match {
        case Right(value) => value
        case Left(reason) =>
          Out.lp_debug_info(reason)
          return NotEncodable(reason)
      }
      stage = encCnfGeneralization(ctx, afterBoolean, generalization, sig) match {
        case Right(value) => value
        case Left(reason) =>
          Out.lp_debug_info(reason)
          return NotEncodable(reason)
      }
    }

    // Recover the original formula and close with its resolved proof.
    val parentStage = encCnfBooleanBlock(ctx, stage, ctx.encParent.term, sig) match {
      case Right(value) => value
      case Left(reason) =>
        Out.lp_debug_info(reason)
        return NotEncodable(reason)
    }
    val closing = encCnfParent(ctx, parentStage) match {
      case Right(value) => value
      case Left(reason) =>
        Out.lp_debug_info(reason)
        return NotEncodable(reason)
    }

    Encoded(parentStage.scripts ++ closing)
  }

  /** Ensure that the variables in the child occur in the right order:
    * First, all "ordinary" variables, i.e. the ones that are not generalized in this CNF step occur.
    * They are followed by the variables to be generalized (the "pending" variables) in the order their generalisation
    * is tracked.
    *
    * If necessary, the variables are reordered using a refine tactic call with a targeted lambda-term, followed by
    * the assumption of the ordinary variables.
    */
  private def encCnfVariablePrefix(ctx: CnfContext,
                                   sig: LpSig): Either[String, CnfStage] = {
    // Given order in the child
    val givenVars = ctx.step.cl.implicitlyBound
    // pending variables in order of generalisation (vacuous variables disappear in the child)
    val pending = ctx.generalizations.filterNot(_.vacuous).map(_.info.corrChildVar)

    // Validate: Only allowed variables occur in the child (and only the expected ones)
    if (pending.exists(variable => !givenVars.contains(variable)))
      return Left(s"CNF step ${ctx.step.id}: non-vacuous generalized variable is absent from the child")
    if (ctx.generalizations.exists(g => g.vacuous && givenVars.exists(_._1 == g.info.corrChildVar._1)))
      return Left(s"CNF step ${ctx.step.id}: vacuous generalized variable occurs in the child")
    if (ctx.encChild.vars.exists(_.isRight) || ctx.encChild.vars.size != givenVars.size ||
      ctx.encChild.metaVars.exists(_.ty.isEmpty))
      return Left(s"CNF step ${ctx.step.id}: expected typed monomorphic child binders")

    // Construct the list of variables in the desired order:
    // Keep ordinary parameters in their existing relative order, placing the
    // whole ordinary block outside the pending generalized variables.
    val pendingIds = pending.map(_._1).toSet
    val ordinary = givenVars.filterNot(variable => pendingIds.contains(variable._1))
    val desired = ordinary ++ pending

    // Compare with given order and permute if necessary
    val givenBinders = ctx.encChild.metaVars
    val bindersById = givenVars.map(_._1).zip(givenBinders).toMap
    val permutation: Seq[LpProofScript] = if (givenVars == desired) Seq.empty else {
      Out.lp_debug_info(s"CNF step ${ctx.step.id}: child variable order ${givenVars.map(_._1)}, desired order ${desired.map(_._1)}")
      // The callback accepts a proof of the same child formula with the desired prefix.
      val desiredBinders = desired.map(variable => bindersById(variable._1))
      val orderedType = LpType.Pi(desiredBinders, LpType.Prf(ctx.encChild.term))
      //  Its name must avoid both signature symbols and local variables.
      val signatureNames = (sig.termNames.valuesIterator ++ sig.typeNames.valuesIterator).map(_.local.value).toSet
      val orderedName = Name(LpSig.freshIfNeeded("ordered", sig.reserved ++ signatureNames ++ ctx.variableMap.values))
      val ordered = LpTerm.Var[Level.Meta](orderedName, Some(orderedType))
      val application = LpTerm.App[Level.Meta](ordered, desiredBinders.map(binder => Arg.Explicit[Level.Meta](binder)))
      // Abstract in the declaration's given order, applying the callback in
      // desired order. Its remaining proof hole therefore has the desired type.
      val body = givenBinders.foldRight[LpTerm[Level.Meta]](application) { case (binder, rest) =>
        LpTerm.Lam[Level.Meta](binder.name -> binder.ty, rest)
      }
      // Applying the wrapper to a hole leaves that reordered proof obligation
      // for the following tactics to establish.
      val callback = LpTerm.Lam[Level.Meta](orderedName -> Some(orderedType), body)
      Seq(Refine(LpTerm.App[Level.Meta](callback,
        Seq(Arg.Explicit[Level.Meta](LpTerm.Wildcard[Level.Meta]())))))
    }

    // Open only the ordinary block; the pending prefix remains part of the goal.
    // The stage records that split alongside the unchanged formula body.
    val introductions = encAssumeStep(ordinary.map(variable => Name(ctx.variableMap(variable._1))))
    val stage = CnfStage(ctx.encChild.term, ordinary, pending, permutation ++ introductions)
    Out.lp_debug_info(s"CNF introduced variables: ${ordinary.map(_._1)}, pending variables: ${pending.map(_._1)}")
    stage.scripts.foreach { script =>
      Out.lp_debug_info(s"CNF prefix script: ${Renderer.proof(script, RenderOptions(), sig)}")
    }
    Right(stage)
  }

  /** Restore an earlier body through a Boolean implication bridge, normalizing
    * both sides beneath the pending prefix while keeping its variables bound.
    * Followed by a refinement reducing the current goal to the state after
    * application of the boolean identities.
    */
  private def encCnfBooleanBlock(ctx: CnfContext,
                                 stage: CnfStage,
                                 earlierBody: LpTerm[Level.Obj],
                                 sig: LpSig): Either[String, CnfStage] = {
    // if no boolean identities were applied in between generalisations, skip this step
    if (earlierBody == stage.body) {
      Out.lp_debug_info(s"CNF step ${ctx.step.id}: Boolean block has identical endpoints; no bridge needed")
      return Right(stage)
    }

    // Wrap the terms presenting the before and after, as well as the selector hole in exactly the same
    // variable context (the currently still pending vars).
    // the former will be used to construct the type of the bridge, the latter will be used to construct the patterns.
    val hole = lpTermBuilder.localObj(Name("x"))
    val (before, after, prefixedHole) =
      stage.pendingVars.foldRight((earlierBody, stage.body, hole)) {
        case ((id, typ), (left, right, pattern)) =>
          val binder = Name(ctx.variableMap(id)) -> LpType.El(type2LP(typ))
          (LogicConst.Forall(binder, left), LogicConst.Forall(binder, right),
            LogicConst.Forall(binder, pattern))
      }
    // Search inside the selected body on each side. (The enclosing implication
    // and pending quantifiers are not targets of the Boolean rule applications.)
    val bodyPattern = RewritePattern(prefixedHole, hole, searchInside = true)
    val leftPattern = PatternBuilder.embedPatternInImp(bodyPattern, Side.Left)
    val rightPattern = PatternBuilder.embedPatternInImp(bodyPattern, Side.Right)

    // Several blocks may occur in one lemma; keep each bridge name distinct
    // from earlier proof bindings, signature symbols, and clause variables.
    val signatureNames = (sig.termNames.valuesIterator ++ sig.typeNames.valuesIterator).map(_.local.value).toSet
    val proofNames = stage.scripts.collect { case Have(name, _, _) => name.value }
    val taken = sig.reserved ++ signatureNames ++ ctx.variableMap.values ++ proofNames
    val bridgeName = Name(LpSig.freshIfNeeded(s"boolean_${ctx.step.id}", taken))
    val hypothesisName = Name(LpSig.freshIfNeeded("h", taken + bridgeName.value))

    // After normalizing both bodies, the bridge is F ⇒ F. Introduce its proof
    // hypothesis only, close by identity
    val bridge = Have(bridgeName, LpType.Prf(LogicConst.Imp(before, after)), Seq(
      Left(LeoTactics.EvalApp.repeatBoolIdsAt(leftPattern)),
      Left(LeoTactics.EvalApp.repeatBoolIdsAt(rightPattern)),
      Left(Assume(Seq(hypothesisName))),
      Left(Refine(proofTermAsTacticArg(lpTermBuilder.localObj(hypothesisName))))))

    // Use the bridge backwards in the main proof to leave the earlier formula as the next obligation.
    val refinement = Refine(LpTerm.App[Level.Meta](
      proofTermAsTacticArg(lpTermBuilder.localObj(bridgeName)),
      Seq(Arg.Explicit[Level.Meta](LpTerm.Wildcard[Level.Meta]()))))
    val scripts = Seq(bridge, refinement)
    Out.lp_debug_info(s"CNF step ${ctx.step.id}: Boolean bridge ${bridgeName.value}, pending variables ${stage.pendingVars.map(_._1)}")
    Out.lp_debug_info(s"CNF Boolean block script:\n${scripts.map(Renderer.proof(_, RenderOptions(), sig)).mkString("\n")}")
    Right(stage.copy(body = earlierBody, scripts = stage.scripts ++ scripts))
  }

  /** Restore one recorded before-state. Use a direct targeted rewrite for a
    * vacuous binder; otherwise prove one implication bridge by moving the
    * quantifier outward in its antecedent, with beta-only cleanup between moves.
    * Update the body; only a non-vacuous event consumes a pending binder.
    */
  private def encCnfGeneralization(ctx: CnfContext,
                                   stage: CnfStage,
                                   generalization: CnfGeneralization,
                                   sig: LpSig): Either[String, CnfStage] = {
    // The preceding Boolean block must have recovered this event's exact after-state.
    if (stage.body != generalization.after.term)
      return Left(s"CNF step ${ctx.step.id}: current body does not match the recorded generalization after-state")

    if (!generalization.vacuous) {
      val moves = planCnfQuantifierLifting(ctx, generalization) match {
        case Right(value) => value
        case Left(reason) => return Left(reason)
      }
      Out.lp_debug_info(s"CNF step ${ctx.step.id}: planned ${moves.size} quantifier move(s) for variable ${generalization.info.corrChildVar._1}")
      moves.foreach { move =>
        Out.lp_debug_info(s"CNF lifting move (body-relative): ${Renderer.proof(Rewrite(Some(move.pattern), move.rule), RenderOptions(), sig)}")
      }
      val scripts = encCnfGeneralizationBridge(ctx, stage, generalization, moves, sig) match {
        case Right(value) => value
        case Left(reason) => return Left(reason)
      }
      // Applying the bridge restores the before-body and consumes just the
      // generalized variable; all other pending variables remain bound.
      val pending = stage.pendingVars.dropRight(1)
      Out.lp_debug_info(s"CNF step ${ctx.step.id}: restored generalization ${generalization.info.corrChildVar._1}, pending variables ${pending.map(_._1)}")
      Right(stage.copy(body = generalization.before.term, pendingVars = pending,
        scripts = stage.scripts ++ scripts))
    } else {
      val scripts = encCnfVacuousBinder(ctx, stage, generalization) match {
        case Right(value) => value
        case Left(reason) => return Left(reason)
      }
      // A vacuous variable never enters the pending prefix. Restore only the
      // formula body, retaining both variable lists and the accumulated proof.
      Out.lp_debug_info(s"CNF step ${ctx.step.id}: restored vacuous binder ${generalization.info.corrChildVar._1}, pending variables ${stage.pendingVars.map(_._1)}")
      Out.lp_debug_info(s"CNF vacuous binder script:\n${scripts.map(Renderer.proof(_, RenderOptions(), sig)).mkString("\n")}")
      Right(stage.copy(body = generalization.before.term, scripts = stage.scripts ++ scripts))
    }
  }

  /** Restore a vacuous binder at its recorded occurrence without introducing
    * an outer variable or an implication bridge.
    */
  private def encCnfVacuousBinder(ctx: CnfContext,
                                 stage: CnfStage,
                                 generalization: CnfGeneralization): Either[String, Seq[LpProofScript]] = {
    if (!generalization.vacuous)
      return Left(s"CNF step ${ctx.step.id}: constant-quantifier reconstruction requires a vacuous event")

    // Replace the whole recorded binder by a hole. Its surrounding context
    // also selects the unquantified body in the current after-state; for a
    // negative existential, the negation stays in that surrounding context.
    val context = PatternBuilder.prepareClausePositionPattern(generalization.occurrence.position) match {
      case Right(value) => value
      case Left(reason) => return Left(s"CNF step ${ctx.step.id}: $reason")
    }
    val (ty, universal) = (generalization.info.polarity, context.selectedTerm) match {
      case (QuantUniv, Forall(typ :::> _)) => (typ, true)
      case (QuantExists, Exists(typ :::> _)) => (typ, false)
      case _ => return Left(s"CNF step ${ctx.step.id}: vacuous position does not select the expected quantifier with an explicit predicate abstraction")
    }
    if (ty != generalization.info.corrChildVar._2)
      return Left(s"CNF step ${ctx.step.id}: vacuous quantifier type does not match the recorded variable type")

    // Retain every pending binder around the occurrence, without opening any
    // variables or searching for other occurrences of the selected body.
    val hole = lpTermBuilder.localObj(Name("x"))
    val bodyPattern = context.plug(RewritePattern(hole, hole))
    val prefixedPattern = stage.pendingVars.foldRight(bodyPattern.LpTerm) { case ((id, typ), body) =>
      LogicConst.Forall(Name(ctx.variableMap(id)) -> LpType.El(type2LP(typ)), body)
    }
    val pattern = bodyPattern.copy(LpTerm = prefixedPattern)

    // Match the constant proposition in the goal, supplying only its binder
    // type. Reverse the equality to restore the binder, then clean up beta-redexes.
    val rule = if (universal) EqRules.AsTerms.mkForallConst(type2LP(ty))
      else EqRules.AsTerms.mkExistsConst(type2LP(ty))
    Right(Seq(Rewrite(Some(pattern), rule, Side.Left), Try(Simplify(onlyBeta = true))))
  }

  /** Plan forward lifting from the recorded quantifier to the formula root,
    * with one body-relative selector per rewrite, in innermost-first order.
    */
  private def planCnfQuantifierLifting(ctx: CnfContext,
                                      generalization: CnfGeneralization): Either[String, Vector[CnfQuantifierMove]] = {
    // The recorded position selects the quantifier itself. Negative
    // existentials need the whole negated existential as their initial focus.
    val position = generalization.occurrence.position
    val focus = generalization.info.polarity match {
      case QuantUniv => position
      case QuantExists =>
        if (!position.pos.seq.lastOption.contains(1))
          return Left(s"CNF step ${ctx.step.id}: negative-existential position must end in negation argument 1")
        position.copy(pos = Position(position.pos.seq.dropRight(1)))
    }

    // Recorded occurrences contain the complete before-formula as one positive
    // literal, even when the original input clause contained several literals.
    val before = position.cl
    if (before.lits.size != 1 || position.litIdx != 0 || position.side != Literal.leftSide ||
        !before.lits.head.polarity || before.lits.head.equational)
      return Left(s"CNF step ${ctx.step.id}: quantifier lifting requires a recorded single positive formula literal")

    // Assumed current producer invariant: clausification visits outer logical
    // binders first and does not descend through ordinary term abstractions
    // or choice predicates. This is not a restriction of Lambdapi rewriting.
    // We also assume the recorded path crosses only conjunctions/disjunctions,
    // apart from the immediate negation of a generalized existential, as this
    // is a direct consequence of the implementation.
    type PatternContext = LpTerm[Level.Obj] => LpTerm[Level.Obj]
    val hole = lpTermBuilder.localObj(Name("x"))

    def visit(currentTerm: Term,
              remainingPath: Position,
              outerContext: PatternContext): Either[String, Vector[CnfQuantifierMove]] = {
      val pattern = RewritePattern(outerContext(hole), hole)
      if (remainingPath == Position.root) {
        // Validate at the endpoint of this single traversal. Negative
        // existentials first become universals at the whole negated site.
        val quantifiedType = (generalization.info.polarity, currentTerm) match {
          case (QuantUniv, Forall(typ :::> _)) => typ
          case (QuantExists, Not(Exists(typ :::> _))) => typ
          case _ => return Left(s"CNF step ${ctx.step.id}: lifting position does not select the expected universal or negated existential with an explicit predicate abstraction")
        }
        if (quantifiedType != generalization.info.corrChildVar._2)
          return Left(s"CNF step ${ctx.step.id}: lifting quantifier type does not match the recorded variable type")

        return Right(generalization.info.polarity match {
          case QuantUniv => Vector.empty
          case QuantExists => Vector(CnfQuantifierMove(Clausification.Terms.notExistsForallNot[Level.Meta], pattern))
        })
      }

      // Extend the selector only along the recorded branch. The lifting law
      // chosen here will later move the universal across this whole connective.
      val (child, childContext, rule): (Term, PatternContext, LpTerm[Level.Meta]) =
        (currentTerm, remainingPath.posHead) match {
          case (left & right, 1) =>
            (left, h => outerContext(LogicConst.And(h, LpTerm.Wildcard[Level.Obj]())),
              Clausification.Terms.forallAndDistLeft[Level.Meta])
          case (left & right, 2) =>
            (right, h => outerContext(LogicConst.And(LpTerm.Wildcard[Level.Obj](), h)),
              Clausification.Terms.forallAndDistRight[Level.Meta])
          case (left ||| right, 1) =>
            (left, h => outerContext(LogicConst.Or(h, LpTerm.Wildcard[Level.Obj]())),
              Clausification.Terms.forallOrDistLeft[Level.Meta])
          case (left ||| right, 2) =>
            (right, h => outerContext(LogicConst.Or(LpTerm.Wildcard[Level.Obj](), h)),
              Clausification.Terms.forallOrDistRight[Level.Meta])
          case _ => return Left(s"CNF step ${ctx.step.id}: unexpected connective or path component ${remainingPath.posHead} while planning quantifier lifting")
        }

      val innerMoves = visit(child, remainingPath.tail, childContext) match {
        case Right(value) => value
        case Left(reason) => return Left(reason)
      }
      // Inner moves bring the quantifier to the child's root. Append this
      // connective crossing afterwards, so the complete plan runs inside out.
      Right(innerMoves :+ CnfQuantifierMove(rule, pattern))
    }

    visit(before.lits.head.left, focus.pos, h => h)
  }

  /** Prove and apply one implication bridge for a whole non-vacuous
    * generalization, keeping the remaining generalized variables bound.
    */
  private def encCnfGeneralizationBridge(ctx: CnfContext,
                                         stage: CnfStage,
                                         generalization: CnfGeneralization,
                                         moves: Vector[CnfQuantifierMove],
                                         sig: LpSig): Either[String, Seq[LpProofScript]] = {
    if (generalization.vacuous || !stage.pendingVars.lastOption.contains(generalization.info.corrChildVar))
      return Left(s"CNF step ${ctx.step.id}: generalization bridge requires the recorded non-vacuous variable innermost in the pending prefix")

    val remaining = stage.pendingVars.dropRight(1)
    val remainingBinders = vars2Lp(remaining, ctx.variableMap)
    val pendingBinders = vars2Lp(stage.pendingVars, ctx.variableMap)

    // Before has its binder at the original site; After has the corresponding
    // free variable, which stays innermost in the consequent's pending prefix.
    val antecedent = lpTermBuilder.forall(remainingBinders, generalization.before.term)
    val consequent = lpTermBuilder.forall(pendingBinders, generalization.after.term)

    // Each whole-event bridge needs a fresh name within this proof. Reuse the
    // Boolean bridge's naming scope, including all earlier local Have bindings.
    val signatureNames = (sig.termNames.valuesIterator ++ sig.typeNames.valuesIterator).map(_.local.value).toSet
    val proofNames = stage.scripts.collect { case Have(name, _, _) => name.value }
    val taken = sig.reserved ++ signatureNames ++ ctx.variableMap.values ++ proofNames
    val bridgeName = Name(LpSig.freshIfNeeded(s"generalization_${ctx.step.id}", taken))
    val hypothesisName = Name(LpSig.freshIfNeeded("h", taken + bridgeName.value))

    // Lift only inside the antecedent, keeping the other pending variables
    // bound. Preserve the planner's exact selectors and inside-out move order.
    val rewrites: Seq[LpProofScript] = moves.flatMap { move =>
      val prefixedPattern = move.pattern.copy(LpTerm = lpTermBuilder.forall(remainingBinders, move.pattern.LpTerm))
      val pattern = PatternBuilder.embedPatternInImp(prefixedPattern, Side.Left)
      Seq(Rewrite(Some(pattern), move.rule), Try(Simplify(onlyBeta = true)))
    }
    // Identity closes only when the lifted antecedent agrees with the recorded
    // consequent, including the valid case of a quantifier already at the root.
    val bridgeBody = rewrites ++ Seq(Assume(Seq(hypothesisName)),
      Refine(proofTermAsTacticArg(lpTermBuilder.localObj(hypothesisName))))
    val bridge = Have(bridgeName, LpType.Prf(LogicConst.Imp(antecedent, consequent)),
      bridgeBody.map(script => Left(script)))
    val refinement = Refine(LpTerm.App[Level.Meta](
      proofTermAsTacticArg(lpTermBuilder.localObj(bridgeName)),
      Seq(Arg.Explicit[Level.Meta](LpTerm.Wildcard[Level.Meta]()))))
    val scripts = Seq(bridge, refinement)
    Out.lp_debug_info(s"CNF step ${ctx.step.id}: generalization bridge ${bridgeName.value}, remaining pending variables ${remaining.map(_._1)}")
    Out.lp_debug_info(s"CNF generalization bridge script:\n${scripts.map(Renderer.proof(_, RenderOptions(), sig)).mkString("\n")}")
    Right(scripts)
  }

  /** Check that replay reached the parent with no pending generalized variables,
    * then apply its resolved proof to the introduced parameters. The returned
    * closing fragment is appended to the accumulated stage script by encCnf.
    */
  private def encCnfParent(ctx: CnfContext,
                           stage: CnfStage): Either[String, Seq[LpProofScript]] = {
    if (stage.pendingVars.nonEmpty)
      return Left(s"CNF step ${ctx.step.id}: generalized variables remain pending at parent application")
    if (stage.body != ctx.encParent.term)
      return Left(s"CNF step ${ctx.step.id}: reconstruction has not reached the parent body")

    // Only ordinary variables have been introduced. Instantiate the resolved
    // parent in its declaration order, using the shared missing-variable fallback.
    val parentVars = ctx.step.annotation.parents.head.cl.implicitlyBound
    val parent = SubstitutionEncoding.instantiateProofTerm(
      parentVars, stage.introducedVars, Seq.empty, ctx.variableMap, ctx.parentProof)
    Out.lp_debug_info(s"CNF step ${ctx.step.id}: closing with parent ${ctx.parentProof}, available variables ${stage.introducedVars.map(_._1)}")
    Right(Seq(Refine(proofTermAsTacticArg(parent))))
  }

  /** Validate the monomorphic source step and translate its parent and child once.
    * Preserve the parent's structure for later position analysis and include
    * recorded definition parameters in the shared variable-name map.
    */
  private def initSkolemContext(step: ClauseProxy,
                                parentProofs: Seq[LpTerm[Level.Obj]],
                                sig: LpSig,
                                useTypedIntroduction: Boolean): Either[String, SkolemContext] = {
    val parents = step.annotation.parents
    if (step.annotation.fromRule != CnfSkolem || parents.size != 2 || parentProofs.size != 2)
      return Left(s"Skolemization step ${step.id}: expected a term-Skolemization with a formula parent, a definition parent, and two resolved proofs")

    val skolemInfo = step.furtherInfo.cnfInfo.addInfoQuants match {
      case Seq(info: SkolemStep) => info
      case _ => return Left(s"Skolemization step ${step.id}: expected exactly one term-Skolem record")
    }
    val parent = parents.head.cl
    val definition = parents(1)
    if (skolemInfo.ftVs.nonEmpty || Seq(parent, step.cl, definition.cl).exists(_.typeVars.nonEmpty))
      return Left(s"Skolemization step ${step.id}: polymorphic Skolemization is not encoded")

    val position = skolemInfo.position match {
      case Some(value) => value
      case None => return Left(s"Skolemization step ${step.id}: missing quantifier position")
    }
    if (position.cl != parent || !parent.lits.isDefinedAt(position.litIdx) ||
        (!parent.lits(position.litIdx).equational && position.side == Literal.rightSide))
      return Left(s"Skolemization step ${step.id}: quantifier position does not address a side of the formula parent")

    if (!sig.orig.allUserConstants.contains(skolemInfo.sko))
      return Left(s"Skolemization step ${step.id}: unknown Skolem symbol")
    val symbol = sig.orig(skolemInfo.sko)
    if (!isPropSet(Signature.PropSkolemConstant, symbol.flag) || !symbol.hasDefn)
      return Left(s"Skolemization step ${step.id}: expected a Skolem symbol with a stored definition")
    if (symbol._ty.isPolyType)
      return Left(s"Skolemization step ${step.id}: polymorphic Skolemization is not encoded")

    val matchesDefinition = (definition.role, definition.annotation, definition.cl.lits) match {
      case (Role_Definition, ClauseAnnotation.FromSystem("definition", _, _), Seq(literal))
        if literal.equational && literal.polarity =>
        Term.Symbol.unapply(literal.left).contains(skolemInfo.sko) && literal.right == symbol._defn
      case _ => false
    }
    if (!matchesDefinition)
      return Left(s"Skolemization step ${step.id}: definition parent does not match the recorded Skolem symbol and definition")
    val definitionProof = LpTerm.Const[Level.Obj](SymRef.LP(nameSkDef(skolemInfo.sko, sig.orig)))
    if (parentProofs(1) != definitionProof)
      return Left(s"Skolemization step ${step.id}: definition parent must resolve to its declared pointwise equality")

    val (variableMap, encoded) = lpClauseInst.apply_to_set(
      Seq(parent, step.cl), skolemInfo.fVs, suppressReductionAt = Set(0))
    val variableIntroduction = encClauseVariableIntroduction(
      encoded(1), useLetBasedIntroduction = useTypedIntroduction, sig = sig)
    val ctx = SkolemContext(step, parent, parentProofs.head, parentProofs(1),
      encoded.head, encoded(1), variableMap, skolemInfo, position, variableIntroduction)
    Out.lp_debug_info(s"Skolemization step ${step.id}: formula parent ${parents.head.id}, definition parent ${definition.id}, position ${position.pretty}")
    Out.lp_debug_info(s"Skolemization translated parent: ${ctx.encParent.term}")
    Out.lp_debug_info(s"Skolemization translated child: ${ctx.encChild.term}")
    Right(ctx)
  }

  /** encSkolem — Outline of the encoded proof
    *
    * Let C[·] be the surrounding formula context, P : a → o the predicate,
    * and k u the Skolem symbol applied to its dependency parameters.
    * The formula parent and child have one of these shapes:
    *
    *   Existential:        C[∃ P]  → C[P(k u)]
    *   Negative universal: C[¬∀ P] → C[¬P(k u)]
    *
    * The pointwise definition k_def u proves k u = choice, where
    * choice is ε [a] P or ε [a] (λ x, ¬P x), respectively.
    * Let Q be the selected quantified subformula and R its choice instance,
    * with the outer predicate application beta-reduced.
    *
    * Abstract proof structure in Lambdapi:
    *
    *   introduce childVariables (assume or typed-hole refinement);
    *   repeat rewrite (k_def dependencyArguments);
    *   have skolemEq : π (Q = R)
    *     { refine (skolemTheorem a P); };
    *   rewrite left .[x in C[x]] skolemEq;
    *   refine (formulaParent parentArguments);
    *
    * skolemTheorem is ∃_skolem or ∀_skolem. Dependency and parent arguments
    * use the available child variables, with witnesses for absent variables.
    *
    * @return encoded proof script or an explanatory NotEncodable result
    */
  def encSkolem(step: ClauseProxy,
                parentProofs: Seq[LpTerm[Level.Obj]],
                sig: LpSig,
                useTypedIntroduction: Boolean = false): EncodeResult = {
    val result = for {
      // Validate the source step and translate both clauses with shared variable names.
      ctx <- initSkolemContext(step, parentProofs, sig, useTypedIntroduction)
      // Recover the normalized predicate and the pattern selecting its quantified subformula.
      site <- analyseSkolemPosition(ctx)
      // Generate repeated definition unfolding for every Skolem occurrence in the child goal.
      unfolding <- encSkolemDefinitionRewrite(ctx)
      // Prove the normalized Skolem equality and rewrite backwards to recover the parent formula.
      folding <- encSkolemQuantifierRewrite(ctx, site)
    } yield {
      // Apply the formula-parent proof to child variables, supplying witnesses where variables disappeared.
      val parent = SubstitutionEncoding.instantiateProofTerm(
        ctx.parent.implicitlyBound, ctx.step.cl.implicitlyBound, Seq.empty, ctx.variableMap, ctx.parentProof)
      // Introduce the child's variables, perform both rewrites, and close with the instantiated parent.
      ctx.variableIntroduction ++ unfolding ++ folding ++ Seq(Refine(proofTermAsTacticArg(parent)))
    }
    result match {
      case Left(reason) => NotEncodable(reason)
      case Right(scripts) => Encoded(scripts)
    }
  }

  /** Locate the recorded parent quantifier, check its kind against the polarity,
    * and translate its type and predicate in the context's variable map.
    * Construct the surrounding pattern, including negation for a negative universal.
    *
    * Assumed invariant of the current clausification implementation: the selected
    * quantifier is not below an enclosing term abstraction. CoreCNF eliminates
    * outer quantifiers before processing their bodies and does not descend into
    * ordinary lambdas or choice bindings. Dependencies on former outer binders
    * are therefore clause variables or Skolem terms, so translating the complete
    * predicate with variableMap needs no additional enclosing-binder environment.
    */
  private def analyseSkolemPosition(ctx: SkolemContext): Either[String, SkolemSite] = {
    // in case of negated universal, the pattern must target the term including the negation
    //  -> adapt the pattern accordingly
    val focus = ctx.skolemInfo.polarity match {
      case QuantExists => ctx.position
      case QuantUniv =>
        if (!ctx.position.pos.seq.lastOption.contains(1))
          return Left(s"Skolemization step ${ctx.step.id}: negative-universal position must end in negation argument 1")
        ctx.position.copy(pos = Position(ctx.position.pos.seq.dropRight(1)))
    }

    // Generate the pattern targeting the skolemized term
    PatternBuilder.prepareClausePositionPattern(focus)
      .left.map(reason => s"Skolemization step ${ctx.step.id}: $reason")
      .flatMap { context =>
        // Locate the quantifier before encoding its predicate.
        val binder: Either[String, (Type, Term)] = (ctx.skolemInfo.polarity, context.selectedTerm) match {
          case (QuantExists, quantifier @ Exists(ty :::> _)) => Right((ty, quantifier))
          case (QuantUniv, Not(quantifier @ Forall(ty :::> _))) => Right((ty, quantifier))
          case _ => Left(s"Skolemization step ${ctx.step.id}: recorded position does not select the expected existential or negated universal with an explicit predicate abstraction")
        }
        binder.flatMap { case (ty, quantifier) =>
          // Normal quantifier encoding preserves the predicate's outer lambda
          // while reducing its body to match the child and Skolem definition.
          term2LP(quantifier, ctx.variableMap) match {
            case LpTerm.App(_, Seq(Arg.Explicit(predicate @ LpTerm.Lam(_, _)))) =>
              val hole = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("x")))
              Right(SkolemSite(type2LP(ty), predicate, context.plug(RewritePattern(hole, hole))))
            case _ => Left(s"Skolemization step ${ctx.step.id}: expected an encoded quantifier with a predicate abstraction")
          }
        }
      }
  }

  /** Apply the pointwise definition to the recorded fVs in order, then generate
    * a repeated forward rewrite to unfold every Skolem occurrence in the goal.
    * Parameters absent from the child are instantiated with witnesses.
    */
  private def encSkolemDefinitionRewrite(ctx: SkolemContext): Either[String, Seq[LpProofScript]] = {
    val definition = SubstitutionEncoding.instantiateProofTerm(
      ctx.skolemInfo.fVs, ctx.step.cl.implicitlyBound, Seq.empty, ctx.variableMap, ctx.definitionProof)
    Right(Seq(Repeat(Rewrite(None, proofTermAsTacticArg(definition), Side.Right))))
  }

  /** Instantiate the existential or negative-universal Skolemization lemma with
    * the site's type and predicate. Expose its beta-reduced right-hand side in a
    * proved local equality before matching it in the backward patterned rewrite.
    */
  private def encSkolemQuantifierRewrite(ctx: SkolemContext, site: SkolemSite): Either[String, Seq[LpProofScript]] = {
    val (binder, body) = site.predicate match {
      case LpTerm.Lam(binding, value) => (binding, value)
      case _ => return Left(s"Skolemization step ${ctx.step.id}: expected an encoded predicate abstraction")
    }
    val (instance, quantified, choicePredicate) = ctx.skolemInfo.polarity match {
      case QuantExists =>
        (Clausification.Inst.skolemExists(site.quantifiedType, site.predicate),
          lpTermBuilder.app(LogicConst.cEx, Seq(site.predicate)), site.predicate)
      case QuantUniv =>
        (Clausification.Inst.skolemNotForall(site.quantifiedType, site.predicate),
          LogicConst.Not(lpTermBuilder.app(LogicConst.cAll, Seq(site.predicate))),
          LpTerm.Lam[Level.Obj](binder, LogicConst.Not(body)))
    }
    // Fix epsilon's type explicitly so inference does not introduce a
    // convertible dependent-arrow type that the rewrite matcher cannot match.
    val choice = LpTerm.App[Level.Obj](LogicConst.cCh,
      Seq(Arg.ImplicitTypeArg(site.quantifiedType), Arg.Explicit(choicePredicate)))
    val instantiatedBody = lpTermBuilder.betaApply(site.predicate, Seq(Arg.Explicit(choice)))
    val skolemized = ctx.skolemInfo.polarity match {
      case QuantExists => instantiatedBody
      case QuantUniv => LogicConst.Not(instantiatedBody)
    }
    val equalityName = Name(s"skolemEq_${ctx.step.id}")
    val equalityType = LpType.Prf(LogicConst.Eq(HolBaseTypes.O, quantified, skolemized))
    Right(Seq(
      Have(equalityName, equalityType, Seq(Left(Refine(proofTermAsTacticArg(instance))))),
      Rewrite(Some(site.pattern), proofTermAsTacticArg(lpTermBuilder.localObj(equalityName)), Side.Left)))
  }

  /** encCnfConj — Outline of the encoded proof
    *
    * From a parent C₀ ∧ (C₁ ∧ ... ∧ Cₙ₋₁), derive the selected clause Cᵢ:
    *
    *   introduce childVariables (assume or typed-hole refinement);
    *   refine (∧ₑₙ i [_, ..., Cᵢ, ..., _] ⊤ᵢ (parent parentArguments));
    *
    * Variables absent from the child are instantiated with witnesses.
    * The recorded count and index refer to the original conjunction, including
    * duplicate conjuncts, even when duplicate output clauses were eliminated.
    */
  def encCnfConj(step: ClauseProxy,
                 parentProofs: Seq[LpTerm[Level.Obj]],
                 sig: LpSig,
                 useTypedIntroduction: Boolean = false): EncodeResult = {
    // Validate the selection and prepare translations and child-variable introduction.
    initCnfConjContext(step, parentProofs, sig, useTypedIntroduction) match {
      case Left(reason) => NotEncodable(reason)
      case Right(ctx) =>
        // Introduce the child's variables and close with conjunction elimination.
        Encoded(ctx.variableIntroduction :+ encConjunctSelection(ctx))
    }
  }

  /** Validate all source metadata and the selected conjunct, then prepare its variable context. */
  private def initCnfConjContext(step: ClauseProxy,
                                 parentProofs: Seq[LpTerm[Level.Obj]],
                                 sig: LpSig,
                                 useTypedIntroduction: Boolean): Either[String, CnfConjContext] = {
    val parents = step.annotation.parents
    if (step.annotation.fromRule != CnfConj || parents.size != 1 || parentProofs.size != 1)
      return Left(s"CNF conjunction step ${step.id}: expected one conjunction parent and one resolved proof")
    val info = step.furtherInfo.cnfConjInfo match {
      case Some(value) => value
      case None => return Left(s"CNF conjunction step ${step.id}: missing conjunction-selection metadata")
    }
    if (info.numOfClauses < 2 || info.idxInConj < 0 || info.idxInConj >= info.numOfClauses)
      return Left(s"CNF conjunction step ${step.id}: invalid index ${info.idxInConj} for ${info.numOfClauses} conjuncts")
    val parent = parents.head.cl
    if (parent.typeVars.nonEmpty || step.cl.typeVars.nonEmpty)
      return Left(s"CNF conjunction step ${step.id}: polymorphic conjunction selection is not encoded")
    parent.lits match {
      case Seq(literal) if literal.polarity && !literal.equational => ()
      case _ => return Left(s"CNF conjunction step ${step.id}: expected one positive non-equational parent literal")
    }

    // Translate both clauses normally, retaining a shared name for each clause variable.
    val (variableMap, encoded) = lpClauseInst.apply_to_set(Seq(parent, step.cl))
    val encParent = encoded.head
    val encChild = encoded(1)

    // Follow the right-nested conjunction spine using the recorded, pre-deduplication count.
    var remaining = encParent.term
    var selected = Option.empty[LpTerm[Level.Obj]]
    var index = 0
    while (index < info.numOfClauses - 1) {
      remaining match {
        case LogicConst.And(head, tail) =>
          if (index == info.idxInConj) selected = Some(head)
          remaining = tail
        case _ => return Left(s"CNF conjunction step ${step.id}: parent does not have the recorded right-nested conjunction shape")
      }
      index += 1
    }
    if (LogicConst.And.unapply(remaining).nonEmpty)
      return Left(s"CNF conjunction step ${step.id}: parent has more conjuncts than recorded")
    if (info.idxInConj == index) selected = Some(remaining)
    if (!selected.contains(encChild.term))
      return Left(s"CNF conjunction step ${step.id}: selected conjunct does not match the child clause")

    val variableIntroduction = encClauseVariableIntroduction(
      encChild, useLetBasedIntroduction = useTypedIntroduction, sig = sig)
    Right(CnfConjContext(parent.implicitlyBound, step.cl.implicitlyBound, parentProofs.head,
      encChild, variableMap, info.idxInConj, info.numOfClauses, variableIntroduction))
  }

  /** Instantiate the parent and select the child using the central conjunction-elimination theorem. */
  private def encConjunctSelection(ctx: CnfConjContext): LpProofScript = {
    // Instantiate disappearing parent variables with witnesses; infer sibling conjuncts from the parent proof.
    val parentProof = SubstitutionEncoding.instantiateProofTerm(
      ctx.parentVars, ctx.childVars, Seq.empty, ctx.variableMap, ctx.parentProof)
    val conjuncts = Seq.fill[LpTerm[Level.Obj]](ctx.clauseCount)(LpTerm.Wildcard[Level.Obj]())
      .updated(ctx.clauseIndex, ctx.encChild.term)
    val selection = MetaTheorems.Inst.selectConjunct(conjuncts, ctx.clauseIndex, parentProof)
    Refine(proofTermAsTacticArg(selection))
  }
}
