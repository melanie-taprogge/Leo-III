package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.{Clause, ClauseAnnotation, ClausePosition, ClauseProxy, Literal, Position, QuantExists, QuantUniv, Role_Definition, Signature, SkolemStep, Term, Type, isPropSet}
import leo.datastructures.Term.:::>
import leo.modules.HOLSignature.{Exists, Forall, Not}
import leo.modules.calculus.CnfSkolem
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.LpLibs.Clausification
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Have, Refine, Repeat, Rewrite, RewritePattern, Side}
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.term2LP
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, HolBaseTypes, Level, LogicConst, LpProofScript, LpSig, LpTerm, LpType, Name, OlMonoType, QName, SymRef, lpClauseInst, lpTermBuilder}
import leo.modules.output.LPoutput.NewModularEncoding.AssumeStep.{encAssumeStep, extractVarNames}
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
                                         assumptions: Seq[LpProofScript])

  /** Inputs to the inverse Skolemization lemma, recovered from the parent.
    * The pattern selects the surrounding subformula; for a negative universal
    * it must include the negation as well as the quantifier.
    */
  private final case class SkolemSite(quantifiedType: OlMonoType,
                                      predicate: LpTerm[Level.Obj],
                                      pattern: RewritePattern)

  /** Residual clausification for both FullCNF and RenameCNF.
    */
  def encCnf(step: ClauseProxy,
             parentProofs: Seq[LpTerm[Level.Obj]],
             sig: LpSig): EncodeResult = {
    NotEncodable(s"CNF step ${step.id}: residual clausification reconstruction is not implemented yet")
  }

  /** Validate the monomorphic source step and translate its parent and child once.
    * Preserve the parent's structure for later position analysis and include
    * recorded definition parameters in the shared variable-name map.
    */
  private def initSkolemContext(step: ClauseProxy,
                                parentProofs: Seq[LpTerm[Level.Obj]],
                                sig: LpSig): Either[String, SkolemContext] = {
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
    val assumptions = encAssumeStep(extractVarNames(encoded(1)))
    val ctx = SkolemContext(step, parent, parentProofs.head, parentProofs(1),
      encoded.head, encoded(1), variableMap, skolemInfo, position, assumptions)
    Out.lp_debug_info(s"Skolemization step ${step.id}: formula parent ${parents.head.id}, definition parent ${definition.id}, position ${position.pretty}")
    Out.lp_debug_info(s"Skolemization translated parent: ${ctx.encParent.term}")
    Out.lp_debug_info(s"Skolemization translated child: ${ctx.encChild.term}")
    Right(ctx)
  }

  /** Backward reconstruction of one monomorphic term-Skolemization.
    * 1. Validate and translate the step and prepare clause-variable assumptions.
    * 2. Recover the predicate, quantified type, and pattern from the parent position.
    * 3. Unfold every occurrence of the Skolem term using its pointwise definition.
    * 4. Rewrite the instantiated Skolemization lemma backwards at the selected site.
    * 5. Refine with the formula-parent proof applied to the available variables.
    * Unsupported source shapes return an explicit reason.
    */
  def encSkolem(step: ClauseProxy,
                parentProofs: Seq[LpTerm[Level.Obj]],
                sig: LpSig): EncodeResult = {
    val result = for {
      ctx <- initSkolemContext(step, parentProofs, sig)
      site <- analyseSkolemPosition(ctx)
      unfolding <- encSkolemDefinitionRewrite(ctx)
      folding <- encSkolemQuantifierRewrite(ctx, site)
    } yield {
      val parent = SubstitutionEncoding.instantiateProofTerm(
        ctx.parent.implicitlyBound, ctx.step.cl.implicitlyBound, Seq.empty, ctx.variableMap, ctx.parentProof)
      ctx.assumptions ++ unfolding ++ folding ++ Seq(Refine(proofTermAsTacticArg(parent)))
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
        // extract predicate applied to the skolemized quantifier
        val binder: Either[String, (Type, Term)] = (ctx.skolemInfo.polarity, context.selectedTerm) match {
          case (QuantExists, Exists(predicate @ (ty :::> _))) => Right((ty, predicate))
          case (QuantUniv, Not(Forall(predicate @ (ty :::> _)))) => Right((ty, predicate))
          case _ => Left(s"Skolemization step ${ctx.step.id}: recorded position does not select the expected existential or negated universal with an explicit predicate abstraction")
        }
        binder.map { case (ty, predicate) =>
          val hole = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("x")))
          SkolemSite(type2LP(ty),
            term2LP(predicate, ctx.variableMap, suppressReduction = true),
            context.plug(RewritePattern(hole, hole)))
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
    val choice = lpTermBuilder.app(LogicConst.cCh, Seq(choicePredicate))
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

  /** Selection of one clause from a clausified conjunction.
    */
  def encCnfConj(step: ClauseProxy,
                 parentProofs: Seq[LpTerm[Level.Obj]],
                 sig: LpSig): EncodeResult = {
    NotEncodable(s"CNF conjunction step ${step.id}: conjunction-selection reconstruction is not implemented yet")
  }
}
