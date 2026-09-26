package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Term._
import leo.datastructures.{Clause, ClauseProxy, MiniscopeCrossNegation, MiniscopePushAtConnective, MiniscopeStopAtConnective, MiniscopeTrace, Position, Signature, Term, Type}
import leo.modules.HOLSignature.{Exists, Forall, Impl, Not, &, |||}
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Refine, Rewrite, RewritePattern, Side, Simplify}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.{Level, LogicConst, LpSig, LpTerm, LpType, Name, QName, RenderOptions, Renderer, SymRef, TypeEncoding, lpClauseInst}

/** Reconstruction of one recorded Miniscope inference. */
object MiniscopeEncoding {
  /** The quantifier inside each post-crossing negation selects the proved law. */
  private sealed trait NegationLaw {
    def name: String
    def theorem: LpTerm[Level.Meta] = Const[Level.Meta](SymRef.LP(QName.local(name)))
  }
  private case object ExistsNotEqNotForall extends NegationLaw { val name = "exists_not_eq_not_forall" }
  private case object ForallNotEqNotExists extends NegationLaw { val name = "forall_not_eq_not_exists" }

  // A binder remains pending while the traversal follows its body. Its kind
  // changes when a recorded crossing moves it under a negation. The pattern
  // name is local to the wrapper; matching does not require the goal's name.
  private final case class PendingBinder(typ: Type, universal: Boolean, patternName: Name) {
    def crossed: PendingBinder = copy(universal = !universal)
  }

  /** Wrap a hole with the part of the Lambdapi goal already traversed. */
  private type PatternContext = LpTerm[Level.Obj] => LpTerm[Level.Obj]

  // Each pattern targets the post-move term. The script consumes moves backward,
  // starting from the recorded child goal.
  private final case class PlannedMove(observation: MiniscopeCrossNegation,
                                       law: NegationLaw,
                                       pattern: RewritePattern)

  // Inputs shared by replay and script emission after checking the step shape.
  private final case class Context(parent: Clause,
                                   child: Clause,
                                   parentProofName: Name,
                                   encParent: lpClauseInst,
                                   encChild: lpClauseInst,
                                   trace: MiniscopeTrace)

  private def initContext(child: ClauseProxy, parentProofNames: Seq[Name]): Either[String, Context] = {
    // This encoder handles one non-equational literal and one parent proof.
    val parents = child.annotation.parents
    if (parents.size != 1 || parentProofNames.size != 1)
      return Left(s"Miniscope step ${child.id}: expected one parent and one resolved proof name")

    val parent = parents.head.cl
    val result = child.cl
    if (Clause.empty(parent) || Clause.empty(result) || !Clause.unit(parent) || !Clause.unit(result) ||
        parent.lits.head.equational || result.lits.head.equational ||
        parent.lits.head.polarity != result.lits.head.polarity)
      return Left(s"Miniscope step ${child.id}: expected non-equational unit clauses with the same literal polarity")

    child.furtherInfo.miniscopeTrace match {
      case None => Left(s"Miniscope step ${child.id}: missing source-decision trace")
      case Some(trace) =>
        // Translate both clauses with one variable map, so later comparisons use
        // the same Lambdapi names for shared free variables.
        val (_, encoded) = lpClauseInst.apply_to_set(Seq(parent, result))
        val ctx = Context(parent, result, parentProofNames.head, encoded.head, encoded(1), trace)
        Out.lp_debug_info(s"Miniscope step ${child.id}: parent ${parents.head.id} as ${ctx.parentProofName.value}, ${ctx.trace.observations.size} source observations")
        Out.lp_debug_info(s"Miniscope translated parent: ${ctx.encParent.term}")
        Out.lp_debug_info(s"Miniscope translated child: ${ctx.encChild.term}")
        Right(ctx)
    }
  }

  /**
    * BLUEPRINT-MINI-2, bounded SCHEMA-01 path:
    * 0. Validate and translate the recorded parent and child together.
    * 1. Apply recorded crossings to the parent and check the resulting child.
    * 2. Emit patterned rewrites backward and refine the parent proof.
    */
  def encMiniscope(child: ClauseProxy, parentProofNames: Seq[Name], sig: LpSig): EncodeResult = {
    Out.lp_debug_info(s"Encoding Miniscope step ${child.id} with ${parentProofNames.size} resolved parent name(s)")
    initContext(child, parentProofNames) match {
      case Left(reason) => NotEncodable(reason)
      case Right(ctx) =>
        planSchema01Replay(ctx, sig) match {
          case Left(reason) =>
            Out.lp_debug_info(reason)
            NotEncodable(reason)
          case Right(moves) => emitSchema01Script(ctx, moves, sig)
        }
    }
  }

  /** Reverse the checked source moves to transform the child goal into the parent goal. */
  private def emitSchema01Script(ctx: Context, moves: Vector[PlannedMove], sig: LpSig): EncodeResult = {
    if (moves.isEmpty) return NotEncodable("Miniscope R1: no supported negation crossings")

    // The Lambdapi goal starts at the child. Each rewrite undoes one recorded
    // crossing; beta cleanup exposes the next target in the resulting goal.
    val reverseMoves = moves.reverse
    val rewrites = reverseMoves.zipWithIndex.flatMap { case (move, index) =>
      val rewrite = Rewrite(Some(move.pattern), move.law.theorem, Side.Left)
      Out.lp_debug_info(s"Miniscope ${move.observation.sourceVisit.pretty}: ${Renderer.proof(rewrite, RenderOptions(), sig)}")
      // beta-reduce between rewrite tactic applications
      if (index < reverseMoves.size - 1) Vector(rewrite, Simplify(onlyBeta = true))
      else Vector(rewrite)
    }
    val refine = Refine(Const[Level.Meta](SymRef.LP(QName.local(ctx.parentProofName.value))))
    Encoded(rewrites :+ refine)
  }

  /** Traverse the parent and consume crossings at each source negation. */
  private def planSchema01Replay(ctx: Context, sig: LpSig): Either[String, Vector[PlannedMove]] = {
    implicit val sourceSig: Signature = sig.orig
    val observations = ctx.trace.observations
    val polarity = ctx.parent.lits.head.polarity
    val moves = Vector.newBuilder[PlannedMove]
    var cursor = 0 // next observation in the producer's source traversal order

    def quant(binder: PendingBinder, body: Term): Term =
      if (binder.universal) Forall(\(binder.typ)(body))
      else Exists(\(binder.typ)(body))

    // Pending binders are ordered outermost first.
    def prefix(binders: Vector[PendingBinder], body: Term): Term =
      binders.reverseIterator.foldLeft(body)((term, binder) => quant(binder, term))
    def surround(body: Term, negations: Int): Term =
      (0 until negations).foldLeft(body)((term, _) => Not(term))

    // A stopped prefix stays outside the connective. Its branches have no
    // pending binders, but their patterns retain that prefix and select one
    // branch with a wildcard for the other.
    def visitConnective(left: Term, right: Term, pending: Vector[PendingBinder], at: Position,
                        outerNegations: Int, outerPattern: PatternContext,
                        sourceConnective: (Term, Term) => Term,
                        patternConnective: (LpTerm[Level.Obj], LpTerm[Level.Obj]) => LpTerm[Level.Obj]): Either[String, Term] = {
      val start = cursor
      while (cursor < observations.size && observations(cursor).sourceVisit == at) cursor += 1
      val here = observations.slice(start, cursor)
      val validStop = here match {
        case Vector(MiniscopeStopAtConnective(_, ordinal)) => ordinal == pending.size - 1
        case _ => false
      }
      if (here.exists(_.isInstanceOf[MiniscopePushAtConnective]))
        Left(s"Miniscope R1: connective push is outside the supported SCHEMA-01 path at ${at.pretty}")
      else if ((pending.isEmpty && here.nonEmpty) ||
               (pending.nonEmpty && !validStop))
        Left(s"Miniscope R1: missing or inconsistent connective stop at ${at.pretty}")
      else {
        Out.lp_debug_info(s"Miniscope R1: unchanged connective at ${at.pretty}, ${pending.size} retained binder(s)")
        val retainedPattern: PatternContext = hole => outerPattern(
          pending.reverseIterator.foldLeft(hole) { (body, binder) =>
            val typedName = (binder.patternName, LpType.El(TypeEncoding.type2LP(binder.typ)))
            if (binder.universal) LogicConst.Forall(typedName, body)
            else LogicConst.Exists(typedName, body)
          })
        val leftPattern: PatternContext = hole =>
          retainedPattern(patternConnective(hole, Wildcard[Level.Obj]()))
        val rightPattern: PatternContext = hole =>
          retainedPattern(patternConnective(Wildcard[Level.Obj](), hole))
        for {
          rebuiltLeft <- visit(left, Vector.empty, at.argPos(1), 0, leftPattern)
          rebuiltRight <- visit(right, Vector.empty, at.argPos(2), 0, rightPattern)
        } yield surround(prefix(pending, sourceConnective(rebuiltLeft, rebuiltRight)), outerNegations)
      }
    }

    // The source visit resolves trace ordinals. Pending binders and enclosing
    // negations describe the current context of this source subterm.
    def visit(term: Term, pending: Vector[PendingBinder], at: Position,
              outerNegations: Int, outerPattern: PatternContext): Either[String, Term] = term match {
      // Delay rebuilding a quantifier until a crossing or the final leaf.
      case Exists(ty :::> body) =>
        visit(body, pending :+ PendingBinder(ty, false, Name(s"mini${pending.size}")),
          at.argPos(2).abstrPos, outerNegations, outerPattern)
      case Forall(ty :::> body) =>
        visit(body, pending :+ PendingBinder(ty, true, Name(s"mini${pending.size}")),
          at.argPos(2).abstrPos, outerNegations, outerPattern)
      case Not(body) =>
        // Consecutive events naming this visit form its crossing group.
        val start = cursor
        // Go through all observations at given position
        while (cursor < observations.size && observations(cursor).sourceVisit == at) cursor += 1
        val here = observations.slice(start, cursor)
        if (here.exists(event => !event.isInstanceOf[MiniscopeCrossNegation]))
          Left(s"Miniscope R1: connective observation at source negation ${at.pretty}")
        else {
          val crossings = here.collect { case event: MiniscopeCrossNegation => event }
          // For this schema the recorder emits one crossing per pending binder,
          // outermost first. A gap would leave an unsupported mixed context.
          if (crossings.map(_.pendingBinderOrdinal) != pending.indices.toVector)
            Left(s"Miniscope R1: incomplete or reordered crossings at ${at.pretty}")
          else {
            // Each event changes one binder kind and captures the context of
            // its post-move target. The term inside the hole is not needed.
            var crossedPending = pending
            // The innermost binder crosses first, so the remaining outer
            // binders are exactly the wrappers around this event's target.
            crossings.reverse.foreach { event =>
              val ordinal = event.pendingBinderOrdinal
              val crossed = crossedPending(ordinal).crossed
              crossedPending = crossedPending.updated(ordinal, crossed)
              val pattern = makePattern(polarity, outerPattern, crossedPending.take(ordinal))
              val law = if (crossed.universal) ExistsNotEqNotForall else ForallNotEqNotExists
              moves += PlannedMove(event, law, pattern)
            }
            // This negation remains outside subsequent source visits. Reuse
            // that wrapper when planning patterns deeper in its body.
            val insideNegation: PatternContext = hole => outerPattern(LogicConst.Not(hole))
            visit(body, crossedPending, at.argPos(1), outerNegations + 1, insideNegation)
          }
        }
      case (left & right) =>
        visitConnective(left, right, pending, at, outerNegations, outerPattern,
          (a, b) => &(a, b), LogicConst.And.apply)
      case (left ||| right) =>
        visitConnective(left, right, pending, at, outerNegations, outerPattern,
          (a, b) => |||(a, b), LogicConst.Or.apply)
      case Impl(left, right) =>
        visitConnective(left, right, pending, at, outerNegations, outerPattern,
          (a, b) => Impl(a, b), LogicConst.Imp.apply)
      case leaf =>
        // No more decisions remain on this path; restore its pending context.
        Right(surround(prefix(pending, leaf), outerNegations))
    }

    val identityPattern: PatternContext = identity
    visit(ctx.parent.lits.head.left, Vector.empty, Position.root, 0, identityPattern).flatMap { result =>
      val planned = moves.result()
      if (cursor != observations.size)
        Left(s"Miniscope R1: ${observations.size - cursor} unconsumed source observations")
      else if (planned.isEmpty)
        Left("Miniscope R1: no supported negation crossings")
      else if (result != ctx.child.lits.head.left)
        Left("Miniscope R1: replay does not reach the recorded child")
      else Right(planned)
    }
  }

  /** Compose the reusable outer context with this move's pending binders. */
  private def makePattern(polarity: Boolean, outer: PatternContext,
                          binders: Vector[PendingBinder]): RewritePattern = {
    val hole = Const[Level.Obj](SymRef.LP(QName.local("x")))
    val bodyPattern = outer(binders.reverseIterator.foldLeft[LpTerm[Level.Obj]](hole) { (body, binder) =>
      val typedName = (binder.patternName, LpType.El(TypeEncoding.type2LP(binder.typ)))
      if (binder.universal) LogicConst.Forall(typedName, body)
      else LogicConst.Exists(typedName, body)
    })
    // PatternBuilder adds the signed literal and unit-clause context.
    val info = PatternBuilder.PatternInfo(0, None, polarity, PatternBuilder.LiteralBody)
    val literalPattern = PatternBuilder.generatePatternLit(info, bodyPattern)
    PatternBuilder.generateClausePattern(0, 1, literalPattern)
  }
}
