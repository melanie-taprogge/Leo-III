package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Term._
import leo.datastructures.{BoundFront, Clause, ClauseProxy, MiniscopeCrossNegation, MiniscopeObservation, MiniscopePush, MiniscopePushAtConnective, MiniscopePushBoth, MiniscopePushLeft, MiniscopePushRight, MiniscopeStopAtConnective, MiniscopeTrace, Position, Signature, Subst, Term, Type}
import leo.modules.HOLSignature.{Exists, Forall, Impl, Not, &, |||}
import leo.modules.output.LPoutput.EncodeResult.{Encoded, NotEncodable}
import leo.modules.output.LPoutput.LpTacticUtil.PatternBuilder
import leo.modules.output.LPoutput.NewLpDatastructures.LpProofScript.{Refine, Rewrite, RewritePattern, Simplify, Try}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Const, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.{Level, LogicConst, LpSig, LpTerm, LpType, Name, QName, RenderOptions, Renderer, SymRef, TypeEncoding, lpClauseInst}

/** Reconstruction of one recorded Miniscope inference. */
object MiniscopeEncoding {
  /** A recorded move selects its proved Lambdapi law. */
  private sealed trait ReplayLaw {
    def name: String
    def theorem: LpTerm[Level.Meta] = Const[Level.Meta](SymRef.LP(QName.local(name)))
  }

  // Lambdapi Theorems used to verify Leo-III operations
  private case object NotForallExistsNot extends ReplayLaw { val name = "¬∀=∃¬" }
  private case object NotExistsForallNot extends ReplayLaw { val name = "¬∃=∀¬" }
  private case object ForallAndBoth extends ReplayLaw { val name = "∀∧" }
  private case object ForallAndDistLeft extends ReplayLaw { val name = "∀∧_dist_l" }
  private case object ForallAndDistRight extends ReplayLaw { val name = "∀∧_dist_r" }
  private case object ForallOrDistLeft extends ReplayLaw { val name = "∀∨_dist_l" }
  private case object ForallOrDistRight extends ReplayLaw { val name = "∀∨_dist_r" }
  private case object ExistsOrLeft extends ReplayLaw { val name = "∃∨_l" }
  private case object ExistsOrRight extends ReplayLaw { val name = "∃∨_r" }
  private case object ExistsImpRight extends ReplayLaw { val name = "∃⇒_r" }
  private case object ExistsImpLeft extends ReplayLaw { val name = "∃⇒_l" }
  private case object ForallImpLeft extends ReplayLaw { val name = "∀⇒_l" }
  private case object ForallImpRight extends ReplayLaw { val name = "∀⇒_r" }
  private case object ExistsImpBoth extends ReplayLaw { val name = "∃⇒" }
  private case object ExistsAndRight extends ReplayLaw { val name = "∃∧_r" }
  private case object ExistsAndLeft extends ReplayLaw { val name = "∃∧_l" }
  private case object ExistsOrBoth extends ReplayLaw { val name = "∃∨" }

  private sealed trait ConnectiveKind {
    def leoRepresentation(left: Term, right: Term): Term
    def lpRepresentation(left: LpTerm[Level.Obj], right: LpTerm[Level.Obj]): LpTerm[Level.Obj]
  }
  private case object Conjunction extends ConnectiveKind {
    override def leoRepresentation(left: Term, right: Term): Term = &(left, right)
    override def lpRepresentation(left: LpTerm[Level.Obj], right: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LogicConst.And(left, right)
  }
  private case object Disjunction extends ConnectiveKind {
    override def leoRepresentation(left: Term, right: Term): Term = |||(left, right)
    override def lpRepresentation(left: LpTerm[Level.Obj], right: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LogicConst.Or(left, right)
  }
  private case object Implication extends ConnectiveKind {
    override def leoRepresentation(left: Term, right: Term): Term = Impl(left, right)
    override def lpRepresentation(left: LpTerm[Level.Obj], right: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LogicConst.Imp(left, right)
  }

  /** Mapping of recorded connective moves to the corresponding child-to-parent equality. */
  private def connectiveLaw(kind: ConnectiveKind, universal: Boolean, movement: MiniscopePush): Option[ReplayLaw] =
    (kind, universal, movement) match {
      case (Conjunction, true, MiniscopePushLeft) => Some(ForallAndDistLeft)
      case (Conjunction, true, MiniscopePushRight) => Some(ForallAndDistRight)
      case (Conjunction, true, MiniscopePushBoth) => Some(ForallAndBoth)
      case (Conjunction, false, MiniscopePushLeft) => Some(ExistsAndLeft)
      case (Conjunction, false, MiniscopePushRight) => Some(ExistsAndRight)
      case (Disjunction, true, MiniscopePushLeft) => Some(ForallOrDistLeft)
      case (Disjunction, true, MiniscopePushRight) => Some(ForallOrDistRight)
      case (Disjunction, false, MiniscopePushLeft) => Some(ExistsOrLeft)
      case (Disjunction, false, MiniscopePushRight) => Some(ExistsOrRight)
      case (Disjunction, false, MiniscopePushBoth) => Some(ExistsOrBoth)
      case (Implication, true, MiniscopePushLeft) => Some(ForallImpLeft)
      case (Implication, true, MiniscopePushRight) => Some(ForallImpRight)
      case (Implication, false, MiniscopePushLeft) => Some(ExistsImpLeft)
      case (Implication, false, MiniscopePushRight) => Some(ExistsImpRight)
      case (Implication, false, MiniscopePushBoth) => Some(ExistsImpBoth)
      case _ => None
    }

  // Inputs shared by replay and script emission after checking the step shape.
  private final case class Context(parent: Clause,
                                   child: Clause,
                                   parentProofName: QName,
                                   encParent: lpClauseInst,
                                   encChild: lpClauseInst,
                                   trace: MiniscopeTrace)

  private def initContext(child: ClauseProxy, parentProofNames: Seq[QName]): Either[String, Context] = {
    // This encoder handles one non-equational literal and one parent proof.
    val parents = child.annotation.parents
    if (parents.size != 1 || parentProofNames.size != 1)
      return Left(s"Miniscope step ${child.id}: expected one parent and one resolved proof name")

    val parent = parents.head.cl
    val result = child.cl
    // ensure both parent and child clauses are non-equational unit clauses
    if (Clause.empty(parent) || Clause.empty(result) || !Clause.unit(parent) || !Clause.unit(result) ||
        parent.lits.head.equational || result.lits.head.equational || parent.lits.head.polarity != result.lits.head.polarity)
      return Left(s"Miniscope step ${child.id}: expected non-equational unit clauses with the same literal polarity")

    child.furtherInfo.miniscopeTrace match {
      case None => Left(s"Miniscope step ${child.id}: missing source-decision trace")
      case Some(trace) =>
        // Translate both clauses with one variable map, so later comparisons use the same Lambdapi names for shared free variables.
        val (_, encoded) = lpClauseInst.apply_to_set(Seq(parent, result))
        val ctx = Context(parent, result, parentProofNames.head, encoded.head, encoded(1), trace)
        Out.lp_debug_info(s"Miniscope step ${child.id}: parent ${parents.head.id} as ${Renderer.qname(ctx.parentProofName, RenderOptions())}, ${ctx.trace.observations.size} source observations")
        Out.lp_debug_info(s"Miniscope source observations: ${ctx.trace.observations}")
        Out.lp_debug_info(s"Miniscope translated parent: ${ctx.encParent.term}")
        Out.lp_debug_info(s"Miniscope translated child: ${ctx.encChild.term}")
        Right(ctx)
    }
  }

  // Orchestrator

  /**
    * Orchestrator for the encoding of Leo-III's `miniscope` steps.
    *
    * Proof blueprint:
    * 1. For each transformation recorded by the trace:
    *   1 a) Replay recorded move by applying the corresponding Lambdapi theorem using 'rewrite'
    *   1 b) Apply the 'simplify rule off' tactic to beta-contract the goal
    * 2. Refine with the parent.
    *
    * Performed transformations are replayed in reverse, transforming the goal representing the derived child one step at a time.
    */
  def encMiniscope(child: ClauseProxy, parentProofNames: Seq[QName], sig: LpSig): EncodeResult = {
    Out.lp_debug_info(s"Encoding Miniscope step ${child.id} with ${parentProofNames.size} resolved parent name(s)")
    initContext(child, parentProofNames) match {
      case Left(reason) => NotEncodable(reason)
      case Right(ctx) =>
        planReplay(ctx, sig) match {
          case Left(reason) =>
            Out.lp_debug_info(reason)
            NotEncodable(reason)
          case Right(moves) => emitScript(ctx, moves, sig)
        }
    }
  }

  // Replay of recorded miniscoping traces

  private final case class PlannedMove(observation: MiniscopeObservation,
                                       law: ReplayLaw,
                                       pattern: RewritePattern)

  // A binder remains pending while the traversal follows its body. Its kind
  // changes when a recorded crossing moves it under a negation. The pattern
  // name is local to the wrapper; matching does not require the goal's name.
  private final case class PendingBinder(typ: Type, universal: Boolean, patternName: Name) {
    def crossed: PendingBinder = copy(universal = !universal)
  }

  /** Traverse the parent and consume source decisions at their recorded visits. */
  private def planReplay(ctx: Context, sig: LpSig): Either[String, Vector[PlannedMove]] = {
    implicit val sourceSig: Signature = sig.orig
    val observations = ctx.trace.observations
    val polarity = ctx.parent.lits.head.polarity
    val moves = Vector.newBuilder[PlannedMove]
    var cursor = 0 // next observation in the producer's source traversal order

    // Reconstruct a binder term
    def quant(binder: PendingBinder, body: Term): Term =
      if (binder.universal) Forall(\(binder.typ)(body))
      else Exists(\(binder.typ)(body))

    // Wrap in pending binders. They are ordered outermost first.
    def prefix(binders: Vector[PendingBinder], body: Term): Term =
      binders.reverseIterator.foldLeft(body)((term, binder) => quant(binder, term))
    // Wrap in pending negations
    def surround(body: Term, negations: Int): Term =
      (0 until negations).foldLeft(body)((term, _) => Not(term))

    // Wrapper for all crossings recorded at a given connective
    final case class ConnectiveReplay(retained: Vector[PendingBinder],
                                      leftInput: Term, leftPending: Vector[PendingBinder],
                                      rightInput: Term, rightPending: Vector[PendingBinder],
                                      moves: Vector[(MiniscopeObservation, ReplayLaw, Vector[PendingBinder])],
                                      description: String)

    // Apply substitutions to fix binders. Necessary to reconstruct and check against child.
    def branchSubst(indices: Vector[Int], branchBinders: Int): Subst =
      indices.foldLeft(Subst.shift(branchBinders): Subst) { (subst, index) =>
        BoundFront(index) +: subst
      }

    // Shared traversal of binary connective terms.
    // All connective decisions share the branch traversal and one-hole
    // contexts; only validation, binder routing, and the proved law vary.
    def visitConnective(left: Term, right: Term, pending: Vector[PendingBinder], at: Position,
                        outerNegations: Int, outerPattern: PatternContext,
                        kind: ConnectiveKind): Either[String, Term] = {
      // collect all recorded crossings at given position
      val start = cursor
      while (cursor < observations.size && observations(cursor).sourceVisit == at) cursor += 1
      val here = observations.slice(start, cursor)
      // The producer tests pending binders from inner to outer and stops at
      // the first binder that cannot move. Validate every recorded decision
      // against its source occurrences.
      var retained = Vector.empty[PendingBinder]
      var leftQuants = Vector.empty[PendingBinder]
      var rightQuants = Vector.empty[PendingBinder]
      var leftIndices = Vector.empty[Int]
      var rightIndices = Vector.empty[Int]
      val planned = Vector.newBuilder[(MiniscopeObservation, ReplayLaw, Vector[PendingBinder])]
      var failure: Option[String] = None
      var stopped = false
      var tested = 0
      while (tested < pending.size && !stopped && failure.isEmpty) {
        val ordinal = pending.size - 1 - tested
        val binder = pending(ordinal)
        val bound = tested + 1
        // test if recorded move is allowed at given position
        val leftOccurs = left.looseBounds.contains(bound)
        val rightOccurs = right.looseBounds.contains(bound)
        // The producer permits duplication only for ∀/∧ and ∃/∨,⇒.
        val canDuplicate = kind match {
          case Conjunction => binder.universal
          case Disjunction | Implication => !binder.universal
        }
        val expected: Option[MiniscopePush] = (leftOccurs, rightOccurs) match {
          case (true, false) => Some(MiniscopePushLeft)
          case (false, true) => Some(MiniscopePushRight)
          case (true, true) if canDuplicate => Some(MiniscopePushBoth)
          case _ => None
        }
        (here.lift(tested), expected) match {
          // expected law is applied on trace -> record planned move
          case (Some(event @ MiniscopePushAtConnective(_, `ordinal`, movement)), Some(expectedMovement))
              if movement == expectedMovement =>
            connectiveLaw(kind, binder.universal, movement) match {
              case None => failure = Some(s"Miniscope: no proved law for $kind $movement at ${at.pretty}")
              case Some(law) =>
                planned += ((event, law, pending.take(ordinal)))
                if (movement == MiniscopePushLeft || movement == MiniscopePushBoth)
                  leftQuants = binder.copy(universal = if (kind == Implication) !binder.universal else binder.universal) +: leftQuants
                if (movement == MiniscopePushRight || movement == MiniscopePushBoth)
                  rightQuants = binder +: rightQuants
                leftIndices = (if (leftQuants.nonEmpty) leftQuants.size else 1) +: leftIndices
                rightIndices = (if (rightQuants.nonEmpty) rightQuants.size else 1) +: rightIndices
            }
          // no further crossing of quantifiers possible -> stop miniscoping
          case (Some(MiniscopeStopAtConnective(_, `ordinal`)), None) =>
            retained = pending.take(ordinal + 1)
            stopped = true
          case _ =>
            failure = Some(s"Miniscope: missing or inconsistent connective decision at ${at.pretty}, binder $ordinal")
        }
        tested += 1
      }
      if (failure.isEmpty && here.size != tested)
        failure = Some(s"Miniscope: extra connective decisions at ${at.pretty}")
      if (failure.isEmpty && pending.isEmpty && here.nonEmpty)
        failure = Some(s"Miniscope: unexpected connective decision at ${at.pretty}")

      // construct a Connective Replay event for successful reconstructions
      val replay: Either[String, ConnectiveReplay] = failure match {
        case Some(reason) => Left(reason)
        case None =>
          val leftSubstituted = left.substitute(branchSubst(leftIndices, leftQuants.size))
          val rightSubstituted = right.substitute(branchSubst(rightIndices, rightQuants.size))
          val leftInput = if (kind == Implication) leftSubstituted else leftSubstituted.betaNormalize
          val rightInput = if (kind == Implication) rightSubstituted else rightSubstituted.betaNormalize
          Right(ConnectiveReplay(retained,
            leftInput, leftQuants, rightInput, rightQuants, planned.result(),
            s"Miniscope: replayed $tested connective decision(s) at ${at.pretty}"))
      }

      replay.flatMap { checked =>
        if (here.nonEmpty) Out.lp_debug_info(checked.description)
        checked.moves.foreach { case (event, law, binders) =>
          // extract the individual moves
          moves += PlannedMove(event, law, makePattern(polarity, outerPattern, binders))
        }
        // construct the necessary patterns
        val retainedPattern: PatternContext = hole =>
          outerPattern(wrapPatternBinders(checked.retained, hole))
        val leftPattern: PatternContext = hole =>
          retainedPattern(kind.lpRepresentation(hole, Wildcard[Level.Obj]()))
        val rightPattern: PatternContext = hole =>
          retainedPattern(kind.lpRepresentation(Wildcard[Level.Obj](), hole))
        for {
          // traverse the branches and re-construct a term
          rebuiltLeft <- visit(checked.leftInput, checked.leftPending, at.argPos(1), 0, leftPattern)
          rebuiltRight <- visit(checked.rightInput, checked.rightPending, at.argPos(2), 0, rightPattern)
        } yield surround(prefix(checked.retained, kind.leoRepresentation(rebuiltLeft, rebuiltRight)), outerNegations)
      }
    }

    // Traverse the term building the sequence of checked moves and reconstructing the child from the trace
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
        val start = cursor // Consecutive events naming this visit form its crossing group.
        // Go through all observations at given position
        while (cursor < observations.size && observations(cursor).sourceVisit == at) cursor += 1
        val here = observations.slice(start, cursor)
        if (here.exists(event => !event.isInstanceOf[MiniscopeCrossNegation]))
          Left(s"Miniscope: connective observation at source negation ${at.pretty}")
        else {
          val crossings = here.collect { case event: MiniscopeCrossNegation => event }
          // For this schema the recorder emits one crossing per pending binder,
          // outermost first. 
          if (crossings.map(_.pendingBinderOrdinal) != pending.indices.toVector)
            Left(s"Miniscope: incomplete or reordered crossings at ${at.pretty}")
          else {
            // Each event changes one binder kind and captures the context of its post-move target.
            var crossedPending = pending
            // The innermost binder crosses first, so the remaining outer binders are exactly the wrappers around this event's target.
            crossings.reverse.foreach { event =>
              val ordinal = event.pendingBinderOrdinal
              val crossed = crossedPending(ordinal).crossed
              crossedPending = crossedPending.updated(ordinal, crossed)
              val pattern = makePattern(polarity, outerPattern, crossedPending.take(ordinal))
              val law = if (crossed.universal) NotForallExistsNot else NotExistsForallNot
              moves += PlannedMove(event, law, pattern)
            }
            // This negation remains outside subsequent source visits, and is added to the outer pattern.
            val insideNegation: PatternContext = hole => outerPattern(LogicConst.Not(hole))
            visit(body, crossedPending, at.argPos(1), outerNegations + 1, insideNegation)
          }
        }
      case (left & right) =>
        visitConnective(left, right, pending, at, outerNegations, outerPattern, Conjunction)
      case (left ||| right) =>
        visitConnective(left, right, pending, at, outerNegations, outerPattern, Disjunction)
      case Impl(left, right) =>
        visitConnective(left, right, pending, at, outerNegations, outerPattern, Implication)
      case leaf =>
        // No more decisions remain on this path; restore its pending context.
        Right(surround(prefix(pending, leaf), outerNegations))
    }

    val identityPattern: PatternContext = identity
    visit(ctx.parent.lits.head.left, Vector.empty, Position.root, 0, identityPattern).flatMap { result =>
      val planned = moves.result()
      if (cursor != observations.size)
        Left(s"Miniscope: ${observations.size - cursor} unconsumed source observations")
      else if (planned.isEmpty)
        Left("Miniscope: no supported moves")
      else if (result != ctx.child.lits.head.left)
        Left("Miniscope: replay does not reach the recorded child")
      else Right(planned)
    }
  }

  /** Wrap a hole with the part of the Lambdapi goal already traversed. */
  private type PatternContext = LpTerm[Level.Obj] => LpTerm[Level.Obj]

  private def wrapPatternBinders(binders: Vector[PendingBinder], hole: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
    binders.reverseIterator.foldLeft(hole) { (body, binder) =>
      val typedName = (binder.patternName, LpType.El(TypeEncoding.type2LP(binder.typ)))
      if (binder.universal) LogicConst.Forall(typedName, body)
      else LogicConst.Exists(typedName, body)
    }

  /** Compose the reusable outer context with this move's pending binders. */
  private def makePattern(polarity: Boolean, outer: PatternContext,
                          binders: Vector[PendingBinder]): RewritePattern = {
    val hole = Const[Level.Obj](SymRef.LP(QName.local("x")))
    val bodyPattern = outer(wrapPatternBinders(binders, hole))
    // PatternBuilder adds the signed literal and unit-clause context.
    val info = PatternBuilder.PatternInfo(0, None, polarity, PatternBuilder.LiteralBody)
    val literalPattern = PatternBuilder.generatePatternLit(info, bodyPattern)
    PatternBuilder.generateClausePattern(0, 1, literalPattern)
  }

  /** Reverse the checked source moves to transform the child goal into the parent goal. */
  private def emitScript(ctx: Context, moves: Vector[PlannedMove], sig: LpSig): EncodeResult = {
    if (moves.isEmpty) return NotEncodable("Miniscope: no supported moves")

    // The Lambdapi goal starts at the child. Each rewrite undoes one recorded
    // move; beta cleanup exposes the next target in the resulting goal.
    val reverseMoves = moves.reverse
    val rewrites = reverseMoves.zipWithIndex.flatMap { case (move, index) =>
      val rewrite = Rewrite(Some(move.pattern), move.law.theorem)
      Out.lp_debug_info(s"Miniscope ${move.observation.sourceVisit.pretty}: ${Renderer.proof(rewrite, RenderOptions(), sig)}")
      // beta-reduce between rewrite tactic applications
      if (index < reverseMoves.size - 1) Vector(rewrite, Try(Simplify(onlyBeta = true)))
      else Vector(rewrite)
    }
    val refine = Refine(Const[Level.Meta](SymRef.LP(ctx.parentProofName)))
    Encoded(rewrites :+ refine)
  }

}
