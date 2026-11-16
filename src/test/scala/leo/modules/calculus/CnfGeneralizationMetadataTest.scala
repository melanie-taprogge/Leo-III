package leo.modules.calculus

import leo.{Checked, LeoTestSuite}
import leo.datastructures._
import leo.modules.HOLSignature.{&, Exists, Forall, Not, |||}
import leo.modules.input.Input

class CnfGeneralizationMetadataTest extends LeoTestSuite {
  private def input(formula: String)(implicit sig: Signature): Clause = {
    val (_, term, _) = Input.readAnnotated(s"fof(test,axiom,($formula)).")
    Clause(Literal(term, true))
  }

  private def moves(result: CoreCNF.CnfResolution): Seq[MoveQuantStep] =
    result.steps.flatMap(_.addInfo.addInfoQuants.collect { case q: MoveQuantStep => q })

  private def at(term: Term, position: Position): Term = {
    if (position == Position.root) term
    else term match {
      case &(left, right) => at(if (position.posHead == 1) left else right, position.tail)
      case |||(left, right) => at(if (position.posHead == 1) left else right, position.tail)
      case Not(body) if position.posHead == 1 => at(body, position.tail)
      case _ => fail(s"Invalid recorded quantifier position ${position.pretty}")
    }
  }

  /** Independently validate that the recorded pair changes only the selected quantifier. */
  private def checkOccurrence(move: MoveQuantStep): GeneralizationOccurrence = {
    val occurrence = move.occurrence.getOrElse(fail("Missing generalization occurrence"))
    val position = occurrence.position
    assert(position.litIdx == 0 && position.side == Literal.leftSide)
    assert(Clause.unit(position.cl) && position.cl.lits.head.polarity)
    val before = position.cl.lits.head.left
    val predicate = (move.polarity, at(before, position.pos)) match {
      case (QuantUniv, Forall(body)) => body
      case (QuantExists, Exists(body)) => body
      case _ => fail("Recorded position does not select the expected quantifier")
    }
    val (index, typ) = move.corrChildVar
    assert(!before.fv.exists(_._1 == index), "Generalization variable must be fresh")
    val instance = Term.mkTermApp(predicate, Term.mkBound(typ, index)).betaNormalize.etaExpand
    val expected = Clause(Literal(before.replaceAt(position.pos, instance), true))
    assert(occurrence.after == expected, "Recorded after-clause includes an unrelated transformation")
    occurrence
  }

  test("Nested generalizations retain complete contexts in source order without extra steps", Checked) {
    implicit val sig: Signature = getFreshSignature
    val parent = input("a & ((![X]:(![Y]:r(X,Y))) | b)")
    val result = FullCNF(freshVarGen(parent), parent)
    val recorded = moves(result)
    assert(recorded.size == 2)
    val first = checkOccurrence(recorded.head)
    val second = checkOccurrence(recorded(1))
    assert(result.steps.size == 1 && result.steps.head.skolem.isEmpty)
    assert(first.position.cl == parent)
    assert(first.position.pos == Position.root.argPos(2).argPos(1))
    assert(second.position.pos == first.position.pos)
    assert(second.position.cl == first.after)
    assert(second.after == result.steps.head.after)
    assert(recorded.map(_.corrChildVar._1).distinct.size == 2)
  }

  test("Generalizations on either side of a Skolemization stay in their respective CNF segments", Checked) {
    implicit val sig: Signature = getFreshSignature
    val parent = input("![X]:(?[Y]:(![Z]:r(X,Y,Z)))")
    val result = FullCNF(freshVarGen(parent), parent)
    assert(result.steps.map(_.skolem.nonEmpty) == Seq(false, true, false))
    assert(result.steps.map(_.addInfo.addInfoQuants.count(_.isInstanceOf[MoveQuantStep])) == Seq(1, 0, 1))
    val recorded = moves(result).map(checkOccurrence)
    assert(recorded.head.position.cl == parent)
    assert(recorded.head.after == result.steps.head.after)
    assert(recorded(1).position.cl == result.steps(1).after)
    assert(recorded(1).after == result.steps.last.after)
    assert(result.steps(1).skolem.get._2.cl == result.steps.head.after)
  }

  test("A generalization between two Skolemizations is emitted only in the intervening CNF metadata", Checked) {
    implicit val sig: Signature = getFreshSignature
    val parent = input("?[X]:(![Y]:(?[Z]:r(X,Y,Z)))")
    val result = FullCNF(freshVarGen(parent), parent)
    assert(result.steps.map(_.skolem.nonEmpty) == Seq(true, false, true))
    assert(result.steps.map(_.addInfo.addInfoQuants.count(_.isInstanceOf[MoveQuantStep])) == Seq(0, 1, 0))
    val recorded = moves(result)
    assert(recorded.size == 1)
    val occurrence = checkOccurrence(recorded.head)
    assert(occurrence.position.cl == result.steps.head.after)
    assert(occurrence.after == result.steps(1).after)
    assert(result.steps.last.skolem.get._2.cl == occurrence.after)
  }

  test("A generalization preserves its pending Skolem sibling in both intermediate clauses", Checked) {
    implicit val sig: Signature = getFreshSignature
    val parent = input("(![X]:p(X)) | (?[Y]:q(Y))")
    val result = FullCNF(freshVarGen(parent), parent)
    assert(result.steps.map(_.skolem.nonEmpty) == Seq(false, true))
    val recorded = moves(result)
    assert(recorded.size == 1)
    val occurrence = checkOccurrence(recorded.head)
    assert(occurrence.position.pos == Position.root.argPos(1))
    assert(occurrence.position.cl == parent)
    assert(occurrence.after == result.steps.head.after)
    assert(at(occurrence.after.lits.head.left, Position.root.argPos(2)) match {
      case Exists(_) => true
      case _ => false
    })
  }

  test("A generalization after a Skolem sibling retains the updated left context", Checked) {
    implicit val sig: Signature = getFreshSignature
    val parent = input("(?[X]:p(X)) | (![Y]:q(Y))")
    val result = FullCNF(freshVarGen(parent), parent)
    assert(result.steps.map(_.skolem.nonEmpty) == Seq(true, false))
    val recorded = moves(result)
    assert(recorded.size == 1)
    val occurrence = checkOccurrence(recorded.head)
    assert(occurrence.position.pos == Position.root.argPos(2))
    assert(occurrence.position.cl == result.steps.head.after)
    assert(occurrence.after == result.steps.last.after)
  }

  test("Negative existential generalization records the quantifier beneath its negation", Checked) {
    implicit val sig: Signature = getFreshSignature
    val parent = input("(~(?[X]:(![Y]:r(X,Y)))) | s")
    val result = FullCNF(freshVarGen(parent), parent)
    assert(result.steps.map(_.skolem.nonEmpty) == Seq(false, true))
    val recorded = moves(result)
    assert(recorded.size == 1 && recorded.head.polarity == QuantExists)
    val occurrence = checkOccurrence(recorded.head)
    assert(occurrence.position.pos == Position.root.argPos(1).argPos(1))
    assert(occurrence.position.cl == parent)
    assert(occurrence.after == result.steps.head.after)
  }

  test("Missing optional local evidence retains the previous metadata-consuming behavior", Checked) {
    implicit val sig: Signature = getFreshSignature
    val parent = input("![X]:p(X)")
    val local = CoreCNF.apply0(Vector.empty, Vector.empty, freshVarGen(parent), None, parent.lits.head)
      .asInstanceOf[CoreCNF.MovedQuant]
    val complete = CoreCNF.cnfFragment2Clause(parent, local)
    for (fragment <- Seq(local.copy(after = None), local.copy(addInfo = None), local.copy(after = None, addInfo = None))) {
      val result = CoreCNF.cnfFragment2Clause(parent, fragment)
      assert(result.clauses == complete.clauses)
      assert(result.steps.map(_.after) == complete.steps.map(_.after))
      assert(moves(result).size == fragment.addInfo.size)
      assert(moves(result).forall(_.occurrence.isEmpty))
    }
  }

  private def cnf(parent: Clause, renaming: Boolean)(implicit sig: Signature): CoreCNF.CnfResolution =
    if (renaming) RenameCNF(freshVarGen(parent), scala.collection.mutable.Map.empty, parent)
    else FullCNF(freshVarGen(parent), parent)

  for ((producer, renaming) <- Seq("FullCNF" -> false, "RenameCNF" -> true)) {
    for ((connective, formula) <- Seq(
      "disjunction" -> "(![X]:p(X)) | (![Y]:q(Y))",
      "conjunction" -> "(![X]:p(X)) & (![Y]:q(Y))")) {
      test(s"$producer: generalizations in both $connective branches retain the evolving context", Checked) {
        implicit val sig: Signature = getFreshSignature
        val parent = input(formula)
        val result = cnf(parent, renaming)
        val recorded = moves(result)
        assert(recorded.size == 2)
        val first = checkOccurrence(recorded.head)
        val second = checkOccurrence(recorded(1))
        assert(first.position.cl == parent)
        assert(first.position.pos == Position.root.argPos(1))
        assert(second.position.pos == Position.root.argPos(2))
        assert(second.position.cl == first.after)
        assert(result.steps.size == 1 && result.steps.head.skolem.isEmpty)
        assert(second.after == result.steps.head.after)
        assert(recorded.map(_.corrChildVar._1) == Seq(1, 2))
        val left = at(second.after.lits.head.left, Position.root.argPos(1))
        val right = at(second.after.lits.head.left, Position.root.argPos(2))
        assert(left.fv == Set(recorded.head.corrChildVar))
        assert(right.fv == Set(recorded(1).corrChildVar))
        val expected = if (connective == "conjunction") Seq(Clause(Literal(left, true)), Clause(Literal(right, true)))
                       else Seq(Clause(Seq(Literal(left, true), Literal(right, true))))
        assert(result.clauses == expected)
      }
    }

    for ((kind, formula, polarity) <- Seq(
      ("universal", "![X]:q", QuantUniv),
      ("negative existential", "~(?[X]:q)", QuantExists))) {
      test(s"$producer: a vacuous $kind retains its occurrence despite its unused variable", Checked) {
        implicit val sig: Signature = getFreshSignature
        val parent = input(formula)
        val result = cnf(parent, renaming)
        val recorded = moves(result)
        assert(recorded.size == 1 && recorded.head.polarity == polarity)
        val occurrence = checkOccurrence(recorded.head)
        assert(occurrence.position.cl == parent)
        assert(occurrence.position.pos == (if (polarity == QuantUniv) Position.root else Position.root.argPos(1)))
        assert(Clause.ground(occurrence.after))
        assert(!occurrence.after.implicitlyBound.contains(recorded.head.corrChildVar))
        val atom = input("q").lits.head.left
        assert(result.clauses == Seq(Clause(Literal(atom, polarity == QuantUniv))))
        assert(result.steps.size == 1 && result.steps.head.after == occurrence.after)
      }
    }

    test(s"$producer: a vacuous outer binder still consumes its variable allocation", Checked) {
      implicit val sig: Signature = getFreshSignature
      val parent = input("![X]:(![Y]:p(Y))")
      val result = cnf(parent, renaming)
      val recorded = moves(result)
      assert(recorded.map(_.corrChildVar._1) == Seq(1, 2))
      val first = checkOccurrence(recorded.head)
      val second = checkOccurrence(recorded(1))
      assert(Clause.ground(first.after))
      assert(first.after == second.position.cl)
      assert(second.after.implicitlyBound == Seq(recorded(1).corrChildVar))
      assert(result.clauses.head.implicitlyBound == Seq(recorded(1).corrChildVar))
      assert(result.steps.size == 1 && second.after == result.steps.head.after)
    }

    test(s"$producer: multiple input literals retain their complete signed disjunction context", Checked) {
      implicit val sig: Signature = getFreshSignature
      val a = input("a").lits.head
      val quantified = input("![X]:p(X)").lits.head
      val notB = Literal(input("b").lits.head.left, false)
      val parent = Clause(Seq(a, quantified, notB))
      assert(parent.lits.size == 3)
      val result = cnf(parent, renaming)
      val recorded = moves(result)
      assert(recorded.size == 1)
      val occurrence = checkOccurrence(recorded.head)
      val expectedBefore = |||(|||(Literal.asTerm(a), Literal.asTerm(quantified)), Literal.asTerm(notB))
      assert(occurrence.position.cl == Clause(Literal(expectedBefore, true)))
      assert(occurrence.position.pos == Position.root.argPos(1).argPos(2))
      val after = occurrence.after.lits.head.left
      assert(at(after, Position.root.argPos(1).argPos(1)) == Literal.asTerm(a))
      assert(at(after, Position.root.argPos(2)) == Literal.asTerm(notB))
      val instance = at(after, occurrence.position.pos)
      assert(result.clauses == Seq(Clause(Seq(a, Literal(instance, true), notB))))
      val expectedFinal = |||(Literal.asTerm(a), |||(instance, Literal.asTerm(notB)))
      assert(result.steps.size == 1 && result.steps.head.after == Clause(Literal(expectedFinal, true)))
      assert(occurrence.after != result.steps.head.after, "The immediate pair must precede final reassociation")
    }

    test(s"$producer: different input literals share one fresh-variable context", Checked) {
      implicit val sig: Signature = getFreshSignature
      val p = input("![X]:p(X)").lits.head
      val q = input("![Y]:q(Y)").lits.head
      val predicate = p.left match { case Forall(body) => body; case _ => fail("Expected universal input") }
      val typ = predicate.ty._funDomainType
      val existing = Term.mkBound(typ, 7)
      val negative = Literal(Term.mkTermApp(predicate, existing).betaNormalize.etaExpand, false)
      val parent = Clause(Seq(p, q, negative))
      val result = cnf(parent, renaming)
      val recorded = moves(result)
      assert(recorded.map(_.corrChildVar) == Seq(8 -> typ, 9 -> typ))
      val first = checkOccurrence(recorded.head)
      val second = checkOccurrence(recorded(1))
      assert(first.position.pos == Position.root.argPos(1).argPos(1))
      assert(second.position.pos == Position.root.argPos(1).argPos(2))
      assert(second.position.cl == first.after)
      assert(at(second.after.lits.head.left, Position.root.argPos(2)) == Literal.asTerm(negative))
      assert(result.clauses.size == 1 && result.clauses.head.lits.size == 3)
      assert(result.clauses.head.implicitlyBound.map(_._1).toSet == Set(7, 8, 9))
      assert(result.clauses.head.lits.contains(negative))
      assert(result.steps.size == 1 && result.steps.head.skolem.isEmpty)
    }
  }

  test("RenameCNF: generalization occurrences survive actual formula renaming", Checked) {
    implicit val sig: Signature = getFreshSignature
    val parent = input("((![X]:p(X)) & a) | (((![Y]:q(Y)) & b) | ((![Z]:r(Z)) & c))")
    val result = cnf(parent, renaming = true)
    assert(result.steps.exists(_.addInfo.renameHappend))
    val recorded = moves(result)
    assert(recorded.nonEmpty)
    recorded.foreach(checkOccurrence)
    assert(result.steps.filter(_.skolem.nonEmpty).forall(step =>
      !step.addInfo.addInfoQuants.exists(_.isInstanceOf[MoveQuantStep])))
  }
}
