package leo.modules.prover

import leo.{Checked, LeoTestSuite}
import leo.datastructures._
import leo.modules.calculus.{CalculusRule, CnfConj, CnfSkolem, CoreCNF, FullCNF, RenameCNF, freshVarGen}
import leo.modules.control.Control
import leo.modules.control.inferenceControl.CNFControl
import leo.modules.input.Input

class CnfControlMetadataTest extends LeoTestSuite {
  private def input(formula: String)(implicit sig: Signature): Clause = {
    val (_, term, _) = Input.readAnnotated(s"fof(test,axiom,($formula)).")
    Clause(Literal(term, true))
  }

  private def cnf(parent: Clause, renaming: Boolean)(implicit sig: Signature): CoreCNF.CnfResolution =
    if (renaming) RenameCNF(freshVarGen(parent), scala.collection.mutable.Map.empty, parent)
    else FullCNF(freshVarGen(parent), parent)

  private def moves(node: ClauseProxy): Seq[MoveQuantStep] =
    node.furtherInfo.cnfInfo.addInfoQuants.collect { case q: MoveQuantStep => q }

  private def ancestry(leaves: Iterable[ClauseProxy]): Vector[ClauseProxy] = {
    val seen = scala.collection.mutable.Set.empty[Long]
    val result = Vector.newBuilder[ClauseProxy]
    def visit(node: ClauseProxy): Unit = if (seen.add(node.id)) {
      node.annotation.parents.foreach(visit)
      result += node
    }
    leaves.foreach(visit)
    result.result()
  }

  private def state(renaming: Boolean)(implicit sig: Signature): State[AnnotatedClause] = {
    val result = State.fresh[AnnotatedClause](sig)
    result.setRunStrategy(RunStrategy.defaultStrategy.copy(renaming = renaming))
    result
  }

  for ((producer, renaming) <- Seq("FullCNF" -> false, "RenameCNF" -> true)) {
    test(s"$producer: annotation preserves complete occurrence and Skolem metadata at every boundary", Checked) {
      implicit val sig: Signature = getFreshSignature
      val parent = input("![X]:(?[Y]:(![Z]:r(X,Y,Z)))")
      val result = cnf(parent, renaming)
      val kind: CalculusRule = if (renaming) RenameCNF else FullCNF
      val properties = ClauseAnnotation.PropSOS | ClauseAnnotation.PropFullySimplified | ClauseAnnotation.PropShallowSimplified
      var last = AnnotatedClause(parent, ClauseAnnotation.NoAnnotation, properties)
      val nodes = result.steps.map { step =>
        val node = CNFControl.annotateCnfSteps(step, sig, last, kind)
        assert(node.cl == step.after)
        assert(node.furtherInfo.cnfInfo == step.addInfo)
        assert(node.annotation.parents.head == last)
        assert(node.properties == ClauseAnnotation.PropSOS)
        step.skolem match {
          case Some((_, position)) =>
            assert(node.annotation.fromRule == CnfSkolem)
            assert(node.annotation.parents.size == 2)
            val definition = node.annotation.parents(1)
            assert(definition.role == Role_Definition && definition.annotation.parents == Seq(last))
            val recorded = node.furtherInfo.cnfInfo.addInfoQuants.collect { case q: SkolemStep => q }
            assert(recorded.size == 1 && recorded.head.position.contains(position))
            assert(position.cl == last.cl)
          case None =>
            assert(node.annotation.fromRule == kind && node.annotation.parents == Seq(last))
        }
        last = node
        node
      }
      assert(nodes.size == 3)
      assert(nodes.map(moves).map(_.size) == Seq(1, 0, 1))
      assert(nodes.flatMap(moves).forall(_.occurrence.isDefined))
    }

    test(s"$producer: conjunction selections retain the shared ancestor records without copying them", Checked) {
      implicit val sig: Signature = getFreshSignature
      implicit val localState: State[AnnotatedClause] = state(renaming)
      val parent = input("(![X]:p(X)) & (![Y]:q(Y))")
      val expected = cnf(parent, renaming)
      val root = AnnotatedClause(parent, ClauseAnnotation.NoAnnotation)
      val leaves = Control.cnf(root)
      assert(leaves.size == 2 && leaves.map(_.cl) == expected.clauses.toSet)
      assert(leaves.forall(_.annotation.fromRule == CnfConj))
      assert(leaves.forall(moves(_).isEmpty))
      val nodes = ancestry(leaves)
      val carriers = nodes.filter(moves(_).nonEmpty)
      assert(carriers.size == 1)
      assert(carriers.head.furtherInfo.cnfInfo == expected.steps.head.addInfo)
      assert(leaves.forall(_.annotation.parents == Seq(carriers.head)))
      val recorded = nodes.flatMap(moves)
      assert(recorded.map(_.corrChildVar._1) == Seq(1, 2))
      assert(recorded.forall(_.occurrence.isDefined))
      assert(nodes.size == 4, "Expected only the root, one CNF node, and two selections")
    }

    test(s"$producer: public CNF retains records and definition parents through an interleaved derivation", Checked) {
      implicit val sig: Signature = getFreshSignature
      implicit val localState: State[AnnotatedClause] = state(renaming)
      val root = AnnotatedClause(input("?[X]:(![Y]:(?[Z]:r(X,Y,Z)))"), ClauseAnnotation.NoAnnotation)
      val leaves = Control.cnf(root)
      assert(leaves.size == 1)
      val nodes = ancestry(leaves)
      val skolemNodes = nodes.filter(_.annotation.fromRule == CnfSkolem)
      assert(skolemNodes.size == 2)
      val carriers = nodes.filter(moves(_).nonEmpty)
      assert(carriers.size == 1 && moves(carriers.head).size == 1)
      val occurrence = moves(carriers.head).head.occurrence.getOrElse(fail("Lost occurrence at control boundary"))
      assert(carriers.head.annotation.parents.head == skolemNodes.head)
      assert(occurrence.position.cl == skolemNodes.head.cl)
      assert(occurrence.after == carriers.head.cl)
      assert(skolemNodes.last.annotation.parents.head == carriers.head)
      assert(nodes.count(_.role == Role_Definition) == 2)
      assert(nodes.size == 6, "Expected the root, three inference nodes, and two definitions")
      for (node <- skolemNodes) {
        val recorded = node.furtherInfo.cnfInfo.addInfoQuants.collect { case q: SkolemStep => q }
        assert(recorded.size == 1 && recorded.head.position.isDefined)
        assert(recorded.head.position.get.cl == node.annotation.parents.head.cl)
      }
    }

    test(s"$producer: the final multi-literal wrapper preserves occurrence records in its ancestor", Checked) {
      implicit val sig: Signature = getFreshSignature
      implicit val localState: State[AnnotatedClause] = state(renaming)
      val parent = Clause(Seq(input("![X]:p(X)").lits.head,
        input("![Y]:q(Y)").lits.head, Literal(input("a").lits.head.left, false)))
      val expected = cnf(parent, renaming)
      val root = AnnotatedClause(parent, ClauseAnnotation.NoAnnotation)
      val leaves = Control.cnf(root)
      assert(leaves.size == 1 && leaves.head.cl == expected.clauses.head)
      assert(leaves.head.cl.lits.size == 3 && moves(leaves.head).isEmpty)
      val nodes = ancestry(leaves)
      val carriers = nodes.filter(moves(_).nonEmpty)
      assert(carriers.size == 1)
      assert(carriers.head.furtherInfo.cnfInfo == expected.steps.head.addInfo)
      assert(leaves.head.annotation.parents == Seq(carriers.head))
      assert(nodes.flatMap(moves).map(_.corrChildVar._1) == Seq(1, 2))
      assert(nodes.size == 3, "Expected the original clause, CNF node, and final clause wrapper")
    }
  }
}
