package leo.modules.output.LPoutput

import java.nio.file.{Files, Paths}
import scala.collection.mutable

import leo.{Configuration, LeoTestSuite}
import leo.datastructures._
import leo.datastructures.ClauseAnnotation.NoAnnotation
import leo.modules.calculus.{CnfConj, CnfSkolem, FullCNF}
import leo.modules.control.Control
import leo.modules.input.{CLParameterParser, Input}
import leo.modules.proofOf
import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.prover.{RunStrategy, State}

class CnfEncodingTest extends LeoTestSuite {
  test("the running example exports both clauses through CNF and Skolemization") {
    val proof = CnfWitness.module()
    assert(proof.contains("symbol p:"))
    assert(!proof.contains("S."))
    assert(proof.contains("// cnf\nopaque symbol generalize_z:"))
    assert(proof.contains("// skolemize\nopaque symbol skolemize_y:"))
    assert(proof.contains("// cnf\nopaque symbol clausify:"))
    assert(proof.contains("// cnfConj\nopaque symbol clause_p:"))
    assert(proof.contains("// cnfConj\nopaque symbol clause_q:"))
    assert(proof.contains("refine (generalize_z "))
    assert(proof.contains("refine (skolemize_y "))
    assert(proof.contains("(clausify "))
    assert(proof.contains("symbol sk1_def (z : τ ι)"))
    assert(proof.contains("opaque symbol generalize_z: Π (z : τ ι)"))
    assert(proof.contains("opaque symbol clausify: Π (x : τ ι), Π (z : τ ι)"))
    assert(proof.contains("p z x y"))
    assert(proof.contains("p z u (sk1 z)"))
    assert("""\b[A-C]\b""".r.findFirstIn(proof).isEmpty)
    assert(proof.contains("symbol parent"))
    assert(proof.contains("repeat rewrite"))
    assert(proof.contains("have skolemEq_"))
    assert(proof.contains("have generalization_"))
    assert(proof.contains("(transform ["))
    assert(proof.contains("(mapAndLeft ["))
    val (beforeSkolem, afterSkolem) = proof.splitAt(proof.indexOf("// skolemize\n"))
    assert(beforeSkolem.contains("have boolean_"))
    assert(afterSkolem.contains("have boolean_"))
    assert(proof.contains("∧ₑₙ 0"))
    assert(proof.contains("∧ₑₙ 1"))
    assert(!proof.contains("admit"))
  }
}

/** Export the native proof graph for both clauses of the running CNF example. */
object CnfWitness {
  private val prelude =
    "require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred;\n" +
      LPoutput.gdvRequireOpenLine + "\n"

  // Leo assigns names independently for each clause and proof context.
  private val inputNames = WitnessVariableNames(Map("A" -> "z", "B" -> "y", "C" -> "x"))
  private val clauseNames = WitnessVariableNames(Map("A" -> "z", "B" -> "x", "C" -> "u"))

  def module(): String = {
    implicit val sig: Signature = Signature.freshWithHOL()
    implicit val state: State[AnnotatedClause] = State.fresh[AnnotatedClause](sig)
    state.setRunStrategy(RunStrategy.defaultStrategy.copy(renaming = false))

    Input.readAnnotated("thf(a_type,type,(a: $o)).")
    Input.readAnnotated("thf(b_type,type,(b: $o)).")
    Input.readAnnotated("thf(p_type,type,(p: $i > $i > $i > $o)).")
    Input.readAnnotated("thf(q_type,type,(q: $i > $i > $o)).")
    val (_, formula, _) = Input.readAnnotated(
      "thf(example,axiom,(![Z:$i]:(a => (b | (?[Y:$i]:((![X:$i]:(p @ Z @ X @ Y)) & (q @ Z @ Y))))))).")
    val parent = AnnotatedClause(Clause(Literal(formula, true)), NoAnnotation)
    val clauses = Control.cnf(parent).toVector.sortBy(_.furtherInfo.cnfConjInfo.get.idxInConj)
    val proof = clauses.flatMap(proofOf).distinctBy(_.id)
    val inferences = proof.filter(_.annotation.fromRule != null)
    val rules = inferences.map(_.annotation.fromRule)
    require(rules == Seq(FullCNF, CnfSkolem, FullCNF, CnfConj, CnfConj),
      s"Unexpected clausification steps: ${rules.map(_.name).mkString(", ")}")
    require(clauses.map(_.cl.implicitlyBound.size) == Seq(2, 1),
      "Only the first final clause should retain the generalized variable X")

    val stepNames = inferences.map(_.id).zip(
      Seq("generalize_z", "skolemize_y", "clausify", "clause_p", "clause_q").map(Name(_))).toMap

    // The declaration generator also renders Skolem equalities, so localize the
    // signature names there as well as in the proof renderer.
    val qualifiedSig = LpSig.fromLeo(sig)
    val lpSig = qualifiedSig.copy(
      termNames = qualifiedSig.termNames.view.mapValues(name => QName.local(name.local.value)).toMap,
      typeNames = qualifiedSig.typeNames.view.mapValues(name => QName.local(name.local.value)).toMap)
    val options = RenderOptions(sigPrefix = false, formulaPrefix = false)
    val (symbols, _, _, _) = LPoutput.generateObjectDeclaartions(proof, lpSig)
    val skolemDeclarations = inferences.flatMap(_.furtherInfo.cnfInfo.addInfoQuants.collect {
      case info: SkolemStep => info.sko
    }).distinct.flatMap { key =>
      val symbol = Stmt.Declaration(lpSig.termNames(key).local, Seq.empty,
        LpType.El(TypeEncoding.type2LP(sig(key)._ty)))
      val definition = DefEncoding.encDfn(key, lpSig, isSk = true)
      Seq(symbol, inputNames.declaration(definition))
    }
    val parentName = QName.local("parent")
    val parentDeclaration = Stmt.Declaration(parentName.local, Seq.empty,
      inputNames.ty(ClauseEncoding.clause2LP(parent.cl).asMl))

    val proofObject = new LPoutput.lpProofObject
    var stepInfo = new LPoutput.lpProofStepInfo(identicalSteps = mutable.HashMap(parent.id -> parentName))
    val statements = proof.filterNot(_ == parent).flatMap { node =>
      val (encoded, nextStepInfo) = LPoutput.step2LP(node, lpSig, proofObject, stepInfo)
      // Exporting the definition node registers its Skolem equality as a parent alias.
      stepInfo = nextStepInfo
      encoded.toSeq.flatMap { step =>
        require(!step.admittedWholesale, step.comment.com)
        val name = stepNames(node.id)
        // Later steps resolve their parent references through the same table.
        stepInfo.identicalSteps.update(node.id, QName.local(name.value))
        val names = if (name.value == "generalize_z") inputNames else clauseNames
        val body = step.body.map {
          // The Skolem equality locally reintroduces y and the original binder for x.
          case Left(have: LpProofScript.Have)
              if node.annotation.fromRule == CnfSkolem && have.name.value.startsWith("skolemEq_") =>
            Left(inputNames.tactic(have))
          case Left(tactic) => Left(names.tactic(tactic))
          case Right(_) => sys.error("Expected a Lambdapi AST tactic in the CNF witness")
        }
        val theorem = Stmt.Definition(name, Seq.empty, Some(names.ty(step.ty)),
          Stmt.DefBody.ProofBody(body), modifiers = Seq(Stmt.Opaque))
        val renderedStep = s"// ${step.comment.com}\n" + Renderer.stmt(theorem, lpSig, options)
        step.auxiliaryLemmas.map(lemma => Renderer.stmt(names.definition(lemma), lpSig, options)) :+ renderedStep
      }
    }

    val reflectionImport = if (ClausificationEncoding.useReflectiveCnfBooleanBridges)
      "require open Leo-III-lambdapi-lib.CNF;\n" else ""
    prelude + reflectionImport + "\n" + symbols.toString + "\n" +
      skolemDeclarations.map(Renderer.stmt(_, lpSig, options)).mkString + "\n" +
      Renderer.stmt(parentDeclaration, lpSig, options) + "\n" + statements.mkString("\n")
  }

  def main(args: Array[String]): Unit = {
    require(args.length == 1, "Usage: CnfWitness OUTPUT_DIRECTORY")
    Configuration.init(new CLParameterParser(Array("cnf-witness")))
    val proof = module()
    val directory = Paths.get(args(0))
    Files.createDirectories(directory)
    Files.writeString(directory.resolve("lambdapi.pkg"), "package_name = cnf_example\nroot_path = CnfExample\n")
    Files.writeString(directory.resolve("Cnf.lp"), proof)
  }
}
