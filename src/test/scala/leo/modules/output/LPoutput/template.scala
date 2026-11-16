package leo.modules.output.LPoutput

import java.nio.file.{Files, Paths}

import leo.{Configuration, LeoTestSuite}
import leo.datastructures._
import leo.datastructures.ClauseAnnotation.NoAnnotation
import leo.modules.calculus.PolaritySwitch
import leo.modules.control.Control
import leo.modules.input.{CLParameterParser, Input}
import leo.modules.output.LPoutput.NewLpDatastructures._
/*
class template extends LeoTestSuite {
  test("a negative literal containing ¬p produces a Lambdapi proof of p from ¬¬p") {
    val module = PolaritySwitchWitness.module()
    assert(module.contains("π (¬ ¬ S.p) → π S.p"))
    assert(module.contains("rewrite PolaritySwitch_lit0"))
    assert(!module.contains("admit"))
  }
}

/** Export a single native Leo inference as a standalone Lambdapi lemma. */
object PolaritySwitchWitness {
  def module(): String = {
    implicit val sig: Signature = Signature.freshWithHOL()

    //// PROBLEM DEFINITION AND LEO PROOF
    // type annotations etc
    Input.readAnnotated("thf(p_type,type,(p: $o)).")

    // define intended parent(s) and child(ren)
    // parent(s)
    val (_, negatedP, _) = Input.readAnnotated("thf(example,axiom,(~ p)).") // first the term
    val parent = AnnotatedClause(Clause(Literal(negatedP, false)), NoAnnotation) // Then embed in an annotated clause

    // child(ren)
    val child = Control.switchPolarity(parent)
    val p = Term.mkAtom(sig("p").key)

    // check that result is as expected
    require(child.cl == Clause(Literal(p, true)))
    require(child.annotation.fromRule == PolaritySwitch && child.annotation.parents == Seq(parent))


    //// LAMBDAPI ENCODING
    // Set up the proof-step structure: The parent is the assumption, from which the
    val lpSig = LpSig.fromLeo(sig)
    val h = Name("h")
    val parentName = QName.local("parent")
    val parentNames = scala.collection.mutable.HashMap(parent.id -> parentName)
    val references = LPoutput.ProofReferences(negConjRef = Some(parentName -> h))
    val (encoded, _) = LPoutput.step2LP(child, lpSig, new LPoutput.lpProofObject,
      new LPoutput.lpProofStepInfo(identicalSteps = parentNames), references)
    val step = encoded.getOrElse(sys.error("The exporter elided the PolaritySwitch step"))
    require(!step.admittedWholesale, step.comment.com)

    val parentType = ClauseEncoding.clause2LP(parent.cl).asMl
    val theorem = Stmt.Definition(Name("polarity_example"), Seq.empty,
      Some(LpType.Arrow(parentType, step.ty)),
      Stmt.DefBody.ProofBody(Left(LpProofScript.Assume(Seq(h))) +: step.body),
      modifiers = Seq(Stmt.Opaque))
    val options = RenderOptions(sigPrefix = true, formulaPrefix = false)
    val prelude = "require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred;\n"
    prelude + LPoutput.gdvRequireOpenLine + "\nrequire PolaritySwitchExample.Signature as S;\n" +
      Renderer.stmt(theorem, lpSig, options)
  }

  def main(args: Array[String]): Unit = {
    require(args.length == 1, "Usage: PolaritySwitchWitness OUTPUT_DIRECTORY")
    Configuration.init(new CLParameterParser(Array("polarity-switch-witness")))
    val directory = Paths.get(args(0))
    Files.createDirectories(directory)
    Files.writeString(directory.resolve("lambdapi.pkg"),
      "package_name = polarity_switch_example\nroot_path = PolaritySwitchExample\n")
    Files.writeString(directory.resolve("Signature.lp"),
      "require open Stdlib.Set Stdlib.Prop Stdlib.HOL Stdlib.Impred;\nsymbol p : τ o;\n")
    Files.writeString(directory.resolve("PolaritySwitch.lp"), module())
  }
}
 */
