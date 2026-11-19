package leo.modules.output.LPoutput

import java.nio.file.{Files, Paths}

import leo.{Configuration, LeoTestSuite}
import leo.datastructures._
import leo.datastructures.ClauseAnnotation.NoAnnotation
import leo.modules.calculus.PolaritySwitch
import leo.modules.control.Control
import leo.modules.input.{CLParameterParser, Input}
import leo.modules.HOLSignature.Not
import leo.modules.output.LPoutput.NewLpDatastructures._

class PolaritySwitchEncodingTest extends LeoTestSuite {
  test("a negative literal containing ¬p produces a Lambdapi proof of p from ¬¬p") {
    val module = PolaritySwitchWitness.module()
    assert(module.contains("symbol parent: π (¬ ¬ S.p);"))
    assert(module.contains("opaque symbol polarity_example: π S.p"))
    assert(module.contains("rewrite PolaritySwitch_lit0"))
    assert(!module.contains("admit"))
  }

  test("implicit type variables precede dependent term variables in polarity replay") {
    val module = PolaritySwitchWitness.polymorphicModule()
    assert(module.contains("assume TA TB B A"))
    assert(module.contains("parent TA TB B A"))
    assert(!module.contains("admit"))
  }

  for (polarity <- Seq(true, false)) {
    test(s"polymorphic polarity replay removes negation on both sides of an equality of polarity $polarity") {
      val module = PolaritySwitchWitness.polymorphicModule(equalityPolarity = Some(polarity))
      assert(module.contains("Stdlib.PropExt.polarity_switch"))
      assert(module.contains("parent TA TB B A"))
      assert(!module.contains("admit"))
    }
  }
}

/** Export a single native Leo inference as a standalone Lambdapi lemma. */
object PolaritySwitchWitness {
  def module(): String = {
    implicit val sig: Signature = Signature.freshWithHOL()
    Input.readAnnotated("thf(p_type,type,(p: $o)).")
    val p = Term.mkAtom(sig("p").key)
    encodeDoubleNegation(p, polymorphic = false)
  }

  def polymorphicModule(equalityPolarity: Option[Boolean] = None): String = {
    implicit val sig: Signature = Signature.freshWithHOL()
    Input.readAnnotated("thf(poly_p_type,type,(poly_p: !> [X:$tType,Y:$tType] : (X > Y > $o))).")
    val xType = Type.mkVarType(1)
    val yType = Type.mkVarType(2)
    val head = Term.mkTypeApp(Term.mkAtom(sig("poly_p").key), Seq(xType, yType))
    val p = Term.mkTermApp(head, Seq(Term.mkBound(xType, 2), Term.mkBound(yType, 1)))
    equalityPolarity match {
      case Some(polarity) =>
        val q = Not(p)
        encode(Literal(Not(p), Not(q), polarity), Literal(p, q, polarity), polymorphic = true)
      case None => encodeDoubleNegation(p, polymorphic = true)
    }
  }

  private def encodeDoubleNegation(p: Term, polymorphic: Boolean)(implicit sig: Signature): String =
    encode(Literal(Not(p), false), Literal(p, true), polymorphic)

  private def encode(before: Literal, after: Literal, polymorphic: Boolean)(implicit sig: Signature): String = {
    val parent = AnnotatedClause(Clause(before), NoAnnotation)
    val child = Control.switchPolarity(parent)
    require(child.cl == Clause(after))
    require(child.annotation.fromRule == PolaritySwitch && child.annotation.parents == Seq(parent))

    // Resolve the parent proof to the standalone symbol declared below.
    val lpSig = LpSig.fromLeo(sig)
    val parentName = QName.local("parent")
    val parentNames = scala.collection.mutable.HashMap(parent.id -> parentName)
    val (encoded, _) = LPoutput.step2LP(child, lpSig, new LPoutput.lpProofObject,
      new LPoutput.lpProofStepInfo(identicalSteps = parentNames))
    val step = encoded.getOrElse(sys.error("The exporter elided the PolaritySwitch step"))
    require(!step.admittedWholesale, step.comment.com)

    val parentType = ClauseEncoding.clause2LP(parent.cl).asMl
    val parentDeclaration = Stmt.Declaration(parentName.local, Seq.empty, parentType)
    val theorem = Stmt.Definition(Name("polarity_example"), Seq.empty, Some(step.ty),
      Stmt.DefBody.ProofBody(step.body),
      modifiers = Seq(Stmt.Opaque))
    val options = RenderOptions(sigPrefix = true, formulaPrefix = false)
    val prelude = "require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.PropExt;\n"
    val polymorphismImport = if (polymorphic) "require open Stdlib.Polymorphism;\n" else ""
    prelude + polymorphismImport + LPoutput.gdvRequireOpenLine + "\nrequire PolaritySwitchExample.Signature as S;\n" +
      Renderer.stmt(parentDeclaration, lpSig, options) +
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
      """require open Stdlib.Set Stdlib.Prop Stdlib.HOL Stdlib.Impred Stdlib.Polymorphism;
        |symbol p : τ o;
        |symbol poly_p : τₛ (`∀ₛ X, `∀ₛ Y, ↑ (X ⤳ Y ⤳ o));
        |""".stripMargin)
    Files.writeString(directory.resolve("PolaritySwitch.lp"), module())
    Term.reset()
    Files.writeString(directory.resolve("PolymorphicPolaritySwitch.lp"), polymorphicModule())
    Term.reset()
    Files.writeString(directory.resolve("PolymorphicEqualityPolaritySwitch.lp"),
      polymorphicModule(equalityPolarity = Some(true)))
    Term.reset()
    Files.writeString(directory.resolve("PolymorphicDisequalityPolaritySwitch.lp"),
      polymorphicModule(equalityPolarity = Some(false)))
  }
}
