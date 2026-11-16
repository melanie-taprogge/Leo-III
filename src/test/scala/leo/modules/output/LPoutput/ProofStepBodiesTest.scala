package leo.modules.output.LPoutput

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

import leo.LeoTestSuite
import leo.datastructures._
import leo.datastructures.ClauseAnnotation.{InferredFrom, NoAnnotation}
import leo.datastructures.Term.mkAtom
import leo.modules.HOLSignature.o
import leo.modules.calculus.CnfConj
import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures._

class ProofStepBodiesTest extends LeoTestSuite {
  test("a step retains its source, ordered parents, body, and diagnostic before wrapping") {
    implicit val sig: Signature = getFreshSignature
    val p = AnnotatedClause(Clause(Literal(mkAtom(sig.addUninterpreted("p", o)), true)), NoAnnotation)
    val q = AnnotatedClause(Clause(Literal(mkAtom(sig.addUninterpreted("q", o)), true)), NoAnnotation)
    val source = AnnotatedClause(p.cl, InferredFrom(CnfConj, Seq(q, p)))
    val script = lpRefine(lpConstantTerm("h"))
    val ty = LpType.Prf(LogicConst.Top)
    val result = LPoutput.toProofStepOld(source, ty, "test_rule", script, None).get
    assert(result.source eq source)
    assert(result.source.annotation.parents.map(_.id) == Seq(q.id, p.id))
    assert(result.name == nameStep_new(source.id).local)
    assert(result.ty == ty)
    assert(result.body == Seq(Right(script)))
    assert(result.comment == LpProofScript.Comment("test_rule"))
  }

  test("unsupported results replace either script representation with an explicit admit") {
    implicit val sig: Signature = getFreshSignature
    val source = AnnotatedClause(Clause(Literal(mkAtom(sig.addUninterpreted("p", o)), true)), NoAnnotation)
    val ty = LpType.Prf(LogicConst.Top)
    val oldResult = LPoutput.toProofStepOld(source, ty, "test_rule", lpRefine(lpConstantTerm("unused")), Some("unsupported variant")).get
    val newResult = LPoutput.toProofStep(source, ty, "test_rule", Left(LpProofScript.Reflexivity), Some("unsupported variant")).get
    assert(oldResult.body == Seq(Left(LpProofScript.Admit)))
    assert(newResult == oldResult)
    assert(oldResult.comment.com == "Unencoded step (test_rule): unsupported variant")
  }

  test("an elided equivalent source step remains absent and retains its alias") {
    implicit val sig: Signature = getFreshSignature
    val clause = Clause(Literal(mkAtom(sig.addUninterpreted("p", o)), true))
    val parent = AnnotatedClause(clause, NoAnnotation)
    val child = AnnotatedClause(clause, InferredFrom(CnfConj, parent))
    val result = LPoutput.step2LP(child, LpSig.fromLeo(sig), new LPoutput.lpProofObject, new LPoutput.lpProofStepInfo)
    assert(result._1.isEmpty)
    assert(result._2.identicalSteps(child.id) == nameStep_new(parent.id))
  }

  test("local have rendering preserves legacy separators while definitions terminate fragments") {
    val sig = LpSig.fromLeo(getFreshSignature)
    val oldScript = lpRefine(lpConstantTerm("h"))
    val body: LpProofScript.Body = Seq(Right(oldScript))
    val local = Renderer.proof(LpProofScript.Have(Name("copy"), LpType.Prf(LogicConst.Top), body), RenderOptions(), sig)
    assert(local.contains("{refine h};"))
    val definition = Renderer.stmt(Stmt.Definition(Name("copy"), Seq.empty,
      Some(LpType.Prf(LogicConst.Top)), Stmt.DefBody.ProofBody(body)), sig)
    assert(definition.contains("refine h;\nend;"))
  }

  test("mixed proof definitions render nested helper scopes, comments, and empty fragments") {
    val rendered = ProofStepBodiesWitness.module()
    assert(rendered.contains("have legacy_copy"))
    assert(rendered.contains("have new_copy"))
    assert(rendered.contains("// legacy comment"))
    assert(!rendered.contains(";;"))
    assert(!rendered.contains("admit"))
  }
}

/** A standalone check of the shared body renderer using proved identity lemmas. */
object ProofStepBodiesWitness {
  def module(): String = {
    val sig = LpSig.fromLeo(Signature.freshWithHOL())
    val top = LpType.Prf(LogicConst.Top)
    val h = LpTerm.Var[Level.Meta](Name("h"), None)
    val oldH = lpConstantTerm("h")
    val assume = LpProofScript.Assume(Seq(Name("h")))
    val oldCopy = lpHave("legacy_copy", lpOlTop.prf, lpProofScript(Seq(lpRefine(oldH))))
    val newCopy = LpProofScript.Have(Name("new_copy"), top, Seq(Right(lpRefine(oldH))))
    val oldCopyRef = LpProofScript.Refine(LpTerm.Const[Level.Meta](SymRef.LP(QName.local("legacy_copy"))))
    val mixedCopy = LpProofScript.Have(Name("mixed_copy"), top, Seq(Right(oldCopy), Left(oldCopyRef)))

    val bodies: Seq[(String, LpProofScript.Body)] = Seq(
      "pure_new" -> Seq(Left(assume), Left(LpProofScript.Refine(h))),
      "pure_legacy" -> Seq(Right(lpProofScript(Seq(lpAssume(Seq(oldH)), oldCopy, lpRefine(lpConstantTerm("legacy_copy")))))),
      "new_then_legacy" -> Seq(Left(assume), Left(newCopy), Right(lpRefine(lpConstantTerm("new_copy")))),
      "legacy_then_new" -> Seq(Right(lpAssume(Seq(oldH))), Right(oldCopy), Left(oldCopyRef)),
      "mixed_nested" -> Seq(Left(assume), Left(mixedCopy), Left(LpProofScript.Refine(LpTerm.Const[Level.Meta](SymRef.LP(QName.local("mixed_copy")))))),
      "legacy_comment" -> Seq(Right(lpProofScript(Seq(lpAssume(Seq(oldH)), lpProofScriptCommentLine("legacy comment")))), Right(oldCopy), Left(oldCopyRef)),
      "empty_fragment" -> Seq(Right(lpProofScript(Seq.empty)), Left(assume), Right(lpRefine(oldH))),
      "already_terminated" -> Seq(Right(lpProofScriptStringProof("assume h;")), Right(lpRefine(oldH)))
    )

    val definitions = bodies.map { case (name, body) =>
      Stmt.Definition(Name(name), Seq.empty, Some(LpType.Arrow(top, top)),
        Stmt.DefBody.ProofBody(body), modifiers = Seq(Stmt.Opaque))
    }
    "require open Stdlib.Prop;\n" + definitions.map(Renderer.stmt(_, sig)).mkString("\n")
  }

  def main(args: Array[String]): Unit = {
    val directory = Paths.get(args(0))
    Files.createDirectories(directory)
    Files.write(directory.resolve("lambdapi.pkg"), "package_name = proof_step_bodies\nroot_path = ProofStepBodies\n".getBytes(StandardCharsets.UTF_8))
    Files.write(directory.resolve("ProofBodies.lp"), module().getBytes(StandardCharsets.UTF_8))
  }
}
