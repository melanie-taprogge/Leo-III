package leo.modules.output.LPoutput

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

import leo.{Configuration, LeoTestSuite}
import leo.modules.input.CLParameterParser
import leo.datastructures._
import leo.datastructures.ClauseAnnotation.{InferredFrom, NoAnnotation, PropNoProp}
import leo.datastructures.Term._
import leo.modules.HOLSignature._
import leo.modules.calculus.CnfConj
import leo.modules.output.LPoutput.LPoutput.{ProofReferences, legacyProofReference}
import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewModularEncoding.ProofTermUtil.{applyProofToVars, proofTermAsTacticArg}
import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures.{PrettyConfig, lpFunctionApp}
import leo.modules.control.Control

class ParentProofReferencesTest extends LeoTestSuite {
  private val rootName = QName.local("root")
  private val stepName = QName.local("step42")
  private val h = Name("h")
  private val references = ProofReferences(Some(rootName -> h), Set(stepName))

  test("resolve aliases before selecting root, axiom, or derived proof") {
    val axiom = QName.in(Prefix.Formula, "axiom")
    val aliases = Map(1L -> rootName, 2L -> axiom, 3L -> stepName, 4L -> stepName)
    assert(references.resolve(1, aliases) == LpTerm.Var[Level.Obj](h, None))
    assert(references.resolve(2, aliases) == LpTerm.Const[Level.Obj](SymRef.LP(axiom)))
    assert(references.resolve(3, aliases) == references.resolve(4, aliases))
    assert(references.resolve(42, Map.empty) == references.proof(stepName))
    assert(ProofReferences().proof(stepName) == LpTerm.Const[Level.Obj](SymRef.LP(stepName)))
    assert(ProofReferences(derivedSteps = Set(stepName)).proof(stepName) == ProofReferences().proof(stepName))
  }

  test("common proof argument precedes clause variables in both representations") {
    val sig = LpSig.fromLeo(getFreshSignature)
    val parent = references.proof(stepName)
    val applied = applyProofToVars(parent, Seq(Name("A"), Name("B")))
    val rendered = Renderer.renderTerm(proofTermAsTacticArg(applied), RenderOptions(), sig)
    assert(rendered.contains("step42 h A B"))
    assert(legacyProofReference(parent).isInstanceOf[lpFunctionApp])
    val legacy = lpFunctionApp(legacyProofReference(parent), Seq(
      legacyProofReference(LpTerm.Var[Level.Obj](Name("A"), None))))
    assert(legacy.pretty(PrettyConfig()).contains("(step42 h) A"))
    assert(legacyProofReference(references.proof(QName.in(Prefix.Formula, "axiom"))).pretty(PrettyConfig()) == "F.axiom")
    assert(legacyProofReference(references.proof(rootName)).pretty(PrettyConfig()) == "h")
  }

  test("parent extraction preserves source order, aliases, and arity diagnostics") {
    implicit val sig: Signature = getFreshSignature
    val first = AnnotatedClause(Clause(Literal(mkAtom(sig.addUninterpreted("p", o)), true)), NoAnnotation)
    val second = AnnotatedClause(Clause(Literal(mkAtom(sig.addUninterpreted("q", o)), true)), NoAnnotation)
    val child = AnnotatedClause(first.cl, InferredFrom(CnfConj, Seq(second, first)))
    val aliases = Map(first.id -> stepName, second.id -> rootName)
    val extracted = LPoutput.extractParentInfoN_new(child, aliases, 2, references).toOption.get
    assert(extracted.map(_.clPr.id) == Seq(second.id, first.id))
    assert(extracted.head.lpName.pretty(PrettyConfig()) == "h")
    assert(extracted(1).lpName.pretty(PrettyConfig()) == "(step42 h)")
    assert(LPoutput.extractParentInfoN_new(child, aliases, 1, references).isLeft)
  }

  test("equivalent-step alias chains retain the canonical proof application") {
    implicit val sig: Signature = getFreshSignature
    val clause = Clause(Literal(mkAtom(sig.addUninterpreted("p", o)), true))
    val source = AnnotatedClause(clause, NoAnnotation)
    val first = AnnotatedClause(clause, InferredFrom(CnfConj, source))
    val second = AnnotatedClause(clause, InferredFrom(CnfConj, first))
    val aliases = scala.collection.mutable.HashMap(source.id -> stepName)
    val encoded = ClauseEncoding.clause2LP(clause)
    assert(!LPoutput.identifySteps_new(first, aliases, encoded)._1)
    assert(!LPoutput.identifySteps_new(second, aliases, encoded)._1)
    assert(references.resolve(second.id, aliases.toMap) == references.proof(stepName))
  }

  test("rewrite preparation retains compound main and rule-parent proofs") {
    implicit val sig: Signature = getFreshSignature
    val clause = Clause(Literal(mkAtom(sig.addUninterpreted("p", o)), true))
    val parent = references.proof(stepName)
    val rule = references.proof(rootName)
    val context = RewritingBasedRuleEncoding.Util.initRewriteRuleCtxt(clause, clause,
      RawClause(clause), Seq(RawClause(clause)), parent, Seq(rule))
    assert(context.parentNameLpEnc == parent)
    assert(context.rewriteRuleNamesLpEnc == Seq(rule))
  }

  test("substitution preserves the compound parent and completes disappearing variables") {
    implicit val sig: Signature = getFreshSignature
    val parent = references.proof(stepName)
    val retained = SubstitutionEncoding.instantiateProofTerm(Seq(1 -> i), Seq(1 -> i), Seq.empty, Map(1 -> "A"), parent)
    val missing = SubstitutionEncoding.instantiateProofTerm(Seq(1 -> i), Seq.empty, Seq.empty, Map.empty, parent)
    val lpSig = LpSig.fromLeo(sig)
    assert(Renderer.renderTerm(proofTermAsTacticArg(retained), RenderOptions(), lpSig).contains("step42 h A"))
    assert(Renderer.renderTerm(proofTermAsTacticArg(missing), RenderOptions(), lpSig).contains("step42 h (el"))
    assert(SubstitutionEncoding.instantiateProofTerm(Seq.empty, Seq.empty, Seq.empty, Map.empty, parent) == parent)
    val context = Util.initUniRuleCtxt(Clause(Vector.empty[Literal]), Clause(Vector.empty[Literal]), parent)
    assert(context.parentNameLpEnc == parent)
  }

  test("new and legacy encoder witnesses use compound parents without admissions") {
    val module = ParentProofReferenceWitness.module()
    assert(module.contains("step42 h"))
    assert(module.contains("stepMiniParent h"))
    assert(!module.contains("admit"))
  }
}

/** Emit the actual encoder scripts for an external Lambdapi check. */
object ParentProofReferenceWitness {
  def module(): String = {
    implicit val sig: Signature = Signature.freshWithHOL()
    val p = mkAtom(sig.addUninterpreted("p", i ->: o))
    val q = mkAtom(sig.addUninterpreted("q", o))
    val px = mkTermApp(p, mkBound(i, 1))
    val parent = AnnotatedClause(Clause(Literal(&(px, q), true)), NoAnnotation)
    val first = AnnotatedClause(Clause(Literal(px, true)), InferredFrom(CnfConj, parent), PropNoProp,
      FurtherInfo(cnfConjInfo = Some(AddInfoCnfConj(0, 2))))
    val second = AnnotatedClause(Clause(Literal(q, true)), InferredFrom(CnfConj, parent), PropNoProp,
      FurtherInfo(cnfConjInfo = Some(AddInfoCnfConj(1, 2))))
    val lpSig = LpSig.fromLeo(sig)
    val ro = RenderOptions(sigPrefix = true, formulaPrefix = false)
    val root = QName.local("root")
    val h = Name("h")
    val refs = ProofReferences(Some(root -> h), Set(QName.local("step42")))
    val aliases = Map(parent.id -> QName.local("step42"))
    val nc = ClauseEncoding.clause2LP(Clause(Literal(Forall(\(i)(&(px, q))), true))).term
    val ncType = Renderer.termP(nc, ro, 0, lpSig)
    val parentType = ClauseEncoding.clause2LP(parent.cl).asMl

    def lemma(name: String, ty: LpType, body: String, assumption: String = "NC"): String = {
      val rootType = LpType.Prf(LpTerm.Const[Level.Obj](SymRef.LP(QName.local(assumption))))
      val fullType = LpType.Pi(Seq(LpTerm.Var[Level.Meta](h, Some(rootType))), ty)
      s"opaque symbol $name : ${Renderer.ty(fullType, ro, lpSig)} ≔\nbegin\nassume h;\n$body\nend;\n"
    }

    def encodedConj(child: AnnotatedClause, context: ProofReferences, names: Map[Long, QName]): String = {
      val result = LPoutput.step2LP(child, lpSig, new LPoutput.lpProofObject,
        new LPoutput.lpProofStepInfo(identicalSteps = scala.collection.mutable.HashMap.from(names)), context)._1.get
      val body = result.body.map {
        case Left(script) => Renderer.proof(script, ro, lpSig)
        case Right(script) => script.pretty(PrettyConfig(sigPrefix = true, formulaPrefix = false))
      }.mkString(";\n")
      body + ";"
    }

    val output = new StringBuilder
    output.append("require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.Epsilon;\n")
    output.append(LPoutput.gdvRequireOpenLine).append("\nflag \"eta_equality\" on;\n")
    output.append("require ParentProofWitness.Signature as S;\n")
    output.append(s"symbol NC : τ o ≔ $ncType;\n")
    output.append(lemma("step42", parentType, "refine h;"))
    output.append(lemma("first", ClauseEncoding.clause2LP(first.cl).asMl, encodedConj(first, refs, aliases)))
    output.append(lemma("second", ClauseEncoding.clause2LP(second.cl).asMl, encodedConj(second, refs, aliases)))
    output.append(lemma("directRoot", ClauseEncoding.clause2LP(second.cl).asMl,
      encodedConj(second, refs, Map(parent.id -> root))))

    val instantiated = SubstitutionEncoding.instantiateProofTerm(parent.cl.implicitlyBound, Seq.empty, Seq.empty, Map.empty, refs.proof(QName.local("step42")))
    val witness = LpTerm.App[Level.Obj](LpTerm.Const(SymRef.LP(QName.local("el"))), Seq(Arg.ExplicitTypeArg(TypeEncoding.type2LP(i))))
    val witnessPx = LpTerm.App[Level.Obj](LpTerm.Const(SymRef.Leo(sig("p").key)), Seq(Arg.Explicit(witness)))
    val instantiatedType = LpType.Prf(LogicConst.And(witnessPx, LpTerm.Const(SymRef.Leo(sig("q").key))))
    output.append(lemma("instantiated", instantiatedType, Renderer.proof(LpProofScript.Refine(proofTermAsTacticArg(instantiated)), ro, lpSig)))

    val miniParent = AnnotatedClause(Clause(Literal(Forall(\(i)(Not(px))), true)), NoAnnotation)
    val miniChild = Control.miniscope(miniParent)
    val miniReferences = ProofReferences(Some(root -> h), Set(QName.local("stepMiniParent")))
    val miniProof = miniReferences.proof(QName.local("stepMiniParent"))
    val miniScript = MiniscopeEncoding.encMiniscope(miniChild, Seq(miniProof), lpSig) match {
      case EncodeResult.Encoded(scripts) => scripts.map(Renderer.proof(_, ro, lpSig)).mkString("\n")
      case EncodeResult.NotEncodable(reason) => throw new IllegalStateException(reason)
    }
    output.append(s"symbol NCmini : τ o ≔ ${Renderer.termP(ClauseEncoding.clause2LP(miniParent.cl).term, ro, 0, lpSig)};\n")
    output.append(lemma("stepMiniParent", ClauseEncoding.clause2LP(miniParent.cl).asMl, "refine h;", "NCmini"))
    output.append(lemma("miniscoped", ClauseEncoding.clause2LP(miniChild.cl).asMl, miniScript, "NCmini"))
    output.toString()
  }

  def main(args: Array[String]): Unit = {
    Configuration.init(new CLParameterParser(Array("parent-proof-witness")))
    val directory = Paths.get(args(0))
    Files.createDirectories(directory)
    Files.write(directory.resolve("lambdapi.pkg"), "package_name = parent_proof_witness\nroot_path = ParentProofWitness\n".getBytes(StandardCharsets.UTF_8))
    Files.write(directory.resolve("Signature.lp"), "require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.HOL Stdlib.Impred;\nsymbol p : τ (ι ⤳ o);\nsymbol q : τ o;\n".getBytes(StandardCharsets.UTF_8))
    Files.write(directory.resolve("ParentProofs.lp"), module().getBytes(StandardCharsets.UTF_8))
  }
}
