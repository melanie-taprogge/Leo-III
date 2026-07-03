package leo.modules.modes

import leo.Configuration
import leo.datastructures.{Role_Definition, Role_Type, Signature, TPTP, Term}
import leo.datastructures.TPTP.AnnotatedFormula
import leo.modules.{SZSException, SZSOutput, SZSResult, termToClause}
import leo.modules.input.Input
import leo.modules.output.{SZS_InputError, SZS_Proof, SZS_Success}
import leo.Out
import leo.modules.output.LPoutput.LPoutput.gdvRequireOpenLine
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, ClauseEncoding, Level, LogicConst, LpProofScript, LpSig, LpTerm, LpType, Name, Prefix, QName, RenderOptions, Renderer, Stmt, SymRef}

/**
  * Experimental GDV mode for TPTP proof obligations that represent a single
  * skolemization step.
  *
  * GDV still owns most of the Lambdapi package context: it prepends `require`
  * commands for Signature.lp, Formulae.lp and parent proof files. Leo prints
  * the `require open` line for the Leo-specific proof libraries it uses, then
  * the Lambdapi proof payload between SZS start/end markers:
  *
  *   - an `encodedProof (h : π F.lambdapi__negated_conjecture) : π target`
  *     proof script;
  *   - a final rewrite rule `rule F.target ↪ λ h, encodedProof h;`.
  *
  * The supported non-admitted proof shape is deliberately narrow. After the
  * outer universal prefix of the target has been assumed, the parent formula
  * must expose the skolemization redex at the current proof goal level. If the
  * redex is below another object-level binder, the current Lambdapi rewrite
  * tactic cannot rewrite it, so this mode emits an admitted proof with an
  * explanatory comment instead of generating a proof script that would fail.
  */
object Skolemize {
  /** Data carried by GDV-style skolemization annotations. */
  final case class SkolemizationInfo(status: String,
                                     newSymbols: Seq[String],
                                     variable: String,
                                     term: String)
  /** The conjecture to prove, the single parent formula it was derived from, and the annotation data. */
  final case class SkolemizationObligation(target: AnnotatedFormula,
                                           parent: AnnotatedFormula,
                                           info: SkolemizationInfo)
  private final case class ProcessedLpInput(sig: LpSig, formulas: Map[String, Term])
  private final case class EncodedFormula(name: String, formula: LpTerm[Level.Obj])
  private final case class ForallPrefix(binders: Seq[(Name, LpType)], body: LpTerm[Level.Obj])
  /** Which skolem rewrite lemma to use, or why this step has to be admitted. */
  private final case class SkolemRewritePlan(ruleName: String, admitReason: Option[String])
  private final val gdvNegatedConjectureName = "lambdapi__negated_conjecture"

  /** A skolemization redex in the parent formula and the Lambdapi lemma that rewrites it. */
  private sealed trait SkolemRedexKind {
    def ruleName: String
  }
  private case object ExistentialRedex extends SkolemRedexKind {
    override val ruleName: String = "∃_skolem"
  }
  private case object NegatedUniversalRedex extends SkolemRedexKind {
    override val ruleName: String = "∀_skolem"
  }

  /**
    * Generate a local Lambdapi name that avoids the current LP signature and
    * the names already introduced in this proof script.
    *
    * In GDV files the problem signature is normally imported as `S`, so a user
    * symbol `h` would render as `S.h`. Still, avoiding those local names keeps
    * the generated script robust against changes to the surrounding require
    * block and against helper names that coincide with problem symbols.
    */
  private final def freshLocalName(base: String, sig: LpSig, occupied: Set[String]): Name = {
    val unavailable = signatureLocalNames(sig) ++ occupied
    @annotation.tailrec
    def loop(index: Int): String = {
      val candidate = if (index == 0) base else s"${base}_$index"
      if (unavailable(candidate)) loop(index + 1) else candidate
    }

    Name(loop(0))
  }

  private final def signatureLocalNames(sig: LpSig): Set[String] = {
    val signatureTermNames = sig.termNames.values.map(_.local.value)
    val signatureTypeNames = sig.typeNames.values.map(_.local.value)
    sig.reserved ++ signatureTermNames ++ signatureTypeNames ++ Set("S", "F")
  }

  final def apply(parsedProblem: Seq[AnnotatedFormula]): Unit = {
    val obligations = extractSkolemizationObligations(parsedProblem)
    val payload =
      obligations match {
        case Seq() =>
          "No skolemization obligations found."
        case Seq(obligation) =>
          val processedLpInput = processLpInput(parsedProblem)
          renderSkolemizationProof(obligation, processedLpInput)
        case _ =>
          throw new SZSException(SZS_InputError, s"Expected at most one skolemization obligation, found ${obligations.size}.")
      }

    Out.output(SZSResult(SZS_Success, Configuration.PROBLEMFILE, "Skolemization mode selected."))
    Out.output(SZSOutput(SZS_Proof, Configuration.PROBLEMFILE, payload))
  }

  private final def processLpInput(parsedProblem: Seq[AnnotatedFormula]): ProcessedLpInput = {
    implicit val sig: Signature = Signature.freshWithHOL()
    parsedProblem.filter(_.role == Role_Type.pretty).foreach(Input.processFormula(_))
    // Skolem definition formulae are not needed for the proof fragment generated
    // here: the type declarations already register the skolem symbols used in the
    // parent/target formulae. We therefore skip definitions in this mode instead of
    // converting and storing them as ordinary proof formulae.
    val processed = parsedProblem.filterNot(formula => formula.role == Role_Type.pretty || formula.role == Role_Definition.pretty).map { formula =>
      val (_, term, role) = Input.processFormula(formula)
      formula.name -> (term, role)
    }
    val formulaTerms = processed.collect {
      case (name, (term, role)) if role != Role_Type && role != Role_Definition => name -> term
    }.toMap
    ProcessedLpInput(LpSig.fromLeo(sig), formulaTerms)
  }

  private final def encodeFormula(name: String, processed: ProcessedLpInput): EncodedFormula = {
    val term = processed.formulas.getOrElse(name, {
      throw new SZSException(SZS_InputError, s"Could not find processed formula '$name' for Lambdapi encoding.")
    })
    val encoded = ClauseEncoding.clause2LP(termToClause(term))
    EncodedFormula(name, encoded.term)
  }

  private final def renderSkolemizationProof(obligation: SkolemizationObligation,
                                             processed: ProcessedLpInput): String = {
    val parent = encodeFormula(obligation.parent.name, processed)
    val target = encodeFormula(obligation.target.name, processed)
    val targetPrefix = stripLeadingForalls(target.formula)
    val parentPrefix = stripForalls(parent.formula, targetPrefix.binders.size, parent.name)

    // The target name is the GDV/Formulae.lp symbol name, not a Leo-internal proof
    // step name. GDV checks completion by seeing an uncommented `rule F.<name>`.
    val ro = RenderOptions(sigPrefix = true, formulaPrefix = true)
    val encodedProofName = freshLocalName("encodedProof", processed.sig, targetPrefix.binders.map(_._1.value).toSet)
    val proofData = skolemizationProofDefinition(obligation, parent, target, targetPrefix, parentPrefix, processed.sig, encodedProofName)
    val applyEncodedProof = LpTerm.App[Level.Meta](
      LpTerm.Const[Level.Meta](SymRef.LP(QName.local(encodedProofName.value))),
      Seq(Arg.Explicit[Level.Meta](LpTerm.Var[Level.Meta](proofData.negatedConjectureProofName, None)))
    )
    val finalRule = Stmt.Rule(
      LpTerm.Const[Level.Meta](SymRef.LP(QName.in(Prefix.Formula, obligation.target.name))),
      Seq.empty,
      LpTerm.Lam[Level.Meta](proofData.negatedConjectureProofName -> None, applyEncodedProof)
    )

    s"""$gdvRequireOpenLine
       |
       |${Renderer.stmt(proofData.definition, processed.sig, ro).trim}
       |
       |${Renderer.stmt(finalRule, processed.sig, ro).trim}""".stripMargin
  }

  private final case class SkolemizationProofData(definition: Stmt.Definition, negatedConjectureProofName: Name)

  private final def skolemizationProofDefinition(obligation: SkolemizationObligation,
                                                 parent: EncodedFormula,
                                                 target: EncodedFormula,
                                                 targetPrefix: ForallPrefix,
                                                 parentPrefix: ForallPrefix,
                                                 sig: LpSig,
                                                 encodedProofName: Name): SkolemizationProofData = {
    val binderNames = targetPrefix.binders.map(_._1.value).toSet
    val negatedConjecture = freshLocalName("negatedConj", sig, binderNames + encodedProofName.value)
    val assumedNames = targetPrefix.binders.map(_._1)
    val parentProofArgs = negatedConjecture +: assumedNames
    val implication = LogicConst.Imp(parentPrefix.body, targetPrefix.body)
    val haveName = freshLocalName("SK_dev", sig, parentProofArgs.map(_.value).toSet + encodedProofName.value)
    val hName = freshLocalName("h", sig, parentProofArgs.map(_.value).toSet ++ Set(encodedProofName.value, haveName.value))
    val rewritePlan = skolemRewritePlan(obligation, targetPrefix.binders.size)

    val skolemRewrite = LpTerm.Const[Level.Meta](SymRef.LP(QName.local(rewritePlan.ruleName)))
    val haveStep = LpProofScript.Have(
      haveName,
      LpType.Prf(implication),
      Seq(
        Left(LpProofScript.Rewrite(None, skolemRewrite)),
        Left(LpProofScript.Simplify()),
        Left(LpProofScript.Assume(Seq(hName))),
        Left(LpProofScript.Refine(LpTerm.Var[Level.Meta](hName, None)))
      )
    )

    val applyHave = LpTerm.App[Level.Meta](
      LpTerm.Const[Level.Meta](SymRef.LP(QName.local(haveName.value))),
      Seq(Arg.Explicit[Level.Meta](LpTerm.Wildcard[Level.Meta]()))
    )
    val applyParent = formulaProofApplication(parent.name, parentProofArgs)
    val proofScript =
      rewritePlan.admitReason match {
        case Some(reason) =>
          Seq(
            LpProofScript.Comment(reason),
            LpProofScript.Admit
          )
        case None =>
          Seq(
            LpProofScript.Assume(assumedNames),
            haveStep,
            LpProofScript.Refine(applyHave),
            LpProofScript.Refine(applyParent)
          )
      }

    SkolemizationProofData(
      Stmt.Definition(
        encodedProofName,
        Seq(
          negatedConjecture -> LpType.Prf(
            LpTerm.Const[Level.Obj](SymRef.LP(QName.in(Prefix.Formula, gdvNegatedConjectureName)))
          )
        ),
        Some(LpType.Prf(target.formula)),
        Stmt.DefBody.ProofBody(proofScript)
      ),
      negatedConjecture
    )
  }

  private final def formulaProofApplication(formulaName: String, args: Seq[Name]): LpTerm[Level.Meta] = {
    val head = LpTerm.Const[Level.Meta](SymRef.LP(QName.in(Prefix.Formula, formulaName)))
    if (args.isEmpty) head
    else {
      LpTerm.App[Level.Meta](head, args.map(name => Arg.Explicit[Level.Meta](LpTerm.Var[Level.Meta](name, None))))
    }
  }

  private final def stripLeadingForalls(formula: LpTerm[Level.Obj]): ForallPrefix = {
    @annotation.tailrec
    def loop(rest: LpTerm[Level.Obj], binders: Seq[(Name, LpType)]): ForallPrefix = rest match {
      case LogicConst.Forall(binder, body) => loop(body, binders :+ binder)
      case _ => ForallPrefix(binders, rest)
    }

    loop(formula, Seq.empty)
  }

  private final def stripForalls(formula: LpTerm[Level.Obj], count: Int, formulaName: String): ForallPrefix = {
    @annotation.tailrec
    def loop(rest: LpTerm[Level.Obj], remaining: Int, binders: Seq[(Name, LpType)]): ForallPrefix = {
      if (remaining == 0) ForallPrefix(binders, rest)
      else rest match {
        case LogicConst.Forall(binder, body) => loop(body, remaining - 1, binders :+ binder)
        case _ => throw new SZSException(SZS_InputError, s"Expected formula '$formulaName' to have at least $count leading universal quantifier(s).")
      }
    }

    loop(formula, count, Seq.empty)
  }

  private final def skolemRewritePlan(obligation: SkolemizationObligation,
                                      strippedOuterUniversals: Int): SkolemRewritePlan = {
    // Use the source formula when possible: the skolemization annotation names
    // the variable whose binding quantifier is rewritten. This avoids guessing
    // the redex from the closest existential; provers are not required to
    // skolemize from outside to inside.
    val skolemizedVariable = obligation.info.variable
    obligation.parent match {
      case TPTP.TFFAnnotated(_, _, TPTP.TFF.Logical(formula), _) =>
        val stripped = stripTFFLeadingUniversals(formula, strippedOuterUniversals)
        planFromLocatedRedex(tffSkolemRedexDepth(stripped, skolemizedVariable), skolemizedVariable)
      case TPTP.FOFAnnotated(_, _, TPTP.FOF.Logical(formula), _) =>
        val stripped = stripFOFLeadingUniversals(formula, strippedOuterUniversals)
        planFromLocatedRedex(fofSkolemRedexDepth(stripped, skolemizedVariable), skolemizedVariable)
      case _ =>
        SkolemRewritePlan(
          ExistentialRedex.ruleName,
          Some(s"Cannot verify skolemization: parent formula format does not expose source quantifiers for skolemized variable '$skolemizedVariable'")
        )
    }
  }

  private final def planFromLocatedRedex(redex: Option[(SkolemRedexKind, Int)],
                                         skolemizedVariable: String): SkolemRewritePlan = {
    redex match {
      case Some((kind, 0)) =>
        SkolemRewritePlan(kind.ruleName, None)
      case Some((kind, _)) =>
        SkolemRewritePlan(
          kind.ruleName,
          Some("Cannot verify skolemization: the skolemization redex occurs under a binder, and the Lambdapi rewrite tactic cannot rewrite under binders here"))
      case None =>
        SkolemRewritePlan(
          ExistentialRedex.ruleName,
          Some(s"Cannot verify skolemization: could not find a quantifier binding skolemized variable '$skolemizedVariable' in the parent formula"))
    }
  }

  private final def stripTFFLeadingUniversals(formula: TPTP.TFF.Formula, count: Int): TPTP.TFF.Formula = {
    @annotation.tailrec
    def loop(current: TPTP.TFF.Formula, remaining: Int): TPTP.TFF.Formula = {
      if (remaining <= 0) current
      else current match {
        case TPTP.TFF.QuantifiedFormula(TPTP.TFF.!, variableList, body) =>
          val (_, keptVariables) = variableList.splitAt(remaining)
          if (keptVariables.isEmpty) loop(body, remaining - variableList.size)
          else TPTP.TFF.QuantifiedFormula(TPTP.TFF.!, keptVariables, body)
        case _ => current
      }
    }

    loop(formula, count)
  }

  private final def stripFOFLeadingUniversals(formula: TPTP.FOF.Formula, count: Int): TPTP.FOF.Formula = {
    @annotation.tailrec
    def loop(current: TPTP.FOF.Formula, remaining: Int): TPTP.FOF.Formula = {
      if (remaining <= 0) current
      else current match {
        case TPTP.FOF.QuantifiedFormula(TPTP.FOF.!, variableList, body) =>
          val (_, keptVariables) = variableList.splitAt(remaining)
          if (keptVariables.isEmpty) loop(body, remaining - variableList.size)
          else TPTP.FOF.QuantifiedFormula(TPTP.FOF.!, keptVariables, body)
        case _ => current
      }
    }

    loop(formula, count)
  }

  private final def tffSkolemRedexDepth(formula: TPTP.TFF.Formula, skolemizedVariable: String): Option[(SkolemRedexKind, Int)] = {
    def minDepth(depths: Option[(SkolemRedexKind, Int)]*): Option[(SkolemRedexKind, Int)] = depths.flatten.minByOption(_._2)

    def variableNames(vars: Seq[(String, Option[TPTP.TFF.Type])]): Seq[String] = vars.map(_._1)

    def loop(current: TPTP.TFF.Formula, binderDepth: Int, negated: Boolean): Option[(SkolemRedexKind, Int)] = current match {
      case TPTP.TFF.QuantifiedFormula(TPTP.TFF.?, variableList, _) if variableNames(variableList).contains(skolemizedVariable) =>
        Some(ExistentialRedex -> binderDepth)
      case TPTP.TFF.QuantifiedFormula(TPTP.TFF.!, variableList, _) if negated && variableNames(variableList).contains(skolemizedVariable) =>
        Some(NegatedUniversalRedex -> binderDepth)
      case TPTP.TFF.QuantifiedFormula(_, _, body) =>
        loop(body, binderDepth + 1, negated = false)
      case TPTP.TFF.UnaryFormula(TPTP.TFF.~, body) =>
        loop(body, binderDepth, !negated)
      case TPTP.TFF.BinaryFormula(_, left, right) =>
        minDepth(loop(left, binderDepth, negated = false), loop(right, binderDepth, negated = false))
      case TPTP.TFF.ConditionalFormula(condition, _, _) =>
        loop(condition, binderDepth, negated = false)
      case _ => None
    }

    loop(formula, 0, negated = false)
  }

  private final def fofSkolemRedexDepth(formula: TPTP.FOF.Formula, skolemizedVariable: String): Option[(SkolemRedexKind, Int)] = {
    def minDepth(depths: Option[(SkolemRedexKind, Int)]*): Option[(SkolemRedexKind, Int)] = depths.flatten.minByOption(_._2)

    def loop(current: TPTP.FOF.Formula, binderDepth: Int, negated: Boolean): Option[(SkolemRedexKind, Int)] = current match {
      case TPTP.FOF.QuantifiedFormula(TPTP.FOF.?, variableList, _) if variableList.contains(skolemizedVariable) =>
        Some(ExistentialRedex -> binderDepth)
      case TPTP.FOF.QuantifiedFormula(TPTP.FOF.!, variableList, _) if negated && variableList.contains(skolemizedVariable) =>
        Some(NegatedUniversalRedex -> binderDepth)
      case TPTP.FOF.QuantifiedFormula(_, _, body) =>
        loop(body, binderDepth + 1, negated = false)
      case TPTP.FOF.UnaryFormula(TPTP.FOF.~, body) =>
        loop(body, binderDepth, !negated)
      case TPTP.FOF.BinaryFormula(_, left, right) =>
        minDepth(loop(left, binderDepth, negated = false), loop(right, binderDepth, negated = false))
      case _ => None
    }

    loop(formula, 0, negated = false)
  }

  final def extractSkolemizationObligations(parsedProblem: Seq[AnnotatedFormula]): Seq[SkolemizationObligation] = {
    val formulaByName = parsedProblem.map(formula => formula.name -> formula).toMap
    // Per GDV invocation, the current proof obligation is the conjecture. Older
    // skolemization steps may be present as axioms in the same `.p` file; those
    // annotations intentionally do not create obligations here.
    parsedProblem.filter(_.role == "conjecture").flatMap { formula =>
      parseSkolemizationAnnotation(formula.annotations).map { case (info, parentNames) =>
        val parentName = parentNames match {
          case Seq(singleParent) => singleParent
          case _ => throw new SZSException(SZS_InputError, s"Expected exactly one skolemization parent for '${formula.name}', found ${parentNames.size}.")
        }
        val parent = formulaByName.getOrElse(parentName, {
          throw new SZSException(SZS_InputError, s"Skolemization parent '$parentName' referenced by '${formula.name}' is not present in the problem.")
        })
        SkolemizationObligation(formula, parent, info)
      }
    }
  }

  private final def parseSkolemizationAnnotation(annotation: TPTP.Annotations): Option[(SkolemizationInfo, Seq[String])] = {
    annotation match {
      case Some((source, _)) => source.data match {
        case Seq(TPTP.MetaFunctionData("inference", Seq(SimpleMetaTerm(ruleName), GeneralList(infoTerms), GeneralList(parentTerms))))
          if ruleName == "skolemize" || ruleName == "skolemization" =>
          val info = parseSkolemizationInfo(infoTerms)
          val parents = parentTerms.flatMap(simpleMetaName)
          Some(info -> parents)
        case _ => None
      }
      case None => None
    }
  }

  private final def parseSkolemizationInfo(infoTerms: Seq[TPTP.GeneralTerm]): SkolemizationInfo = {
    var status: Option[String] = None
    var newSymbols: Option[Seq[String]] = None
    var variable: Option[String] = None
    var term: Option[String] = None

    infoTerms.foreach {
      case TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData("status", Seq(SimpleMetaTerm(statusName)))), None) =>
        status = setOnce("status", status, statusName)
      case TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData("new_symbols", Seq(SimpleMetaTerm("skolem"), GeneralList(symbolTerms)))), None) =>
        newSymbols = setOnce("new_symbols(skolem, ...)", newSymbols, symbolTerms.flatMap(simpleMetaName))
      case TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData("skolemize", Seq(skolemVariable, skolemTerm))), None) =>
        variable = setOnce("skolemize variable", variable, simpleName(skolemVariable).getOrElse {
          throw new SZSException(SZS_InputError, s"Could not parse skolemized variable from annotation term '${skolemVariable.pretty}'.")
        })
        term = setOnce("skolemize term", term, skolemTerm.pretty)
      case _ =>
    }

    SkolemizationInfo(
      requireOne("status", status),
      requireOne("new_symbols(skolem, ...)", newSymbols),
      requireOne("skolemize variable", variable),
      requireOne("skolemize term", term)
    )
  }

  private final def setOnce[A](fieldName: String, previous: Option[A], next: A): Option[A] = previous match {
    case None => Some(next)
    case Some(_) => throw new SZSException(SZS_InputError, s"Duplicate $fieldName entry in skolemization annotation.")
  }

  private final def requireOne[A](fieldName: String, value: Option[A]): A = value match {
    case Some(result) => result
    case None => throw new SZSException(SZS_InputError, s"Missing $fieldName entry in skolemization annotation.")
  }

  private final def simpleMetaName(term: TPTP.GeneralTerm): Option[String] = term match {
    case SimpleMetaTerm(name) => Some(name)
    case _ => None
  }

  private final def simpleName(term: TPTP.GeneralTerm): Option[String] = term match {
    case SimpleMetaTerm(name) => Some(name)
    case TPTP.GeneralTerm(Seq(TPTP.MetaVariable(name)), None) => Some(name)
    case _ => None
  }

  private object SimpleMetaTerm {
    def unapply(term: TPTP.GeneralTerm): Option[String] = term match {
      case TPTP.GeneralTerm(Seq(TPTP.MetaFunctionData(name, Seq())), None) => Some(name)
      case _ => None
    }
  }

  private object GeneralList {
    def unapply(term: TPTP.GeneralTerm): Option[Seq[TPTP.GeneralTerm]] = term match {
      case TPTP.GeneralTerm(Seq(), Some(terms)) => Some(terms)
      case _ => None
    }
  }
}
