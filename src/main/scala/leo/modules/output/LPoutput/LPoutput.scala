package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.{ClauseProxy, Role_Axiom, Role_Conjecture, Role_NegConjecture, Signature, isPropSet}
import leo.modules.output.{fusebVarListwithMap, makeBVarList}
import leo.modules.prover.LocalState
import leo.modules.{saturatedUserSignature, symbolsInProof}
import leo.modules.output.LPoutput.Encodings._
import leo.modules.output.LPoutput.LPSignature.{lpDne, tempLib}
import leo.modules.output.LPoutput.ModularProofEncoding.ParamodEncoding.encPara
import leo.modules.output.LPoutput.ModularProofEncoding.CnfConjEncoding.encCnfConj
import leo.modules.output.LPoutput.ModularProofEncoding.RenameCnfEncoding.encRenameCnf_conj
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.ModularProofEncoding._

import java.nio.file.{Files, Path, Paths, StandardOpenOption}
import java.nio.charset.StandardCharsets
import scala.collection.mutable

/**
  * Generation of the various files making up the Lambdapi encoding
  *
  * @author Melanie Taprogge
  */

object LPoutput {

  val permlibFile = "MetaTheorems"
  val multiNDFile = "Multi_ND"
  val calcRuleLibFile = "EPrules"
  val leoSimpTacticFile = "UserTactic"
  val nameLeoIIILPlib = "Leo-III-lambdapi-lib"
  val nameProofFile = "encodedProof"
  val nameSignatureFile = "Signature"
  val abbreviationSignatureFile = "S"
  val nameFormulaeFile = "Formulae"
  val abbreviationFormulaeFile = "F"

  val nameTempFile = "UserTactics"

  val applyAllDefsTacName = "applyAllDefinitions"

  val permLibStr: String = f"${nameLeoIIILPlib}.${permlibFile}"
  val multiNdLibStr: String = f"${nameLeoIIILPlib}.${multiNDFile}"
  val simpTacLibStr = f"${nameLeoIIILPlib}.${leoSimpTacticFile}"
  val calcRuleLibStr = f"${nameLeoIIILPlib}.${calcRuleLibFile}"

  final class lpProofObject {
    var etaExpFlag: Boolean = false
    var defRuleDefined: Boolean = false
  }

  final class lpProofStepInfo (val clausifiedSteps: Map[lpConstantTerm, lpConstantTerm] = Map.empty,
                               val identicalSteps: mutable.HashMap[Long, lpConstantTerm] = mutable.HashMap.empty,
                               val tptpDefinedSymbols: Set[lpStatement] = Set.empty,
                               val additionalDefinedSymbols: Set[Signature.Key] = Set.empty,
                               val skDefinitions: Seq[lpDeclaration] = Seq.empty)

  def toProofStep(stepName: String, encStep: lpMlType, ruleName: String, proofTerm: lpProofScript, notEncoded: Option[String]): Seq[lpProofScriptStep] = {
    if (notEncoded.isDefined) {
      // if the step is actually new, we want to add it to the output
      // add substeps for which the encoding is not implemented using the "admit" tactic
      // todo: encode these rules! :)
      Out.lp_debug_info(s"Not encoded yet (${notEncoded.get})\n")
      Seq(lpProofScriptCommentLine(s"Unencoded step ($ruleName): " + notEncoded.get), lpHave(stepName, encStep, lpProofScript(Seq(lpProofScriptAdmit()))))
    } else {
      Out.lp_debug_info(s"Encoding finished!\n")
      // add the encoded proofs to the overall proof as substeps
      Seq(lpProofScriptCommentLine(ruleName), lpHave(stepName, encStep, proofTerm))
      // and add the necessary symbols to the generated Signature
    }
  }

  def identifySteps(cl: ClauseProxy, identicalSteps: mutable.HashMap[Long, lpConstantTerm], sig:Signature, encStep: lpClause): (Boolean, mutable.HashMap[Long, lpConstantTerm]) = {
    var encodeStep = false
    cl.annotation.parents foreach { parent =>
      val encParent = clause2LP(parent.cl, Set.empty, sig)._1
      if (encParent == encStep) {
        if (identicalSteps.contains(cl.id)) {
          if (identicalSteps(cl.id) != nameStep(parent.id)) {
            throw new Exception(s"step $cl.id ($encStep) is equivalent to two parents: ${cl.id}, ${parent.id} ")
          }
        }
        if (identicalSteps.contains(parent.id)) {
          // in this case we already have the parent as a key and want to map the new child to the parents parent
          val exVal = identicalSteps(parent.id)
          identicalSteps.update(cl.id, exVal)
        } else {
          // in this case we just want to link the child to the parent
          val exVal = nameStep(parent.id)
          identicalSteps.update(cl.id, exVal)
        }
      } else encodeStep = true
    }
    (encodeStep, identicalSteps)
  }

  final case class ParentInfo(clPr: ClauseProxy, lpName: lpConstantTerm)

  def extractParentInfoN(child: ClauseProxy,
                         identicalSteps: Map[Long, lpConstantTerm],
                         expectedParents: Int
                        ): Either[String, Seq[ParentInfo]] = {
    val parents = child.annotation.parents
    if (parents.length != expectedParents)
      Left(s"Lambdapi encoding error: expected $expectedParents parents, got ${parents.length} (child id ${child.id})")
    else {
      def nameOf(p: ClauseProxy): lpConstantTerm =
        identicalSteps.getOrElse(p.id, nameStep(p.id))

     Right(parents.map(p => ParentInfo(p, nameOf(p))))
    }
  }

  def extractParentInfo2(child: ClauseProxy, identicalSteps: Map[Long, lpConstantTerm]): Either[String, (ParentInfo, ParentInfo)] = {
    extractParentInfoN(child, identicalSteps, 2) match {
      case Left(error) => Left(error)
      case Right(Seq(parent0, parent1)) => Right((parent0, parent1))
      case _ => Left(s"Lambdapi encoding error: Failure when extracting parent info")
    }
  }

  def extractParentInfo1(child: ClauseProxy, identicalSteps: Map[Long, lpConstantTerm]): Either[String, ParentInfo] = {
    extractParentInfoN(child, identicalSteps, 1) match {
      case Left(error) => Left(error)
      case Right(Seq(parent0)) => Right(parent0)
      case _ => Left(s"Lambdapi encoding error: Failure when extracting parent info")
    }
  }

  def step2LP(cl: ClauseProxy, sig: Signature, st: lpProofObject, stepInfo: lpProofStepInfo): (Seq[lpProofScriptStep], lpProofStepInfo) = {

    val stepName = nameStep(cl.id).name
    val rule = cl.annotation.fromRule
    // since we do not write out steps that are identical in our encoding, we keep track of what the reference to the parent clause in LP is
    val parentInLpEncID = cl.annotation.parents.map(parent => stepInfo.identicalSteps.getOrElse(parent.id, nameStep(parent.id)))
    Out.lp_debug_info(s"Encoding step $stepName: application of caluclus rule ${if (rule == null) "Tautology" else rule.name}")
    Out.lp_debug_info(s"The parents are ${parentInLpEncID.map(term => term.pretty).mkString(", ")}")

    val (encStep, newTptpDefinedSymbols) = clause2LP(cl.cl, Set(), sig)
    val (needsEnc, newIdenticalSteps) = identifySteps(cl,stepInfo.identicalSteps,sig,encStep)

    if ((cl.role != Role_Conjecture) && needsEnc && (rule != null)) {
      rule match {

        case _ =>
          val outputInfo = new lpProofStepInfo(Map.empty,newIdenticalSteps,newTptpDefinedSymbols)
          Out.lp_debug_info(s"new symbols: ${newTptpDefinedSymbols.map(_.pretty)}")

          rule match {
            case leo.modules.calculus.CnfConj =>
              val parent = extractParentInfo1(cl, stepInfo.identicalSteps.toMap) match {
                case Left(error) => throw new Exception(error)
                case Right(value) => value
              }
              val idx = cl.furtherInfo.cnfConjInfo match {
                case Some(value) => value
                case None => throw new Exception("Error in Lmabdapi encoding: No additional information for the Lambdapi encoding was supplied")
              }
              val encProof = encCnfConj(cl, parent, idx, sig)
              (toProofStep(stepName, encStep, rule.name, encProof, None), outputInfo)

            case leo.modules.calculus.RenameCNF =>
              val encodingCNF = encRenameCnf_conj(cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.cnfInfo, sig)
              val stepsCNF = toProofStep(stepName, encodingCNF._3, "RenameCNF_conj", encodingCNF._1, encodingCNF._2)
              val outputInfo = new lpProofStepInfo(Map.empty,newIdenticalSteps,newTptpDefinedSymbols,encodingCNF._4,Seq())
              (stepsCNF,outputInfo)


            case leo.modules.calculus.PolaritySwitch =>
              val encoding = encPolaritySwitch(cl, cl.annotation.parents.head, parentInLpEncID.head, sig) //¿polarity switch always only has one parent, right?
              (toProofStep(stepName, encStep, "PolaritySwitch", encoding._1, None),outputInfo)

            case leo.modules.calculus.FuncExt =>
              val encoding = encFuncExtPos(cl, cl.annotation.parents.head, cl.furtherInfo.edLitBeforeAfter, parentInLpEncID.head, sig)
              (toProofStep(stepName, encStep, "FuncExt", encoding._1, encoding._3),outputInfo)

            case leo.modules.calculus.BoolExt =>
              val encoding = encBoolExt(cl, cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.addInfoBoolExt, sig)
              (toProofStep(stepName, encStep, "BoolExt", encoding._1, encoding._3),outputInfo)

            case leo.modules.calculus.OrderedEqFac =>
              val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoEqFac, parentInLpEncID.head, sig)
              (toProofStep(stepName, encStep, "OrderedEqFac", encodings._1, None),outputInfo)

            ////////////////////////////////////////
            // Paramodulation encoding
            case leo.modules.calculus.OrderedParamod =>
              val (parentWithClause, parentIntoClause) = extractParentInfo2(cl, stepInfo.identicalSteps.toMap) match {
                case Left(error) => throw new Exception(error)
                case Right(value) => value
              }
              val addInfoPara = cl.furtherInfo.para match {
                case Some(value) => value
                case None => throw new Exception("Error in Lmabdapi encoding: No additional information for the Lambdapi encoding was supplied")
              }
              val (encProof, cantencode) = encPara(cl.cl, parentWithClause, parentIntoClause, addInfoPara, sig)
              (toProofStep(stepName, encStep, "OrderedPara", encProof, cantencode),outputInfo)

            case leo.modules.calculus.DefExpSimp =>
              //throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoDefExp}")
              // todo: eta expansion
              val (proofSteps, cantENcode) = EncDefExSimp(cl, cl.annotation.parents.head, st.defRuleDefined, cl.furtherInfo.rwUnderBinder, cl.furtherInfo.addInfoDefExp, applyAllDefsTacName, parentInLpEncID.head, sig)
              if (!cantENcode.isDefined) st.etaExpFlag = true
              (toProofStep(stepName, encStep, "DefExpand", lpProofScript(proofSteps), cantENcode),outputInfo)

            case leo.modules.calculus.Simp =>
              if (cl.furtherInfo.addInfoSimpRule.isDefined) {
                if (cl.furtherInfo.addInfoSimpRule.get == "eqSimp") {
                  if (cl.furtherInfo.rwUnderBinder) {
                    (toProofStep(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Some("Simp: This instance can not be encoded yet as it requires RW under Binder")),outputInfo)
                  }
                  else {
                    val (allSteps, usedSymbols) = newSimpEncoding(cl.cl, cl.annotation.parents.head.cl, parentInLpEncID.head, sig)
                    (toProofStep(stepName, encStep, s"FormulaSimp", lpProofScript(allSteps), None),outputInfo)
                  }
                } else if (cl.furtherInfo.addInfoSimpRule.get == "paraSimp") {
                  if (cl.furtherInfo.rwUnderBinder) {
                    (toProofStep(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Some("Simp: This instance can not be encoded yet as it requires RW under Binder")), outputInfo)
                  }
                  else {
                    val (allSteps, usedSymbols) = newSimpEncoding(cl.cl, cl.annotation.parents.head.cl, parentInLpEncID.head, sig, Seq(cl.annotation.parents.head.cl.lits.length - 1))
                    (toProofStep(stepName, encStep, s"FormulaSimp", lpProofScript(allSteps), None), outputInfo)
                  }
                }else {
                  val annotation = Some(s"Simp: ${cl.furtherInfo.addInfoSimpRule.get} currently not encoded")
                  (toProofStep(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), annotation),outputInfo)
                }
              } else {
                val annotation = Some("Simp: Unidentified formula simplification unencoded")
                (toProofStep(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), annotation),outputInfo)
              }

            case leo.modules.calculus.PreUni =>
              val encodingPreUni = encPreUni(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoUni, cl.furtherInfo.addInfoUniRule, parentInLpEncID.head, sig)
              (toProofStep(stepName, encStep, "PreUni", encodingPreUni._1, encodingPreUni._3),outputInfo)

            case leo.modules.calculus.RewriteSimp =>
              val encodingRewrite = encRewrite(cl, cl.annotation.parents, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoRewriting, parentInLpEncID, sig)
              (toProofStep(stepName, encStep, "RewriteSimp", encodingRewrite._1, encodingRewrite._3),outputInfo)

            case leo.modules.calculus.LiftEq =>
              val encodingLiftEq = encLiftEq(cl, cl.annotation.parents, cl.furtherInfo.addInfoLiftEq, parentInLpEncID, sig)
              (toProofStep(stepName, encStep, "LiftEq", encodingLiftEq._1, encodingLiftEq._3),outputInfo)
            case _ =>
              val parentIDs = parentInLpEncID.map(id => id.name)
              (toProofStep(stepName, encStep, rule.name, lpProofScript(Seq.empty), Option(s"unencoded rule applied to ${parentIDs.mkString(", ")}")),outputInfo)
          }
      }
    }else{
      val outputInfo = new lpProofStepInfo(Map.empty, newIdenticalSteps, newTptpDefinedSymbols)
      if (rule == null && (cl.role != Role_Conjecture)) {
        Out.lp_debug_info(s"role : ${cl.role}")
        (toProofStep(stepName, encStep, "Tautology", lpProofScript(Seq.empty), Some("Tautology generation not yet encoded")), outputInfo)
      }else{
        (Seq.empty, outputInfo)
      }
    }
  }

  def createLambdapiFiles(outputFolderPath: Path, nameLpOutputFolder:String, pkgFileName: String, proofFileName: String): Unit = {

    val pkgFileContent =
      s"""package_name = $nameLpOutputFolder
         |root_path    = $nameLpOutputFolder
         |""".stripMargin

    // Write the package file
    val pkgFilePath = outputFolderPath.resolve(pkgFileName)
    Files.write(
      pkgFilePath,
      pkgFileContent.getBytes(StandardCharsets.UTF_8),
      StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING
    )

    // Create the makefile
    val makefileContent = s"""|.POSIX:
                              |SRC = $proofFileName.lp
                              |OBJ = $${SRC:.lp=.lpo}
                              |.SUFFIXES:
                              |
                              |all: $${OBJ}
                              |
                              |install: $${OBJ} $pkgFileName
                              |\tlambdapi install $pkgFileName $${OBJ} $${SRC}
                              |
                              |uninstall:
                              |\tlambdapi uninstall $pkgFileName
                              |
                              |clean:
                              |\trm -f $${OBJ}
                              |
                              |.SUFFIXES: .lp .lpo
                              |
                              |.lp.lpo:
                              |\tlambdapi check --gen-obj $$<
                              |""".stripMargin


    // Write the Makefile using Files.write
    val makefilePath = outputFolderPath.resolve("Makefile")
    Files.write(
      makefilePath,
      makefileContent.getBytes(StandardCharsets.UTF_8),
      StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING
    )
    Out.lp_debug_info(s"Makefile written to: ${makefilePath.toAbsolutePath}")
  }

  def generateObjectDeclaartions(signatureSymbols: Set[Signature.Key], st: lpProofObject, sig:Signature) = {

    var tptpDefinedSymbols: Set[lpStatement] = Set.empty
    var definitions: Set[String] = Set.empty
    val typeDecSB: mutable.StringBuilder = new StringBuilder()
    val skDecsSB: mutable.StringBuilder = new StringBuilder()
    val tacticSB: mutable.StringBuilder = new StringBuilder()
    val defSB: mutable.StringBuilder = new StringBuilder()

    signatureSymbols.foreach { key =>
      val symbol = sig.apply(key)
      val sName = lpEscapeName(symbol.name, sig, false)

      if (symbol.hasKind) {
        typeDecSB.append(lpDeclaration(lpConstantTerm(sName), Seq.empty, lpSet).pretty)
      } else {
        if (symbol.hasType) {
          if (isPropSet(Signature.PropSkolemConstant, symbol.flag)) {
            val typeDec = type2LP(symbol._ty, sig, true)
            skDecsSB.append(lpDeclaration(lpConstantTerm(sName), Seq.empty, typeDec.lift2Meta).pretty)
          }
          else {
            val typeDec = type2LP(symbol._ty, sig, false)
            typeDecSB.append(lpDeclaration(lpConstantTerm(sName), Seq.empty, typeDec.lift2Meta).pretty)
          }
        }

        if (symbol.hasDefn) { // && (! additionalSymbols.contains(key))) {

          val defTermType = type2LP(symbol._defn.ty, sig, true)

          if (isPropSet(Signature.PropSkolemConstant, symbol.flag)) {
            //todo: maybe generally encode defs with free vars like this?
            //Extract the lambda terms of the new definition and build a quantified version where the variables are applied to the skolem term
            val (bVarTys, strippedDef) = collectLambdasLP(symbol._defn)
            val newBVars = makeBVarList(bVarTys, 0)
            val encBvars = newBVars.map(v => lpOlTypedVar(lpOlConstantTerm(v._1),type2LP(v._2,sig)) )
            val appliedSk = lpOlFunctionApp(lpOlConstantTerm(sName),encBvars.map(Left(_)))
            val (definition, tptpDefinedSymbols0) = term2LP(strippedDef, fusebVarListwithMap(newBVars, Map()), sig, Set.empty, false, true)
            val defAsEq = lpOlTypedBinaryConnectiveTerm(lpEq, defTermType, lpOlFunctionApp(appliedSk, Seq.empty), definition)
            val encodedDef = lpDeclaration(lpConstantTerm(s"${sName}_def"), encBvars, defAsEq.prf)
            tptpDefinedSymbols = tptpDefinedSymbols ++ tptpDefinedSymbols0
            skDecsSB.append(encodedDef.pretty)
          }
          else {
            val (definition, tptpDefinedSymbols0) = term2LP(symbol._defn, Map(), sig, Set.empty, false, true)
            tptpDefinedSymbols = tptpDefinedSymbols ++ tptpDefinedSymbols0
            val defAsEq = lpOlTypedBinaryConnectiveTerm(lpEq, defTermType, lpOlFunctionApp(lpOlConstantTerm(s"${abbreviationSignatureFile}." + sName), Seq.empty), definition)
            val encodedDef = lpDeclaration(lpConstantTerm(s"${sName}_def"), Seq.empty, defAsEq.prf)
            defSB.append(encodedDef.pretty)
            // add to the list of definitions that should later be extended in the corresponding steps
            definitions += s"${sName}_def"
          }
        }
      }
    }

    if (definitions.nonEmpty) {
      // define a tactic rewriting with all of the definitions
      val allDefsListName = "allDefinitions"
      val decAllDefs = lpDefinition(lpConstantTerm(allDefsListName), Seq(), None, lpList(definitions.map(defName => lpRewrite(None, lpOlConstantTerm(s"${abbreviationFormulaeFile}." + defName)).olTermApp).toSeq))
      val applyAllDefsTact = lpDefinition(lpConstantTerm(applyAllDefsTacName), Seq(), None, lpRepeat(applyAnyStep(lpOlConstantTerm(allDefsListName))).olTermApp)
      tacticSB.append(decAllDefs.pretty)
      tacticSB.append(applyAllDefsTact.pretty)
    }

    (tptpDefinedSymbols, typeDecSB, skDecsSB, defSB, tacticSB)
  }

  def extractNecessaryFormulas(state: LocalState, gdv_mode: Boolean)  = {

    val proofFileSB: mutable.StringBuilder = new StringBuilder()
    val signatureFileSB: mutable.StringBuilder = new StringBuilder()
    val formulaeFileSB: mutable.StringBuilder = new StringBuilder()
    var proofSteps: Seq[lpProofScriptStep] = Seq.empty

    val flagSt = new lpProofObject

    val sig = state.signature
    val proof = state.proof

    var tptpDefinedSymbols: Set[lpStatement] = Set.empty
    var additionalSymbols: Set[Signature.Key] = Set.empty
    if ((sig.allUserConstants intersect symbolsInProof(proof)).filter(key => !isPropSet(Signature.PropSkolemConstant, sig(key).flag)).map(sig.apply(_).hasDefn).contains(true)) flagSt.defRuleDefined = true


    // encode the clauses representing the steps
    // todo: Also make it possible to just output one long lambda-term
    val compressedProof = proof
    var idClauseMap: mutable.HashMap[Long, ClauseProxy] = mutable.HashMap.empty
    val identicalSteps: mutable.HashMap[Long, lpConstantTerm] = mutable.HashMap.empty
    var skDefinitions: Set[lpDeclaration] = Set.empty
    val clausifiedSteps: mutable.HashMap[lpConstantTerm, lpConstantTerm] = mutable.HashMap.empty
    var conjEnc = false
    var axCounter = 0
    val conjName = lpConstantTerm(s"negatedConjecture")

    val problemEncSB: mutable.StringBuilder = new StringBuilder()

    var conjecture: lpOlTerm = lpOlBot // default Bot, as Leo omits conjecture from proof in this case todo: should we change that?!

    compressedProof foreach { step =>
      val stepId = step.id
      idClauseMap = idClauseMap + (stepId -> step)

      if (step.role == Role_NegConjecture) {
        if (conjEnc) throw new Exception("found more than one negated conjecture in the proof object to encode in LP")
        conjEnc = true
        val (encConj, tptpDefinedSymbols0) = clause2LP(step.cl, Set(), sig)
        tptpDefinedSymbols = tptpDefinedSymbols ++ tptpDefinedSymbols0
        identicalSteps += (stepId -> conjName)
        conjecture = encConj.lits match {
          case Seq(lpOlUnaryConnectiveTerm(lpNot, conj)) => conj
          case _ => throw new Exception(s"given negated conjecture ${encConj.pretty} not negated")
        }
      } else if (step.role == Role_Axiom) { //todo: what about other roles like lamme etc. ?
        val (encClause, tptpDefinedSymbols0) = clause2LP(step.cl, Set(), sig)
        tptpDefinedSymbols = tptpDefinedSymbols ++ tptpDefinedSymbols0
        Out.lp_debug_info(s"${step.annotation.pretty}")
        Out.lp_debug_info(s"${step.annotation.pretty.dropRight(1)}")
        Out.lp_debug_info(s"${step.annotation.pretty.dropRight(1)}")
        val tptpName = step.annotation.pretty
        val axName0 = if (tptpName == "introduced(axiom_of_choice)") "axiom_of_choice" else s"${tptpName.dropRight(1).split(",", 2)(1)}"
        val axName = if (gdv_mode) axName0 else axName0 + s"_p$axCounter"
        val safeAxName = lpEscapeName(axName,sig,false)
        problemEncSB.append(lpDeclaration(lpConstantTerm(safeAxName), Seq.empty, encClause).pretty(PrettyConfig(true,false)))
        identicalSteps += (stepId -> lpConstantTerm(s"${abbreviationFormulaeFile}.$safeAxName"))
        axCounter = axCounter + 1
      } else {
        val infoForStep = new lpProofStepInfo(clausifiedSteps.toMap, identicalSteps, tptpDefinedSymbols)
        val (newProofSteps, newInfo) = step2LP(step, sig, flagSt, infoForStep)
        clausifiedSteps ++= newInfo.clausifiedSteps
        identicalSteps ++= newInfo.identicalSteps
        tptpDefinedSymbols = tptpDefinedSymbols ++ newInfo.tptpDefinedSymbols
        additionalSymbols = additionalSymbols ++ newInfo.additionalDefinedSymbols
        skDefinitions = skDefinitions ++ newInfo.skDefinitions
        proofSteps = proofSteps ++ newProofSteps
      }
    }

    // add symbols of the user defined TPTP problem signature if necessary
    val signatureSymbols = saturatedUserSignature(symbolsInProof(proof) ++ additionalSymbols)(sig)

    val (tptpDefinedSymbols_defs, typeDecSB, skDecSB, defSB, tacticSB) = generateObjectDeclaartions(signatureSymbols, flagSt, sig)

    tptpDefinedSymbols = tptpDefinedSymbols_defs ++ tptpDefinedSymbols

    //val objectDecSB = typeDecSB.append(defSB)

    // set necessary flags
    if (flagSt.etaExpFlag) proofFileSB.append("// FLAGS /////////////////////////////////\n\nflag \"eta_equality\" on;\n")

    // Generate declarations of symbols that are implicit in TPTP but not mapped to a Lambdapi encoding
    if (tptpDefinedSymbols.nonEmpty) {
      Out.lp_debug_info(s"adding the following TPTPT defined symbols: ${tptpDefinedSymbols.map(_.pretty).mkString(", ")}")
      var declareInts = false
      val tptpSymbolsSB: mutable.StringBuilder = new StringBuilder()
      tptpDefinedSymbols foreach { tptpSymbol =>
        tptpSymbol match {
          case lpInt(_) =>
            declareInts = true
            val intDec = lpDeclaration(tptpSymbol, Seq(), lpIntType.lift2Meta)
            tptpSymbolsSB.append(intDec.pretty)
          case lpTptpOperator(name, ty, vars) =>
            tptpSymbolsSB.append(lpTptpOperator(name, ty, vars).dec.pretty)
          case _ => Out.lp_debug_info(s"LP-Encoding: Found TPTP defined symbol ${tptpSymbol.pretty}")
        }
      }
      if (declareInts) {
        val intDec = lpDeclaration(lpIntType, Seq(), lpSet)
        Out.lp_debug_info(s"need to define ints: ${intDec.pretty}")
        tptpSymbolsSB.insert(0, intDec.pretty)
      }
      signatureFileSB.append("// TPTP SYMBOL ENCODINGS /////////////////////////////////\n\n")
      signatureFileSB.append(tptpSymbolsSB)
    }
    if (typeDecSB.length != 0) {
      signatureFileSB.append("\n\n// OBJECT DECLARATIONS ///////////////////////////////////\n\n")
      signatureFileSB.append(typeDecSB)
    }

    if (skDefinitions.nonEmpty || skDecSB.length != 0) {
      proofFileSB.append("\n\n// SKOLEM TERMS ///////////////////////////////////\n\n")
      proofFileSB.append(skDecSB)
      proofFileSB.append(skDefinitions.map(defn => s"// ${defn.pretty}").mkString(""))
    }

    if (tacticSB.nonEmpty) {
      proofFileSB.append("\n\n// TACTIC TERMS ///////////////////////////////////\n\n")
      proofFileSB.append(tacticSB)
    }

    if (problemEncSB.length != 0 || defSB.length != 0) {
      formulaeFileSB.append("\n\n// PROBLEM ENCODING //////////////////////////////////////\n\n")
      formulaeFileSB.append(defSB).append(problemEncSB)
    }
    Out.info("Done enocoding the inference rules")

    proofFileSB.append("\n\n// PROOF ENCODING ////////////////////////////////////////\n\n")

    // construct the proof based on all the individual steps
    // in the proof of the conjecture, first instanciate dne, then assume the negated conjecture
    proofSteps = lpAssume(Seq(conjName)) +: proofSteps
    proofSteps = lpRefine(lpFunctionApp(lpDne.name, Seq(conjecture, lpWildcard))) +: proofSteps
    // finally, test if the derived last clause is the empty clause or a flex-flex clause.
    // Instanciate with the empty clause or introduce an additional step in case of a flex-flex clause
    val emptyClause = lpClause(Seq(), Seq(lpOlBot))
    val lastStep = proofSteps.last match {
      case lpHave(name, `emptyClause`, _, _) => lpConstantTerm(name)
      case lpHave(name, flexFlex0, _, _) =>
        // transformation of flex-flex to bot necessary todo
        Out.lp_debug_info(s"Transformation of flex-flex literal to bot necessary...")
        val proofFun = lpMlFunctionType(Seq(flexFlex0, lpOlBot.prf))
        val flexFlexStepName = "flexflex_to_bot"
        val (appliedflexFlexStepName, appliedStepName) = flexFlex0 match {
          case lpClause(vars, lits) =>
            val appliedVars = vars.map(var0 => lpWitness(isTermVar(var0).ty))
            (lpFunctionApp(lpConstantTerm(flexFlexStepName), appliedVars), (lpFunctionApp(lpConstantTerm(name), appliedVars)))
          case _ => (lpConstantTerm(flexFlexStepName), lpConstantTerm(name))
        }
        //throw new Exception(s"vars are ${variablesToApply.map(_.pretty)}")
        val proofHave = lpHave(flexFlexStepName, proofFun, lpProofScript(Seq(lpProofScriptAdmit())))
        proofSteps = proofSteps :+ proofHave
        lpFunctionApp(appliedflexFlexStepName, Seq(appliedStepName))
      case _ => throw new Exception(s"in the encoding, the last step had an unexptected tactic: ${proofSteps.last.pretty}")
    }
    proofSteps = proofSteps :+ lpRefine(lpFunctionApp(lastStep, Seq.empty))
    val completeProof = lpDefinition(lpConstantTerm("encodedProof"), Seq.empty, Some(conjecture.prf), lpProofScript(proofSteps), Seq(), Seq(lpOpaque))
    proofFileSB.append(completeProof.pretty(PrettyConfig(true,false)))

    (proofFileSB,signatureFileSB,formulaeFileSB)
  }

  def outputLPFiles(state: LocalState, lpOutputPath0: String, nameLpOutputFolder: String):Unit={

    val lpOutputPath = Paths.get(lpOutputPath0).resolve(nameLpOutputFolder)
    val (proofFileSB,signatureFileSB,formulaeFileSB) = extractNecessaryFormulas(state, false)

    val tempLibStr: String = s"${nameLpOutputFolder}.${nameTempFile}"


    // create a folder for the lambdapi package
    // Create the output directory if it doesn't exist
    if (!Files.exists(lpOutputPath)) {
      Files.createDirectory(lpOutputPath)
      println(s"Folder '$nameLpOutputFolder' created.")
    } else {
      println(s"Folder '$nameLpOutputFolder' already exists, overwriting files.")
    }

    // write the files
    Out.info("Writing the Lambdapi files")

    // todo: only require what we need
    val reqList = Seq("Stdlib.Set","Stdlib.Prop","Stdlib.Classic","Stdlib.FOL","Stdlib.HOL","Stdlib.Eq","Stdlib.Impred","Stdlib.FunExt","Stdlib.PropExt","Stdlib.Nat","Stdlib.Bool","Stdlib.List","Stdlib.Epsilon",tempLibStr,calcRuleLibStr,permLibStr,multiNdLibStr)
    //val reqString = s"require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt Stdlib.PropExt Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Epsilon $calcRuleLibStr $simpTacLibStr $permLibStr;\n"
    val reqString = reqList.map(s => s"require open $s;\n").mkString("")
    var additions = ""

    if (signatureFileSB.length != 0) {
      val signatureFilePath = lpOutputPath.resolve(s"$nameSignatureFile.lp")
      signatureFileSB.insert(0, reqString)
      Files.write(signatureFilePath, signatureFileSB.toString.getBytes(StandardCharsets.UTF_8))
      additions = s"require ${nameLpOutputFolder}.$nameSignatureFile as $abbreviationSignatureFile; \n"
    }

    if (formulaeFileSB.length != 0) {
      val formulaeFilePath = lpOutputPath.resolve(s"$nameFormulaeFile.lp")
      formulaeFileSB.insert(0, reqString + additions + "\n\n")
      Files.write(formulaeFilePath, formulaeFileSB.toString.getBytes(StandardCharsets.UTF_8))
      additions = additions + s"require ${nameLpOutputFolder}.$nameFormulaeFile as $abbreviationFormulaeFile;\n"
    }

    val proofFilePath = lpOutputPath.resolve(s"$nameProofFile.lp")
    proofFileSB.insert(0, reqString + additions + "\n\n") // maybe it may be necessary in some cases to add "\nnotation ∨ infix right 6;"
    Files.write(proofFilePath, proofFileSB.toString.getBytes(StandardCharsets.UTF_8))

    val tempFilePath = lpOutputPath.resolve(s"$nameTempFile.lp")
    Files.write(tempFilePath, tempLib.getBytes(StandardCharsets.UTF_8))

    // create the Makefile and the pkg file
    val pkgFileName = "lambdapi.pkg"
    createLambdapiFiles(lpOutputPath, nameLpOutputFolder, pkgFileName, nameProofFile)
  }

  def proof2LP(state: LocalState):String = {
    val lpContextPlaceholder = "LAMBDAPI_CONTEXT"
    val reqString = s"require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt Stdlib.PropExt Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Epsilon $calcRuleLibStr $simpTacLibStr $permLibStr $multiNdLibStr;\nrequire $lpContextPlaceholder.Signature as S;\nrequire $lpContextPlaceholder.Formulae as F \n\n;"
    val (proofFileSB,_,_) = extractNecessaryFormulas(state, true)
    proofFileSB.insert(0, reqString)
    val conjName = s"${state.conjecture.annotation.pretty.dropRight(1).split(",", 2)(1)}"
    val finalRule = lpRule(lpConstantTerm(s"$abbreviationFormulaeFile." + conjName), Seq.empty,lpConstantTerm(nameProofFile))
    proofFileSB.append("\n")
    proofFileSB.append(finalRule.pretty)
    proofFileSB.toString()
  }
}