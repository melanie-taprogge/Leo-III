package leo.modules.output.LPoutput

import leo.{Out, modules}
import leo.datastructures.Term.Integer
import leo.datastructures.{ClauseProxy, Role_Axiom, Role_Conjecture, Role_NegConjecture, Signature, isPropSet}
import leo.modules.HOLSignature.{HOLDifference, HOLGreater, HOLGreaterEq, HOLLess, HOLLessEq, HOLProduct, HOLQuotient, HOLSum, HOLUnaryMinus}
import leo.modules.output.LPoutput.DetUniSimpEncoding.encodeDetUniSimp
import leo.modules.output.LPoutput.LpLibs.ND.Terms
import leo.modules.prover.LocalState
import leo.modules.{numbersInProof, saturatedUserSignature, symbolsInProof}
import leo.modules.output.LPoutput.OldLpDatastructures.Encodings._
import leo.modules.output.LPoutput.OldLpDatastructures.LPSignature.{lpDne, tempLib, tempLibDeps}
import leo.modules.output.LPoutput.ModularProofEncoding.ParamodEncoding.encPara
import leo.modules.output.LPoutput.ModularProofEncoding.CnfConjEncoding.encCnfConj
import leo.modules.output.LPoutput.ModularProofEncoding.RwCnfEncoding.encRenameCnf_conj
import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures._
import leo.modules.output.LPoutput.ModularProofEncoding._
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.{Obj, Wildcard}
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{El, LpSet}
import leo.modules.output.LPoutput.NewLpDatastructures.Stmt.Opaque
import leo.modules.output.LPoutput.NewLpDatastructures.nameGeneration.nameInt

import java.nio.file.{Files, Path, Paths, StandardOpenOption}
import java.nio.charset.StandardCharsets
import scala.collection.mutable
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, ClauseEncoding, DefEncoding, HolBaseTypes, Level, LogicConst, LpProofScript, LpSig, LpTerm, LpType, Name, Prefix, QName, RenderOptions, Renderer, Stmt, SymRef, TermEncoding, TypeEncoding}
import leo.modules.output.LPoutput.UnificationEncoding.encodePatternUni

/**
  * Generation of the various files making up the Lambdapi encoding
  *
  * @author Melanie Taprogge
  */

object LPoutput {

  val outputSingleFile = false

  val permlibFile = "MetaTheorems"
  val calcRuleLibFile = "EPrules"
  val leoSimpTacticFile = "UserTactic"
  val nameLeoIIILPlib = "Leo-III-lambdapi-lib"
  val nameProofFile = "encodedProof"
  val nameSignatureFile = "Signature"
  val abbreviationSignatureFileNoDot = "S"
  val abbreviationSignatureFile = if (outputSingleFile) "" else abbreviationSignatureFileNoDot + "."
  val nameFormulaeFile = "Formulae"
  val abbreviationFormulaeFileNoDot = "F"
  val abbreviationFormulaeFile = if (outputSingleFile) "" else abbreviationFormulaeFileNoDot + "."

  val nameTempFile = "UserTactic"
  val customUserTacFile = false

  val applyAllDefsTacName0 = "applyAllDefinitions"

  val permLibStr: String = f"${nameLeoIIILPlib}.${permlibFile}"
  val simpTacLibStr = f"${nameLeoIIILPlib}.${leoSimpTacticFile}"
  val calcRuleLibStr = f"${nameLeoIIILPlib}.${calcRuleLibFile}"

  final class lpProofObject {
    var etaExpFlag: Boolean = true
    var defRuleDefined: Boolean = false
  }

  final class lpProofStepInfo (val clausifiedSteps: Map[lpConstantTerm, lpConstantTerm] = Map.empty,
                               val identicalSteps: mutable.HashMap[Long, QName] = mutable.HashMap.empty,
                               val additionalDefinedSymbols: Set[Signature.Key] = Set.empty) //todo: remove additionalDefinedSymbols

  def toProofStepOld(stepName: String, encStep: LpType, ruleName: String, proofTerm: lpProofScriptStep, notEncoded: Option[String]): Option[(LpProofScript.Comment, LpProofScript)] = {
    toProofStepOld(stepName, encStep, ruleName, Right(proofTerm), notEncoded)
  }

    def toProofStepOld(stepName: String, encStep: LpType, ruleName: String, proofTerm: Either[Seq[LpProofScript], lpProofScriptStep], notEncoded: Option[String]): Option[(LpProofScript.Comment,LpProofScript)] = {
    if (notEncoded.isDefined) {
      // if the step is actually new, we want to add it to the output
      // add substeps for which the encoding is not implemented using the "admit" tactic
      Out.lp_debug_info(s"Not encoded yet (${notEncoded.get})\n")
      //val proofScript = lpHave(stepName, encStep, lpProofScript(Seq(lpProofScriptAdmit())))
      val proofScript = LpProofScript.Have(Name(stepName),encStep,Seq(Left(LpProofScript.Admit)))
      Some((LpProofScript.Comment(s"Unencoded step ($ruleName): " + notEncoded.get), proofScript))
    } else {
      Out.lp_debug_info(s"Encoding finished!\n")
      // add the encoded proofs to the overall proof as substeps
      val proofScript = proofTerm match {
        case Left(newScr) => LpProofScript.Have(Name(stepName),encStep,newScr.map(step => Left(step)))
        case Right(oldScr) => LpProofScript.Have(Name(stepName),encStep,Seq(Right(oldScr)))
      }
      Some((LpProofScript.Comment(ruleName), proofScript))
      // and add the necessary symbols to the generated Signature
    }
  }

  def toProofStep(stepName: String, encStep: LpType, ruleName: String, proofTerm: lpProofScriptStep, notEncoded: Option[String]): Option[(LpProofScript.Comment, LpProofScript)] = {
    toProofStepOld(stepName, encStep, ruleName, Right(proofTerm), notEncoded)
  }

  def toProofStep(stepName: String, encStep: LpType, ruleName: String, proofTerm: Either[LpProofScript, lpProofScriptStep], notEncoded: Option[String]): Option[(LpProofScript.Comment, LpProofScript)] = {
    // todo: use the new trait for results rather than optional stirngs
    if (notEncoded.isDefined) {
      // if the step is actually new, we want to add it to the output
      // add substeps for which the encoding is not implemented using the "admit" tactic
      Out.lp_debug_info(s"Not encoded yet (${notEncoded.get})\n")
      //val proofScript = lpHave(stepName, encStep, lpProofScript(Seq(lpProofScriptAdmit())))
      val proofScript = LpProofScript.Have(Name(stepName), encStep, Seq(Left(LpProofScript.Admit)))
      Some((LpProofScript.Comment(s"Unencoded step ($ruleName): " + notEncoded.get), proofScript))
    } else {
      Out.lp_debug_info(s"Encoding finished!\n")
      // add the encoded proofs to the overall proof as substeps
      val proofScript = LpProofScript.Have(Name(stepName), encStep, Seq(proofTerm))
      Some((LpProofScript.Comment(ruleName), proofScript))
      // and add the necessary symbols to the generated Signature
    }
  }

  def identifySteps(cl: ClauseProxy, identicalSteps: mutable.HashMap[Long, lpConstantTerm], sig:LpSig, encStep: lpClause): (Boolean, mutable.HashMap[Long, lpConstantTerm]) = {
    var encodeStep = false
    cl.annotation.parents foreach { parent =>
      val encParent = clause2LP(parent.cl, Set.empty, sig.orig)._1
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

  def identifySteps_new(cl: ClauseProxy, identicalSteps: mutable.HashMap[Long, QName], encStep: NewLpDatastructures.lpClauseInst): (Boolean, mutable.HashMap[Long, QName]) = {
    var encodeStep = false
    cl.annotation.parents foreach { parent => // todo: save them rather than translating over and over again
      val encParent = NewLpDatastructures.ClauseEncoding.clause2LP(parent.cl)
      if (encParent == encStep) { // case: any potential differences are abstracted away by rendering -> need not prove
        if (identicalSteps.contains(cl.id)) {
          if (identicalSteps(cl.id) != nameStep(parent.id)) {
            throw new Exception(s"step $cl.id ($encStep) is equivalent to two parents: ${cl.id}, ${parent.id} ")
          }
        }
        if (identicalSteps.contains(parent.id)) {
          // in this case we already have the parent as a key and want to map the new child to the parents parent
          val exVal = identicalSteps(parent.id)
          Out.lp_debug_info(s"identical steps for parent ${parent.id} (maps to ${exVal})")
          identicalSteps.update(cl.id, exVal)
        } else {
          // in this case we just want to link the child to the parent
          val exVal = nameStep_new(parent.id)
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

  def extractParentInfoN_new(child: ClauseProxy,
                         identicalSteps: Map[Long, QName],
                         expectedParents: Int
                        ): Either[String, Seq[ParentInfo]] = {
    val parents = child.annotation.parents
    if (parents.length != expectedParents)
      Left(s"Lambdapi encoding error: expected $expectedParents parents, got ${parents.length} (child id ${child.id})")
    else {
      def nameOf(p: ClauseProxy): lpConstantTerm = {
        val asName = identicalSteps.getOrElse(p.id, nameStep_new(p.id))
        lpConstantTerm(Renderer.qname(asName,RenderOptions(!outputSingleFile,!outputSingleFile,monomorphic)))
      }

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

  def extractParentInfo2_new(child: ClauseProxy, identicalSteps: Map[Long, QName]): Either[String, (ParentInfo, ParentInfo)] = {
    extractParentInfoN_new(child, identicalSteps, 2) match {
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

  def extractParentInfo1_new(child: ClauseProxy, identicalSteps: Map[Long, QName]): Either[String, ParentInfo] = {
    extractParentInfoN_new(child, identicalSteps, 1) match {
      case Left(error) => Left(error)
      case Right(Seq(parent0)) => Right(parent0)
      case _ => Left(s"Lambdapi encoding error: Failure when extracting parent info")
    }
  }

  def step2LP(cl: ClauseProxy, sig: LpSig, st: lpProofObject, stepInfo: lpProofStepInfo): (Option[(LpProofScript.Comment,LpProofScript)], lpProofStepInfo) = {

    val stepName = nameStep(cl.id).name
    val rule = cl.annotation.fromRule
    // since we do not write out steps that are identical in our encoding, we keep track of what the reference to the parent clause in LP is
    val parentInLpEncID_new = cl.annotation.parents.map(parent => stepInfo.identicalSteps.getOrElse(parent.id, nameStep_new(parent.id)))

    // for compatibility, temproarily translate the names to constantnt terms...
    val parentInLpEncID = {
      parentInLpEncID_new.map(nm => lpConstantTerm(Renderer.qname(nm,RenderOptions(!outputSingleFile,!outputSingleFile,monomorphic))))
    }
    Out.lp_debug_info(s"parents in lp encoding new : $parentInLpEncID_new, as terms: $parentInLpEncID")

    Out.lp_debug_info(s"Encoding step $stepName: application of caluclus rule ${if (rule == null) "Tautology" else rule.name}")
    Out.lp_debug_info(s"The parents are ${parentInLpEncID_new.map(term => term.local.value).mkString(", ")}")

    val (encStep0) = ClauseEncoding.clause2LP(cl.cl)
    val encStep = encStep0.asMl
    val (needsEnc, newIdenticalSteps) = identifySteps_new(cl,stepInfo.identicalSteps,encStep0)

    if ((cl.role != Role_Conjecture) && needsEnc && (rule != null)) {
      rule match {

        case _ =>
          val outputInfo = new lpProofStepInfo(Map.empty,newIdenticalSteps)

          rule match {
            case leo.modules.calculus.CnfConj =>
              val parent = extractParentInfo1_new(cl, stepInfo.identicalSteps.toMap) match {
                case Left(error) => throw new Exception(error)
                case Right(value) => value
              }
              val idx = cl.furtherInfo.cnfConjInfo match {
                case Some(value) => value
                case None => throw new Exception("Error in Lmabdapi encoding: No additional information for the Lambdapi encoding was supplied")
              }
              val encProof = encCnfConj(cl, parent, idx, sig.orig)
              (toProofStepOld(stepName, encStep, rule.name, encProof, None), outputInfo)

            case leo.modules.calculus.RenameCNF =>
              val encodingCNF = encRenameCnf_conj(cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.cnfInfo, sig.orig)
              val compatibleStep = LpType.Old(encodingCNF._3.pretty(PrettyConfig(!outputSingleFile,!outputSingleFile)))
              val stepsCNF = toProofStepOld(stepName, compatibleStep, "RenameCNF_conj", encodingCNF._1, encodingCNF._2)
              val outputInfo = new lpProofStepInfo(Map.empty,newIdenticalSteps,encodingCNF._4)
              (stepsCNF,outputInfo)

            case leo.modules.calculus.PolaritySwitch =>
              val encoding = encPolaritySwitch(cl, cl.annotation.parents.head, parentInLpEncID.head, sig.orig) //¿polarity switch always only has one parent, right?
              (toProofStepOld(stepName, encStep, "PolaritySwitch", encoding, None),outputInfo)

            case leo.modules.calculus.FuncExt =>
              val encoding = encFuncExtPos(cl, cl.annotation.parents.head, cl.furtherInfo.edLitBeforeAfter, parentInLpEncID.head, sig.orig)
              (toProofStepOld(stepName, encStep, "FuncExt", encoding._1, encoding._2),outputInfo)

            case leo.modules.calculus.BoolExt =>
              val encoding = encBoolExt(cl, cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.addInfoBoolExt, sig.orig)
              (toProofStepOld(stepName, encStep, "BoolExt", encoding._1, encoding._2),outputInfo)

            case leo.modules.calculus.OrderedEqFac =>
              val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoEqFac, parentInLpEncID.head, sig.orig)
              (toProofStepOld(stepName, encStep, "OrderedEqFac", encodings._1, None),outputInfo)

            ////////////////////////////////////////
            // Paramodulation encoding
            case leo.modules.calculus.OrderedParamod =>
              val (parentWithClause, parentIntoClause) = extractParentInfo2_new(cl, stepInfo.identicalSteps.toMap) match {
                case Left(error) => throw new Exception(error)
                case Right(value) => value
              }
              val addInfoPara = cl.furtherInfo.para match {
                case Some(value) => value
                case None => throw new Exception("Error in Lmabdapi encoding: No additional information for the Lambdapi encoding was supplied")
              }
              val (encProof, cantencode) = encPara(cl.cl, parentWithClause, parentIntoClause, addInfoPara, sig.orig)
              (toProofStepOld(stepName, encStep, "OrderedPara", encProof, cantencode),outputInfo)

            case leo.modules.calculus.DefExpSimp =>
              //throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoDefExp}")
              // todo: eta expansion
              val (proofSteps, cantENcode) = EncDefExSimp(cl, cl.annotation.parents.head, st.defRuleDefined, cl.furtherInfo.rwUnderBinder, cl.furtherInfo.addInfoDefExp, applyAllDefsTacName0, parentInLpEncID.head, sig.orig)
              if (!cantENcode.isDefined) st.etaExpFlag = true
              (toProofStepOld(stepName, encStep, "DefExpand", lpProofScript(proofSteps), cantENcode),outputInfo)

            case leo.modules.calculus.Simp =>
              if (cl.furtherInfo.addInfoSimpRule.isDefined) {
                if (cl.furtherInfo.addInfoSimpRule.get == "eqSimp") {
                  if (cl.furtherInfo.rwUnderBinder) {
                    (toProofStepOld(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Some("Simp: This instance can not be encoded yet as it requires RW under Binder")),outputInfo)
                  }
                  else {
                    val allSteps = newSimpEncoding(cl.cl, cl.annotation.parents.head.cl, parentInLpEncID.head, sig.orig)
                    (toProofStepOld(stepName, encStep, s"FormulaSimp", lpProofScript(allSteps), None),outputInfo)
                  }
                } else if (cl.furtherInfo.addInfoSimpRule.get == "paraSimp") {
                  if (cl.furtherInfo.rwUnderBinder) {
                    (toProofStepOld(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Some("Simp: This instance can not be encoded yet as it requires RW under Binder")), outputInfo)
                  }
                  else {
                    val allSteps = newSimpEncoding(cl.cl, cl.annotation.parents.head.cl, parentInLpEncID.head, sig.orig, Seq(cl.annotation.parents.head.cl.lits.length - 1))
                    (toProofStepOld(stepName, encStep, s"FormulaSimp", lpProofScript(allSteps), None), outputInfo)
                  }
                }else if (cl.furtherInfo.addInfoSimpRule.get == "detUniInferences") {
                  val encProof = encodeDetUniSimp(cl.annotation.parents.head,cl,Name(parentInLpEncID.head.name),sig)
                  encProof match {
                    case EncodeResult.Encoded(scripts) => (toProofStepOld(stepName, encStep, "DetUniSimp", Left(scripts), None), outputInfo)
                    case EncodeResult.NotEncodable(reason) => (toProofStepOld(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Some(reason)), outputInfo)
                  }
                } else {
                  val annotation = Some(s"Simp: ${cl.furtherInfo.addInfoSimpRule.get} currently not encoded")
                  (toProofStepOld(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), annotation),outputInfo)
                }
              } else {
                val annotation = Some("Simp: Unidentified formula simplification unencoded")
                (toProofStepOld(stepName, encStep, s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), annotation),outputInfo)
              }

            case leo.modules.calculus.PreUni =>
              val encodingPreUni = encPreUni(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoUni, cl.furtherInfo.addInfoUniRule, parentInLpEncID.head, sig.orig)
              (toProofStepOld(stepName, encStep, "PreUni", encodingPreUni._1, encodingPreUni._2),outputInfo)

            case leo.modules.calculus.RewriteSimp =>
              val encodingRewrite = encRewrite(cl, cl.annotation.parents, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoRewriting, parentInLpEncID, sig.orig)
              (toProofStepOld(stepName, encStep, "RewriteSimp", encodingRewrite._1, encodingRewrite._2),outputInfo)

            case leo.modules.calculus.LiftEq =>
              val encodingLiftEq = encLiftEq(cl, cl.annotation.parents, cl.furtherInfo.addInfoLiftEq, parentInLpEncID, sig.orig)
              (toProofStepOld(stepName, encStep, "LiftEq", encodingLiftEq._1, encodingLiftEq._2),outputInfo)

            case leo.modules.calculus.PatternUni =>
              val encProof = encodePatternUni(cl.annotation.parents.head,cl,Name(parentInLpEncID.head.name),sig)
              encProof match {
                case EncodeResult.Encoded(scripts) => (toProofStepOld(stepName, encStep, rule.name, Left(scripts), None),outputInfo)
                case EncodeResult.NotEncodable(reason) => (toProofStepOld(stepName, encStep, rule.name, Left(Seq.empty), Some(reason)),outputInfo)
              }

            case _ =>
              val parentIDs = parentInLpEncID.map(id => id.name)
              (toProofStepOld(stepName, encStep, rule.name, lpProofScript(Seq.empty), Option(s"unencoded rule applied to ${parentIDs.mkString(", ")}")),outputInfo)
          }
      }
    }else{
      val outputInfo = new lpProofStepInfo(Map.empty, newIdenticalSteps)
      if (rule == null && (cl.role != Role_Conjecture)) {
        Out.lp_debug_info(s"role : ${cl.role}")
        (toProofStepOld(stepName, encStep, "Tautology", lpProofScript(Seq.empty), Some("Tautology generation not yet encoded")), outputInfo)
      }else{
        (None, outputInfo)
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
    if (!outputSingleFile){
      Files.write(
        pkgFilePath,
        pkgFileContent.getBytes(StandardCharsets.UTF_8),
        StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING
      )
    }

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
    if (!outputSingleFile){
      val makefilePath = outputFolderPath.resolve("Makefile")
      Files.write(
        makefilePath,
        makefileContent.getBytes(StandardCharsets.UTF_8),
        StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING
      )
      Out.lp_debug_info(s"Makefile written to: ${makefilePath.toAbsolutePath}")
    }
  }

  def generateObjectDeclaartions(proof: modules.Proof, sig: LpSig): (StringBuilder, StringBuilder, StringBuilder, StringBuilder) = {

    // add symbols of the user defined TPTP problem signature if necessary
    val proofSymbols = symbolsInProof(proof)
    val signatureSymbols = saturatedUserSignature(proofSymbols)(sig.orig)

    val numbers = numbersInProof(proof)

    val typeDecSB: mutable.StringBuilder = new StringBuilder()
    val skDecsSB: mutable.StringBuilder = new StringBuilder()
    val tacticSB: mutable.StringBuilder = new StringBuilder()
    val defSB: mutable.StringBuilder = new StringBuilder()

    // if necessary, add declarations of numbers
    if (numbers.nonEmpty) {
      val intsSB: mutable.StringBuilder = new StringBuilder()

      numbers foreach (num =>
        num match {
          case Integer(n) =>
            Out.lp_debug_info(s"int $n")
            val newDec = Stmt.Declaration(Name(nameInt(n)), Seq(), El(HolBaseTypes.Int))
            intsSB.append(NewLpDatastructures.Renderer.stmt(newDec, sig, RenderOptions(false, !outputSingleFile, monomorphic)))
          case _ => throw new Exception(s"Error in LP encoding: Trying to declare Numbers other than Ints") //todo
        }
        )

      if (intsSB.length() != 0){
        // add the tptp type of the found numbers
        val intDec = Stmt.Declaration(sig.typeNames(HolBaseTypes.intTyN.id).local, Seq(), LpType.LpSet)
        typeDecSB.append("// Integers\n")
        typeDecSB.append(NewLpDatastructures.Renderer.stmt(intDec, sig, RenderOptions(false, !outputSingleFile, monomorphic)))
        typeDecSB.append(intsSB)
        typeDecSB.append("\n")
      }

      // declare necessary connectives
      val arithmaticConnecitves: Set[Signature.Key] = Set(HOLLess.key, HOLLessEq.key, HOLGreater.key, HOLGreaterEq.key, HOLUnaryMinus.key, HOLSum.key, HOLDifference.key, HOLProduct.key, HOLQuotient.key)
      val conInProof = proofSymbols.intersect(arithmaticConnecitves)

      conInProof foreach{con =>
        val sName = sig.termNames(con)
        if (sig.orig(con).hasType) {
          Out.lp_debug_info(s"declaring $sName")
          val typeDec = TypeEncoding.polyType2Lp(sig.orig(con)._ty)
          typeDecSB.append(NewLpDatastructures.Renderer.stmt(NewLpDatastructures.Stmt.Declaration((sName.local), Seq.empty, typeDec), sig, RenderOptions(false, false, monomorphic)))
        }
      }

    }

    signatureSymbols.foreach { key =>
      val symbol = sig.orig.apply(key)

      if (symbol.hasKind) {
        val sName = sig.typeNames(symbol.key)
        typeDecSB.append(NewLpDatastructures.Renderer.stmt(NewLpDatastructures.Stmt.Declaration((sName.local), Seq.empty, LpSet), sig, RenderOptions(false, false, monomorphic)))
      } else {
        val sName = sig.termNames(symbol.key)
        val isSk = isPropSet(Signature.PropSkolemConstant, symbol.flag)
        if (symbol.hasType) {
          val typeDec = TypeEncoding.type2LP(symbol._ty)
          if (isSk) skDecsSB.append(NewLpDatastructures.Renderer.stmt(NewLpDatastructures.Stmt.Declaration((sName.local), Seq.empty, El(typeDec)), sig, RenderOptions(!outputSingleFile, !outputSingleFile, monomorphic)))
          else typeDecSB.append(NewLpDatastructures.Renderer.stmt(NewLpDatastructures.Stmt.Declaration((sName.local), Seq.empty, El(typeDec)), sig, RenderOptions(false, false, monomorphic)))
        }

        if (symbol.hasDefn) {
          val defDec = DefEncoding.encDfn(key, sig, isSk)
          if (isSk) skDecsSB.append(NewLpDatastructures.Renderer.stmt(defDec, sig, RenderOptions(!outputSingleFile, !outputSingleFile, monomorphic)))
          else defSB.append(NewLpDatastructures.Renderer.stmt(defDec, sig, RenderOptions(!outputSingleFile, false, monomorphic)))
        }
      }
    }

    (typeDecSB, skDecsSB, defSB, tacticSB)
  }

  def extractNecessaryFormulas(state: LocalState, gdv_mode: Boolean)  = {

    val proofFileSB: mutable.StringBuilder = new StringBuilder()
    val signatureFileSB: mutable.StringBuilder = new StringBuilder()
    val formulaeFileSB: mutable.StringBuilder = new StringBuilder()
    var proofSteps: Seq[LpProofScript] = Seq.empty

    val flagSt = new lpProofObject

    val sig0 = state.signature
    val sig = LpSig.fromLeo(sig0)
    val proof = state.proof

    var tptpDefinedSymbols: Set[QName] = Set.empty
    var additionalSymbols: Set[Signature.Key] = Set.empty
    if ((sig.orig.allUserConstants intersect symbolsInProof(proof)).filter(key => !isPropSet(Signature.PropSkolemConstant, sig.orig(key).flag)).map(sig.orig.apply(_).hasDefn).contains(true)) flagSt.defRuleDefined = true


    // encode the clauses representing the steps
    // todo: Also make it possible to just output one long lambda-term
    val compressedProof = proof
    var idClauseMap: mutable.HashMap[Long, ClauseProxy] = mutable.HashMap.empty
    val identicalSteps: mutable.HashMap[Long, QName] = mutable.HashMap.empty
    val clausifiedSteps: mutable.HashMap[lpConstantTerm, lpConstantTerm] = mutable.HashMap.empty
    var conjEnc = false
    var axCounter = 0
    val conjName = QName.local(s"negatedConjecture")

    val problemEncSB: mutable.StringBuilder = new StringBuilder()

    var conjecture: LpTerm[Level.Obj] = LogicConst.Bot // default Bot, as Leo omits conjecture from proof in this case todo: should we change that?!

    compressedProof foreach { step =>
      val stepId = step.id
      idClauseMap = idClauseMap + (stepId -> step)

      if (step.role == Role_NegConjecture) {
        if (conjEnc) throw new Exception("found more than one negated conjecture in the proof object to encode in LP")
        conjEnc = true
        val (encConj, _) = clause2LP(step.cl, Set(), sig.orig)
        val (newEncConj) = ClauseEncoding.clause2LP(step.cl)
        identicalSteps += (stepId -> conjName)
        conjecture = newEncConj.lits.map(_.term) match {
          case Seq(LogicConst.Not(conj)) => conj
          case _ => throw new Exception(s"given negated conjecture ${encConj.pretty} not negated")
        }
      } else if (step.role == Role_Axiom) { //todo: what about other roles like lamme etc. ?
        val encClause = ClauseEncoding.clause2LP(step.cl)
        val tptpName = step.annotation.pretty
        val axName0 = if (tptpName == "introduced(axiom_of_choice)") "axiom_of_choice" else s"${tptpName.dropRight(1).split(",", 2)(1)}"
        val axName = if (gdv_mode) axName0 else axName0 + s"_p$axCounter"
        val safeAxName = lpEscapeName(axName,sig.orig,false)
        problemEncSB.append(NewLpDatastructures.Renderer.stmt(NewLpDatastructures.Stmt.Declaration(Name(safeAxName),Seq.empty,encClause.asMl),sig,RenderOptions(!outputSingleFile,false,monomorphic)))
        identicalSteps += (stepId -> QName.in(Prefix.Formula, safeAxName))
        Out.lp_debug_info(s"linking to axiom $safeAxName (id: $stepId)")
        axCounter = axCounter + 1
      } else {
        val infoForStep = new lpProofStepInfo(clausifiedSteps.toMap, identicalSteps)
        val (newProofSteps, newInfo) = step2LP(step, sig, flagSt, infoForStep)
        clausifiedSteps ++= newInfo.clausifiedSteps
        identicalSteps ++= newInfo.identicalSteps
        additionalSymbols = additionalSymbols ++ newInfo.additionalDefinedSymbols
        val newStepsSeq = if (newProofSteps.isDefined) Seq(newProofSteps.get._1,newProofSteps.get._2) else Seq.empty
        proofSteps = proofSteps ++ newStepsSeq
      }
    }

    val (typeDecSB, skDecSB, defSB, tacticSB) = generateObjectDeclaartions(proof, sig)

    // set necessary flags
    if (flagSt.etaExpFlag) proofFileSB.append("// FLAGS /////////////////////////////////\n\nflag \"eta_equality\" on;\n")


    // Generate declarations of symbols that are implicit in TPTP but not mapped to a Lambdapi encoding
    /*
    if (tptpDefinedSymbols.nonEmpty) {
      Out.lp_debug_info(s"adding the following TPTPT defined symbols: ${tptpDefinedSymbols.map(_.local.value).mkString(", ")}")
      var declareInts = false
      val tptpSymbolsSB: mutable.StringBuilder = new StringBuilder()
      tptpDefinedSymbols foreach { tptpSymbol =>
        tptpSymbol match {
          case LpTerm.TptpInt(_) =>
            declareInts = true
            val intDec = Stmt.Declaration(tptpSymbol.local,Seq(),LpType.El(HolBaseTypes.Int))
            tptpSymbolsSB.append(Renderer.stmt(intDec,sig,RenderOptions(false,!outputSingleFile,monomorphic)))
          case lpTptpOperator(name, ty, vars) =>
            tptpSymbolsSB.append(lpTptpOperator(name, ty, vars).dec.pretty)
          case _ => Out.lp_debug_info(s"LP-Encoding: Found TPTP defined symbol ${tptpSymbol.pretty(sig)}")
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
    */
    if (typeDecSB.length != 0) {
      signatureFileSB.append("\n\n// OBJECT DECLARATIONS ///////////////////////////////////\n\n")
      signatureFileSB.append(typeDecSB)
    }

    if (skDecSB.length != 0) {
      proofFileSB.append("\n\n// SKOLEM TERMS ///////////////////////////////////\n\n")
      proofFileSB.append(skDecSB)
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
    proofSteps = LpProofScript.Assume(Seq(conjName.local)) +: proofSteps
    val refineStep = LpProofScript.Refine(LpTerm.App[Level.Meta](Obj(Terms.lpDne),Seq(Arg.Explicit(LpTerm.Obj(conjecture)),Arg.Explicit(Wildcard[Level.Meta]))))
    proofSteps = refineStep +: proofSteps
    // finally, test if the derived last clause is the empty clause or a flex-flex clause.
    // Instanciate with the empty clause or introduce an additional step in case of a flex-flex clause
    val emptyClause = NewLpDatastructures.lpClauseInst(Seq(),Seq()).asMl//lpClause(Seq(), Seq(lpOlBot))
    val lastStep: LpTerm[Level.Meta] = proofSteps.last match {
      //case lpHave(name, `emptyClause`, _, _) => lpConstantTerm(name)
      case LpProofScript.Have(name,`emptyClause`,_) => LpTerm.Const(SymRef.LP(QName.local(name.value)))
      case LpProofScript.Have(name, flexFlex0, _) =>
        //throw new Exception(s"flex flex clause!")
        // transformation of flex-flex to bot necessary todo
        Out.lp_debug_info(s"Transformation of flex-flex literal to bot necessary...")
        val proofFun = LpType.Arrow(flexFlex0,LpType.Prf(LogicConst.Bot))//lpMlFunctionType(Seq(flexFlex0, lpOlBot.prf))
        val flexFlexStepName = "flexflex_to_bot"
        throw new Exception(s"flex flex clause!, ${flexFlex0}")
        LpTerm.Const(SymRef.LP(QName.local(name.value)))
        /*
        val (appliedflexFlexStepName, appliedStepName) = flexFlex0 match {
          case LpType.Pi(binders, body) =>
            val appliedVars = binders.map(bind => bind.ty match {
              case Some(LpType.El(olT)) => ND.Inst.lpWitness(olT)
              case _ => throw new Exception(s"encountered clause bindings with illegal format")
            }
          case lpClause(vars, lits) =>
            val appliedVars = vars.map(var0 => lpWitness(isTermVar(var0).ty))
            (lpFunctionApp(lpConstantTerm(flexFlexStepName), appliedVars), (lpFunctionApp(lpConstantTerm(name), appliedVars)))
          case _ => (lpConstantTerm(flexFlexStepName), lpConstantTerm(name))
        }
        //throw new Exception(s"vars are ${variablesToApply.map(_.pretty)}")
        val proofHave = lpHave(flexFlexStepName, proofFun, lpProofScript(Seq(lpProofScriptAdmit())))
        proofSteps = proofSteps :+ proofHave
        lpFunctionApp(appliedflexFlexStepName, Seq(appliedStepName))


         */



      case _ => throw new Exception(s"in the encoding, the last step had an unexptected tactic: ${proofSteps.last}")
    }
    //proofSteps = proofSteps :+ lpRefine(lpFunctionApp(lastStep, Seq.empty))
    proofSteps = proofSteps :+ LpProofScript.Refine(lastStep)
    //val completeProof = lpDefinition(lpConstantTerm("encodedProof"), Seq.empty, Some(conjecture.prf), lpProofScript(proofSteps), Seq(), Seq(lpOpaque))
    val prettyTy = Renderer.ty(LpType.Prf(conjecture),RenderOptions(),sig)
    Out.lp_debug_info(s"can encode conjecture: $prettyTy")
    /*
    proofSteps foreach{st =>
      val encSt = Renderer.proof(st,RenderOptions(true,true,true),sig)
      Out.lp_debug_info(s"can encode: \n$encSt")
    }
     */
    val completeProof = Stmt.Definition(Name("encodedProof"),Seq.empty,Some(LpType.Prf(conjecture)),Stmt.DefBody.ProofBody(proofSteps),Seq(),Seq(Opaque))
    proofFileSB.append(Renderer.stmt(completeProof,sig,RenderOptions(!outputSingleFile,!outputSingleFile,monomorphic)))

    (proofFileSB,signatureFileSB,formulaeFileSB)
  }

  def outputLPFiles(state: LocalState, lpOutputPath0: String, nameLpOutputFolder: String):Unit={

    val lpOutputPath = if (outputSingleFile) Paths.get(lpOutputPath0) else Paths.get(lpOutputPath0).resolve(nameLpOutputFolder)
    val (proofFileSB,signatureFileSB,formulaeFileSB) = extractNecessaryFormulas(state, false)

    val tempLibStr: String = if (customUserTacFile) s"${nameLpOutputFolder}.${nameTempFile}" else s"${nameLeoIIILPlib}.${leoSimpTacticFile}"


    // create a folder for the lambdapi package
    // Create the output directory if it doesn't exist
    if (!outputSingleFile){
      if (!Files.exists(lpOutputPath)) {
        Files.createDirectory(lpOutputPath)
        println(s"Folder '$nameLpOutputFolder' created.")
      } else {
        println(s"Folder '$nameLpOutputFolder' already exists, overwriting files.")
      }
    }

    // write the files
    Out.info("Writing the Lambdapi files")

    // todo: only require what we need
    lazy val reqList = Seq("Stdlib.Set","Stdlib.Prop","Stdlib.Classic","Stdlib.FOL","Stdlib.HOL","Stdlib.Eq","Stdlib.Impred","Stdlib.FunExt","Stdlib.PropExt","Stdlib.Nat","Stdlib.Bool","Stdlib.List","Stdlib.Epsilon","Stdlib.Disj","Stdlib.Conj",calcRuleLibStr,permLibStr)
    lazy val reqString = reqList.map(s => s"require open $s;\n").mkString("")
    var additions = ""
    val singleProof: mutable.StringBuilder = new StringBuilder()

    if (!outputSingleFile) {
      if (customUserTacFile){
        val tempFilePath = lpOutputPath.resolve(s"$nameTempFile.lp")
        val wholeTempLib = tempLibDeps + tempLib
        Files.write(tempFilePath, wholeTempLib.getBytes(StandardCharsets.UTF_8))
      }
    } //else singleProof.append(tempLib)
    additions = additions + s"require open $tempLibStr;\n"

    if (signatureFileSB.length != 0) {
      if (!outputSingleFile){
        val signatureFilePath = lpOutputPath.resolve(s"$nameSignatureFile.lp")
        signatureFileSB.insert(0, reqString)
        Files.write(signatureFilePath, signatureFileSB.toString.getBytes(StandardCharsets.UTF_8))
        additions = additions + s"require ${nameLpOutputFolder}.$nameSignatureFile as $abbreviationSignatureFileNoDot; \n"
      } else{
        singleProof.append(signatureFileSB)
      }
    }

    if (formulaeFileSB.length != 0){
      if (!outputSingleFile){
        val formulaeFilePath = lpOutputPath.resolve(s"$nameFormulaeFile.lp")
        formulaeFileSB.insert(0, reqString + additions + "\n\n")
        Files.write(formulaeFilePath, formulaeFileSB.toString.getBytes(StandardCharsets.UTF_8))
        additions = additions + s"require ${nameLpOutputFolder}.$nameFormulaeFile as $abbreviationFormulaeFileNoDot;\n"
      }
      singleProof.append(formulaeFileSB)
    }

    val proofFilePath = if (!outputSingleFile) lpOutputPath.resolve(s"$nameProofFile.lp") else lpOutputPath.resolve(s"$nameLpOutputFolder.lp")
    if (!outputSingleFile){
      proofFileSB.insert(0, reqString + additions + "\n\n") // maybe it may be necessary in some cases to add "\nnotation ∨ infix right 6;"
      Files.write(proofFilePath, proofFileSB.toString.getBytes(StandardCharsets.UTF_8))
    } else {
      val wholeProof = singleProof.append(proofFileSB)
      wholeProof.insert(0, reqString + additions + "\n\n") // maybe it may be necessary in some cases to add "\nnotation ∨ infix right 6;"
      Files.write(proofFilePath, wholeProof.toString.getBytes(StandardCharsets.UTF_8))
    }

    if (!outputSingleFile){
      // create the Makefile and the pkg file
      val pkgFileName = "lambdapi.pkg"
      createLambdapiFiles(lpOutputPath, nameLpOutputFolder, pkgFileName, nameProofFile)
    }
  }

  def proof2LP(state: LocalState):String = {
    val lpContextPlaceholder = "LAMBDAPI_CONTEXT"
    val reqString = s"require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt Stdlib.PropExt Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Epsilon $calcRuleLibStr $simpTacLibStr $permLibStr;\nrequire $lpContextPlaceholder.Signature as S;\nrequire $lpContextPlaceholder.Formulae as F \n\n;"
    val (proofFileSB,_,_) = extractNecessaryFormulas(state, true)
    proofFileSB.insert(0, reqString)
    val conjName = s"${state.conjecture.annotation.pretty.dropRight(1).split(",", 2)(1)}"
    val finalRule = lpRule(lpConstantTerm(s"$abbreviationFormulaeFile" + conjName), Seq.empty,lpConstantTerm(nameProofFile))
    proofFileSB.append("\n")
    proofFileSB.append(finalRule.pretty)
    proofFileSB.toString()
  }
}