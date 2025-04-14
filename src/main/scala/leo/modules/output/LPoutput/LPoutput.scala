package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.{ClauseProxy, Role_Axiom, Role_NegConjecture, Signature}
import leo.modules.output.{fusebVarListwithMap, makeBVarList}
import leo.modules.prover.LocalState
import leo.modules.{calculus, saturatedUserSignature, symbolsInProof, userSignature}
import leo.modules.output.LPoutput.Encodings._
import leo.modules.output.LPoutput.LPSignature.{cnfLib, lpDne}
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
  val calcRuleLibFile = "EPrules"
  val leoSimpTacticFile = "SimpTactic"
  val nameLeoIIILPlib = "Leo-III-lambdapi-lib"
  val nameProofFile = "encodedProof"

  val nameCnfFile = "cnfLib"

  val applyAllDefsTacName = "applyAllDefinitions"

  def step2LP(cl: ClauseProxy, parentInLpEncID: Seq[lpConstantTerm], sig: Signature, rule: calculus.CalculusRule, defRuleDefined: Boolean): (String, lpProofScript, Set[lpStatement], Option[String]) = {

    if (!Seq(leo.datastructures.Role_Conjecture).contains(cl.role)) {
      if (rule== null) ("Tautology", lpProofScript(Seq.empty), Set.empty, Some("Tautology generation not yet encoded"))
      else {
        rule match {

          case leo.modules.calculus.PolaritySwitch =>
            val encoding = encPolaritySwitch(cl, cl.annotation.parents.head, parentInLpEncID.head, sig) //¿polarity switch always only has one parent, right?
            ("PolaritySwitch", encoding._1, encoding._2, None)

          case leo.modules.calculus.FuncExt =>
            val encoding = encFuncExtPos(cl, cl.annotation.parents.head, cl.furtherInfo.edLitBeforeAfter, parentInLpEncID.head, sig)
            ("FuncExt", encoding._1, encoding._2, encoding._3)

          case leo.modules.calculus.BoolExt =>
            val encoding = encBoolExt(cl, cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.addInfoBoolExt, sig)
            ("BoolExt", encoding._1, encoding._2, encoding._3)

          case leo.modules.calculus.OrderedEqFac =>
            val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoEqFac, parentInLpEncID.head, sig)
            ("OrderedEqFac", encodings._1, encodings._2, None)

        case leo.modules.calculus.DefExpSimp =>
          //throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoDefExp}")
          // todo: eta expansion
          val (proofSteps, cantENcode) = EncDefExSimp(cl, cl.annotation.parents.head, defRuleDefined, cl.furtherInfo.rwUnderBinder, cl.furtherInfo.addInfoDefExp, applyAllDefsTacName, parentInLpEncID.head, sig)
          ("DefExpand", lpProofScript(proofSteps), Set(), cantENcode)


        case leo.modules.calculus.Simp =>
          if (cl.furtherInfo.addInfoSimpRule.isDefined) {
            if (cl.furtherInfo.addInfoSimpRule.get == "eqSimp"){
              if (cl.furtherInfo.rwUnderBinder) (s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Set.empty, Some("Simp: This instance can not be encoded yet as it requires RW under Binder"))
              else {
                val (allSteps, usedSymbols) = newSimpEncoding(cl.cl, cl.annotation.parents.head.cl, parentInLpEncID.head, sig)
                (s"FormulaSimp", lpProofScript(allSteps), usedSymbols, None)
              }
            }else{
              val annotation = Some(s"Simp: ${cl.furtherInfo.addInfoSimpRule.get} currently not encoded")
              (s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Set.empty, annotation)
            }
          }else{
            val annotation = Some("Simp: Unidentified formula simplification unencoded")
            (s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Set.empty, annotation)
          }
        /*
        case leo.modules.calculus.RenameCNF =>
            encRenameCnf(cl,cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.unencodableCNF, sig)
          ("RenameCNF", lpProofScript(Seq()), Set(), Some("not encoded"))
         */

        case leo.modules.calculus.PreUni =>
          val encodingPreUni = encPreUni(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoUni, cl.furtherInfo.addInfoUniRule, parentInLpEncID.head, sig)
          ("PreUni", encodingPreUni._1, encodingPreUni._2, encodingPreUni._3)

        case leo.modules.calculus.RewriteSimp =>
          val encodingRewrite = encRewrite(cl, cl.annotation.parents, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoRewriting, parentInLpEncID, sig)
          ("RewriteSimp", encodingRewrite._1, encodingRewrite._2, encodingRewrite._3)

        case leo.modules.calculus.LiftEq =>
          val encodingLiftEq = encLiftEq(cl, cl.annotation.parents, cl.furtherInfo.addInfoLiftEq, parentInLpEncID, sig)
          ("LiftEq", encodingLiftEq._1, encodingLiftEq._2, encodingLiftEq._3)
        case _ =>
          val parentIDs = parentInLpEncID.map(id => id.name)
          ("", lpProofScript(Seq.empty), Set.empty, Option(s"Unencoded rule ${rule.name} applied to ${parentIDs.mkString(", ")}"))
        }
      }
    } //todo: either introduce else or filter out conj before!
    else ("no role or conjecture?", lpProofScript(Seq.empty), Set.empty, Option("no role or conjecture?"))
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

  def outputLPFiles(state: LocalState, lpOutputPath0: String, nameLpOutputFolder: String):Unit={

    val lpOutputPath = Paths.get(lpOutputPath0).resolve(nameLpOutputFolder)

    val proofFileSB: mutable.StringBuilder = new StringBuilder()
    var proofSteps: Seq[lpProofScriptStep] = Seq.empty

    def extractNecessaryFormulas(state:LocalState):Unit={

      val sig = state.signature
      val proof = state.proof

      var tptpDefinedSymbols:Set[lpStatement] = Set.empty
      var definitions: Set[String] = Set.empty
      val typeDecSB: mutable.StringBuilder = new StringBuilder()
      val defSB: mutable.StringBuilder = new StringBuilder()

      // add symbols of the user defined TPTP problem signature if necessary
      val signatureSymbols = saturatedUserSignature(symbolsInProof(proof))(sig)
      signatureSymbols.foreach { key =>
      //val (relevantSymbols, additionalSymbols) = userSignature(symbolsInProof(proof))(sig)
      //(relevantSymbols union additionalSymbols).foreach {key =>
        val symbol = sig.apply(key)
        val sName = lpEscapeName(symbol.name,sig)

        if (symbol.hasKind) {
          //user defined types: add declarations to the problem
          //todo: what is saved as a kind? look at lines 96-99 in toTPTPscala again
          typeDecSB.append(lpDeclaration(lpConstantTerm(sName),Seq.empty,lpSet).pretty)
        }else{
          if (symbol.hasType) {
            val typeDec = type2LP(symbol._ty, sig)
            typeDecSB.append(lpDeclaration(lpConstantTerm(sName),Seq.empty,typeDec.lift2Meta).pretty)
          }

          if (symbol.hasDefn){// && (! additionalSymbols.contains(key))) {

            val (bVarTys, _) = collectLambdasLP(symbol._defn)
            val newBVars = makeBVarList(bVarTys,0)
            val (definition, tptpDefinedSymbols0) = term2LP(symbol._defn, fusebVarListwithMap(newBVars, Map()), sig)
            tptpDefinedSymbols = tptpDefinedSymbols ++ tptpDefinedSymbols0

            val defTermType = type2LP(symbol._defn.ty, sig)
            val defAsEq = lpOlTypedBinaryConnectiveTerm(lpEq, defTermType, lpOlFunctionApp(lpOlConstantTerm(sName), Seq.empty), definition)
            val encodedDef = lpDeclaration(lpConstantTerm(s"${sName}_def"), Seq.empty, defAsEq.prf)
            //Out.lp_debug_info(s"${symbol._defn.pretty}")
            //Out.lp_debug_info(s"${encodedDef.pretty}")
            defSB.append(encodedDef.pretty)

            // furthermore, we need to build a tactic that combines all of our definitions into one
            definitions += s"${sName}_def"
          }
        }
      }

      if (definitions.nonEmpty){
        // define a tactic rewriting with all of the definitions
        val allDefsListName = "allDefinitions"
        val decAllDefs = lpDefinition(lpConstantTerm(allDefsListName), Seq(), None, lpList(definitions.map(defName => lpRewrite(None, lpOlConstantTerm(defName)).olTermApp).toSeq))
        val applyAllDefsTact = lpDefinition(lpConstantTerm(applyAllDefsTacName), Seq(), None, lpRepeat(applyAnyStep(lpOlConstantTerm(allDefsListName))).olTermApp)
        //lpRepeat(lpOlConstantTerm(allDefsListName)).olTermApp
        defSB.append("\n")
        defSB.append(decAllDefs.pretty)
        defSB.append(applyAllDefsTact.pretty)
      }

      val objectDecSB = typeDecSB.append(defSB)


      // encode the clauses representing the steps
      // todo: Also make it possible to just output one long lambda-term
        val compressedProof = proof
        var idClauseMap: mutable.HashMap[Long,ClauseProxy] = mutable.HashMap.empty
        val identicalSteps: mutable.HashMap[Long,lpConstantTerm] = mutable.HashMap.empty
        var conjEnc = false
        var axCounter = 0
        val conjName = lpConstantTerm(s"negatedConjecture")

      val problemEncSB: mutable.StringBuilder = new StringBuilder()

        var conjecture : lpOlTerm = lpOlNothing

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
          } else if (step.role == Role_Axiom){ //todo: what about other roles like lamme etc. ?
            val (encClause, tptpDefinedSymbols0) = clause2LP(step.cl, Set(), sig)
            tptpDefinedSymbols = tptpDefinedSymbols ++ tptpDefinedSymbols0
            val axName = lpConstantTerm(s"axiom$axCounter")
            problemEncSB.append(lpDeclaration(axName, Seq.empty, encClause).pretty)
            identicalSteps += (stepId -> axName)
            axCounter = axCounter + 1
          }else {

            val (encStep, tptpDefinedSymbols0) = clause2LP(step.cl, Set(), sig)
            tptpDefinedSymbols = tptpDefinedSymbols ++ tptpDefinedSymbols0

            var encodeStep = false

            step.annotation.parents foreach {parent =>
              if (!Seq().contains(parent.role)) {
                val encParent = clause2LP(parent.cl, Set.empty, sig)._1
                if (encParent == encStep) {
                  if (identicalSteps.contains(stepId)) {
                    if (identicalSteps(stepId) != nameStep(parent.id.toInt)) {
                      throw new Exception(s"step $stepId ($encStep) is equivalent to two parents: ${step.id}, ${parent.id} ")
                    }
                  }
                  if (identicalSteps.contains(parent.id)) {
                    // in this case we already have the parent as a key and want to map the new child to the parents parent
                    val exVal = identicalSteps(parent.id)
                    identicalSteps.update(stepId, exVal)
                  } else {
                    // in this case we just want to link the child to the parent
                    val exVal = nameStep(parent.id.toInt)
                    identicalSteps.update(stepId, exVal)
                  }
                } else encodeStep = true
              }
            }
            // embed the proof step
            if (encodeStep == true) {

              // construct a proof

              // since we do not write out steps that are identical in our encoding, we keep track of what the reference to the parent clause in LP is
              val parentInLpEncID = step.annotation.parents.map(parent => identicalSteps.getOrElse(parent.id, nameStep(parent.id.toInt)))
              //print(s"encoding Rule ${step.annotation.fromRule} for step ${nameStep(step.id.toInt).name} from parents ${parentInLpEncID.map(s => s.pretty)}\n")
              val stepName = nameStep(step.id.toInt).name
              val rule = step.annotation.fromRule
              Out.lp_debug_info(s"Encoding step $stepName: application of caluclus rule ${if (rule==null) "Tautology" else rule.name}")
              Out.lp_debug_info(s"The parents are ${parentInLpEncID.map(term => term.pretty).mkString(", ")}")
              val (ruleName,proofTerm, updatedUsedSymbols, notEncoded) = step2LP(step, parentInLpEncID, sig, rule, definitions.nonEmpty)

              // if the step is actually new, we want to add it to the output
              if (notEncoded.isDefined) {
                // add substeps for which the encoding is not implemented using the "admit" tactic
                // todo: encode these rules! :)
                Out.lp_debug_info(s"Not encoded yet (${notEncoded.get})\n")
                proofSteps = proofSteps :+ lpProofScriptCommentLine(notEncoded.get)
                proofSteps = proofSteps :+ lpHave(stepName, encStep, lpProofScript(Seq(lpProofScriptAdmit())))
              } else {
                Out.lp_debug_info(s"Encoding finished!\n")
                // add the encoded proofs to the overall proof as substeps
                proofSteps = proofSteps :+ lpProofScriptCommentLine(ruleName)
                proofSteps = proofSteps :+ lpHave(stepName,encStep,proofTerm)
                // and add the necessary symbols to the generated Signature
              }
            }
          }
      }

      // Generate declarations of symbols that are implicit in TPTP but not mapped to a Lambdapi encoding
      if (tptpDefinedSymbols.nonEmpty){
        var declareInts = false
        val tptpSymbolsSB: mutable.StringBuilder = new StringBuilder()
        tptpDefinedSymbols foreach {tptpSymbol =>
          tptpSymbol match {
          case lpInt(_) =>
              declareInts = true
              val intDec = lpDeclaration(tptpSymbol,Seq(),lpIntType.lift2Meta)
              tptpSymbolsSB.append(intDec.pretty)
          case lpTptpOperator(name,ty,vars) =>
              tptpSymbolsSB.append(lpTptpOperator(name,ty,vars).dec.pretty)
          case _ => Out.lp_debug_info(s"LP-Encoding: Found TPTP defined symbol ${tptpSymbol.pretty}")
        }
        }
        if (declareInts) {
          val intDec = lpDeclaration(lpIntType,Seq(),lpSet)
          Out.lp_debug_info(s"need to define ints: ${intDec.pretty}")
          tptpSymbolsSB.insert(0,intDec.pretty)
        }
        proofFileSB.append("// TPTP SYMBOL ENCODINGS /////////////////////////////////\n\n")
        proofFileSB.append(tptpSymbolsSB)
      }
      if (objectDecSB.length != 0) {
        proofFileSB.append("\n\n// OBJECT DECLARATIONS ///////////////////////////////////\n\n")
        proofFileSB.append(objectDecSB)
      }

      if (problemEncSB.length != 0) {
        proofFileSB.append("\n\n// PROBLEM ENCODING //////////////////////////////////////\n\n")
        proofFileSB.append(problemEncSB)
      }
      Out.info("Done enocoding the inference rules")

      proofFileSB.append("\n\n// PROOF ENCODING ////////////////////////////////////////\n\n")

      // construct the proof based on all the individual steps
      // in the proof of the conjecture, first instanciate dne, then assume the negated conjecture
      proofSteps =  lpAssume(Seq(conjName)) +: proofSteps
      proofSteps =  lpRefine(lpFunctionApp(lpDne.name,Seq(conjecture, lpWildcard))) +: proofSteps
      // finally, test if the derived last clause is the empty clause or a flex-flex clause.
      // Instanciate with the empty clause or introduce an additional step in case of a flex-flex clause
      val emptyClause = lpClause(Seq(),Seq(lpOlBot))
      val lastStep = proofSteps.last match {
        case lpHave(name, `emptyClause`,_,_) => lpConstantTerm(name)
        case lpHave(name, flexFlex0,_,_) =>
          // transformation of flex-flex to bot necessary todo
          Out.lp_debug_info(s"Transformation of flex-flex literal to bot necessary...")
          val proofFun = lpMlFunctionType(Seq(flexFlex0,lpOlBot.prf))
          val flexFlexStepName = "flexflex_to_bot"
          val (appliedflexFlexStepName, appliedStepName) = flexFlex0 match {
            case lpClause(vars,lits) =>
              val appliedVars = vars.map(var0 => lpWitness(isTermVar(var0).ty))
              (lpFunctionApp(lpConstantTerm(flexFlexStepName),appliedVars),(lpFunctionApp(lpConstantTerm(name),appliedVars)))
            case _ => (lpConstantTerm(flexFlexStepName), lpConstantTerm(name))
          }
          //throw new Exception(s"vars are ${variablesToApply.map(_.pretty)}")
          val proofHave = lpHave(flexFlexStepName,proofFun,lpProofScript(Seq(lpProofScriptAdmit())))
          proofSteps = proofSteps :+ proofHave
          lpFunctionApp(appliedflexFlexStepName,Seq(appliedStepName))
        case _ => throw new Exception(s"in the encoding, the last step had an unexptected tactic: ${proofSteps.last.pretty}")
      }
      proofSteps = proofSteps :+ lpRefine(lpFunctionApp(lastStep,Seq.empty))
      val completeProof = lpDefinition(lpConstantTerm("encodedProof"),Seq.empty,Some(conjecture.prf),lpProofScript(proofSteps),Seq(),Seq(lpOpaque))
      proofFileSB.append(completeProof.pretty)

      val permLibStr: String = f"${nameLeoIIILPlib}.${permlibFile}"
      val simpTacLibStr = f"${nameLeoIIILPlib}.${leoSimpTacticFile}"
      val calcRuleLibStr = f"${nameLeoIIILPlib}.${calcRuleLibFile}"
      val cnfLibStr: String = f"${nameLpOutputFolder}.${nameCnfFile}"

      proofFileSB.insert(0,s"require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt Stdlib.PropExt Stdlib.Nat Stdlib.Bool Stdlib.List Stdlib.Epsilon $calcRuleLibStr $simpTacLibStr $permLibStr $cnfLibStr;\n\n") // maybe it may be necessary in some cases to add "\nnotation ∨ infix right 6;"

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

      val proofFilePath = lpOutputPath.resolve(s"$nameProofFile.lp")
      Files.write(proofFilePath, proofFileSB.toString.getBytes(StandardCharsets.UTF_8))

      nameCnfFile

      val cnfFilePath = lpOutputPath.resolve(s"$nameCnfFile.lp")
      Files.write(cnfFilePath, cnfLib.getBytes(StandardCharsets.UTF_8))

      // create the Makefile and the pkg file
      val pkgFileName = "lambdapi.pkg"
      createLambdapiFiles(lpOutputPath, nameLpOutputFolder, pkgFileName, nameProofFile)

    }
    extractNecessaryFormulas(state)
  }
}
