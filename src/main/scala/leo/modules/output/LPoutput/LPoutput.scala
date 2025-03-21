package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.{ClauseProxy, Role_Axiom, Role_NegConjecture, Signature}
import leo.modules.output.{fusebVarListwithMap, makeBVarList}
import leo.modules.prover.LocalState
import leo.modules.{calculus, symbolsInProof, userSignature}
import leo.modules.output.LPoutput.Encodings._
import leo.modules.output.LPoutput.LPSignature.{calcRuleLib, leoSimpTactic, lpDne, newPropExtLib, permLib}
import leo.modules.output.LPoutput.lpDatastructures.{lpSimpRuleVersion, _}
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

  val nameLogicFile = "extt"
  val permlibFile = "permuteLib"
  val simplibFile = "simpLib"
  val calcRuleLibFile = "calcRuleLib"
  val propLibFile = "newPropExtLib"
  val leoSimpTacticFile = "simpTactic"
  val nameRulesFile = "rules"
  val nameProofFile = "encodedProof"

  var inclduePermLib = false
  var incldueSimpLib = true

  def generateSignature(usedSymbols: Set[lpStatement], nameLpOutputFolder: String): (mutable.StringBuilder) = {

    val rulesFileSB: mutable.StringBuilder = new StringBuilder()
    // todo: once lambdapi is fixed, remove the declaration here
    rulesFileSB.append(s"require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Nat Stdlib.Bool ${nameLpOutputFolder}.$nameLogicFile;\n\n") // maybe it will be necessary for now to add \nnotation ∨ infix right 6;

    //var simplificationRules: Set[SimplificationEncoding.simplificationRules] = Set.empty
    var otherRules: Set[lpDefinedRules] = Set.empty
    var infRules: Set[lpInferenceRuleEncoding.inferenceRules] = Set.empty
    var infRulesRWfree: Set[lpInferenceRuleEncoding.inferenceRules] = Set.empty

    // sort the symbols
    usedSymbols foreach { symbol =>
      symbol match {
        //case basicRule: lpBasicRules =>
        //  basicRules = basicRules + basicRule
        case simpRule: SimplificationEncoding.simplificationRules =>
          //simplificationRules = simplificationRules + simpRule
          incldueSimpLib = true
        case simpRule: lpSimpRuleVersion =>
          incldueSimpLib = true
        case infRule: lpInferenceRuleEncoding.inferenceRules =>
          /*
          Out.lp_debug_info(s"used rule: $infRule")
          if (infRule == metaPermutation) {
            Out.lp_debug_info(s"Permutation-Lib is needed")
            inclduePermLib = true
          }
          else if (infRule.proofRWfree) infRulesRWfree = infRulesRWfree + infRule
          else infRules = infRules + infRule
           */

        case defRule: lpDefinedRules =>
          otherRules = otherRules + defRule
        case _ =>
        // do nothing
      }
    }

    // now print the symbols
    val output: mutable.StringBuilder = new StringBuilder()
    val correctnessSb: mutable.StringBuilder = new StringBuilder()
    output.append("//SIGNATURE\n\n\n\n")

    // add simplification rules
    /*
    if (simplificationRules.nonEmpty) output.append("////// Simplification Rules \n\n")
    simplificationRules foreach { simpRrule =>
      rulesFileSB.append(simpRrule.pretty)
      rulesFileSB.append("\n")
    }
     */

    // add inference rules, todo: in some cases trigger the dynamic generation of rules here
    if (infRules.nonEmpty) output.append("////// Inference Rules with RW rules \n\n")
    infRules foreach { infRrule =>
      if (infRrule.proofIsDefined) rulesFileSB.append(infRrule.pretty)
      else rulesFileSB.append(infRrule.dec.pretty)
      rulesFileSB.append("\n")
    }

    // add inference rules, todo: in some cases trigger the dynamic generation of rules here
    if (infRulesRWfree.nonEmpty) output.append("////// Inference Rules \n\n")
    infRulesRWfree foreach { infRrule =>
      if (infRrule.proofIsDefined) rulesFileSB.append(infRrule.pretty)
      else rulesFileSB.append(infRrule.dec.pretty)
      rulesFileSB.append("\n")
    }

    // add other Rules
    if (otherRules.nonEmpty) rulesFileSB.append("////// Other Rules \n\n")
    otherRules foreach { otherRule =>
      rulesFileSB.append(otherRule.pretty)
      rulesFileSB.append("\n")
    }

    (rulesFileSB)
  }

  def step2LP(cl: ClauseProxy, idClauseMap: mutable.HashMap[Long, ClauseProxy], parentInLpEncID: Seq[lpConstantTerm], sig: Signature, parameters0: (Int, Int, Int, Int), rule: calculus.CalculusRule): (String, lpProofScript, Set[lpStatement], Option[String]) = {

    val skripts = true

    val continuousNumbers = true

    val parameters = if (continuousNumbers) parameters0 else (0, 0, 0, 0)

    if (!Seq(leo.datastructures.Role_Conjecture).contains(cl.role)) { // we start our proof with the negated conjecture
      if (rule== null) ("Tautology", lpProofScript(Seq.empty), Set.empty, Some("Tautology generation not yet encoded"))
      else {
        rule match {
          case leo.modules.calculus.PolaritySwitch =>
            //todo: dont forget to map to the correct formula! make special case for negated conjecture
            //val encoding = encPolaritySwitchClause(cl, cl.annotation.parents.head,parentInLpEncID.head,sig,parameters) //¿polarity switch always only has one parent, right?
            //encoding
            val encoding = encPolaritySwitch(cl, cl.annotation.parents.head, parentInLpEncID.head, sig) //¿polarity switch always only has one parent, right?
            ("PolaritySwitch", encoding._1, encoding._2, None)

          case leo.modules.calculus.FuncExt =>
            val encoding = encFuncExtPos(cl, cl.annotation.parents.head, cl.furtherInfo.edLitBeforeAfter, parentInLpEncID.head, sig)
            ("FuncExt", encoding._1, encoding._2, encoding._3)

          case leo.modules.calculus.BoolExt =>
            val encoding = encBoolExt(cl, cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.addInfoBoolExt, sig)
            ("BoolExt", encoding._1, encoding._2, encoding._3)

          case leo.modules.calculus.OrderedEqFac =>
            //val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head,cl.furtherInfo.addInfoEqFac,parentInLpEncID.head,sig)
            //(encodings._1,(0,0,0,0),encodings._2)
            val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoEqFac, parentInLpEncID.head, sig)
            ("OrderedEqFac", encodings._1, encodings._2, None)

          /*
        case leo.modules.calculus.DefExpSimp =>
          //throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoDefExp}")
          // todo: eta expansion
          val encodingsSimp = encDefExSimp(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoDefExp, parentInLpEncID.head, sig)
          print(s"RESPULT: ${encodingsSimp._4}\n\n")
          ("DexExpand", encodingsSimp._1, encodingsSimp._2, encodingsSimp._4)
         */

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

          case leo.modules.calculus.PreUni =>
            val encodingPreUni = encPreUni(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoUni, cl.furtherInfo.addInfoUniRule, parentInLpEncID.head, sig)
            ("PreUni", encodingPreUni._1, encodingPreUni._2, encodingPreUni._3)
          //throw new Exception(s"${cl.furtherInfo.addInfoUni}")

          case leo.modules.calculus.RewriteSimp =>
            //throw new Exception(s"add info rewriting: ${cl.furtherInfo.addInfoRewriting}")
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

    val lpOutputPath = Paths.get(lpOutputPath0).resolve(nameLpOutputFolder)//s"${lpOutputPath0}${nameLpOutputFolder}/"

    val proofFileSB: mutable.StringBuilder = new StringBuilder()
    var proofSteps: Seq[lpProofScriptStep] = Seq.empty

    def extractNecessaryFormulas(state:LocalState):Unit={

      val sig = state.signature
      val proof = state.proof

      var usedSymbols: Set[lpStatement] = Set.empty // always add them because they are necessary for equality tactics. Todo: handle differently
      var tptpDefinedSymbols:Set[lpStatement] = Set.empty // always add them because they are necessary for equality tactics. Todo: handle differently
      var parameters: (Int,Int,Int,Int) = (0,0,0,0)

      // add symbols of the user defined TPTP problem signature if necessary

      val (relevantSymbols, additionalSymbols) = userSignature(symbolsInProof(proof))(sig)

      val typeDecSB: mutable.StringBuilder = new StringBuilder()
      val defSB: mutable.StringBuilder = new StringBuilder()

      (relevantSymbols union additionalSymbols).foreach {key =>
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

          if (symbol.hasDefn && (! additionalSymbols.contains(key))) {

            //val encAsRewriteRule = false

            val (bVarTys, _) = collectLambdasLP(symbol._defn)
            val newBVars = makeBVarList(bVarTys,0)
            val (definition, tptpDefinedSymbols0) = term2LP(symbol._defn, fusebVarListwithMap(newBVars, Map()), sig)
            tptpDefinedSymbols = tptpDefinedSymbols ++ tptpDefinedSymbols0

            val defTermType = type2LP(symbol._defn.ty, sig)
            val defAsEq = lpOlTypedBinaryConnectiveTerm(lpEq, defTermType, lpOlFunctionApp(lpOlConstantTerm(sName), Seq.empty), definition)
            val encodedDef = lpDeclaration(lpConstantTerm(s"${sName}_def"), Seq.empty, defAsEq.prf)
            Out.lp_debug_info(s"${symbol._defn.pretty}")
            Out.lp_debug_info(s"${encodedDef.pretty}")
            defSB.append(encodedDef.pretty)
          }
        }
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
            //print(s" symbols in negated conjecture: ${symbols(step.cl).map(sig.apply(_).name)}\n")
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
              if (!Seq().contains(parent.role)) { //Role_NegConjecture Role_Conjecture
                val encParent = clause2LP(parent.cl, usedSymbols, sig)._1
                if (encParent == encStep) {
                  val existingValue: lpConstantTerm = {
                    if (identicalSteps.contains(stepId)) {
                      if (identicalSteps(stepId) != nameStep(parent.id.toInt)) {
                        throw new Exception(s"step $stepId ($encStep) is equivalent to two parents: ${step.id}, ${parent.id} ")
                      }
                    }
                    if (identicalSteps.contains(parent.id)) {
                      // in this case we already have the parent as a key and want to map the new child to the parents parent
                      val exVal = identicalSteps(parent.id)
                      identicalSteps.update(stepId, exVal)
                      exVal
                    } else {
                      // in this case we just want to link the child to the parent
                      val exVal = nameStep(parent.id.toInt)
                      identicalSteps.update(stepId, exVal)
                      exVal
                    }
                  }
                } else encodeStep = true
              }
            }
            // embed the proof step
            if (encodeStep == true) {

              // try to construct a proof

              // since we do not write out steps that are identical in our encoding, we keep track of what the reference to the parent clause in LP is
              val parentInLpEncID = step.annotation.parents.map(parent => identicalSteps.getOrElse(parent.id, nameStep(parent.id.toInt)))
              //print(s"encoding Rule ${step.annotation.fromRule} for step ${nameStep(step.id.toInt).name} from parents ${parentInLpEncID.map(s => s.pretty)}\n")
              val stepName = nameStep(step.id.toInt).name
              val rule = step.annotation.fromRule
              Out.lp_debug_info(s"Encoding step $stepName: application of caluclus rule ${if (rule==null) "Tautology" else rule.name}")
              Out.lp_debug_info(s"The parents are ${parentInLpEncID.map(term => term.pretty).mkString(", ")}")
              val (ruleName,proofTerm, updatedUsedSymbols, notEncoded) = step2LP(step, idClauseMap, parentInLpEncID, sig, parameters, rule)

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
                usedSymbols = usedSymbols ++ updatedUsedSymbols
              }
            }
          }
      }

      // Generate declarations of symbols that are implicit in TPTP but not mapped to a Lambdapi encoding
      if (tptpDefinedSymbols.nonEmpty){
        var declareInts = false
        var tptpSymbolsSB: mutable.StringBuilder = new StringBuilder()
        tptpDefinedSymbols foreach {tptpSymbol =>
          tptpSymbol match {
          case lpInt(n) =>
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
      val completeProof = lpDefinition(lpConstantTerm("encodedProof"),Seq.empty,Some(conjecture.prf),lpProofScript(proofSteps))
      proofFileSB.append(completeProof.pretty)

      // generate the signature

      Out.lp_debug_info("Generating Signature")
      val rulesFileSB = generateSignature(usedSymbols, nameLpOutputFolder)

      val permLibStr: String = f"${nameLpOutputFolder}.${permlibFile}"
      //val simpLibStr: String = f"${nameLpOutputFolder}.${simplibFile}"
      val propLibStr = f"${nameLpOutputFolder}.${propLibFile}"
      val simpTacLibStr = f"${nameLpOutputFolder}.${leoSimpTacticFile}"
      val calcRuleLibStr = f"${nameLpOutputFolder}.${calcRuleLibFile}"

      proofFileSB.insert(0,s"require open Stdlib.Set Stdlib.Prop Stdlib.Classic Stdlib.FOL Stdlib.HOL Stdlib.Eq Stdlib.Impred Stdlib.FunExt Stdlib.Nat Stdlib.Bool Stdlib.List $propLibStr $calcRuleLibStr $simpTacLibStr $permLibStr;\n\n") // maybe it may be necessary in some cases to add "\nnotation ∨ infix right 6;"


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

      //val exttFilePath = lpOutputPath.resolve(s"$nameLogicFile.lp")
      //Files.write(exttFilePath, ExTTenc.getBytes(StandardCharsets.UTF_8))

      val permLibFilePath = lpOutputPath.resolve(s"$permlibFile.lp")
      Files.write(permLibFilePath, permLib.getBytes(StandardCharsets.UTF_8))

      // propLibFile leoSimpTacticFile
      //val simpLibFilePath = lpOutputPath.resolve(s"$simplibFile.lp")
      //val completeSimpLibFile = s"require open Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.Impred Stdlib.FOL Stdlib.Bool Stdlib.List ${nameLpOutputFolder}.$nameLogicFile;\n\n"
      //if (incldueSimpLib) Files.write(simpLibFilePath, (completeSimpLibFile + simpLib).getBytes(StandardCharsets.UTF_8))

      val propLibFilePath = lpOutputPath.resolve(s"$propLibFile.lp")
      Files.write(propLibFilePath, newPropExtLib.getBytes(StandardCharsets.UTF_8))

      // calcRuleLibFile
      val calcRuleLibFilePath = lpOutputPath.resolve(s"$calcRuleLibFile.lp")
      val reqcalcRuleLibFile = s"require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Classic Stdlib.Bool Stdlib.List Stdlib.HOL Stdlib.Impred ${nameLpOutputFolder}.$propLibFile;\n\n"
      Files.write(calcRuleLibFilePath, (reqcalcRuleLibFile + calcRuleLib).getBytes(StandardCharsets.UTF_8))

      val simpTacticLibFilePath = lpOutputPath.resolve(s"$leoSimpTacticFile.lp")
      val reqSimpTacticLibFile = s"require open Stdlib.Set Stdlib.Prop Stdlib.Eq Stdlib.Impred Stdlib.Classic Stdlib.FOL Stdlib.List ${nameLpOutputFolder}.$propLibFile;\n\n"
      Files.write(simpTacticLibFilePath, (reqSimpTacticLibFile + leoSimpTactic).getBytes(StandardCharsets.UTF_8))

      //val rulesFilePath = lpOutputPath.resolve(s"$nameRulesFile.lp")
      //Files.write(rulesFilePath, rulesFileSB.toString.getBytes(StandardCharsets.UTF_8))

      val proofFilePath = lpOutputPath.resolve(s"$nameProofFile.lp")
      Files.write(proofFilePath, proofFileSB.toString.getBytes(StandardCharsets.UTF_8))

      // create the Makefile and the pkg file
      val pkgFileName = "lambdapi.pkg"
      createLambdapiFiles(lpOutputPath, nameLpOutputFolder, pkgFileName, nameProofFile)

      /*
      if (lpInitSuccess) {
        val commandCheck = Seq("/bin/sh", "-c", s"cd $lpOutputPath0 && make && lambdapi check ${nameProofFile}.lp")

        val checkLpFiles = commandCheck.!

        if (checkLpFiles == 1) {
          println(s"\nFailed to check Lambdapi files (exit code $initLP).")
          lpInitSuccess = false
          Files.createDirectories(Paths.get(lpOutputPath))
        }
      }
       */
    }
    extractNecessaryFormulas(state)
  }
}
