package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures.Clause.symbols
import leo.datastructures.Literal.asTerm
import leo.datastructures.{ClauseProxy, Literal, Role_Axiom, Role_NegConjecture, Signature}
import leo.modules.output.{fusebVarListwithMap, makeBVarList}
import leo.modules.prover.LocalState
import leo.modules.{calculus, symbolsInProof, userSignature}
import leo.modules.output.LPoutput.Encodings._
import leo.modules.output.LPoutput.LPSignature.{ExTTenc, RwRenc, lpNpp, permLib}
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.ModularProofEncoding._

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import scala.collection.mutable
import scala.sys.process._
import scala.util.{Failure, Success, Try}

/**
  * Generation of the various files making up the Lambdapi encoding
  *
  * @author Melanie Taprogge
  */

object LPoutput {

  val nameLogicFile = "extt"
  val permlibFile = "permuteLib"
  val nameRulesFile = "rules"
  val nameProofFile = "encodedProof"

  var inclduePermLib = true

  def generateSignature(usedSymbols: Set[lpStatement], nameLpOutputFolder: String): (mutable.StringBuilder) = {

    val rulesFileSB: mutable.StringBuilder = new StringBuilder()
    // todo: once lambdapi is fixed, remove the declaration here
    rulesFileSB.append(s"require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Nat Stdlib.Bool ${nameLpOutputFolder}.$nameLogicFile;\nnotation ∨ infix right 6;\n\n") // maybe it will be necessary for now to add \nnotation ∨ infix right 6;

    var simplificationRules: Set[SimplificationEncoding.simplificationRules] = Set.empty
    var otherRules: Set[lpDefinedRules] = Set.empty
    var infRules: Set[lpInferenceRuleEncoding.inferenceRules] = Set.empty
    var infRulesRWfree: Set[lpInferenceRuleEncoding.inferenceRules] = Set.empty

    // sort the symbols
    usedSymbols foreach { symbol =>
      symbol match {
        //case basicRule: lpBasicRules =>
        //  basicRules = basicRules + basicRule
        case simpRule: SimplificationEncoding.simplificationRules =>
          simplificationRules = simplificationRules + simpRule
        case infRule: lpInferenceRuleEncoding.inferenceRules =>
          if (infRule.proofRWfree) infRulesRWfree = infRulesRWfree + infRule
          else infRules = infRules + infRule
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
    if (simplificationRules.nonEmpty) output.append("////// Simplification Rules \n\n")
    simplificationRules foreach { simpRrule =>
      rulesFileSB.append(simpRrule.pretty)
      rulesFileSB.append("\n")
    }

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
          //throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoSimp}")
          // todo: eta expansion
          //val encodingsSimp = encDefExSimp(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoDefExp, parentInLpEncID.head, sig)
          //("?", encodingsSimp._1, (0, 0, 0, 0), encodingsSimp._2)
          (s"Rule ${rule.name} not encoded yet", lpProofScript(Seq.empty), Set.empty, Option("Formula simplification not encoded yet"))

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
          ("", lpProofScript(Seq.empty), Set.empty, Option(s"Rule ${rule.name} not encoded yet, parents are: ${parentIDs.mkString(", ")}"))
      }
    } //todo: either introduce else or filter out conj before!
    else ("no role or conjecture?", lpProofScript(Seq.empty), Set.empty, Option("no role or conjecture?"))
  }


  def outputLPFiles(state: LocalState, lpOutputPath0: String, nameLpOutputFolder: String):Unit={

    val lpOutputPath = s"${lpOutputPath0}${nameLpOutputFolder}/"

    val proofFileSB: mutable.StringBuilder = new StringBuilder()
    val permLibStr: String ={
      if (inclduePermLib) f"${nameLpOutputFolder}.${permlibFile}"
      else ""
    }
    proofFileSB.append(s"require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Impred Stdlib.Nat Stdlib.Bool Stdlib.List ${nameLpOutputFolder}.$nameLogicFile ${nameLpOutputFolder}.${nameRulesFile} $permLibStr;\nnotation ∨ infix right 6;\nsymbol el a : τ a;\n\n") // maybe it may be necessary in some cases to add "\nnotation ∨ infix right 6;"
    var proofSteps: Seq[lpProofScriptStep] = Seq.empty

    def extractNecessaryFormulas(state:LocalState):Unit={

      val sig = state.signature
      val proof = state.proof

      var usedSymbols:Set[lpStatement] = Set.empty // always add them because they are necessary for equality tactics. Todo: handle differently
      var parameters: (Int,Int,Int,Int) = (0,0,0,0)

      proofFileSB.append("// OBJECT DECLARATIONS ///////////////////////////////////\n\n")

      // add symbols of the user defined TPTP problem signature if necessary

      val (relevantSymbols, additionalSymbols) = userSignature(symbolsInProof(proof))(sig)

      Out.lp_debug_info(s"additional symbols: ${additionalSymbols.map(sig.apply(_).name)}")
      Out.lp_debug_info(s"relevant symbols: ${relevantSymbols.map(sig.apply(_).name)}")

      val typeDecSB: mutable.StringBuilder = new StringBuilder()
      val defSB: mutable.StringBuilder = new StringBuilder()

      (relevantSymbols union additionalSymbols).foreach {key =>
        val symbol = sig.apply(key)
        val sName = lpEscapeName(symbol.name,sig)

        if (symbol.hasKind) {
          //user defined types: add declarations to the problem
          //todo: what is saved as a kind? look at lines 96-99 in toTPTPscala again
          typeDecSB.append(lpDeclaration(lpConstantTerm(sName),Seq.empty,lpSet).pretty)
          usedSymbols = usedSymbols + lpSet

        }else{
          if (symbol.hasType) {
            val (typeDec, updatedUsedSymbols) = type2LP(symbol._ty, sig, usedSymbols)
            usedSymbols = updatedUsedSymbols
            typeDecSB.append(lpDeclaration(lpConstantTerm(sName),Seq.empty,typeDec.lift2Meta).pretty)
          }

          if (symbol.hasDefn && (! additionalSymbols.contains(key))) {

            val encAsRewriteRule = false

            val (bVarTys, body) = collectLambdasLP(symbol._defn)
            val newBVars = makeBVarList(bVarTys,0)
            val (definition, _) = term2LP(symbol._defn, fusebVarListwithMap(newBVars, Map()), sig)

            /*
            val (definition, updatedUsedSymbols,boundVars) = def2LP(symbol._defn, sig, usedSymbols, encAsRewriteRule)
            usedSymbols = updatedUsedSymbols
            var variables: Seq[lpOlUntypedVar] = Seq.empty
            boundVars foreach { v_t =>
              variables = variables :+ lpOlUntypedVar(lpOlConstantTerm(v_t._1))
              // todo: for poylmorphic types this might have to be extended
              //if (encAsRewriteRule) variables = variables :+ lpRuleVariable(lpOlConstantTerm(v_t._1))
              //else variables = variables :+ lpOlUntypedVar(lpOlConstantTerm(v_t._1))
            }
            val encodedDef = {
              if (encAsRewriteRule) {
                lpRule(lpOlConstantTerm(sName),variables,definition)
              } else {
                val defTermType = type2LP(symbol._defn.ty,sig)._1
                val defAsEq = lpOlTypedBinaryConnectiveTerm(lpEq,defTermType,lpOlFunctionApp(lpOlConstantTerm(sName),variables.map(Left(_))),definition)
                lpDeclaration(lpConstantTerm(s"${sName}_def"),variables,defAsEq.prf)
              }
             */

            val defTermType = type2LP(symbol._defn.ty, sig)._1
            val defAsEq = lpOlTypedBinaryConnectiveTerm(lpEq, defTermType, lpOlFunctionApp(lpOlConstantTerm(sName), Seq.empty), definition)
            val encodedDef = lpDeclaration(lpConstantTerm(s"${sName}_def"), Seq.empty, defAsEq.prf)
            Out.lp_debug_info(s"${encodedDef.pretty}")
            defSB.append(encodedDef.pretty)
          }
        }
      }
      proofFileSB.append(typeDecSB).append(defSB)

      // encode the clauses representing the steps
      // todo: Also make it possible to just output one long lambda-term
        val compressedProof = proof
        var idClauseMap: mutable.HashMap[Long,ClauseProxy] = mutable.HashMap.empty
        val identicalSteps: mutable.HashMap[Long,lpConstantTerm] = mutable.HashMap.empty
        var conjEnc = false
        var axCounter = 0
        val conjName = lpConstantTerm(s"negatedConjecture")

      proofFileSB.append("\n\n// PROBLEM ENCODING //////////////////////////////////////\n\n")

        var conjecture : lpOlTerm = lpOlNothing

        compressedProof foreach { step =>
          val stepId = step.id
          idClauseMap = idClauseMap + (stepId -> step)

          if (step.role == Role_NegConjecture) {
            //print(s" symbols in negated conjecture: ${symbols(step.cl).map(sig.apply(_).name)}\n")
            if (conjEnc) throw new Exception("found more than one negated conjecture in the proof object to encode in LP")
            conjEnc = true
            val (encConj, _) = clause2LP(step.cl, usedSymbols, sig)
            identicalSteps += (stepId -> conjName)
            conjecture = encConj.lits match {
              case Seq(lpOlUnaryConnectiveTerm(lpNot, conj)) => conj
              case _ => throw new Exception(s"given negated conjecture ${encConj.pretty} not negated")
            }
          } else if (step.role == Role_Axiom){ //todo: what about other roles like lamme etc. ?
            val (encClause, usedSymbolsNew) = clause2LP(step.cl, usedSymbols, sig)
            usedSymbols = usedSymbolsNew
            val axName = lpConstantTerm(s"axiom$axCounter")
            proofFileSB.append(lpDeclaration(axName, Seq.empty, encClause).pretty)
            identicalSteps += (stepId -> axName)
            axCounter = axCounter + 1
          }else {

            val (encStep, usedSymbolsNew) = clause2LP(step.cl, usedSymbols, sig)
            usedSymbols = usedSymbolsNew

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
              Out.lp_debug_info(s"Encoding step $stepName: application of caluclus rule ${rule.name}")
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
                proofSteps = proofSteps :+ lpProofScriptCommentLine(s"${step.annotation.fromRule}")
                proofSteps = proofSteps :+ lpHave(stepName,encStep,proofTerm)
                // and add the necessary symbols to the generated Signature
                usedSymbols = usedSymbols ++ updatedUsedSymbols
              }
            }
          }
      }
      Out.info("Done enocoding the inference rules")

      proofFileSB.append("\n\n// PROOF ENCODING ////////////////////////////////////////\n\n")

      // construct the proof based on all the individual steps
      // in the proof of the conjecture, first instanciate npp, then assume the negated conjecture
      proofSteps =  lpAssume(Seq(conjName)) +: proofSteps
      proofSteps =  lpRefine(lpFunctionApp(lpNpp.name,Seq(conjecture, lpWildcard))) +: proofSteps
      // finally, refine with the last step.
      val lastStepName = proofSteps.last match {
        case lpHave(name, _,_,_) => name
        case _ => throw new Exception(s"in the encoding, the last step had an unexptected tactic: ${proofSteps.last.pretty}")
      }
      proofSteps = proofSteps :+ lpRefine(lpFunctionApp(lpConstantTerm(lastStepName),Seq.empty))
      val completeProof = lpDefinition(lpConstantTerm("encodedProof"),Seq.empty,conjecture.prf,lpProofScript(proofSteps))
      proofFileSB.append(completeProof.pretty)

      // generate the signature

      Out.info("Generating Signature")
      val rulesFileSB = generateSignature(usedSymbols, nameLpOutputFolder)

      // initiate a lambdapi package

      var lpInitSuccess = true

      val command = Seq("/bin/bash", "-c", s"cd $lpOutputPath0 && lambdapi init $nameLpOutputFolder")

      val initLP = Try(command.!)

      initLP match {
        case Success(exitCode) => {
          if (exitCode != 0) {
            lpInitSuccess = false
            Files.createDirectories(Paths.get(lpOutputPath))
          }
        }
        case Failure(exception) => {
          lpInitSuccess = false
          Files.createDirectories(Paths.get(lpOutputPath))
        }
      }

      // write the files
      Out.info("Writing the Lambdapi files")

      val exttFilePath = Paths.get(s"${lpOutputPath}${nameLogicFile}.lp")
      Files.write(exttFilePath, ExTTenc.getBytes(StandardCharsets.UTF_8))

      //
      val permLibFilePath = Paths.get(s"${lpOutputPath}${permlibFile}.lp")
      Files.write(permLibFilePath, permLib.getBytes(StandardCharsets.UTF_8))

      val rulesFilePath = Paths.get(s"${lpOutputPath}${nameRulesFile}.lp")
      Files.write(rulesFilePath, rulesFileSB.toString.getBytes(StandardCharsets.UTF_8))

      val proofFilePath = Paths.get(s"${lpOutputPath}${nameProofFile}.lp")
      Files.write(proofFilePath, proofFileSB.toString.getBytes(StandardCharsets.UTF_8))


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
