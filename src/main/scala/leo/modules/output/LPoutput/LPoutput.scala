package leo.modules.output.LPoutput

import leo.datastructures.{ClauseProxy, Role_Axiom, Role_NegConjecture, Signature}
import leo.modules.output.tptpEscapeName
import leo.modules.prover.LocalState
import leo.modules.symbolsInProof
import leo.modules.output.LPoutput.Encodings._
import leo.modules.output.LPoutput.LPSignature.{ExTTenc, RwRenc}
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.ModularProofEncoding._
import leo.modules.output.LPoutput.NaturalDeductionRules._

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import scala.collection.mutable
import scala.sys.process._
import scala.util.{Try, Success, Failure}

/**
  * Generation of the various files making up the Lambdapi encoding
  *
  * @author Melanie Taprogge
  */

object LPoutput {

  val nameLogicFile = "extt"
  val nameRewriteRuleFile = "rwr"
  val nameCorrectnessFile = "correctness"
  val nameNaturalDeductionFile = "nd"
  val nameRulesFile = "rules"
  val nameProofFile = "encodedProof"

  def generateSignature(usedSymbols: Set[lpStatement], nameLpOutputFolder: String): (mutable.StringBuilder,mutable.StringBuilder,mutable.StringBuilder) = {

    val correctnessFileSB: mutable.StringBuilder = new StringBuilder()
    correctnessFileSB.append(s"require open ${nameLpOutputFolder}.$nameLogicFile ${nameLpOutputFolder}.${nameRewriteRuleFile};\n\n")
    // todo: encode the remaining rules and change back to automated selection of necessary rules
    correctnessFileSB.append(allNDDefs)
    val naturalDeductionFileSB: mutable.StringBuilder = new StringBuilder()
    naturalDeductionFileSB.append(s"require open ${nameLpOutputFolder}.${nameLogicFile};\n\n")
    naturalDeductionFileSB.append(allNDDecs)
    val rulesFileSB: mutable.StringBuilder = new StringBuilder()
    rulesFileSB.append(s"require open ${nameLpOutputFolder}.$nameLogicFile ${nameLpOutputFolder}.${nameNaturalDeductionFile};\n\n")

    var simplificationRules: Set[SimplificationEncoding.simplificationRules] = Set.empty
    var otherRules: Set[lpDefinedRules] = Set.empty
    var infRules: Set[lpInferenceRuleEncoding.inferenceRules] = Set.empty
    var infRulesRWfree: Set[lpInferenceRuleEncoding.inferenceRules] = Set.empty
    var basicRules: Set[lpBasicRules] = Set.empty

    // sort the symbols
    usedSymbols foreach { symbol =>
      symbol match {
        case basicRule: lpBasicRules =>
          basicRules = basicRules + basicRule
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

    // add basic rules to output and to correctness
    // todo: make sure that things like the basic rules that can depend on each other are given in the right order
    if (basicRules.nonEmpty) output.append("////// Basic Rules \n\n")
    /*
    basicRules foreach { basicRule =>
      correctnessFileSB.append(basicRule.pretty)
      correctnessFileSB.append("\n")
      naturalDeductionFileSB.append(basicRule.dec.pretty)
      naturalDeductionFileSB.append("\n")
    }
     */

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

    (correctnessFileSB, naturalDeductionFileSB,rulesFileSB)
  }

  def step2LP(cl: ClauseProxy, idClauseMap: mutable.HashMap[Long, ClauseProxy], parentInLpEncID: Seq[lpConstantTerm], sig: Signature, parameters0: (Int, Int, Int, Int)): (String, lpStatement, (Int, Int, Int, Int), Set[lpStatement]) = {

    val skripts = true

    val rule = cl.annotation.fromRule

    val continuousNumbers = true

    val parameters = if (continuousNumbers) parameters0 else (0, 0, 0, 0)

    if (!Seq(leo.datastructures.Role_Conjecture).contains(cl.role)) { // we start our proof with the negated conjecture

      rule match {
        case leo.modules.calculus.PolaritySwitch =>
          //todo: dont forget to map to the correct formula! make special case for negated conjecture
          //val encoding = encPolaritySwitchClause(cl, cl.annotation.parents.head,parentInLpEncID.head,sig,parameters) //¿polarity switch always only has one parent, right?
          //encoding
          val encoding = encPolaritySwitch(cl, cl.annotation.parents.head, parentInLpEncID.head, sig) //¿polarity switch always only has one parent, right?
          ("PolaritySwitch", encoding._1, (0, 0, 0, 0), encoding._2)

        case leo.modules.calculus.FuncExt =>
          val encoding = encFuncExtPos(cl, cl.annotation.parents.head, cl.furtherInfo.edLitBeforeAfter, parentInLpEncID.head, sig)
          ("FuncExt", encoding._1, parameters, encoding._2)

        case leo.modules.calculus.BoolExt =>
          val encoding = encBoolExt(cl, cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.addInfoBoolExt, sig)
          ("BoolExt", encoding._1, (0, 0, 0, 0), encoding._2)

        case leo.modules.calculus.OrderedEqFac =>
          //val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head,cl.furtherInfo.addInfoEqFac,parentInLpEncID.head,sig)
          //(encodings._1,(0,0,0,0),encodings._2)
          val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoEqFac, parentInLpEncID.head, sig)
          ("OrderedEqFac", encodings._1, parameters, encodings._2)

        case leo.modules.calculus.DefExpSimp =>
          //throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoDefExp}")
          // todo: eta expansion
          val encodingsSimp = encDefExSimp(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoDefExp, parentInLpEncID.head, sig)
          ("DexExpand", encodingsSimp._1, (0, 0, 0, 0), encodingsSimp._2)
        case leo.modules.calculus.Simp =>
          throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoSimp}")
          // todo: eta expansion
          val encodingsSimp = encDefExSimp(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoDefExp, parentInLpEncID.head, sig)
          ("?", encodingsSimp._1, (0, 0, 0, 0), encodingsSimp._2)
        case leo.modules.calculus.PreUni =>
          val encodingPreUni = encPreUni(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoUni, cl.furtherInfo.addInfoUniRule, parentInLpEncID.head, sig)
          ("PreUni", encodingPreUni._1, parameters, encodingPreUni._2)
        //throw new Exception(s"${cl.furtherInfo.addInfoUni}")
        case leo.modules.calculus.RewriteSimp =>
          //throw new Exception(s"add info rewriting: ${cl.furtherInfo.addInfoRewriting}")
          val encodingRewrite = encRewrite(cl, cl.annotation.parents, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoRewriting, parentInLpEncID, sig)
          ("RewriteSimp", encodingRewrite._1, parameters, encodingRewrite._2)
        case _ =>
          //print(s"\n $rule not encoded yet \n\n")
          (s"Rule ${rule.name} not encoded yet", lpOlNothing, parameters, Set.empty)
      }
    } //todo: either introduce else or filter out conj before!
    else ("no role or conjecture?", lpOlNothing, parameters, Set.empty)
  }


  def outputLPFiles(state: LocalState, lpOutputPath0: String, nameLpOutputFolder: String):Unit={

    val lpOutputPath = s"${lpOutputPath0}${nameLpOutputFolder}/"

    val proofFileSB: mutable.StringBuilder = new StringBuilder()
    proofFileSB.append(s"require open ${nameLpOutputFolder}.$nameLogicFile ${nameLpOutputFolder}.${nameNaturalDeductionFile} ${nameLpOutputFolder}.${nameRulesFile};\n\n")

    val proofStepsSB: mutable.StringBuilder = new StringBuilder()

    def extractNecessaryFormulas(state:LocalState):Unit={

      val sig = state.signature
      val proof = state.proof

      var usedSymbols:Set[lpStatement] = Set(eqDef(),eqRef()) // always add them because they are necessary for equality tactics. Todo: handle differently
      var parameters: (Int,Int,Int,Int) = (0,0,0,0)


      // encode the typing and definition formulas:
      val keysToTypeDecsAndDefs = sig.allUserConstants.intersect(symbolsInProof(proof).union(sig.typeSymbols))

      proofFileSB.append("// OBJECT DECLARATIONS ///////////////////////////////////\n\n")

      keysToTypeDecsAndDefs.foreach {key =>
        val symbol = sig.apply(key)
        val sName = tptpEscapeName(symbol.name)

        if (symbol.hasKind) {
          //user defined types: add declarations to the problem
          //todo: what is saved as a kind? look at lines 96-99 in toTPTPscala again
          proofFileSB.append(lpDeclaration(lpConstantTerm(sName),Seq.empty,lpSet).pretty)
          usedSymbols = usedSymbols + lpSet

        }else{
          if (symbol.hasType) {
            val (typeDec, updatedUsedSymbols) = type2LP(symbol._ty, sig, usedSymbols)
            usedSymbols = updatedUsedSymbols
            proofFileSB.append(lpDeclaration(lpConstantTerm(sName),Seq.empty,typeDec.lift2Meta).pretty)
          }

          if (symbol.hasDefn) {

            val encAsRewriteRule = true

            val (definition, updatedUsedSymbols,boundVars) = def2LP(symbol._defn, sig, usedSymbols, encAsRewriteRule)
            usedSymbols = updatedUsedSymbols
            var variables: Seq[lpVariable] = Seq.empty
            boundVars foreach { v_t =>
              // todo: for poylmorphic types this might have to be extended
              if (encAsRewriteRule) variables = variables :+ lpRuleVariable(lpOlConstantTerm(v_t._1))
              else variables = variables :+ lpUntypedVar(lpOlConstantTerm(v_t._1))
            }
            val encodedDef = {
              if (encAsRewriteRule) {
                lpRule(lpOlConstantTerm(sName),variables,definition)
              } else {
                val defTermType = type2LP(symbol._defn.ty,sig)._1
                val defAsEq = lpOlTypedBinaryConnectiveTerm(lpEq,defTermType,lpOlFunctionApp(lpOlConstantTerm(sName),variables),definition)
                lpDeclaration(lpConstantTerm(s"${sName}_def"),variables,defAsEq.prf)
              }
            }
            proofFileSB.append(encodedDef.pretty)
          }
        }
      }

      // encode the clauses representing the steps
      // todo: Also make it possible to just output one long lambda-term
        val compressedProof = proof
        var idClauseMap: mutable.HashMap[Long,ClauseProxy] = mutable.HashMap.empty
        val identicalSteps: mutable.HashMap[Long,lpConstantTerm] = mutable.HashMap.empty
        var conjCounter = 0
        var axCounter = 0

      proofFileSB.append("\n\n// PROBLEM ENCODING //////////////////////////////////////\n\n")

        compressedProof foreach { step =>
          val stepId = step.id
          idClauseMap = idClauseMap + (stepId -> step)

          if (step.role == Role_NegConjecture) {
            val (encConj, usedSymbolsNew) = clause2LP(step.cl, usedSymbols, sig)
            usedSymbols = usedSymbolsNew
            val conjName = lpConstantTerm(s"negatedConjecture$conjCounter")
            proofFileSB.append(lpDeclaration(conjName, Seq.empty, encConj).pretty)
            // let the corresponding step number point to "negated_conjecture"
            identicalSteps += (stepId -> conjName)
            conjCounter = conjCounter + 1
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

            step.annotation.parents foreach { parent =>
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
              val (ruleName,proofTerm, updatedParameters, updatedUsedSymbols) = step2LP(step, idClauseMap, parentInLpEncID, sig, parameters)

              // if the step is actually new, we want to add it to the output
              if (proofTerm == lpOlNothing) {
                // todo: encode these rules! :)
                proofStepsSB.append(s"// The rule ${step.annotation.fromRule} is not encoded yet\n")
                proofStepsSB.append(s"symbol step${step.id} : ${encStep.pretty};\n\n")
              } else {
                // otherwise we provide it as an axiom
                //encodedProblem.append(s"\nsymbol step${step.id} : $encStep $colonEq\n")
                // and encode the proof based on its parent clauses
                //encodedProblem.append(s"$proofTerm;\n")
                proofStepsSB.append(s"// $ruleName\n${lpDefinition(nameStep(step.id.toInt), Seq.empty, encStep, proofTerm, Seq.empty, Seq(lpOpaque)).pretty}\n")
                // and we will add the necessary symbols to the generated Signature
                usedSymbols = usedSymbols ++ updatedUsedSymbols
                parameters = updatedParameters
              }
            }
          }
      }

      proofFileSB.append("\n\n// PROOF ENCODING ////////////////////////////////////////\n\n")

      proofFileSB.append(proofStepsSB)

      // generate the signature

      val (correctnessFileSB, naturalDeductionFileSB,rulesFileSB) = generateSignature(usedSymbols, nameLpOutputFolder)

      // initiate a lambdapi package

      var lpInitSuccess = true

      val command = Seq("/bin/sh", "-c", s"cd $lpOutputPath0 && lambdapi init $nameLpOutputFolder")

      val initLP = Try(command.!)

      initLP match {
        case Success(exitCode) => {
          if (exitCode != 0) {
            println(s"\nFailed to initiate Lambdapi package (exit code $exitCode).\nFiles are saved to the output directory.")
            lpInitSuccess = false
            Files.createDirectories(Paths.get(lpOutputPath))
          }
        }
        case Failure(exception) => {
          println(s"\nFailed to initiate Lambdapi package ($exception).\nFiles are saved to the output directory.")
          lpInitSuccess = false
          Files.createDirectories(Paths.get(lpOutputPath))
        }
      }

      // write the files

      val exttFilePath = Paths.get(s"${lpOutputPath}${nameLogicFile}.lp")
      Files.write(exttFilePath, ExTTenc.getBytes(StandardCharsets.UTF_8))

      val rwrFilePath = Paths.get(s"${lpOutputPath}${nameRewriteRuleFile}.lp")
      Files.write(rwrFilePath, s"require open ${nameLpOutputFolder}.$nameLogicFile; \n\n${RwRenc}".getBytes(StandardCharsets.UTF_8))

      val correctnessFilePath = Paths.get(s"${lpOutputPath}${nameCorrectnessFile}.lp")
      Files.write(correctnessFilePath, correctnessFileSB.toString.getBytes(StandardCharsets.UTF_8))

      naturalDeductionFileSB.append(s"builtin \"eqind\" ≔ ${eqDef().name.pretty};\n")//todo: pass linking to builtin differently")
      naturalDeductionFileSB.append(s"builtin \"refl\" ≔ ${eqRef().name.pretty};\n")//todo: pass linking to builtin differently")
      val ndFilePath = Paths.get(s"${lpOutputPath}${nameNaturalDeductionFile}.lp")
      Files.write(ndFilePath, naturalDeductionFileSB.toString.getBytes(StandardCharsets.UTF_8))

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
