package leo.modules.output.LPoutput

import leo.datastructures.{ClauseProxy, Role_Axiom, Role_Conjecture, Role_NegConjecture}
import leo.modules.embeddings.DHOLEmbedding.constants
import leo.modules.output.{ToTPTP, tptpEscapeName}
import leo.modules.prover.LocalState
import leo.modules.{axiomsInProof, compressedProofOf, symbolsInProof, userSignatureToTPTP}
import leo.modules.output.LPoutput.Encodings._
import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.ToTPTP.toTPTP
import leo.modules.proof_object.CompressProof
import leo.modules.output.LPoutput.lpDatastructures.{lpDefinedRules, _}
import leo.modules.output.LPoutput.calculusEncoding._
import leo.modules.output.LPoutput.lpUseful._
import leo.modules.output.LPoutput.lpInferenceRuleEncoding._
import leo.modules.output.LPoutput.SimplificationEncoding
import leo.modules.output.LPoutput.Transformations._
import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets

import scala.collection.mutable

object LPoutput {

  val nameLpOutputFolder = "testOutput"
  val nameLogicFile = "extt"
  val nameRewriteRuleFile = "rwr"
  val nameCorrectnessFile = "correctness"
  val nameNaturalDeductionFile = "nd"
  val nameRulesFile = "rules"
  val nameProofFile = "encodedProof"

  def generateSignature(usedSymbols: Set[lpStatement]): (mutable.StringBuilder,mutable.StringBuilder,mutable.StringBuilder) = {

    val correctnessFileSB: mutable.StringBuilder = new StringBuilder()
    correctnessFileSB.append(s"require open ${nameLpOutputFolder}.$nameLogicFile ${nameLpOutputFolder}.${nameRewriteRuleFile};\n\n")
    val naturalDeductionFileSB: mutable.StringBuilder = new StringBuilder()
    naturalDeductionFileSB.append(s"require open ${nameLpOutputFolder}.${nameLogicFile};\n\n")
    val rulesFileSB: mutable.StringBuilder = new StringBuilder()
    rulesFileSB.append(s"require open ${nameLpOutputFolder}.$nameLogicFile ${nameLpOutputFolder}.${nameNaturalDeductionFile};\n\n")

    print(s"used symbols: ${usedSymbols.map(symb => (symb))}")

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
    basicRules foreach { basicRule =>
      correctnessFileSB.append(basicRule.pretty)
      correctnessFileSB.append("\n")
      naturalDeductionFileSB.append(basicRule.dec.pretty)
      naturalDeductionFileSB.append("\n")
    }

    // add simplification rules
    if (simplificationRules.nonEmpty) output.append("////// Simplification Rules \n\n")
    simplificationRules foreach { simpRrule =>
      rulesFileSB.append(simpRrule.dec.pretty)
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
      rulesFileSB.append(otherRule.dec.pretty)
      rulesFileSB.append("\n")
    }

    (correctnessFileSB, naturalDeductionFileSB,rulesFileSB)
  }

  def outputLPFiles(state: LocalState, lpOutputPath: String):Unit={

    val proofFileSB: mutable.StringBuilder = new StringBuilder()
    proofFileSB.append(s"require open ${nameLpOutputFolder}.$nameLogicFile ${nameLpOutputFolder}.${nameNaturalDeductionFile} ${nameLpOutputFolder}.${nameRulesFile};\n\n")


    print(s"\n\nLP-ENCODING\n\n")

    def extractNecessaryFormulas(state:LocalState):Unit={

      val sig = state.signature
      val proof = state.proof

      //val encodedProblem: StringBuffer = new StringBuffer()
      //val encodedProof: StringBuffer = new StringBuffer()
      var usedSymbols:Set[lpStatement] = Set(eqDef(),eqRef()) // always add them because they are necessary for equality tactics. Todo: handle differently
      var parameters: (Int,Int,Int,Int) = (0,0,0,0)


      // encode the typing and definition formulas:
      val keysToTypeDecsAndDefs = sig.allUserConstants.intersect(symbolsInProof(proof).union(sig.typeSymbols))

      proofFileSB.append("// PROBLEM ENCODING ///////////////////////////\n")

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
            //val variables: StringBuffer = new StringBuffer()
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
            //val encodedDef = s"rule $Prf($sName$variables) $ruleArrow $Prf($definition);\n"
            proofFileSB.append(encodedDef.pretty)
          }
        }
      }

      // encode the used axioms
      /*
      var axCounter = 0
      axiomsInProof(proof) foreach {ax =>
        val (encClause, usedSymbolsNew) = clause2LP(ax.cl,usedSymbols,sig)
        usedSymbols = usedSymbolsNew
        //encodedProblem.append(s"symbol axiom$axCounter : $encClause")
        encodedProblem.append(lpDeclaration(lpConstantTerm(s"axiom$axCounter"),Seq.empty,encClause).pretty)
        axCounter = axCounter +1
      }
       */

      // encode the conjecture
      /*
      var conjCounter = 0
      state.negConjecture foreach{conj =>
        val (encConj, usedSymbolsNew) = clause2LP(conj.cl, usedSymbols, sig)
        usedSymbols = usedSymbolsNew
        //encodedProblem.append(s"symbol negatedConjecture$conjCounter : $encConj;\n")
        val conjName = lpConstantTerm(s"negatedConjecture$conjCounter")
        encodedProblem.append(lpDeclaration(conjName,Seq.empty,encConj).pretty)
        conjCounter = conjCounter + 1
      }
       */

      //print(s"\n\nPROBLEM SO FAR:\n\n${encodedProblem.toString}\n\nNow we do the steps\n\n")
      // encode the clauses representing the steps
      // todo: Also make it possible to just output one long lambda-term
        //val compressedProof = compressedProofOf(CompressProof.stdImportantInferences)(state.derivationClause.get)
        val compressedProof = proof
        var idClauseMap: mutable.HashMap[Long,ClauseProxy] = mutable.HashMap.empty
        val identicalSteps: mutable.HashMap[Long,lpConstantTerm] = mutable.HashMap.empty
        var conjCounter = 0
        var axCounter = 0

        proofFileSB.append("// PROOF ENCODING ///////////////////////////\n")

        compressedProof foreach { step =>
          val stepId = step.id
          idClauseMap = idClauseMap + (stepId -> step)

          //print(s"step num: $stepId\n")

          if (step.role == Role_NegConjecture) {
            val (encConj, usedSymbolsNew) = clause2LP(step.cl, usedSymbols, sig)
            usedSymbols = usedSymbolsNew
            //encodedProblem.append(s"symbol negatedConjecture$conjCounter : $encConj;\n")
            val conjName = lpConstantTerm(s"negatedConjecture$conjCounter")
            proofFileSB.append(lpDeclaration(conjName, Seq.empty, encConj).pretty)
            // let the corresponding step number point to "negated_conjecture"
            identicalSteps += (stepId -> conjName)
            //print(s"identical steps: $identicalSteps\n")
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
                //print(s"\nstep number ${parent.id} endoing ${encParent.pretty}, role ${parent.role}\n\n")
                if (encParent == encStep) {
                  // update the dictionary keeping track of eqivalent steps
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
                  //val existingValue = identicalSteps.getOrElseUpdate(stepId, nameStep(parent.id.toInt))
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
                proofFileSB.append(s"\n// The rule ${step.annotation.fromRule} is not encoded yet\n")
                proofFileSB.append(s"symbol step${step.id} : ${encStep.pretty};\n")
              } else {
                // otherwise we provide it as an axiom
                //encodedProblem.append(s"\nsymbol step${step.id} : $encStep $colonEq\n")
                // and encode the proof based on its parent clauses
                //encodedProblem.append(s"$proofTerm;\n")
                proofFileSB.append(s"\n// $ruleName\n${lpDefinition(nameStep(step.id.toInt), Seq.empty, encStep, proofTerm).pretty}\n")
                // and we will add the necessary symbols to the generated Signature
                usedSymbols = usedSymbols ++ updatedUsedSymbols
                parameters = updatedParameters
              }
            }
          }

          //print(encodedProblem.toString)

          //encodedProblem.append(s"symbol Step${step.id} : $encStep;\n")

          /*
          print(s"step ${step.id}: $encStep\n")
          print(s"parents: ${step.annotation.parents}\n")
          if (step.annotation.parents.length == 1) {
            print(s"parents: only one\n")
            val parent = step.annotation.parents.head
            if (encStep == clause2LP(parent.cl,usedSymbols,sig)._1){
              print(s"nothing changed\n")
            }else{
              //print(s"${parent.cl}\n${step.cl}\n")
              print(s"${encStep}\n${clause2LP(parent.cl,usedSymbols,sig)._1}\n")
            }
          }
          print(s"${step.annotation}\n\n")
           */
      }

      // generate the signature

      val (correctnessFileSB, naturalDeductionFileSB,rulesFileSB) = generateSignature(usedSymbols)

      //print(encodedProblem)
      //print(encodedProof)

      //print(s"change order proof:\n ${changePositions(Seq(0,2,1),"fdsafda")._1.pretty}")
      //print(s"apply only to some literals:\n${generateClorRule(Seq(false,true,true),"jaaaaas")._1.pretty}")

      val content = "This is the new content to write into the file."

      // write the files

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

    }

    extractNecessaryFormulas(state)









  }

}
