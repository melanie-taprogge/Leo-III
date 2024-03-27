package leo.modules.output.LPoutput

import leo.datastructures.{ClauseProxy, Role_Conjecture, Role_NegConjecture}
import leo.modules.embeddings.DHOLEmbedding.constants
import leo.modules.output.{ToTPTP, tptpEscapeName}
import leo.modules.prover.LocalState
import leo.modules.{axiomsInProof, compressedProofOf, symbolsInProof, userSignatureToTPTP}
import leo.modules.output.LPoutput.Encodings._
import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.ToTPTP.toTPTP
import leo.modules.proof_object.CompressProof
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.calculusEncoding._

import scala.collection.mutable

object LPoutput {

  def dosomething(state: LocalState):Unit={

    print(s"\n\nLP-ENCODING\n\n")

    def extractNecessaryFormulas(state:LocalState):Unit={

      val sig = state.signature
      val proof = state.proof

      val encodedProblem: StringBuffer = new StringBuffer()
      var usedSymbols:Set[lpStatement] = Set.empty
      var parameters: (Int,Int,Int,Int) = (0,0,0,0)


      // encode the typing and definition formulas:
      val keysToTypeDecsAndDefs = sig.allUserConstants.intersect(symbolsInProof(proof).union(sig.typeSymbols))

      keysToTypeDecsAndDefs.foreach {key =>
        val symbol = sig.apply(key)
        val sName = tptpEscapeName(symbol.name)

        if (symbol.hasKind) {
          //user defined types: add declarations to the problem
          //todo: what is saved as a kind? look at lines 96-99 in toTPTPscala again
          encodedProblem.append(lpDeclaration(lpConstantTerm(sName),Seq.empty,lpSet).pretty)
          usedSymbols = usedSymbols + lpSet

        }else{
          if (symbol.hasType) {
            val (typeDec, updatedUsedSymbols) = type2LP(symbol._ty, sig, usedSymbols)
            usedSymbols = updatedUsedSymbols
            encodedProblem.append(lpDeclaration(lpConstantTerm(sName),Seq.empty,typeDec.lift2Meta).pretty)
          }

          if (symbol.hasDefn) {
            val (definition, updatedUsedSymbols,boundVars) = def2LP(symbol._defn, sig, usedSymbols)
            usedSymbols = updatedUsedSymbols
            //val variables: StringBuffer = new StringBuffer()
            var variables: Seq[lpRuleVariable] = Seq.empty
            boundVars foreach {v_t =>
              // todo: for poylmorphic types this might have to be extended
              variables = variables :+ lpRuleVariable(lpOlConstantTerm(v_t._1))
            }
            val encodedDef = lpRule(lpOlConstantTerm(sName),variables,definition)
            //val encodedDef = s"rule $Prf($sName$variables) $ruleArrow $Prf($definition);\n"
            encodedProblem.append(encodedDef.pretty)
          }
        }
      }

      // encode the used axioms
      var axCounter = 0
      axiomsInProof(proof) foreach {ax =>
        val (encClause, usedSymbolsNew) = clause2LP(ax.cl,usedSymbols,sig)
        usedSymbols = usedSymbolsNew
        //encodedProblem.append(s"symbol axiom$axCounter : $encClause")
        encodedProblem.append(lpDeclaration(lpConstantTerm(s"axiom$axCounter"),Seq.empty,encClause).pretty)
        axCounter = axCounter +1
      }

      // encode the conjecture
      var conjCounter = 0
      state.negConjecture foreach{conj =>
        val (encConj, usedSymbolsNew) = clause2LP(conj.cl, usedSymbols, sig)
        usedSymbols = usedSymbolsNew
        //encodedProblem.append(s"symbol negatedConjecture$conjCounter : $encConj;\n")
        encodedProblem.append(lpDeclaration(lpConstantTerm(s"negatedConjecture$conjCounter"),Seq.empty,encConj).pretty)
        conjCounter = conjCounter + 1
      }

      //print(s"\n\nPROBLEM SO FAR:\n\n${encodedProblem.toString}\n\nNow we do the steps\n\n")
      // encode the clauses representing the steps
      // todo: Also make it possible to just output one long lambda-term
        //val compressedProof = compressedProofOf(CompressProof.stdImportantInferences)(state.derivationClause.get)
        val compressedProof = proof
        var idClauseMap: mutable.HashMap[Long,ClauseProxy] = mutable.HashMap.empty
        val identicalSteps: mutable.HashMap[Long,Long] = mutable.HashMap.empty

        compressedProof foreach {step =>
          val stepId = step.id
          idClauseMap = idClauseMap + (stepId -> step)

          val (encStep,usedSymbolsNew) = clause2LP(step.cl,usedSymbols,sig)
          usedSymbols = usedSymbolsNew

          var encodeStep = false
          step.annotation.parents foreach {parent =>
            if (!Seq().contains(parent.role)){//Role_NegConjecture Role_Conjecture
              val encParent = clause2LP(parent.cl, usedSymbols, sig)._1
              if (encParent == encStep) {
                // update the dictionary keeping track of eqivalent steps
                val existingValue = identicalSteps.getOrElseUpdate(stepId, parent.id)
                if (existingValue != parent.id) {
                  throw new Exception(s"step $stepId ($encStep) is equivalent to two parents: $existingValue, ${parent.id} ")
                }
              } else encodeStep = true
            }
          }
          // embed the proof step
          if (encodeStep == true){

            // try to construct a proof
            // since we do not write out steps that are identical in our encoding, we keep track of what the reference to the parent clause in LP is
            val parentInLpEncID = step.annotation.parents.map(parent => identicalSteps.getOrElse(parent.id, parent.id))
            val (proofTerm,updatedParameters,updatedUsedSymbols) = step2LP(step, idClauseMap, parentInLpEncID, sig, parameters)

            // if the step is actually new, we want to add it to the output
            if (proofTerm == lpOlNothing) {
              // todo: encode these rules! :)
              encodedProblem.append(s"\n// The rule ${step.annotation.fromRule} is not encoded yet\n")
              encodedProblem.append(s"symbol step${step.id} : ${encStep.pretty};\n")
            } else {
              // otherwise we provide it as an axiom
              //encodedProblem.append(s"\nsymbol step${step.id} : $encStep $colonEq\n")
              // and encode the proof based on its parent clauses
              //encodedProblem.append(s"$proofTerm;\n")
              encodedProblem.append(s"\n${lpDefinition(nameStep(step.id.toInt),Seq.empty,encStep,proofTerm).pretty}\n")
              // and we will add the necessary symbols to the generated Signature
              usedSymbols = updatedUsedSymbols
              parameters = updatedParameters
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

      print(encodedProblem)
    }

    extractNecessaryFormulas(state)









  }

}
