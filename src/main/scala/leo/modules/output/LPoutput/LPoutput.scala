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

import scala.collection.mutable

object LPoutput {

  def dosomething(state: LocalState):Unit={

    print(s"\n\nLP-ENCODING\n\n")

    def extractNecessaryFormulas(state:LocalState):Unit={

      val sig = state.signature
      val proof = state.proof

      val encodedProblem: StringBuffer = new StringBuffer()
      var usedSymbols:Set[String] = Set.empty


      // encode the typing and definition formulas:
      val keysToTypeDecsAndDefs = sig.allUserConstants.intersect(symbolsInProof(proof).union(sig.typeSymbols))

      keysToTypeDecsAndDefs.foreach {key =>
        val symbol = sig.apply(key)
        val sName = tptpEscapeName(symbol.name)

        if (symbol.hasKind) {
          //throw new Error(s"Kinds not yet implemented ${symbol.kind}")
          //kind2LP(symbol.kind.get,sig)
          //todo: what is saved as a kind? look at lines 96-99 in toTPTPscala again
          encodedProblem.append(s"symbol $sName : $typeOfTptptTypes;\n")
          usedSymbols = usedSymbols + typeOfTptptTypes

        }else{
          if (symbol.hasType) {
            val (typeDec, updatedUsedSymbols) = type2LP(symbol._ty, sig, usedSymbols)
            usedSymbols = updatedUsedSymbols
            encodedProblem.append(s"symbol $sName : $Els($uparrow $typeDec);\n")
          }

          if (symbol.hasDefn) {
            //val (definition, updatedUsedSymbols) = term2LP(symbol._defn, Map(), sig, usedSymbols)
            val (definition, updatedUsedSymbols,boundVars) = def2LP(symbol._defn, sig, usedSymbols)
            usedSymbols = updatedUsedSymbols
            val variables: StringBuffer = new StringBuffer()
            boundVars foreach {v_t =>
              val (encType, updatedUsedSymbols) = type2LP(v_t._2, sig, usedSymbols)
              usedSymbols = updatedUsedSymbols
              // todo: for poylmorphic types this might have to be extended
              //variables.append(s" (${v_t._1} : $Els($uparrow $encType))")
              variables.append(s" ${v_t._1}")
            }
            val encodedDef = s"rule $Prf($sName$variables) $ruleArrow $Prf($definition);\n"
            encodedProblem.append(encodedDef)
          }
        }
      }

      // encode the used axioms
      var axCounter = 0
      axiomsInProof(proof) foreach {ax =>
        val (encClause, usedSymbolsNew) = clause2LP(ax.cl,usedSymbols,sig)
        usedSymbols = usedSymbolsNew
        encodedProblem.append(s"symbol axiom$axCounter : $encClause")
        axCounter = axCounter +1
      }

      // encode the conjecture
      var conjCounter = 0
      state.negConjecture foreach{conj =>
        val (encConj, usedSymbolsNew) = clause2LP(conj.cl, usedSymbols, sig)
        usedSymbols = usedSymbolsNew
        encodedProblem.append(s"symbol negatedConjecture$conjCounter : $encConj;\n")
        conjCounter = conjCounter + 1
      }

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
            //todo: introduce a new independent string buffer for the proofs and put them in the end

            // try to construct a proof
            val parentInLpEncID = step.annotation.parents.map(parent => identicalSteps.getOrElse(parent.id, parent.id))
            val (proofTerm,updatedUsedSymbols) = step2LP(step, idClauseMap, parentInLpEncID, sig)

            // if the step is actually new, we want to add it to the output
            if (proofTerm == "") {
              encodedProblem.append(s"\n// The rule ${step.annotation.fromRule} is not encoded yet\n")
              encodedProblem.append(s"symbol step${step.id} : $encStep;\n")
            } else {
              // otherwise we provide it as an axiom
              encodedProblem.append(s"\nsymbol step${step.id} : $encStep $colonEq\n")
              // and encode the proof based on its parent clauses
              encodedProblem.append(s"$proofTerm;\n")
              // and we will add the necessary symbols to the generated Signature
              usedSymbols = updatedUsedSymbols
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
