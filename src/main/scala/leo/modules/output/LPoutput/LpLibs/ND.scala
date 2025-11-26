package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.Level
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
object ND {

  //todo: do naming uniformly

  object Names {

    // ** Names as Strings
    // Standard Library Axioms
    val witnessStr = "el"
    val emStr = "em"

    val allAscii = Seq(witnessStr, emStr)

    // ND rules
    val lpLorelimS: SymRef  = SymRef.LP(QName.local("∨ₑ"))
    val lpLorIntro1S: SymRef  = SymRef.LP(QName.local("∨ᵢ₁"))
    val lpLorIntro2S: SymRef  = SymRef.LP(QName.local("¬¬ₑ"))
    // ...


    // axioms
    // excluded middle
    val lpEmS: SymRef  = SymRef.LP(QName.local(emStr))
    // double negation elimination
    val lpDneS: SymRef  = SymRef.LP(QName.local("¬¬ₑ"))
    // non-emptiness of sets
    private[ND] val lpWitnessConS: SymRef = SymRef.LP(QName.local(witnessStr))

  }

  object MlTerms {
    import Names._

    val lpDne = LpTerm.Const[Level.Meta](lpDneS)
    val lpWitnessCon = LpTerm.Const[Level.Meta](lpWitnessConS)

    // ...
  }

  object Inst {
    import  MlTerms._

    /*
    def lpWitness(ty : OlType): LpTerm[Level.Obj] = {
      LpTerm.App[Level.Meta](lpWitnessCon,Seq(Arg.ExplicitTypeArg(ty)))
    }

     */
  }

}

