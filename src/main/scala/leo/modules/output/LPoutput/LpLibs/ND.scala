package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.Level
object ND {

  object Names {
    // ND rules
    val lpLorelimS: SymRef  = SymRef.LP(QName.local("∨ₑ"))
    val lpLorIntro1S: SymRef  = SymRef.LP(QName.local("∨ᵢ₁"))
    val lpLorIntro2S: SymRef  = SymRef.LP(QName.local("¬¬ₑ"))
    // ...


    // axioms
    // excluded middle
    val lpEmS: SymRef  = SymRef.LP(QName.local("em"))
    // double negation elimination
    val lpDneS: SymRef  = SymRef.LP(QName.local("¬¬ₑ"))
    // non-emptiness of sets
    private[ND] val lpWitnessConS: SymRef = SymRef.LP(QName.local("el"))

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

