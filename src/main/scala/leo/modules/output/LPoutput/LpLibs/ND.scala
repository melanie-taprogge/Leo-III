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

    // proven standard library theorems
    val eqSymStr = "=_sym"

    val allAscii = Seq(witnessStr, emStr, eqSymStr)

    // ND rules
    val lpLorelimS: SymRef  = SymRef.LP(QName.local("∨ₑ"))
    val lpLorIntro1S: SymRef  = SymRef.LP(QName.local("∨ᵢ₁"))
    // ...


    // axioms
    // excluded middle
    val lpEmS: SymRef  = SymRef.LP(QName.local(emStr))
    // double negation elimination
    val lpDneS: SymRef  = SymRef.LP(QName.local("¬¬ₑ"))
    // non-emptiness of sets
    private[ND] val lpWitnessConS: SymRef = SymRef.LP(QName.local(witnessStr))

    // symmetry of equality
    private[ND] val eqSymS: SymRef = SymRef.LP(QName.local(eqSymStr))

  }

  object Terms {
    import Names._

    def lpDne[L <: Level]: LpTerm.Const[L] =
      LpTerm.Const[L](lpDneS)
    def lpWitnessCon[L <: Level]: LpTerm.Const[L] =
      LpTerm.Const[L](lpWitnessConS)
    def eqSym[L <: Level]: LpTerm.Const[L] =
      LpTerm.Const[L](eqSymS)

    // ...
  }

  object Inst {
    import  Terms._

    /*
    def lpWitness(ty : OlType): LpTerm[Level.Obj] = {
      LpTerm.App[Level.Meta](lpWitnessCon,Seq(Arg.ExplicitTypeArg(ty)))
    }

     */
  }

}

