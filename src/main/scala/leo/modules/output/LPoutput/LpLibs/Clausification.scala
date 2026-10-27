package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._

/** References to the clausification equalities provided by CNFeq.lp. */
object Clausification {
  object Names {
    private val skolemExistsStr = "∃_skolem"
    private val skolemNotForallStr = "∀_skolem"

    private[Clausification] val skolemExists: SymRef = SymRef.LP(QName.local(skolemExistsStr))
    private[Clausification] val skolemNotForall: SymRef = SymRef.LP(QName.local(skolemNotForallStr))
  }

  object Terms {
    def skolemExists[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.skolemExists)
    def skolemNotForall[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.skolemNotForall)
  }

  object Inst {
    def skolemExists(ty: OlMonoType, predicate: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App[Level.Obj](Terms.skolemExists[Level.Obj],
        Seq(Arg.ExplicitTypeArg(ty), Arg.Explicit(predicate)))

    /** The theorem takes the unnegated predicate of the negative universal. */
    def skolemNotForall(ty: OlMonoType, predicate: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App[Level.Obj](Terms.skolemNotForall[Level.Obj],
        Seq(Arg.ExplicitTypeArg(ty), Arg.Explicit(predicate)))
  }
}
