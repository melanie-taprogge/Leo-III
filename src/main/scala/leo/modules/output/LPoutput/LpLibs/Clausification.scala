package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._

/** References to the clausification equalities provided by CNFeq.lp. */
object Clausification {
  object Names {
    private val skolemExistsStr = "∃_skolem"
    private val skolemNotForallStr = "∀_skolem"
    private val notExistsForallNotStr = "¬∃=∀¬"
    private val forallAndDistLeftStr = "∀∧_dist_l"
    private val forallAndDistRightStr = "∀∧_dist_r"
    private val forallOrDistLeftStr = "∀∨_dist_l"
    private val forallOrDistRightStr = "∀∨_dist_r"

    private[Clausification] val skolemExists: SymRef = SymRef.LP(QName.local(skolemExistsStr))
    private[Clausification] val skolemNotForall: SymRef = SymRef.LP(QName.local(skolemNotForallStr))
    private[Clausification] val notExistsForallNot: SymRef = SymRef.LP(QName.local(notExistsForallNotStr))
    private[Clausification] val forallAndDistLeft: SymRef = SymRef.LP(QName.local(forallAndDistLeftStr))
    private[Clausification] val forallAndDistRight: SymRef = SymRef.LP(QName.local(forallAndDistRightStr))
    private[Clausification] val forallOrDistLeft: SymRef = SymRef.LP(QName.local(forallOrDistLeftStr))
    private[Clausification] val forallOrDistRight: SymRef = SymRef.LP(QName.local(forallOrDistRightStr))
  }

  object Terms {
    def skolemExists[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.skolemExists)
    def skolemNotForall[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.skolemNotForall)
    def notExistsForallNot[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.notExistsForallNot)
    def forallAndDistLeft[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.forallAndDistLeft)
    def forallAndDistRight[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.forallAndDistRight)
    def forallOrDistLeft[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.forallOrDistLeft)
    def forallOrDistRight[L <: Level]: LpTerm.Const[L] = LpTerm.Const[L](Names.forallOrDistRight)
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
