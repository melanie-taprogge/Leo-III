package leo.modules.output.LPoutput.LpLibs

import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.Level
import leo.modules.output.LPoutput.NewLpDatastructures.lpEncSig._
object EqRules {

  //todo: do naming uniformly

  object Names {

    // ** Names as Strings
    // Simplifications of PropExt.lp in Standard Library
    private val negEq_idem = "¬=_idem"
    private val orBot = "∨⊥"
    private val eqTop = "=⊤"
    private val eqBot = "=⊥"


    // Standard Library Theorems of Equality
    private val eqImpS = "=⇒"

    val allAscii = Seq()

    private[EqRules] val negEq_idem_S: SymRef = SymRef.LP(QName.local(negEq_idem))
    private[EqRules] val orBot_S: SymRef = SymRef.LP(QName.local(orBot))
    private[EqRules] val eqTop_S: SymRef = SymRef.LP(QName.local(eqTop))
    private[EqRules] val eqBot_S: SymRef = SymRef.LP(QName.local(eqBot))

    private[EqRules] val eqImp_S: SymRef = SymRef.LP(QName.local(eqImpS))

  }

  object AsTerms {
    import Names._

    def lpSimp_negEq_idem[L <: Level] = LpTerm.Const[L](negEq_idem_S)
    def lpSimp_orBot[L <: Level] = LpTerm.Const[L](orBot_S)
    def lpSimp_eqTop[L <: Level] = LpTerm.Const[L](eqTop_S)
    def lpSimp_eqBot[L <: Level] = LpTerm.Const[L](eqBot_S)
    def eqImp[L <: Level] = LpTerm.Const[L](eqImp_S)

  }


}

