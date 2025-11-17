import leo.datastructures.{Signature, mkDisjunction}
import leo.modules.input.Input.parseProblem
import leo.modules.input.TPTPParser
import leo.modules.output.LPoutput.NewLpDatastructures.LogicConst.cOr
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Lam
import leo.modules.output.LPoutput.NewLpDatastructures.Stmt._
import leo.modules.output.LPoutput.NewLpDatastructures.Proof._
import leo.modules.output.LPoutput.NewLpDatastructures.Renderer._
import leo.modules.output.LPoutput.NewLpDatastructures._
import leo.modules.output.LPoutput.NewLpDatastructures.nAry
import leo.modules.output.LPoutput.NewLpDatastructures.pretty._
import leo.modules.output.LPoutput.NewLpDatastructures.{Level, LpTerm, Name, Renderer}

val t: LpTerm[Level.Obj] = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("p")))
val emptyOrigSig = Signature.freshWithHOL()
implicit val emptySig = LpSigBuilder.build(emptyOrigSig)
Renderer.LpTermObj(t,emptySig) // or t.pp
t.pretty

// translate some TPTP forumula

val problem = "%----Zoey and Mel are islanders\nthf(kk_6_4,axiom,\n    ( ( is_a @ zoey @ islander )\n    & ( is_a @ mel @ islander ) ) ).\n\n%----Zoey says Mel is a knave\nthf(kk_6_5,axiom,\n    says @ zoey @ ( is_a @ mel @ knave ) ).\n\n%----Mel says 'Neither Zoey nor I are knaves'\nthf(kk_6_6,axiom,\n    ( says @ mel\n    @ ~ ( ( is_a @ zoey @ knave )\n        | ( is_a @ mel @ knave ) ) ) )."

TPTPParser.problem(problem).formulas.map(_.formula)

val testTerm0 = LogicConst.Or(LogicConst.Top,LogicConst.Bot)
val testTerm1 = LogicConst.Or(LogicConst.And(LogicConst.Top, LogicConst.Bot),LogicConst.Top)
val testTerm2 = LogicConst.Or(LogicConst.Imp(LogicConst.And(LogicConst.Top, LogicConst.Bot),LogicConst.Top),LogicConst.Bot)

testTerm0.pretty
testTerm1.pretty
testTerm2.pretty

// testing a term writing connective terms in infix notation
val testTerm3 = LpTerm.App(cOr,Seq(Arg.Explicit(t),Arg.Explicit(t)))

testTerm3.pretty

val atom0 = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("atom0")))
val atom1 = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("atom1")))
val atom2 = LpTerm.Const[Level.Obj](SymRef.LP(QName.local("atom2")))

nAry.disjunction(Seq(atom0,atom1,atom2))
nAry.disjunction(Seq(atom0,atom1,atom2)).pretty

val nestedApp = LpTerm.App(atom0,Seq(Arg.Explicit(LpTerm.App(atom1,Seq(Arg.Explicit(atom2))))))
nestedApp.pretty
