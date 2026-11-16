package leo.modules.calculus

import leo.{Checked, LeoTestSuite}
import leo.datastructures.{Clause, Literal, Signature}
import leo.modules.input.Input

/**
  * Created by mwisnie on 4/4/16.
  */
class CNFTestSuite extends LeoTestSuite {

  val testProblems : Seq[String] = Seq(
    "fof(1,axiom,a&b).",
    "fof(2,axiom,a|b).",
    "fof(3,axiom,a&(b|c)).",
    "fof(4,axiom,(a|b)&(c|d)).",
    "fof(5,axiom,(a&b)|(c&d)).",
    "fof(6,axiom,((a & b) | c) & (d | (b & f))).",
    "fof(7,axiom,a=>b)."
  )


  for(p <- testProblems)
    test(s"Test : ($p)", Checked) {
      implicit val sig: Signature = getFreshSignature
      val (_,l,_) = Input.readAnnotated(p)
      val s : StringBuilder = new StringBuilder
      s.append("CNF on\n  ")
      val pc = Clause(Literal(l,true))
      s.append(pc.pretty)
      s.append("\n")
      val vargen1 = freshVarGen(pc)
      val vargen2 = freshVarGen(pc)
      val cnf1 = FullCNF(vargen1, pc).clauses
//      val cnf2 = CNF(vargen2, pc)
      val cnf3 = StepCNF.exhaust(pc)
      s.append(" >Max CNF\n   ")
      s.append(cnf1.map(_.pretty).mkString("\n   "))
//      s.append("\n >Alex CNF\n   ")
//      s.append(cnf2.map(_.pretty).mkString("\n   "))
      s.append("\n >Step CNF\n   ")
      s.append(cnf3.map(_.pretty).mkString("\n   "))
      s.append(s"\n >Congruent: ${eq(cnf1, cnf3)}")
      println(s.toString())
      assert(eq(cnf1, cnf3), "Both normalizations printed a different cnf.")

    }

  test("CNF conclusions and conjunction extraction use right-nested conjunctions", Checked) {
    implicit val sig: Signature = getFreshSignature
    val (_, term, _) = Input.readAnnotated("fof(conjunction,axiom,a&b&c).")
    val input = Clause(Literal(term, true))
    val cnf = FullCNF(freshVarGen(input), input)
    val Seq(a, b, c) = cnf.clauses.map(Clause.asTerm)
    val expected = Clause(Literal(leo.modules.HOLSignature.&(a, leo.modules.HOLSignature.&(b, c)), true))

    assert(cnf.steps.lastOption.map(_.after).getOrElse(input) == expected)
    assert(CnfConj(cnf.clauses)._1 == expected)
  }

  test("CNF conclusions and conjunction extraction use right-nested clause disjunctions", Checked) {
    implicit val sig: Signature = getFreshSignature
    val (_, term, _) = Input.readAnnotated("fof(disjunction,axiom,d&(a|b|c)).")
    val input = Clause(Literal(term, true))
    val cnf = FullCNF(freshVarGen(input), input)
    val Seq(d, disjunction) = cnf.clauses
    val Seq(a, b, c) = disjunction.lits.map(Literal.asTerm)
    val expectedDisjunction = leo.modules.HOLSignature.|||(a, leo.modules.HOLSignature.|||(b, c))
    val expected = Clause(Literal(leo.modules.HOLSignature.&(Clause.asTerm(d), expectedDisjunction), true))

    assert(cnf.steps.lastOption.map(_.after).getOrElse(input) == expected)
    assert(CnfConj(cnf.clauses)._1 == expected)
  }

  private def eq(c1 : Seq[Clause], c2 : Seq[Clause]) = {
    (c1 forall (c11 => c2.exists(_.cong(c11)))) && (c2 forall (c11 => c1.exists(_.cong(c11))))
  }
}
