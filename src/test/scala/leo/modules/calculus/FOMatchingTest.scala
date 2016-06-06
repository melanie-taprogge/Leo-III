package leo.modules.calculus

import leo.{Checked, LeoTestSuite}
import leo.datastructures._
import Term._
import leo.modules.CLParameterParser

/**
  * Created by lex on 6/6/16.
  */
class MatchingTestSuite extends LeoTestSuite {
  type UEq = Seq[(Term, Term)]

  import leo.modules.calculus.matching.FOMatching

  test("f(x,x) = f(a,a)", Checked){
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)
    val t1 : Term = mkTermApp(f , Seq(x,x))
    val t2 : Term = mkTermApp(f , Seq(a,a))

    val result = FOMatching.decideMatch(t1, t2)

    assertResult(true)(result)
  }

  test("f(x,x) = f(a,a) unifier", Checked){
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)
    val t1 : Term = mkTermApp(f , Seq(x,x))
    val t2 : Term = mkTermApp(f , Seq(a,a))

    val expectedSubst: Subst = Subst.fromMap(Map(1 -> a))
    val result = FOMatching.matches(t1, t2)

    assertResult(true)(result.isDefined)
    assertResult(expectedSubst)(result.get)
  }

  test("x(a) = f(a,a)", Checked){
    val s = getFreshSignature

    val vargen = freshVarGenFromBlank
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i ->: s.i))

    val t1 : Term = mkTermApp(vargen(s.i ->: s.i),a)
    val t2 : Term = mkTermApp(f , Seq(a,a))

    val result = FOMatching.decideMatch(t1, t2)
    assertResult(false)(result)
  }

  test("f(x,g(y)) = f(a,g(f(a)))", Checked){
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))
    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)
    val y = vargen(s.i)

    val t1 : Term = mkTermApp(f , Seq(x, mkTermApp(g, y)))
    val t2 : Term = mkTermApp(f , Seq(a, mkTermApp(g, mkTermApp(f, a))))

    val result = FOMatching.decideMatch(t1, t2)

    assertResult(true)(result)
  }

  test("f(x,g(y)) = f(a,g(f(a))) unifier", Checked){
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))
    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)
    val y = vargen(s.i)

    val t1 : Term = mkTermApp(f , Seq(x, mkTermApp(g, y)))
    val t2 : Term = mkTermApp(f , Seq(a, mkTermApp(g, mkTermApp(f, a))))

    val expectedSubst: Subst = Subst.fromMap(Map(1 -> a, 2 -> mkTermApp(f, a)))
    val result = FOMatching.matches(t1, t2)

    assertResult(true)(result.isDefined)
    assertResult(expectedSubst)(result.get)
  }

  test("f(x,g(x)) = f(a,g(f(a)))", Checked){
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))
    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)
    val y = vargen(s.i)

    val t1 : Term = mkTermApp(f , Seq(x, mkTermApp(g, x)))
    val t2 : Term = mkTermApp(f , Seq(a, mkTermApp(g, mkTermApp(f, a))))

    val result = FOMatching.decideMatch(t1, t2)

    assertResult(false)(result)
  }

  test("f(x,g(y)) = f(a,g(f(z)))", Checked){
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))
    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)
    val y = vargen(s.i)
    val z = vargen(s.i)

    val t1 : Term = mkTermApp(f , Seq(x, mkTermApp(g, y)))
    val t2 : Term = mkTermApp(f , Seq(a, mkTermApp(g, mkTermApp(f, z))))

    val result = FOMatching.decideMatch(t1, t2)

    assertResult(true)(result)
  }

  test("f(x,g(y)) = f(a,g(f(z))) unifier", Checked){
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))
    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)
    val y = vargen(s.i)
    val z = vargen(s.i)

    val t1 : Term = mkTermApp(f , Seq(x, mkTermApp(g, y)))
    val t2 : Term = mkTermApp(f , Seq(a, mkTermApp(g, mkTermApp(f, z))))

    val expectedSubst: Subst = Subst.fromMap(Map(1 -> a, 2 -> mkTermApp(f, z)))
    val result = FOMatching.matches(t1, t2)

    assertResult(true)(result.isDefined)
    assertResult(expectedSubst)(result.get)
  }

  test("f(x,g(a)) = f(a,g(z))", Checked){
    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))
    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)
    val y = vargen(s.i)
    val z = vargen(s.i)

    val t1 : Term = mkTermApp(f , Seq(x, mkTermApp(g, a)))
    val t2 : Term = mkTermApp(f , Seq(a, mkTermApp(g, z)))

    val result = FOMatching.decideMatch(t1, t2)

    assertResult(false)(result)
  }

  test("(f(a) = x) = (f(a) = g(a))", Checked){
    import leo.datastructures.{=== => EQ}

    val s = getFreshSignature
    val a = mkAtom(s.addUninterpreted("a",s.i))
    val f = mkAtom(s.addUninterpreted("f", s.i ->: s.i))
    val g = mkAtom(s.addUninterpreted("g", s.i ->: s.i))

    val vargen = freshVarGenFromBlank
    val x = vargen(s.i)

    val t1 : Term = EQ(mkTermApp(f , a), x)
    val t2 : Term = EQ(mkTermApp(f , a), mkTermApp(g, a))

    val result = FOMatching.decideMatch(t1, t2)

    assertResult(true)(result)
  }
}