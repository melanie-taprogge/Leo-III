package leo.modules.output.LPoutput

import leo.datastructures.Literal.{asTerm, vars}
import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.LPoutput.Encodings._
import leo.datastructures.{Clause, ClauseProxy, Literal, Signature, Term}
import leo.modules.HOLSignature._
import leo.modules.calculus.BoolExt
import leo.modules.output.intToName
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.LPoutput.Transformations._


object lpUseful {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// USEFUL TERMS //////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  object Identity extends lpTerm{
    val x1 = lpUntypedVar(lpConstantTerm("x"))
    val definition = lpLambdaTerm(Seq(x1),x1)

    override def pretty: String = definition.pretty
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// APPLY DEDUCTION RULES /////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def applyToEqualityTerm(ty: lpOlType, lhs: lpOlTerm, rhs: lpOlTerm, eqTermName: lpTerm, p: lpOlTerm, prfPlhsName: Option[lpTerm]): lpFunctionApp = {
    // todo: I think I can remove this whole funciton and instead directly instanciate terms...
    if (reducedLogic) {
      val args = if (prfPlhsName.isDefined) Seq(lhs,rhs,eqTermName,p,prfPlhsName.get) else Seq(lhs,rhs,eqTermName,p)
      //lpFunctionApp(lpConstantTerm("=def"),args)
      eqDef().instanciate(ty.lift2Poly,lhs,rhs,Some(eqTermName),Some(p),prfPlhsName)
    }
    else {
      val args = if (prfPlhsName.isDefined) Seq(p,prfPlhsName.get) else Seq(p)
      lpFunctionApp(eqTermName,args)
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// TRANSFORMATIONS ///////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class transformations extends lpDefinedRules

  case class flipLiteral(polarity: Boolean) extends transformations {

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")

    override def name: lpConstantTerm = {
      if (polarity) lpConstantTerm("flipPosLiteral")
      else lpConstantTerm("flipNegLiteral")
    }

    // flipLiteralPosEq [T] x y: Prf(= [mono o] (= [T] x y) (= [T] y x))
    // flipLiteralNegEq [T] x y: Prf(= [mono o] (¬ (= [T] x y)) (¬ (= [T] y x)))

    override def ty: lpMlType = {
      if (polarity) lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,x,y),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,y,x)).prf
      else lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,x,y)),lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,y,x))).prf
    }

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x, y), ty)

    // todo: encode properly
    override def proof: lpProofScript = {
      if (polarity) lpProofScript(Seq(lpProofScriptCommentLine("this is not properly encoded yet\n    assume T x y;\n    have H1: Prf(= [T] x y) → Prf(= [T] y x)\n        {assume h;\n        symmetry;\n        refine h};\n    have H2: Prf(= [T] y x) → Prf(= [T] x y)\n        {assume h;\n        symmetry;\n        refine h};\n    refine propExt (= [T] x y) (= [T] y x) H1 H2")))
      else lpProofScript(Seq(lpProofScriptCommentLine("this is not properly encoded yet\n    assume T x y;\n    have H1: Prf ¬(= [T] x y) → Prf ¬(= [T] y x)\n        {assume h;\n        have H1_1: Prf(= [T] y x) → Prf(= [T] x y)\n            {assume h1;\n            symmetry;\n            refine h1};\n        have H1_2: Prf(= [T] y x) → Prf(⊥)\n            {assume h1;\n            refine ¬E (= [T] x y) (H1_1 h1) h};\n        refine ¬I (= [T] y x) H1_2};\n\n    have H2: Prf ¬(= [T] y x) → Prf ¬(= [T] x y)\n        {assume h;\n        have H2_1: Prf(= [T] x y) → Prf(= [T] y x)\n            {assume h1;\n            symmetry;\n            refine h1};\n        have H2_2: Prf(= [T] x y) → Prf(⊥)\n            {assume h1;\n            refine ¬E (= [T] y x) (H2_1 h1) h};\n\n        refine ¬I (= [T] x y) H2_2};\n\n    refine propExt (¬(= [T] x y)) (¬(= [T] y x)) H1 H2")))
    }

    override def pretty: String = lpDefinition(name, Seq(x, y), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, prfXeqY0: Option[lpTerm]): lpFunctionApp = {
      val prfXeqY = prfXeqY0 match {
        case Some(prfTerm) => Seq(prfTerm)
        case None => Seq()
      }
      lpFunctionApp(name, Seq(x0, y0) ++ prfXeqY)
    }

    def res(T0: lpOlPolyType, x0: lpOlTerm, y0: lpOlTerm)= { // todo unite encoding with type
      if (polarity) lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, x0)
      else lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, x0))
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// NATURAL DEDUCTION RULES ///////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class lpBasicRules extends lpDefinedRules

  case class eqDef() extends lpBasicRules {

    val T = lpOlUserDefinedPolyType("T")
    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")
    val p = lpOlConstantTerm("p")

    override def name: lpConstantTerm = lpConstantTerm("=def")

    // =def [T] x y: Prf (= [T] x y) → Π (p: Els T → Prop), Prf (p y) → Prf (p x)
    override def ty: lpMlType = lpMlFunctionType(Seq(lpOlTypedBinaryConnectiveTerm(lpEq,T,x,y).prf,lpMlDependType(Seq(lpTypedVar(p,lpMlFunctionType(Seq(T.lift2Meta,lpOtype.lift2Meta)))),lpMlFunctionType(Seq(lpOlFunctionApp(p,Seq(y)).prf,lpOlFunctionApp(p,Seq(x)).prf)))))

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x, y), ty, Seq(T))

    // todo: encode properly
    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("this is not properly encoded yet\n    assume T x y h1 p h2;\n    have H : Prf (= [T] y x)\n        {have H_2: Prf(= [T] x x)\n            {assume p2 h3;\n            refine h3};\n        refine (h1 (λ z, = [T] z x)) H_2};\n    refine H p h2")))

    override def pretty: String = s"${lpDefinition(name, Seq(x, y), ty, proof, Seq(T)).pretty}builtin \"eqind\" ≔ ${name.pretty};\n" //todo: pass linking to builtin differently

    def instanciate(T0: lpOlPolyType, x0: lpOlTerm, y0: lpOlTerm, prfXeqY0: Option[lpTerm], p0: Option[lpOlTerm], prfPy0: Option[lpTerm]): lpFunctionApp = {
      val prfXeqY = prfXeqY0 match {
        case Some(prfTerm) => Seq(prfTerm)
        case None => Seq()}
      val p = p0 match {
        case Some(term) => Seq(term)
        case None => Seq()}
      val prfPy = prfPy0 match {
        case Some(prfTerm) => Seq(prfTerm)
        case None => Seq()}
      lpFunctionApp(name, Seq(x0, y0) ++ prfXeqY ++ p ++ prfPy,Seq(T0))
    }
  }

  case class eqRef() extends lpBasicRules {

    val T = lpOlUserDefinedPolyType("T")
    val x = lpOlConstantTerm("x")

    override def name: lpConstantTerm = lpConstantTerm("=ref")

    // =ref [T] x : Prf(= [T] x x)
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,T,x,x).prf

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x), ty, Seq(T))

    // todo: encode properly
    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("this is not properly encoded yet\n    assume T x p h;\n    refine h")))

    override def pretty: String = lpDefinition(name, Seq(x), ty, proof, Seq(T)).pretty
  }

  case class orIl() extends lpBasicRules {
    // x y : Prf x → Prf(x ∨ y)

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")
    override def name: lpConstantTerm = lpConstantTerm("∨Il")

    override def ty: lpMlType = lpMlFunctionType(Seq(x.prf,lpOlUntypedBinaryConnectiveTerm(lpOr,x,y).prf))
    override def dec: lpDeclaration = lpDeclaration(name, Seq(x,y), ty)
    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("not properly encoded yet\n    assume x y h1 b h2 h3;\n    refine h2 h1")))
    override def pretty: String = lpDefinition(name, Seq(x,y), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, PrfX: Option[lpTerm]): lpFunctionApp = {
      val arg = PrfX match {
        case Some(prfTerm) => Seq(prfTerm)
        case None => Seq()
      }
      lpFunctionApp(name, Seq(x0,y0) ++ arg)
    }
  }

  case class orIr() extends lpBasicRules {
    // x y :Prf y → Prf(x ∨ y)

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")

    override def name: lpConstantTerm = lpConstantTerm("∨Ir")

    override def ty: lpMlType = lpMlFunctionType(Seq(y.prf, lpOlUntypedBinaryConnectiveTerm(lpOr, x, y).prf))

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x, y), ty)

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("not properly encoded yet\n    assume x y h1 b h2 h3;\n    refine h3 h1")))

    override def pretty: String = lpDefinition(name, Seq(x, y), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, PrfY: Option[lpTerm]): lpFunctionApp = {
      val arg = PrfY match {
        case Some(prfTerm) => Seq(prfTerm)
        case None => Seq()
      }
      lpFunctionApp(name, Seq(x0, y0) ++ arg)
    }
  }

  case class orE() extends lpBasicRules {
    // x y z : (Prf  x → Prf z) → (Prf y → Prf z) → (Prf (x ∨ y) → Prf z)

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")
    val z = lpOlConstantTerm("z")

    override def name: lpConstantTerm = lpConstantTerm("∨E")

    override def ty: lpMlType = lpMlFunctionType(Seq(lpMlFunctionType(Seq(x.prf,z.prf)),lpMlFunctionType(Seq(y.prf,z.prf)),lpOlUntypedBinaryConnectiveTerm(lpOr, x, y).prf,z.prf))

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x, y, z), ty)

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("not properly encoded yet\n    assume x y z h1 h2 h3;\n    refine h3 z h1 h2")))

    override def pretty: String = lpDefinition(name, Seq(x, y, z), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, z0: lpOlTerm, PrfXZ: Option[lpTerm] = None, PrfYZ: Option[lpTerm] = None, PrfXorY: Option[lpTerm] = None): lpFunctionApp = {
      var args: Seq[lpTerm] = Seq(x0, y0, z0)
      if(PrfXZ.isDefined) args = args :+ PrfXZ.get
      if(PrfYZ.isDefined) args = args :+ PrfYZ.get
      if(PrfXorY.isDefined) args = args :+ PrfXorY.get
      lpFunctionApp(name, args)
    }
  }






















}
