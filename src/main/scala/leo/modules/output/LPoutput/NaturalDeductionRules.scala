package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._



object NaturalDeductionRules {


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// NATURAL DEDUCTION RULES ///////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class lpBasicRules extends lpDefinedRules

  case class eqDef() extends lpBasicRules {

    val T = lpOlUserDefinedMonoType("T")
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
