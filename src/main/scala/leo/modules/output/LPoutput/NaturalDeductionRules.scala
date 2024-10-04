package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._

/**
  * Representations of the rules of natural deduction and some additional fundamental rules
  *
  * @author Melanie Taprogge
  */

//todo: add the remaining rules and encode proofs properly

object NaturalDeductionRules {

  val allNDDecs = "///////////////////////////////////////////////////////////////////////////////////////\n////////////////////////////// NATURAL DEDUCTION RULES ////////////////////////////////\n///////////////////////////////////////////////////////////////////////////////////////\n\nsymbol ⇒I : Π x: Prop, Π y: Prop, (Prf x → Prf y) → Prf (x ⇒ y);\n\nsymbol ⇒E : Π x: Prop, Π y: Prop, Prf (x ⇒ y) → Prf x → Prf y;\n\nsymbol ∨Ir : Π x: Prop, Π y: Prop, Prf y → Prf (x ∨ y);\n\nsymbol ∨Il : Π x: Prop, Π y: Prop, Prf x → Prf (x ∨ y);\n\nsymbol ∨E : Π x: Prop, Π y: Prop, Π z: Prop, (Prf x → Prf z) → (Prf y → Prf z) → Prf (x ∨ y) → Prf z;\n\nsymbol ∧I : Π x: Prop, Π y: Prop, Prf x → Prf y → Prf (x ∧ y);\n\nsymbol ∧El : Π x: Prop, Π y: Prop, Prf (x ∧ y) → Prf x;\n\nsymbol ∧Er : Π x: Prop, Π y: Prop, Prf (x ∧ y) → Prf y;\n\nsymbol ¬I : Π x: Prop, (Prf x → Prf ⊥) → Prf (¬ x);\n\nsymbol ¬E : Π x: Prop, Prf x → Prf (¬ x) → Prf ⊥;\n\nsymbol ⊤I : Prf ⊤;\n\nsymbol ⊥E: Π a: Prop, Prf ⊥ → Prf a;\n\nsymbol =def : Π [T: MonoSet], Π x: El T, Π y: El T, Prf (x = y) → Π p: (El T → El o), Prf (p y) → Prf (p x);\n\nsymbol =ref : Π [T: MonoSet], Π x: El T, Prf (x = x);\n\nopaque symbol npp x : Prf(¬ ¬ x) → Prf x ≔\nbegin\n    assume x h1;\n    refine ∨E x (¬ x) x _ _(em x)\n        {assume h2;\n        refine h2}\n        {assume h2;\n        refine ⊥E x (¬E (¬ x) h2 h1)}\nend;\n\n"

  val allNDDefs = "///////////////////////////////////////////////////////////////////////////////////////\n////////////////////////////// NATURAL DEDUCTION RULES ////////////////////////////////\n///////////////////////////////////////////////////////////////////////////////////////\n\nsymbol ⇒I : Π x: Prop, Π y: Prop, (Prf x → Prf y) → Prf (x ⇒ y)\n≔ λ x y h1 h2, h1 h2;\n\nsymbol ⇒E : Π x: Prop, Π y: Prop, Prf (x ⇒ y) → Prf x → Prf y\n≔ λ x y h1 h2, h1 h2;\n\nsymbol ∀I : Π T: MonoSet, Π p: (El T → Prop), (Π x: El T, Prf (p x)) → Prf (`∀ y, p y)\n≔ λ T p h1, h1;\n\nsymbol ∀E : Π T: MonoSet, Π p: (El T → Prop), Prf (`∀ y, p y) → Π x: El T, Prf (p x)\n≔ λ T p h1, h1;\n\nsymbol ∨Ir : Π x: Prop, Π y: Prop, Prf y → Prf (x ∨ y)\n≔ λ x y h1 b _ h3, h3 h1;\n\nsymbol ∨Il : Π x: Prop, Π y: Prop, Prf x → Prf (x ∨ y)\n≔ λ x y h1 b h2 _, h2 h1;\n\nsymbol ∨E : Π x: Prop, Π y: Prop, Π z: Prop, (Prf x → Prf z) → (Prf y → Prf z) → Prf (x ∨ y) → Prf z\n≔ λ x y z h1 h2 h3, h3 z h1 h2;\n\nsymbol ∧I : Π x: Prop, Π y: Prop, Prf x → Prf y → Prf (x ∧ y)\n≔ λ x y h1 h2 b h3, h3 h1 h2;\n\nsymbol ∧El : Π x: Prop, Π y: Prop, Prf (x ∧ y) → Prf x\n≔ λ x y h1, h1 x (λ h2 _, h2);\n\nsymbol ∧Er : Π x: Prop, Π y: Prop, Prf (x ∧ y) → Prf y\n≔ λ x y h1, h1 y (λ _ h3, h3);\n\nsymbol ¬I : Π x: Prop, (Prf x → Prf ⊥) → Prf (¬ x)\n≔ λ x h1 h2, h1 h2;\n\nsymbol ¬E : Π x: Prop, Prf x → Prf (¬ x) → Prf ⊥\n≔ λ x h1 h2, h2 h1;\n\nsymbol ⊤I : Prf ⊤\n≔ λ b h1, h1;\n\nsymbol ⊥E: Π a: Prop, Prf ⊥ → Prf a\n≔ λ a h1, h1 a;\n\nsymbol =def : Π [T: MonoSet], Π x: El T, Π y: El T, Prf (x = y) → Π p: (El T → El o), Prf (p y) → Prf (p x)\n≔ λ T x y h1 p h2, h1 (λ z, z = x) (λ p2 h3, h3) p h2;\n\nsymbol =ref : Π [T: MonoSet], Π x: El T, Prf (x = x)\n≔ λ T x p h, h;\n\n"

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
    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("    assume T x y h1 p h2;\n    have H : Prf (y = x)\n        {have H_2: Prf(x = x)\n            {assume p2 h3;\n            refine h3};\n        refine (h1 (λ z, z = x)) H_2};\n    refine H p h2")))
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

    val T = lpOlUserDefinedMonoType("T")
    val x = lpOlTypedVar(lpOlConstantTerm("x"),T)

    override def name: lpConstantTerm = lpConstantTerm("=ref")

    // =ref [T] x : Prf(= [T] x x)
    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,T,x.name,x).prf

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x), ty, Seq(T))

    // todo: encode properly
    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("    assume T x p h;\n    refine h")))

    override def pretty: String = lpDefinition(name, Seq(x), ty, proof, Seq(T)).pretty
  }

  case class orIl() extends lpBasicRules {
    // x y : Prf x → Prf(x ∨ y)

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")
    override def name: lpConstantTerm = lpConstantTerm("∨Il")

    override def ty: lpMlType = lpMlFunctionType(Seq(x.prf,lpOlUntypedBinaryConnectiveTerm(lpOr,x,y).prf))
    override def dec: lpDeclaration = lpDeclaration(name, Seq(x,y), ty)
    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("    assume x y h1 b h2 h3;\n    refine h2 h1")))
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

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("    assume x y h1 b h2 h3;\n    refine h3 h1")))

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

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("    assume x y z h1 h2 h3;\n    refine h3 z h1 h2")))

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
