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
    if (reducedLogic) {
      val args = if (prfPlhsName.isDefined) Seq(lhs,rhs,eqTermName,p,prfPlhsName.get) else Seq(lhs,rhs,eqTermName,p)
      lpFunctionApp(lpConstantTerm("=def"),args)
    }
    else {
      val args = if (prfPlhsName.isDefined) Seq(p,prfPlhsName.get) else Seq(p)
      lpFunctionApp(eqTermName,args)
    }
  }




  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// NATURAL DEDUCTION RULES ///////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class lpNaturalDeduction extends lpDefinedRules

  case class orIl() extends lpDefinedRules{
    // x y : Prf x → Prf(x ∨ y)

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")
    override def name: String = "∨Il"

    override def ty: lpMlType = lpMlFunctionType(Seq(x.prf,lpOlUntypedBinaryConnectiveTerm(lpOr,x,y).prf))
    override def dec: lpDeclaration = lpDeclaration(lpConstantTerm(name), Seq(x,y), ty)
    override def proof: lpProofScript = throw new Exception("proof for natural deduction rules not encoded yet")
    override def pretty: String = lpDefinition(lpConstantTerm(name), Seq(x,y), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, PrfX: Option[lpTerm]): lpFunctionApp = {
      val arg = PrfX match {
        case Some(prfTerm) => Seq(prfTerm)
        case None => Seq()
      }
      lpFunctionApp(lpConstantTerm(name), Seq(x0,y0) ++ arg)
    }
  }

  case class orIr() extends lpDefinedRules {
    // x y :Prf y → Prf(x ∨ y)

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")

    override def name: String = "∨Ir"

    override def ty: lpMlType = lpMlFunctionType(Seq(y.prf, lpOlUntypedBinaryConnectiveTerm(lpOr, x, y).prf))

    override def dec: lpDeclaration = lpDeclaration(lpConstantTerm(name), Seq(x, y), ty)

    override def proof: lpProofScript = throw new Exception("proof for natural deduction rules not encoded yet")

    override def pretty: String = lpDefinition(lpConstantTerm(name), Seq(x, y), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, PrfY: Option[lpTerm]): lpFunctionApp = {
      val arg = PrfY match {
        case Some(prfTerm) => Seq(prfTerm)
        case None => Seq()
      }
      lpFunctionApp(lpConstantTerm(name), Seq(x0, y0) ++ arg)
    }
  }

  case class orE() extends lpDefinedRules {
    // x y z : (Prf  x → Prf z) → (Prf y → Prf z) → (Prf (x ∨ y) → Prf z)

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")
    val z = lpOlConstantTerm("z")

    override def name: String = "∨E"

    override def ty: lpMlType = lpMlFunctionType(Seq(lpMlFunctionType(Seq(x.prf,z.prf)),lpMlFunctionType(Seq(y.prf,z.prf)),lpOlUntypedBinaryConnectiveTerm(lpOr, x, y).prf,z.prf))

    override def dec: lpDeclaration = lpDeclaration(lpConstantTerm(name), Seq(x, y, z), ty)

    override def proof: lpProofScript = throw new Exception("proof for natural deduction rules not encoded yet")

    override def pretty: String = lpDefinition(lpConstantTerm(name), Seq(x, y, z), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, z0: lpOlTerm, PrfXZ: Option[lpTerm] = None, PrfYZ: Option[lpTerm] = None, PrfXorY: Option[lpTerm] = None): lpFunctionApp = {
      var args: Seq[lpTerm] = Seq(x0, y0, z0)
      if(PrfXZ.isDefined) args = args :+ PrfXZ.get
      if(PrfYZ.isDefined) args = args :+ PrfYZ.get
      if(PrfXorY.isDefined) args = args :+ PrfXorY.get
      lpFunctionApp(lpConstantTerm(name), args)
    }
  }






















}
