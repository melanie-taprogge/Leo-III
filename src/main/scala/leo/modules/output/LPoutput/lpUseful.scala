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


}
