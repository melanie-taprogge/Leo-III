package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures._

/** Definitions of the Inferences rules of the calculus EP
  *
  * @author Melanie Taprogge
  */

object lpInferenceRuleEncoding {

  ////////////////////////////////////////////////////////////////
  ////////// Primary Inference Rules
  ////////////////////////////////////////////////////////////////

  case class eqFactoring_script(polarity: Boolean) extends lpNameRef {

    override def name: lpConstantTerm = {
      val pol = if (polarity) "_p" else "_n"
      lpConstantTerm(s"EqFact$pol")
    }

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, z0: lpOlTerm, v0: lpOlTerm, T0: lpOlPolyType): lpFunctionApp = {
      lpFunctionApp(name, Seq(x0, y0, z0, v0), Seq(T0))
    }

    def result(x0: lpOlTerm, y0: lpOlTerm, z0: lpOlTerm, v0: lpOlTerm, T0: lpOlPolyType): Seq[lpOlTerm] = {
      if (polarity) { //todo: mane both these terms and the rhs of the rule depend on one defined version
        Seq(lpOlTypedBinaryConnectiveTerm(lpEq, T0, x0, y0), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, x0, z0)), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, v0)))
      } else {
        Seq(lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, x0, y0)), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, x0, z0)), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, v0)))
      }
    }
  }


  ////////////////////////////////////////////////////////////////
  ////////// Extensionality
  ////////////////////////////////////////////////////////////////

  case class encPFE() extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm(s"PFE")

    def instanciate(TS0:Option[(lpOlPolyType,lpOlPolyType)],f:lpOlTerm,g:lpOlTerm,x:lpOlTerm):lpFunctionApp ={
      val ImpArgs = TS0 match {
        case Some((t,s)) => Seq(t,s)
        case None => Seq.empty
      }
      lpFunctionApp(name,Seq(f,g):+x,ImpArgs)
    }
    def premAndRes(T: lpOlType, S: lpOlType, f : lpOlTerm, g : lpOlTerm, x : lpOlTerm) = {
      val prem = lpOlTypedBinaryConnectiveTerm(lpEq,lpOlFunctionType(Seq(T,S)),f,g)
      val res = lpOlTypedBinaryConnectiveTerm(lpEq,lpOlFunctionType(Seq(T,S)),lpOlFunctionApp(f,Seq(Left(x))),lpOlFunctionApp(g,Seq(Left(x))))
      (prem, res)
    }
  }

  case class boolExt(lhsNeg: Boolean, polarity: Boolean) extends lpNameRef {

    override def name: lpConstantTerm = {
      val pol = if (polarity) "P" else "N"
      val category = {
        if (polarity & lhsNeg) "_l"
        else if (polarity & !lhsNeg) "_r"
        else if (!polarity & lhsNeg) "_p"
        else "_n"
      }
      lpConstantTerm(s"${pol}BE$category")
    }

    def instanciate(x0: lpOlTerm, y0: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(x0,y0))
    }
  }


  ////////////////////////////////////////////////////////////////
  ////////// Additional Leo-III Inferences
  ////////////////////////////////////////////////////////////////

  case object polaritySwitchEqLit extends lpNameRef {
    // in non eq case, we use simp 17, for equational case this is encoded
    // todo: update to standard library
    // a b : π ((a = b) = ((¬ a) = (¬ b)))

    override def name: lpConstantTerm = lpConstantTerm(s"polaritySwitchEqLit")

    def instanciate(a: lpOlTerm, b: lpOlTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(a,b))
    }
  }

  ////////////////////////////////////////////////////////////////
  ////////// Meta-Theorem
  ////////////////////////////////////////////////////////////////

  case object  metaPermutation extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm(s"permute")

    def instanciate(σ: Seq[Int], c: Seq[lpOlTerm], before: lpTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(lpList(σ.map(indx => lpNum(indx))), lpList(c), lpOlTop_i, before))
    }
  }

  case object metaDeletion extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm(s"delete")
    def instanciate(c: Seq[lpOlTerm], indxList: Seq[Int], before: lpTerm): lpFunctionApp = {
      val outputIndx = indxList.distinct
      lpFunctionApp(name, Seq(lpList(indxList.map(indx => lpNum(indx))), lpList(outputIndx.map(indx => lpNum(indx))), lpList(c), lpOlTop_i, before))
    }
  }

  case object metaTransform extends lpNameRef {
    override def name: lpConstantTerm = lpConstantTerm(s"transform")
    def instanciate(c: Seq[lpOlTerm], n: Int, rule: lpTerm, before: lpTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(lpList(c), lpNum(n), rule, before))
    }
  }

  case object metaSelect extends lpNameRef {

    override def name: lpConstantTerm = lpConstantTerm(s"∧ₑₙ")

    def instanciate(c: Seq[lpOlTerm], n: Int, before: lpTerm): lpFunctionApp = {
      lpFunctionApp(name, Seq(lpNum(n), lpList(c), lpOlTop_i, before))
    }
  }


}
