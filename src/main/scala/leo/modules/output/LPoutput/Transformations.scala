package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.LPSignature.{HOLtop, Prf, lpPropExt, oType,lpEm}
import leo.modules.output.LPoutput.calculusEncoding.{nameBottom, nameHypothesis, nameX, nameType}
import leo.modules.output.LPoutput.lpDatastructures._

object Transformations {

  // combining rule applications

  def selfImp(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int)) = {
    //throw new Exception("CHANGE selfImp")
    var xCount = parameters._3
    var hCount = parameters._3

    val x1 = nameX(xCount)
    xCount = xCount + 1
    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1

    if (a == lpOlNothing) { // return type Pi x ,Prf x -> Prf x
      val lambdaTerm_str = s"(λ $x1 ($h1: $Prf($x1)), $h1)"
      val lambdaTerm = lpLambdaTerm(Seq(lpUntypedVar(x1),lpTypedVar(h1,x1.prf)),h1)
      (lambdaTerm, (hCount, parameters._2, xCount, parameters._4))
    } else { // return instanciated version
      val lambdaTerm_str = s"((λ $x1 ($h1: $Prf($x1)), $h1)$a)"
      val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpTypedVar(h1,x1.prf)),h1),Seq(a))
      (lambdaTerm, (hCount, parameters._2, xCount, parameters._4))
    }
  }

  def impTrans(a: String, b: String, c: String, prfAimpB: String, prfBimpC: String, parameters: (Int, Int, Int, Int)): (String, (Int, Int, Int, Int), Set[String]) = {
    // Provide a proof of the type  (Prf a → Prf b) → (Prf b → Prf c) → (Prf a → Prf c)
    // todo: replace with proper lp term
    // todo: track used symbols
    // todo: Normalize?
    throw new Exception("CHANGE impTrans")
/*
    var hCount = parameters._1
    var xCount = parameters._3

    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1
    val x3: String = nameX(xCount)
    xCount = xCount + 1
    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3: String = nameHypothesis(hCount)
    hCount = hCount + 1

    val lambdaTerm = s"(((λ $x1 $x2 $x3 ($h1 : Prf $x1 → Prf $x2) ($h2 : Prf $x2 → Prf $x1) $h3, $h2 ($h1 $h3)) $a $b $c) $prfAimpB $prfBimpC)"
    (lambdaTerm, (hCount, parameters._2, xCount), Set())

 */
  }

  def impTrans4(a: lpOlTerm, b: lpOlTerm, c: lpOlTerm, d: lpOlTerm, prfAimpB: lpTerm, prfBimpC: lpTerm, prfCimpD: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type  (Prf a → Prf b) → (Prf b → Prf c) → (Prf a → Prf c)
    // todo: replace with proper lp term
    // todo: track used symbols
    // todo: Normalize?
    //throw new Exception("CHANGE impTrans4")


    var hCount = parameters._1
    var xCount = parameters._3

    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1
    val x3 = nameX(xCount)
    xCount = xCount + 1
    val x4 = nameX(xCount)
    xCount = xCount + 1
    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h4 = nameHypothesis(hCount)
    hCount = hCount + 1

    //val lambdaTerm_str = s"(((λ $x1 $x2 $x3 $x4                                                                                           ($h1 : Prf $x1 → Prf $x2) ($h2 : Prf $x2 → Prf $x3) ($h3 : Prf $x3 → Prf $x4) $h4, $h3 ($h2 ($h1 $h4))) $a $b $c $d) $prfAimpB $prfBimpC $prfCimpD)"

    val lambdaTerm =lpFunctionApp(lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpUntypedVar(x2),lpUntypedVar(x3),lpUntypedVar(x4),lpTypedVar(h1,lpMlFunctionType(Seq(x1.prf,x2.prf))),lpTypedVar(h2,lpMlFunctionType(Seq(x2.prf,x3.prf))),lpTypedVar(h3,lpMlFunctionType(Seq(x3.prf,x4.prf))),lpUntypedVar(h4)),lpFunctionApp(h3,Seq(lpFunctionApp(h2,Seq(lpFunctionApp(h1,Seq(h4))))))),Seq(a,b,c,d)),Seq(prfAimpB,prfBimpC,prfCimpD))
    //val unappliedLambdaTerm = lpLambdaTerm(Seq(lpUntypedVar(x1),lpUntypedVar(x2),lpUntypedVar(x3),lpUntypedVar(x4),lpTypedVar(h1,lpMlFunctionType(Seq(x1.prf,x2.prf))),lpTypedVar(h2,lpMlFunctionType(Seq(x2.prf,x3.prf))),lpTypedVar(h3,lpMlFunctionType(Seq(x3.prf,x4.prf))),lpUntypedVar(h4)),lpFunctionApp(h3,Seq(lpFunctionApp(h2,Seq(lpFunctionApp(h1,Seq(h4)))))))

    //print(s"unapplied lambda Term:\n${unappliedLambdaTerm.pretty}\n")

    (lambdaTerm, (hCount, parameters._2, xCount, parameters._4), Set())

  }



  // changing positions in clauses/ literals

  def eqCom(T: String, a: String, b: String, parameters: (Int, Int, Int, Int)): (String, (Int, Int, Int, Int)) = {
    // Provides proof term of type Prf(eq [T] a b) → Prf(eq [T] b a)
    throw new Exception("CHANGE impTrans4")
    /*
    var xCount = parameters._3
    var hCount = parameters._3

    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1
    val x3: String = nameX(xCount)
    xCount = xCount + 1
    val x4: String = nameX(xCount)
    xCount = xCount + 1
    val x5: String = nameX(xCount)
    xCount = xCount + 1
    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    if ((a == "") & (b == "") & (T == "")) { // return non instanciated version
      val lambdaTerm = s"(λ $x1 $x2 $x3 ($h1 : Prf (eq [$x1] $x2 $x3)), $h1 (λ $x4, eq [$x1] $x4 $x2) (λ $x5 $h2, $h2))"
      (lambdaTerm, (hCount, parameters._2, xCount))
    } else { // return (partly) inst. version
      val lambdaTerm = s"((λ $x1 $x2 $x3 ($h1 : Prf (eq [$x1] $x2 $x3)), $h1 (λ $x4, eq [$x1] $x4 $x2) (λ $x5 $h2, $h2)) ($T) ($a) ($b))"
      (lambdaTerm, (hCount, parameters._2, xCount))
    }

     */
  }

  def inEqCom(T: lpType, a: lpOlTerm, b: lpOlTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int)) = {
    // Provides proof term of type Prf(eq [T] a b) → Prf(eq [T] b a)
    //throw new Exception("CHANGE inEqCom")
    
    var xCount = parameters._3
    var hCount = parameters._1
    var tCount = parameters._4

    val x2 = nameX(xCount)
    xCount = xCount + 1
    val x3 = nameX(xCount)
    xCount = xCount + 1
    val x4 = nameX(xCount)
    xCount = xCount + 1
    val x5 = nameX(xCount)
    xCount = xCount + 1
    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3 = nameHypothesis(hCount)
    hCount = hCount + 1
    val t1 = nameType(tCount)
    tCount = tCount + 1

    val lambdaTerm_unap = lpLambdaTerm(Seq(lpUntypedVar(t1), lpUntypedVar(x2), lpUntypedVar(x3), lpTypedVar(h1, lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, t1, x2, x3)).prf), lpTypedVar(h2, lpOlTypedBinaryConnectiveTerm(lpEq, t1, x3, x2).prf)), lpFunctionApp(h1, Seq(lpFunctionApp(h2, Seq(lpLambdaTerm(Seq(lpUntypedVar(x4)), lpOlTypedBinaryConnectiveTerm(lpEq, t1, x4, x3)), lpLambdaTerm(Seq(lpUntypedVar(x5), lpUntypedVar(h3)), h3))))))

    if ((a == lpOlNothing) & (b == lpOlNothing) & (T == lpOlNothing)) { // return non instanciated version
      //val lambdaTerm_str = s"(λ $x1 $x2 $x3 ($h1 : Prf (¬ (eq [$x1] $x2 $x3))) ($h2 : Prf (eq [$x1] $x3 $x2)),                                                                                                           $h1 ($h2 (λ $x4, eq [$x1] $x4 $x3)                                                                                             (λ $x5 $h3, $h3)))"
      (lambdaTerm_unap, (hCount, parameters._2, xCount, tCount))
    } else { // return (partly) inst. version
      //val lambdaTerm_str = s"((λ $x1 $x2 $x3 ($h1 : Prf (¬ (eq [$x1] $x2 $x3))) ($h2 : Prf (eq [$x1] $x3 $x2)), $h1 ($h2 (λ $x4, eq [$x1] $x4 $x3) (λ $x5 $h3, $h3))) ($T) ($a) ($b))"
      val lambdaTerm = lpFunctionApp(lambdaTerm_unap,Seq(T,a,b))
      (lambdaTerm, (hCount, parameters._2, xCount, tCount))
    }
    
  }


  // encoding non equational literals as equational and vice versa

  def mkNegPropNegLit(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type  Prf(¬ a) → Prf(eq [↑ o] a ⊥)
    // todo: replace with proper lp term
    // todo: track used symbols
    //throw new Exception("CHANGE inEqCom")


    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1
    val b1 = nameBottom(bCount)
    bCount = bCount + 1
    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3 = nameHypothesis(hCount)
    hCount = hCount + 1

    val lambdaTerm_str = s"((λ $x1 $h1 ($h2 : Prf (eq [↑ o] $x1 ⊤)), $h2                                                                  (λ $x2, ¬ $x2) $h1 (λ $b1 $h3, $h3)) $a)"
    val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpUntypedVar(h1),lpTypedVar(h2,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x1,lpOlTop).prf)),lpFunctionApp(h2,Seq(lpLambdaTerm(Seq(lpUntypedVar(x2)),lpOlUnaryConnectiveTerm(lpNot,x2)),h1,lpLambdaTerm(Seq(lpUntypedVar(b1),lpUntypedVar(h3)),h3)))),Seq(a))

    //print(s"mkneg lambda: \n${lambdaTerm.pretty}\n")

    (lambdaTerm, (hCount, bCount, xCount, parameters._4), Set())

  }

  def mkNegPropPosLit(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type Prf(¬ a) → Prf(eq [↑ o] (¬ a) ⊤)
    // todo: replace with proper lp term
    // todo: track used symbols
    //throw new Exception("CHANGE mkNegPropPosLit")

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1 = nameBottom(bCount)
    bCount = bCount + 1
    val x1 = nameX(xCount)
    xCount = xCount + 1

    //val lambdaTerm_str = s"((λ $x1 $h1, propExt (¬ $x1) ⊤                                                                                                                   (λ _ $b1 $h2, $h2) (λ _, $h1)) $a)"
    val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpUntypedVar(h1)),lpFunctionApp(lpPropExt.name,Seq(lpOlUnaryConnectiveTerm(lpNot,x1),lpOlTop,lpLambdaTerm(Seq(lpUntypedVar(lpWildcard),lpUntypedVar(b1),lpUntypedVar(h2)),h2),lpLambdaTerm(Seq(lpUntypedVar(lpWildcard)),h1)))),Seq(a))

    (lambdaTerm, (hCount, bCount, xCount, parameters._4), Set(lpPropExt))

  }

  case class mkNegPropPosLit_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(¬ a) → Prf(= [mono o] (¬ a) ⊤)

    override def name: lpConstantTerm = lpConstantTerm("mkNegPropPosEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm(patternVarName)), lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm(patternVarName)), lpOlTop)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def transformLit(x0: lpOlTerm): (lpOlTerm,lpOlTerm,lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop),lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop)

  }

  case class mkNegPropNegLit_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [mono o] (¬ a) (¬ (= [mono o] a ⊤)))

    override def name: lpConstantTerm = lpConstantTerm("mkNegPropNegEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName)), lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlTop))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def transformLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop)), x0, lpOlTop)

  }

  case class mkNegLitPosProp_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [mono o] (¬ (= [mono o] (¬ a) ⊤)) a)

    override def name: lpConstantTerm = lpConstantTerm("mkNegLitPosPropEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm(patternVarName)),lpOlTop)),lpOlConstantTerm(patternVarName)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkNegLitPosProp_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def instanciate(x0: lpOlTerm) = lpFunctionApp(name, Seq(x0))

    def transformLit(x0: lpOlTerm): (lpOlTerm) = x0

  }

  case class mkNegLitNegProp_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [mono o] (¬ (= [mono o] a ⊤)) (¬ a))

    override def name: lpConstantTerm = lpConstantTerm("mkNegLitNegPropEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlConstantTerm(patternVarName), lpOlTop)), lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkNegLitPosProp_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def instanciate(x0: lpOlTerm) = lpFunctionApp(name, Seq(x0))

    def transformLit(x0: lpOlTerm): (lpOlTerm) = lpOlUnaryConnectiveTerm(lpNot, x0)

  }

  case class mkPosLitNegProp_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [mono o] (= [mono o] (¬ a) ⊤) (¬ a))

    override def name: lpConstantTerm = lpConstantTerm("mkPosLitNegPropEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName)), lpOlTop), lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosLitNegProp_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def instanciate(x0: lpOlTerm) = lpFunctionApp(name, Seq(x0))

    def transformLit(x0: lpOlTerm): (lpOlTerm) =  lpOlUnaryConnectiveTerm(lpNot, x0)

  }

  case class mkNegPropEqBot_script(patternVarName: String = "x") extends lpDefinedRules {

    override def name: lpConstantTerm = lpConstantTerm("mkNegPropEqBot")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName)), lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlBot)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkNegPropEqBot_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty
  }

  def mkPosPropNegLit(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type Prf(a) → Prf(¬(eq [↑ o] (¬ a) ⊤))
    // todo: replace with proper lp term
    // todo: track used symbols
    //throw new Exception("CHANGE mkNegPropPosLit")

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3 = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1 = nameBottom(bCount)
    bCount = bCount + 1
    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1
    //val lambdaTerm_str = s"((λ $x1 $h1 ($h2 : Prf (eq [↑ o] (¬ $x1) ⊤)),                                                                                                                           $h2 (λ $x2, ¬ $x2) (λ $b1, $b1 $h1)                                                                                                  (λ $b1 $h3, $h3)) $a)"
    val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpUntypedVar(h1),lpTypedVar(h2,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUnaryConnectiveTerm(lpNot,x1),lpOlTop).prf)),lpFunctionApp(h2,Seq(lpLambdaTerm(Seq(lpUntypedVar(x2)),lpOlUnaryConnectiveTerm(lpNot,x2)),lpLambdaTerm(Seq(lpUntypedVar(b1)),lpFunctionApp(b1,Seq(h1))),lpLambdaTerm(Seq(lpUntypedVar(b1),lpUntypedVar(h3)),h3)))),Seq(a))
    (lambdaTerm, (hCount, bCount, xCount, parameters._4), Set())

  }

  case class mkPosPropNegLit_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [mono o] a (¬(= [mono o] (¬ a) ⊤)))

    override def name: lpConstantTerm = lpConstantTerm("mkPosPropNegEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm(patternVarName)), lpOlTop))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    //def instanciate():lpFunctionApp =
    def transformLit(x0: lpOlTerm): (lpOlTerm,lpOlTerm,lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop)),lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop)
  }

  case class mkPosPropPos_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [mono o] a (= [mono o] a ⊤))

    override def name: lpConstantTerm = lpConstantTerm("mkPosPropPosEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlTop)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    //def instanciate():lpFunctionApp =
    def transformLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop), x0, lpOlTop)
  }

  def mkPosPropPosLit(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type Prf(a) → Prf(eq [↑ o] a ⊤)
    // todo: replace with proper lp term
    // todo: track used symbols
    //throw new Exception("CHANGE mkPosPropPosLit")

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1 = nameBottom(bCount)
    bCount = bCount + 1
    val x1 = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm_str = s"((λ $x1 $h1, propExt $x1 ⊤ (λ _ $b1 $h2, $h2) (λ _, $h1)) $a)"
    val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpUntypedVar(h1)),lpFunctionApp(lpPropExt.name,Seq(x1,lpOlTop,lpLambdaTerm(Seq(lpUntypedVar(lpWildcard),lpUntypedVar(b1),lpUntypedVar(h2)),h2),lpLambdaTerm(Seq(lpUntypedVar(lpWildcard)),h1)))),Seq(a))
    (lambdaTerm, (hCount, bCount, xCount, parameters._4), Set(lpPropExt))

  }

  case class mkPosPropPosLit_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(a) → Prf(eq [↑ o] a ⊤)

    override def name: lpConstantTerm = lpConstantTerm("mkPosPropPosEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlConstantTerm(patternVarName),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlConstantTerm(patternVarName),lpOlTop)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name,Seq(lpUntypedVar(lpConstantTerm(patternVarName))),ty)

    override def pretty: String = lpDefinition(name,Seq(lpUntypedVar(lpConstantTerm(patternVarName))),ty,proof).pretty
  }

  def mkPosLitNegProp(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type Prf(eq [↑ o] (¬ a) ⊤) → Prf (¬ a)
    // todo: replace with proper lp term
    // todo: track used symbols
    //throw new Exception("CHANGE mkPosLitNegProp")

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3 = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1 = nameBottom(bCount)
    bCount = bCount + 1
    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1

    //val lambdaTerm_str = s"((λ $x1 ($h1 : Prf (eq [↑ o] (¬ $x1) ⊤)),                                                                        em (¬ $x1) (¬ $x1)                                                                                                            (λ $h2, $h2)                           (λ $h2, $h1 (λ $x2, ¬ $x2) $h2                                                                                                   (λ $b1 $h3, $h3) (¬ $x1))) $a)"
    val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpTypedVar(h1,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUnaryConnectiveTerm(lpNot,x1),lpOlTop).prf)),lpFunctionApp(lpEm.name,Seq(lpOlUnaryConnectiveTerm(lpNot,x1),lpOlUnaryConnectiveTerm(lpNot,x1),lpLambdaTerm(Seq(lpUntypedVar(h2)),h2),lpLambdaTerm(Seq(lpUntypedVar(h2)),lpFunctionApp(h1,Seq(lpLambdaTerm(Seq(lpUntypedVar(x2)),lpOlUnaryConnectiveTerm(lpNot,x2)),h2,lpLambdaTerm(Seq(lpUntypedVar(b1),lpUntypedVar(h3)),h3),lpOlUnaryConnectiveTerm(lpNot,x1))))))),Seq(a))
    (lambdaTerm, (hCount, bCount, xCount, parameters._4), Set(lpEm))
  }

  def mkPosLitPosProp(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type Prf(eq [↑ o] a ⊤) → Prf a
    // todo: replace with proper lp term
    // todo: track used symbols
    //throw new Exception("CHANGE mkPosLitPosProp")

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3 = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1 = nameBottom(bCount)
    bCount = bCount + 1
    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm_str = s"((λ $x1 ($h1 : Prf (eq [↑ o] $x1 ⊤)),                                                                                em $x1 $x1 (λ $h2, $h2)                                                     (λ $h2, $h1 (λ $x2, ¬ $x2) $h2                                                                                    (λ $b1 $h3, $h3) $x1)) $a)"
    val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpTypedVar(h1,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x1,lpOlTop).prf)),lpFunctionApp(lpEm.name,Seq(x1, x1, lpLambdaTerm(Seq(lpUntypedVar(h2)),h2), lpLambdaTerm(Seq(lpUntypedVar(h2)),lpFunctionApp(h1, Seq(lpLambdaTerm(Seq(lpUntypedVar(x2)),lpOlUnaryConnectiveTerm(lpNot,x2)), h2, lpLambdaTerm(Seq(lpUntypedVar(b1),lpUntypedVar(h3)),h3),x1)))))),Seq(a))
    (lambdaTerm, (hCount, bCount, xCount, parameters._4), Set(lpEm))

  }

  def mkNegLitNegProp(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type Prf(¬ (eq [↑ o] a ⊤)) → Prf(¬ a)
    // todo: replace with proper lp term
    // todo: track used symbols
    //throw new Exception("CHANGE mkPosLitPosProp")

    var hCount = parameters._1
    var xCount = parameters._3

    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1
    val x3 = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm_str = s"((λ $x1 ($h1 : Prf (¬ (eq [↑ o] $x1 ⊤))) $h2, $h1                                                                                                                          (propExt $x1 ⊤ (λ _ $x2 $x3, $x3) (λ _, $h2))) $a)"
    val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpTypedVar(h1,lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,x1,lpOlTop)).prf),lpUntypedVar(h2)),lpFunctionApp(h1, Seq(lpFunctionApp(lpPropExt.name, Seq(x1,lpOlTop,lpLambdaTerm(Seq(lpUntypedVar(lpWildcard),lpUntypedVar(x2),lpUntypedVar(x3)),x3),lpLambdaTerm(Seq(lpUntypedVar(lpWildcard)),h2)))))),Seq(a))
    (lambdaTerm, (hCount, parameters._2, xCount, parameters._4), Set(lpPropExt))

  }

  def mkNegLitPosProp(a: lpTerm, parameters: (Int, Int, Int, Int)): (lpTerm, (Int, Int, Int, Int), Set[lpStatement]) = {
    // Provide a proof of the type Prf(¬ (eq [↑ o] (¬ a) ⊤)) → Prf a
    // todo: replace with proper lp term
    // todo: track used symbols
    //throw new Exception("CHANGE mkNegLitPosProp")

    var hCount = parameters._1
    var xCount = parameters._3

    val h1 = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2 = nameHypothesis(hCount)
    hCount = hCount + 1
    val x1 = nameX(xCount)
    xCount = xCount + 1
    val x2 = nameX(xCount)
    xCount = xCount + 1

    //val lambdaTerm_str = s"((λ $x1 ($h1 : Prf (¬ (eq [↑ o] (¬ $x1) ⊤))),                                                                                                                                      em $x1 $x1 (λ $h2, $h2)                                                     (λ $h2, $h1 (propExt (¬ $x1) ⊤                                                                                                  (λ _ $x1 $x2, $x2) (λ _, $h2)) $x1)) $a)"
    val lambdaTerm = lpFunctionApp(lpLambdaTerm(Seq(lpUntypedVar(x1),lpTypedVar(h1,lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlUnaryConnectiveTerm(lpNot,x1),lpOlTop)).prf)),lpFunctionApp(lpEm.name,Seq(x1, x1, lpLambdaTerm(Seq(lpUntypedVar(h2)),h2),lpLambdaTerm(Seq(lpUntypedVar(h2)),lpFunctionApp(h1,Seq(lpFunctionApp(lpPropExt.name, Seq(lpOlUnaryConnectiveTerm(lpNot,x1),lpOlTop,lpLambdaTerm(Seq(lpUntypedVar(lpWildcard),lpUntypedVar(x1),lpUntypedVar(x2)),x2),lpLambdaTerm(Seq(lpUntypedVar(lpWildcard)),h2))),x1)))))),Seq(a))
    (lambdaTerm, (hCount, parameters._2, xCount, parameters._4), Set(lpPropExt, lpEm))

  }

}
