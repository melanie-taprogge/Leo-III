package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.LPSignature.Prf
import leo.modules.output.LPoutput.calculusEncoding.{nameHypothesis, nameBottom, nameX}
import leo.modules.output.LPoutput.lpDatastructures._

object Transformations {

  // combining rule applications

  def selfImp(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int)) = {

    var xCount = parameters._3
    var hCount = parameters._3

    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1

    if (a == "") { // return type Pi x ,Prf x -> Prf x
      val lambdaTerm = s"(λ $x1 ($h1: $Prf($x1)), $h1)"
      (lambdaTerm, (hCount, parameters._2, xCount))
    } else { // return instanciated version
      val lambdaTerm = s"((λ $x1 ($h1: $Prf($x1)), $h1)$a)"
      (lambdaTerm, (hCount, parameters._2, xCount))
    }
  }

  def impTrans(a: String, b: String, c: String, prfAimpB: String, prfBimpC: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type  (Prf a → Prf b) → (Prf b → Prf c) → (Prf a → Prf c)
    // todo: replace with proper lp term
    // todo: track used symbols
    // todo: Normalize?

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
  }

  def impTrans4(a: String, b: String, c: String, d: String, prfAimpB: String, prfBimpC: String, prfCimpD: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type  (Prf a → Prf b) → (Prf b → Prf c) → (Prf a → Prf c)
    // todo: replace with proper lp term
    // todo: track used symbols
    // todo: Normalize?

    var hCount = parameters._1
    var xCount = parameters._3

    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1
    val x3: String = nameX(xCount)
    xCount = xCount + 1
    val x4: String = nameX(xCount)
    xCount = xCount + 1
    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h4: String = nameHypothesis(hCount)
    hCount = hCount + 1

    val lambdaTerm = s"(((λ $x1 $x2 $x3 $x4 ($h1 : Prf $x1 → Prf $x2) ($h2 : Prf $x2 → Prf $x3) ($h3 : Prf $x3 → Prf $x4) $h4, $h3 ($h2 ($h1 $h4))) $a $b $c $d) $prfAimpB $prfBimpC $prfCimpD)"
    (lambdaTerm, (hCount, parameters._2, xCount), Set())
  }



  // changing positions in clauses/ literals

  def eqCom(T: String, a: String, b: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int)) = {
    // Provides proof term of type Prf(eq [T] a b) → Prf(eq [T] b a)
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
  }

  def inEqCom(T: String, a: String, b: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int)) = {
    // Provides proof term of type Prf(eq [T] a b) → Prf(eq [T] b a)
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
    val h3: String = nameHypothesis(hCount)
    hCount = hCount + 1
    if ((a == "") & (b == "") & (T == "")) { // return non instanciated version
      val lambdaTerm = s"(λ $x1 $x2 $x3 ($h1 : Prf (¬ (eq [$x1] $x2 $x3))) ($h2 : Prf (eq [$x1] $x3 $x2)), $h1 ($h2 (λ $x4, eq [$x1] $x4 $x3) (λ $x5 $h3, $h3)))"
      (lambdaTerm, (hCount, parameters._2, xCount))
    } else { // return (partly) inst. version
      val lambdaTerm = s"((λ $x1 $x2 $x3 ($h1 : Prf (¬ (eq [$x1] $x2 $x3))) ($h2 : Prf (eq [$x1] $x3 $x2)), $h1 ($h2 (λ $x4, eq [$x1] $x4 $x3) (λ $x5 $h3, $h3))) ($T) ($a) ($b))"
      (lambdaTerm, (hCount, parameters._2, xCount))
    }
  }



  // encoding non equational literals as equational and vice versa

  def mkNegPropNegLit(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type  Prf(¬ a) → Prf(eq [↑ o] a ⊥)
    // todo: replace with proper lp term
    // todo: track used symbols

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1
    val b1: String = nameBottom(bCount)
    bCount = bCount + 1
    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3: String = nameHypothesis(hCount)
    hCount = hCount + 1

    val lambdaTerm = s"((λ $x1 $h1 ($h2 : Prf (eq [↑ o] $x1 ⊤)), $h2 (λ $x2, ¬ $x2) $h1 (λ $b1 $h3, $h3)) $a)"
    //val lambdaTerm = s"((λ $x1 $h1, propExt $x1 ⊥ $h1 (λ $h2, $h2 $x1)) $a)"
    (lambdaTerm, (hCount, bCount, xCount), Set())
  }

  def mkNegPropPosLit(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type Prf(¬ a) → Prf(eq [↑ o] (¬ a) ⊤)
    // todo: replace with proper lp term
    // todo: track used symbols

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1: String = nameBottom(bCount)
    bCount = bCount + 1
    val x1: String = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm = s"((λ $x1 $h1, propExt (¬ $x1) ⊤ (λ _ $b1 $h2, $h2) (λ _, $h1)) $a)"
    (lambdaTerm, (hCount, bCount, xCount), Set("propExt"))
  }

  def mkPosPropNegLit(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type Prf(a) → Prf(¬(eq [↑ o] (¬ a) ⊤))
    // todo: replace with proper lp term
    // todo: track used symbols

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1: String = nameBottom(bCount)
    bCount = bCount + 1
    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1
    val lambdaTerm = s"((λ $x1 $h1 ($h2 : Prf (eq [↑ o] (¬ $x1) ⊤)), $h2 (λ $x2, ¬ $x2) (λ $b1, $b1 $h1) (λ $b1 $h3, $h3)) $a)"
    (lambdaTerm, (hCount, bCount, xCount), Set())
  }

  def mkPosPropPosLit(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type Prf(a) → Prf(eq [↑ o] a ⊤)
    // todo: replace with proper lp term
    // todo: track used symbols

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1: String = nameBottom(bCount)
    bCount = bCount + 1
    val x1: String = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm = s"((λ $x1 $h1, propExt $x1 ⊤ (λ _ $b1 $h2, $h2) (λ _, $h1)) $a)"
    (lambdaTerm, (hCount, bCount, xCount), Set("propExt"))
  }

  def mkPosLitNegProp(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type Prf(eq [↑ o] (¬ a) ⊤) → Prf (¬ a)
    // todo: replace with proper lp term
    // todo: track used symbols

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1: String = nameBottom(bCount)
    bCount = bCount + 1
    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm = s"((λ $x1 ($h1 : Prf (eq [↑ o] (¬ $x1) ⊤)), em (¬ $x1) (¬ $x1) (λ $h2, $h2) (λ $h2, $h1 (λ $x2, ¬ $x2) $h2 (λ $b1 $h3, $h3) (¬ $x1))) $a)"
    (lambdaTerm, (hCount, bCount, xCount), Set("em"))
  }

  def mkPosLitPosProp(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type Prf(eq [↑ o] a ⊤) → Prf a
    // todo: replace with proper lp term
    // todo: track used symbols

    var hCount = parameters._1
    var bCount = parameters._2
    var xCount = parameters._3

    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h3: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val b1: String = nameBottom(bCount)
    bCount = bCount + 1
    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm = s"((λ $x1 ($h1 : Prf (eq [↑ o] $x1 ⊤)), em $x1 $x1 (λ $h2, $h2) (λ $h2, $h1 (λ $x2, ¬ $x2) $h2 (λ $b1 $h3, $h3) $x1)) $a)"
    (lambdaTerm, (hCount, bCount, xCount), Set("em"))
  }

  def mkNegLitNegProp(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type Prf(¬ (eq [↑ o] a ⊤)) → Prf(¬ a)
    // todo: replace with proper lp term
    // todo: track used symbols

    var hCount = parameters._1
    var xCount = parameters._3

    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1
    val x3: String = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm = s"((λ $x1 ($h1 : Prf (¬ (eq [↑ o] $x1 ⊤))) $h2, $h1 (propExt $x1 ⊤ (λ _ $x2 $x3, $x3) (λ _, $h2))) $a)"
    (lambdaTerm, (hCount, parameters._2, xCount), Set("propExt", HOLtop))
  }

  def mkNegLitPosProp(a: String, parameters: (Int, Int, Int)): (String, (Int, Int, Int), Set[String]) = {
    // Provide a proof of the type Prf(¬ (eq [↑ o] (¬ a) ⊤)) → Prf a
    // todo: replace with proper lp term
    // todo: track used symbols

    var hCount = parameters._1
    var xCount = parameters._3

    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val h2: String = nameHypothesis(hCount)
    hCount = hCount + 1
    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val x2: String = nameX(xCount)
    xCount = xCount + 1

    val lambdaTerm = s"((λ $x1 ($h1 : Prf (¬ (eq [↑ o] (¬ $x1) ⊤))), em $x1 $x1 (λ $h2, $h2) (λ $h2, $h1 (propExt (¬ $x1) ⊤ (λ _ $x1 $x2, $x2) (λ _, $h2)) $x1)) $a)"
    (lambdaTerm, (hCount, parameters._2, xCount), Set("propExt", "em", HOLtop))
  }

}
