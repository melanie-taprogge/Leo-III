package leo.modules.output.LPoutput

import leo.datastructures.Literal.{asTerm, symbols, vars}
import leo.datastructures.Term.{Integer, Rational, Real}
import leo.datastructures.{Clause, ClauseAnnotation, ClauseProxy, Kind, Literal, Role, Signature, Term, Type}
import leo.datastructures.Type._
import leo.datastructures.Term._
import leo.modules.HOLSignature._
import leo.modules.control._
import leo.modules.control.Control
import leo.modules.calculus._
import leo.modules.output._
import leo.modules.output.LPoutput.LPSignature._
import leo.modules.output.LPoutput.calculusEncoding._
import leo.modules.output.ToTPTP.{collectExists, collectForall}

import scala.collection.mutable

object Encodings {
/*
  def kind2LP(kind:Kind, sig: Signature)={

    // todo: what cases can we have here? is it really only possible to have pure kind declarations?
    print(s"\nkind = ${kind.pretty}")
  }

 */

  def type2LP (ty: Type, sig: Signature):(String,Set[String])={
    type2LP(ty, sig, Set.empty)
  }
  def type2LP (ty: Type, sig: Signature, usedSymbols:Set[String]):(String,Set[String])={
    ty match {
      case BaseType(id) =>
        val baseType = tptpEscapeExpression(sig(id).name)
        if (tptpDefinedTypeMap.keySet.contains(baseType)){
          (tptpDefinedTypeMap(baseType), usedSymbols + tptpDefinedTypeMap(baseType))
        }else{
          (baseType, usedSymbols)
        }
      case ComposedType(id, args) => (s"(${tptpEscapeExpression(sig(id).name)} ${args.map(type2LP(_,sig,usedSymbols)).mkString(" ")})",usedSymbols)
      case BoundType(scope) =>
        throw new Error(s"Composed Type not yet encoded, unable to do ${ty.pretty}")
        //original: "T" + intToName(scope - 1) todo
      case tl -> tr =>
        val (encodeTl,updatedSymbolsL) = type2LP(tl,sig,usedSymbols)
        val (encodeTr,updatedSymbolsR) = type2LP(tr,sig,usedSymbols)
        val allNewSymbols = updatedSymbolsL ++ updatedSymbolsR + HOLarrow
        (s"($encodeTl $HOLarrow $encodeTr)",allNewSymbols)
      case ProductType(tys) =>
        throw new Error(s"ProductType not yet encoded, unable to do ${ty.pretty}")
        //original: tys.map(tyDec2LP(_,sig)).mkString("[", ",", "]") todo
      case ∀(_) =>
        throw new Error(s"Poly Type not yet encoded, unable to do ${ty.pretty}")
        //original:val (tyAbsCount, bodyTy) = collectForallTys(0, ty)
        //s"!> [${(1 to tyAbsCount).map(i => s"T${intToName(i - 1)}: $$tType").mkString(",")}]: ${typeToTHF1(bodyTy)(sig)}"
    }
  }

  protected[output] final def makeDefBVarList(tys: Seq[Type], offset: Int): Seq[(String, Type)] = {
    // we calculate the indizes of the variables to name and assign names accordningly
    tys.zipWithIndex.map { case (ty, idx) => (s"$$${intToName(offset + idx)}", ty) }
  }



  // shamelessly stolen from ToTPTP (... for now, I will have to change to a different one/ change permissions)
  final private def collectLambdasLP(t: Term): (Seq[Type], Term) = {
    collectLambdasLP0(Seq.empty, t)
  }
  @inline final private def collectLambdasLP0(vars: Seq[Type], t: Term): (Seq[Type], Term) = {
    t match {
      case ty :::> b => collectLambdasLP0(vars :+ ty, b)
      case _ => (vars, t)
    }
  }
  private final def collectTyLambdas(count: Int, t: Term): (Int, Term) = {
    t match {
      case TypeLambda(body) => collectTyLambdas(count + 1, body)
      case _ => (count, t)
    }
  }
  final private def collectExists(t: Term): (Seq[Type], Term) = {
    collectExists0(Seq.empty, t)
  }
  @inline final private def collectExists0(vars: Seq[Type], t: Term): (Seq[Type], Term) = {
    t match {
      case Exists(ty :::> b) => collectExists0(vars :+ ty, b)
      case Exists(_) => collectExists0(vars, t.etaExpand)
      case _ => (vars, t)
    }
  }
  final private def collectForall(t: Term): (Seq[Type], Term) = {
    collectForall0(Seq.empty, t)
  }
  @inline final private def collectForall0(vars: Seq[Type], t: Term): (Seq[Type], Term) = {
    t match {
      case Forall(ty :::> b) => collectForall0(vars :+ ty, b)
      case Forall(_) => collectForall0(vars, t.etaExpand)
      case _ => (vars, t)
    }
  }

  def def2LP(t:Term,sig:Signature,usedSymbols:Set[String]): (String,Set[String],Seq[(String, Type)])={
    // Definitions must be handled differently because we want to translate them to rules in LP.
    // Therefore we need to extract the used variable symbols and proceed them with a "$"
    t match {
      case _ :::> _ =>
        // In case of an abstraction the definition defines a function.
        // todo: other forms of defintion that have to be treated seperateley?
        val (bVarTys, body) = collectLambdasLP(t)
        val newBVars = makeDefBVarList(bVarTys, 0)
        val (encbody, updatedUsedSymbols0) = term2LP(body, fusebVarListwithMap(newBVars, Map()), sig, usedSymbols)
        var updatedUsedSymbols = updatedUsedSymbols0
        val abstractions: StringBuffer = new StringBuffer()
        newBVars foreach {
          s_ty =>
            val (ty, updatedUsedSymbols0) = type2LP(s_ty._2, sig, updatedUsedSymbols)
            updatedUsedSymbols = updatedUsedSymbols0
            // todo: I think i will need to edit here to make changes for definitions, maybe do optional input for
            abstractions.append(s"(${s_ty._1} : $ty)")
          // todo: summarize same types into one bracket
        }
        (s"$encbody", updatedUsedSymbols, newBVars)
    }
  }

  final def clauseVars2LP(fvs: Seq[(Int, Type)], sig: Signature, usedSymbols0: Set[String]): (String, Map[Int, String],Set[String]) = {
    val fvCount = fvs.size
    val boundVars: StringBuffer = new StringBuffer()
    var usedSymbols = usedSymbols0

    var resultBindingMap: Map[Int, String] = Map()
    var curImplicitlyQuantified = fvs
    var i = 0
    while (i < fvCount) {
      val (scope, ty) = curImplicitlyQuantified.head
      val name = intToName(fvCount - i - 1)
      val (encType, usedSymbolsNew) = type2LP(ty,sig,usedSymbols)
      usedSymbols = usedSymbolsNew
      boundVars.append(s"$Pi $name : $Els($uparrow $encType) , ")// todo: cases where we embed sth of type scheme?
      resultBindingMap = resultBindingMap + (scope -> name)

      curImplicitlyQuantified = curImplicitlyQuantified.tail
      i = i + 1
    }
    (boundVars.toString, resultBindingMap, usedSymbols)
  }

  final def clause2LP(cl: Clause, usedSymbols0: Set[String], sig: Signature): (String,Set[String]) = {
    val freeVarsExist = cl.implicitlyBound.nonEmpty || cl.typeVars.nonEmpty
    var usedSymbols = usedSymbols0
    if (freeVarsExist) {
      val quantifiedVars = new StringBuffer()
      quantifiedVars.append(cl.typeVars.reverse.map(i => s"$Pi T${intToName(i - 1)} : $metaType ,").mkString(" "))
      val (namedFVEnumerationLP, bVarMap, usedSymbolsNew) = clauseVars2LP(cl.implicitlyBound, sig,usedSymbols)
      quantifiedVars.append(namedFVEnumerationLP)
      val (encClause,usedSymbolsClause) = clause2LP0(cl,bVarMap,sig,usedSymbolsNew)
      usedSymbols = usedSymbolsClause
      (s"($quantifiedVars $Prf ($encClause))",usedSymbols)
    }else{
      val (encClause, usedSymbolsClause) = clause2LP0(cl, Map.empty, sig, usedSymbols)
      usedSymbols = usedSymbolsClause
      (s"$Prf ($encClause)",usedSymbols)
    }
  }
  def clause2LP0(cl: Clause, bVarMap: Map[Int, String],sig: Signature, usedSymbols0: Set[String]): (String,Set[String]) = {
    val encodedClause = new StringBuilder
    var usedSymbols = usedSymbols0
    if (cl.lits.isEmpty) {
      val (encBot,usedSymbolsNew) = term2LP(LitFalse,bVarMap,sig,usedSymbols)
      usedSymbols = usedSymbolsNew
      encodedClause.append(encBot)
    }else{
      val litIt = cl.lits.iterator
      while (litIt.hasNext) {
        val lit = litIt.next()
        if (lit.equational) {
          val (left, right) = (lit.left, lit.right)
          val (lefEnc, usedSymbolsL) = term2LP(left, bVarMap, sig, usedSymbols)
          val (refEnc, usedSymbolsR) = term2LP(right, bVarMap, sig, usedSymbolsL)
          val (encTyTl, updatedUsedSymbolsTyL) = type2LP(left.ty,sig,usedSymbolsR)
          usedSymbols = updatedUsedSymbolsTyL
          if (lit.polarity) {
            // todo: add type of terms to eq
            encodedClause.append(s"($equ [$uparrow $encTyTl] $lefEnc $refEnc)")
          } else {
            // as for lit.poliarity: todo: add type of terms to eq
            encodedClause.append(s"($inEqu [$uparrow $encTyTl] $lefEnc $refEnc)")
          }
        } else {
          val (termEnc, usedSymbolsNew) = term2LP(lit.left, bVarMap, sig, usedSymbols)
          usedSymbols = usedSymbolsNew
          if (lit.polarity){
            encodedClause.append(termEnc)
          }else{
              encodedClause.append(s"$lnot $termEnc")
            }
          }
        if (litIt.hasNext) encodedClause.append(s" $lor ")
        }
      }
    (encodedClause.toString(),usedSymbols)
    }

  def term2LP(t: Term, bVars: Map[Int,String], sig:Signature): (String,Set[String]) = {
    term2LP(t,bVars,sig,Set.empty)
  }
  def term2LP(t: Term, bVars: Map[Int,String], sig:Signature, usedSymbols:Set[String]): (String,Set[String]) = {

    // modelled after toTPTP0

    t match {
      // Constant symbols
      case Symbol(id) => val name = sig(id).name
        val symbol = tptpDefinedSymbolMap.getOrElse(tptpEscapeExpression(name), tptpEscapeExpression(name))
        if (symbol != tptpEscapeExpression(name)) (symbol, usedSymbols+symbol)
        else (symbol, usedSymbols)
      // Numbers
      case Integer(n) => throw new Error(s"integers are not encoded yet ${t.pretty}") //n.toString
      case Rational(n, d) => throw new Error(s"rationals are not encoded yet ${t.pretty}") //s"$n/$d"
      case Real(w, d, e) => throw new Error(s"reals are not encoded yet ${t.pretty}") //if (e == 0) s"$w.$d" else s"$w.${d}E$e"
      // Give Bound variables names
      case Bound(_, scope) => (bVars(scope),usedSymbols) //throw new Error(s"bound vars are not encoded yet ${t.pretty}") //bVars(scope)

      // Unary connectives
      case Not(t2) =>
        val (encBody, usedSymbolsNew) = term2LP(t2, bVars, sig, usedSymbols)
        (s"($lnot $encBody)", usedSymbolsNew + lnot)
      case Forall(_) =>
        val (bVarTys, body) = collectForall(t)
        val newBVars = makeBVarList(bVarTys, bVars.size)
        val (encBody, usedSymbolsNew) = term2LP(body, fusebVarListwithMap(newBVars, bVars), sig, usedSymbols)
        var usedSymbolsQuant = usedSymbolsNew
        var prevQuant = encBody
        newBVars foreach { s_ty =>
          val (encType, usedSymbolsTyNew) = type2LP(s_ty._2, sig, usedSymbolsQuant)
          usedSymbolsQuant = usedSymbolsTyNew
          prevQuant = s"($objectForAll($LPlambda ${s_ty._1}: $Els($uparrow $encType), $prevQuant))"
        }
        (prevQuant, usedSymbolsQuant+objectForAll)
        //throw new Error(s"quantifiers are not encoded yet 1 ${t.pretty}")
      case Exists(_) =>
        // todo: Add explicit types for quantifiers?
        val (bVarTys, body) = collectExists(t)
        val newBVars = makeBVarList(bVarTys, bVars.size)
        val(encBody, usedSymbolsNew) = term2LP(body,fusebVarListwithMap(newBVars, bVars),sig,usedSymbols)
        var usedSymbolsQuant = usedSymbolsNew
        var prevQuant = encBody
        newBVars foreach {s_ty =>
          val(encType, usedSymbolsTyNew) = type2LP(s_ty._2,sig,usedSymbolsQuant)
          usedSymbolsQuant = usedSymbolsTyNew
          prevQuant = s"($objectExists($LPlambda ${s_ty._1}: $Els($uparrow $encType), $prevQuant))"
        }
        (prevQuant,usedSymbolsQuant+objectExists)
        //throw new Error(s"quantifiers are not encoded yet 2 ${t.pretty}")
      case TyForall(_) => throw new Error(s"type quantifiers are not encoded yet 3 ${t.pretty}")
      case leo.modules.HOLSignature.Choice(_) => throw new Error(s"choice not encoded yet ${t.pretty}")

      // Binary connectives
      case tl ||| tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        (s"($encodedTl $lor $encodedTr)", updatedUsedSymbolsR + lor)
      case tl & tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        (s"($encodedTl $land $encodedTr)", updatedUsedSymbolsR + land)
      case tl === tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        val (encTyTl, updatedUsedSymbolsTyL) = type2LP(tl.ty,sig,updatedUsedSymbolsR)
        // todo: here i need to make changes for polymorphic types of LP TYPE Scheme
        (s"($equ [$uparrow $encTyTl] $encodedTl $encodedTr)", updatedUsedSymbolsTyL + equ)
      case tl !=== tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        val (encTyTl, updatedUsedSymbolsTyL) = type2LP(tl.ty,sig,updatedUsedSymbolsR)
        // like equ: todo: here i need to make changes for polymorphic types of LP TYPE Scheme
        (s"($inEqu [$uparrow $encTyTl] $encodedTl $encodedTr)", updatedUsedSymbolsTyL + inEqu)
      case tl Impl tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        (s"($encodedTl $HOLimpl $encodedTr)", updatedUsedSymbolsR + HOLimpl)
      case tl Impl tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        (s"($encodedTl $HOLimpl $encodedTr)", updatedUsedSymbolsR + HOLimpl)
      case t1 <= t2 => throw new Error(s"encountered un-encoded connective <= ${t.pretty}")
      case t1 <=> t2 => throw new Error(s"encountered un-encoded connective <=> ${t.pretty}")
      case t1 ~& t2 => throw new Error(s"encountered un-encoded connective ~& ${t.pretty}")
      case t1 ~||| t2 => throw new Error(s"encountered un-encoded connective ~||| ${t.pretty}")
      case t1 <~> t2 => throw new Error(s"encountered un-encoded connective <~> ${t.pretty}")

      // term abstraction in terms
      case _ :::> _ =>
        val t0 = t.etaContract
        if (t != t0) term2LP(t0, bVars, sig, usedSymbols)
        else {
          val (bVarTys, body) = collectLambdasLP(t)
          val newBVars = makeBVarList(bVarTys, bVars.size)
          val (encbody, updatedUsedSymbols0) = term2LP(body,fusebVarListwithMap(newBVars, bVars),sig,usedSymbols)
          var updatedUsedSymbols = updatedUsedSymbols0
          val abstractions: StringBuffer = new StringBuffer()
          newBVars foreach { s_ty =>
            val (ty, updatedUsedSymbols0) = type2LP(s_ty._2, sig, updatedUsedSymbols)
            updatedUsedSymbols = updatedUsedSymbols0
            abstractions.append(s"(${s_ty._1} : $Els($uparrow $ty))") //todo: for polymorphy we might also need to use Scheme types here
            // todo: summarize same types into one bracket
          }
          (s"($LPlambda $abstractions, $encbody)", updatedUsedSymbols)
        }

      case TypeLambda(_) =>
        val (tyAbsCount, body) = collectTyLambdas(0, t)
        //s"^ [${(1 to tyAbsCount).map(i => "T" + intToName(i - 1) + ": $tType").mkString(",")}]: (${toTPTP0(body, tyVarCount + tyAbsCount, bVars)(sig)})"
        // todo: not really sure how this should be encoded, check with examples
        throw new Error(s"encountered typeLambda, this is not encoded yet ${t.pretty}")

      // match pattern of application
      case _@Symbol(id) ∙ args if leo.modules.input.InputProcessing.adHocPolymorphicArithmeticConstants.contains(id) =>
        // todo: no idea what is happening here
        throw new Error(s"encountered something that is not encoded yet ${t.pretty}")

      case f ∙ args =>
        val (translatedF, updatedUsedSymbols0) = term2LP(f, bVars, sig, usedSymbols)
        var updatedUsedSymbols = updatedUsedSymbols0
        val arguments: StringBuffer = new StringBuffer()
        args foreach { arg =>
          arg match {
            case Left(termArg) =>
              val (encArg, updatedUsedSymbols0) = term2LP(termArg, bVars, sig, updatedUsedSymbols)
              updatedUsedSymbols = updatedUsedSymbols0
              arguments.append(s" $encArg")
            case Right(tyArg) =>
              val (encArg, updatedUsedSymbols0) = type2LP(tyArg, sig, updatedUsedSymbols)
              updatedUsedSymbols = updatedUsedSymbols0
              arguments.append(s" $encArg")
          }
        }
        (s"($translatedF$arguments)",updatedUsedSymbols)

      // Others should be invalid
      case _ => throw new IllegalArgumentException("Unexpected term format during conversion to LP")
    }
  }

  def selfImp(a: String,parameters: (Int,Int,Int)):(String, (Int,Int,Int))={

    var xCount = parameters._3
    var hCount = parameters._3

    val x1: String = nameX(xCount)
    xCount = xCount + 1
    val h1: String = nameHypothesis(hCount)
    hCount = hCount + 1

    if(a == ""){ // return type Pi x ,Prf x -> Prf x
      val lambdaTerm = s"(λ $x1 ($h1: $Prf($x1)), $h1)"
      (lambdaTerm,(hCount,parameters._2,xCount))
    }else{ // return instanciated version
      val lambdaTerm = s"((λ $x1 ($h1: $Prf($x1)), $h1)$a)"
      (lambdaTerm,(hCount,parameters._2,xCount))
    }
  }

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
    if ((a == "")&(b == "")&(T == "")) { // return non instanciated version
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
  def mkPosPropNegLit(a : String, parameters: (Int, Int, Int)):(String,(Int, Int, Int),Set[String])={
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
    (lambdaTerm,(hCount,bCount,xCount),Set())
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
    (lambdaTerm, (hCount, parameters._2, xCount), Set("propExt","em",HOLtop))
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


  def step2LP(cl: ClauseProxy, idClauseMap: mutable.HashMap[Long,ClauseProxy], parentInLpEncID: Seq[Long], sig: Signature): (String,Set[String]) = {
    val rule = cl.annotation.fromRule

    if (!Seq(leo.datastructures.Role_Conjecture,leo.datastructures.Role_NegConjecture).contains(cl.role)){ // we start our proof with the negated conjecture

      rule match {
        case leo.modules.calculus.PolaritySwitch =>
          //todo: dont forget to map to the correct formula! make special case for negated conjecture
          val encoding = encPolaritySwitchClause(cl, cl.annotation.parents.head,parentInLpEncID.head,sig) //¿polarity switch always only has one parent, right?
          (encoding._1,encoding._3)
        case leo.modules.calculus.FuncExt =>
          val encoding = encFuncExtPosClause(cl, cl.annotation.parents.head,cl.furtherInfo.edLitBeforeAfter,parentInLpEncID.head,sig)
          (encoding._1, Set.empty) // no new symbols this time
        case leo.modules.calculus.BoolExt =>
          val encoding = encBoolExtClause(cl, cl.annotation.parents.head,parentInLpEncID.head, sig)
          (encoding._1, encoding._3)
        case leo.modules.calculus.OrderedEqFac =>
          val encodings = encEqFactClause(cl, cl.annotation.parents.head,cl.furtherInfo.addInfoEqFac,parentInLpEncID.head,sig)
          //throw new Exception(s"Eq factoring info: ${cl.furtherInfo.addInfoEqFac}")
          (encodings._1, encodings._3)
        //case leo.modules.calculus.PreUni =>
         // throw new Exception(s"${}")
        case _ =>
          //print(s"\n $rule not encoded yet \n\n")
          ("",Set.empty)
      }
    }//todo: either introduce else or filter out conj before!
    else ("",Set.empty)
  }

}
