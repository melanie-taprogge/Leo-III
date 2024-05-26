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
import leo.modules.output.ToTPTP.{collectExists, collectForall, typeToTHF}
import leo.modules.output.LPoutput.lpDatastructures._

import scala.collection.mutable

////////////// ENCODING OF TYPES, TERMS, CLAUSES, DEFINITIONS AND PROOF STEPS

object Encodings {
/*
  def kind2LP(kind:Kind, sig: Signature)={

    // todo: what cases can we have here? is it really only possible to have pure kind declarations?
    print(s"\nkind = ${kind.pretty}")
  }

 */

  def type2LP (ty: Type, sig: Signature):(lpOlType,Set[lpStatement])={
    type2LP(ty, sig, Set.empty)
  }
  def type2LP (ty: Type, sig: Signature, usedSymbols0:Set[lpStatement]):(lpOlType,Set[lpStatement])={
    var usedSymbols = usedSymbols0
    ty match {
      case BaseType(id) =>
        val baseType = tptpEscapeExpression(sig(id).name)
        if (tptpDefinedTypeMap.keySet.contains(baseType)){
          (tptpDefinedTypeMap(baseType), usedSymbols + tptpDefinedTypeMap(baseType))
        }else{
          (lpOlUserDefinedType(baseType), usedSymbols)
        }
      case ComposedType(id, args) =>
        var encArgs: Seq[lpType] = Seq.empty
        args foreach{arg =>
          val (encArg, usedSymbolsUpdated) = type2LP(arg,sig,usedSymbols)
          usedSymbols = usedSymbolsUpdated
          encArgs = encArgs :+ encArg
        }
        throw new Exception(s"attempting to encode composed Type, this was never tested! \ninput was ${ty.pretty}\noutput would be ${lpOlMonoComposedType(lpConstantTerm(tptpEscapeExpression(sig(id).name)),encArgs).pretty}")
        (lpOlMonoComposedType(lpConstantTerm(tptpEscapeExpression(sig(id).name)),encArgs),usedSymbols)
      case BoundType(scope) =>
        throw new Error(s"BoundType not yet encoded, unable to do ${ty.pretty}")
        //original: "T" + intToName(scope - 1) todo
      case tl -> tr =>
        val (encodeTl,updatedSymbolsL) = type2LP(tl,sig,usedSymbols)
        val (encodeTr,updatedSymbolsR) = type2LP(tr,sig,usedSymbols)
        usedSymbols = updatedSymbolsL ++ updatedSymbolsR + lpOlTypeConstructor
        (lpOlFunctionType(Seq(encodeTl,encodeTr)),usedSymbols)
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

  final def clauseImplicitsToTPTPQuantifierList_map(implicitlyQuantified: Seq[(Int, Type)])(sig: Signature): Map[Int, String] = {
    // shoretened version to only consruct the map
    //todo either incorporate somewhere or make it a proper function
    val count = implicitlyQuantified.size
    var resultBindingMap: Map[Int, String] = Map()

    var curImplicitlyQuantified = implicitlyQuantified
    var i = 0
    while (i < count) {
      val (scope, _) = curImplicitlyQuantified.head
      curImplicitlyQuantified = curImplicitlyQuantified.tail
      val name = intToName(count - i - 1)
      resultBindingMap = resultBindingMap + (scope -> name)
      i = i + 1
    }
    resultBindingMap
  }


  def def2LP(t:Term,sig:Signature,usedSymbols:Set[lpStatement], encAsRewriteRule: Boolean): (lpOlTerm,Set[lpStatement],Seq[(String, Type)])={
    // Definitions must be handled differently because we want to translate them to rules in LP.
    // Therefore we need to extract the used variable symbols and proceed them with a "$"

      t match {
        case _ :::> _ =>
          // In case of an abstraction the definition defines a function.
          // todo: other forms of defintion that have to be treated seperateley?
          val (bVarTys, body) = collectLambdasLP(t)
          val newBVars = if (encAsRewriteRule) makeDefBVarList(bVarTys, 0) else makeBVarList(bVarTys,0)
          val (encbody, updatedUsedSymbols0) = term2LP(body, fusebVarListwithMap(newBVars, Map()), sig, usedSymbols)
          var updatedUsedSymbols = updatedUsedSymbols0
          (encbody, updatedUsedSymbols, newBVars)
        case _ => throw new Exception(s"encountered unexpected definition format when trying to encode ${t.pretty} in LP")
      }
  }

  final def clauseVars2LP(fvs: Seq[(Int, Type)], sig: Signature, usedSymbols0: Set[lpStatement]): (Seq[lpOlTypedVar], Map[Int, String],Set[lpStatement]) = {
    val fvCount = fvs.size
    //val boundVars: StringBuffer = new StringBuffer()
    var boundVars: Seq[lpOlTypedVar] = Seq.empty
    var usedSymbols = usedSymbols0

    // A new map is created to keep track of the names of the implicitly quantfied variables
    var resultBindingMap: Map[Int, String] = Map()
    var curImplicitlyQuantified = fvs
    var i = 0
    while (i < fvCount) {
      val (scope, ty) = curImplicitlyQuantified.head
      val name = intToName(fvCount - i - 1)
      val (encType, usedSymbolsUpdated) = type2LP(ty,sig,usedSymbols)
      usedSymbols = usedSymbolsUpdated
      //boundVars.append(s"$Pi $name : $Els($uparrow $encType) , ")// todo: cases where we embed sth of type scheme?
      boundVars = boundVars :+ lpOlTypedVar(lpOlConstantTerm(name),encType)
      resultBindingMap = resultBindingMap + (scope -> name)

      curImplicitlyQuantified = curImplicitlyQuantified.tail
      i = i + 1
    }
    (boundVars, resultBindingMap, usedSymbols)
  }
  def clause2LP0(cl: Clause, bVarMap: Map[Int, String],sig: Signature, usedSymbols0: Set[lpStatement]): (lpOlUntypedBinaryConnectiveTerm_multi,Set[lpStatement]) = {
    //val encodedClause = new StringBuilder
    var encodedClause: lpOlUntypedBinaryConnectiveTerm_multi = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,Seq(lpOlNothing))
    var usedSymbols = usedSymbols0
    // if the clause has no literals, we retrun bottom
    if (cl.lits.isEmpty) {
      val (encBot,usedSymbolsUpdated) = term2LP(LitFalse,bVarMap,sig,usedSymbols)
      usedSymbols = usedSymbolsUpdated
      encodedClause = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,Seq(encBot))
    }else{
      var lits: Seq[lpOlTerm] = Seq.empty
      // otherwise we encode and add the literals one by one
      val litIt = cl.lits.iterator
      while (litIt.hasNext) {
        val lit = litIt.next()
        var encLit: lpOlTerm = lpOlBot
        if (lit.equational) {
          val (left, right) = (lit.left, lit.right)
          val (lefEnc, usedSymbolsL) = term2LP(left, bVarMap, sig, usedSymbols)
          val (rigEnc, usedSymbolsR) = term2LP(right, bVarMap, sig, usedSymbolsL)
          val (encTyTl, updatedUsedSymbolsTyL) = type2LP(left.ty,sig,usedSymbolsR)
          usedSymbols = updatedUsedSymbolsTyL
          if (lit.polarity) {
            encLit = lpOlTypedBinaryConnectiveTerm(lpEq,encTyTl,lefEnc,rigEnc)
          } else {
            encLit = lpOlTypedBinaryConnectiveTerm(lpInEq,encTyTl,lefEnc,rigEnc)
          }
        } else {
          //print(s"here is the problem 1\n")
          val (termEnc, usedSymbolsUpdated) = term2LP(lit.left, bVarMap, sig, usedSymbols)
          //print(s"encoded term: ${termEnc.pretty}\n")
          usedSymbols = usedSymbolsUpdated
          if (lit.polarity){
            encLit = termEnc
          }else{
            encLit = lpOlUnaryConnectiveTerm(lpNot,termEnc)
            }
          }
        // either start the clause with the encoded lit (if no lits have been added so far) or add it to the disjunction
        lits = lits :+ encLit
        }
      encodedClause = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,lits)
      }
    (encodedClause,usedSymbols)
    }

  final def clause2LP_unquantified(cl: Clause, usedSymbols0: Set[lpStatement], sig: Signature): (Seq[lpOlTypedVar],lpOlUntypedBinaryConnectiveTerm_multi, Set[lpStatement]) = {
    //print(s"\nencoding ${cl.pretty}\n")
    val freeVarsExist = cl.implicitlyBound.nonEmpty || cl.typeVars.nonEmpty
    var usedSymbols = usedSymbols0
    if (freeVarsExist) {
      // If there are free variables, they are implicitly quantified over, in the encoding this quantification should be explicit
      // Add implicitly quantified type variables
      var quantifiedVars: Seq[lpOlTypedVar] = Seq.empty
      // todo: add the T vars to counted here
      //  and: is it right to just make these things Set types? It should be since we can only quantify over mono types right?
      quantifiedVars = quantifiedVars ++ (cl.typeVars.reverse.map(i => lpOlTypedVar(lpOlConstantTerm(s"T${intToName(i - 1)}"), lpSet)))
      // Add implicitly quantified typed variables
      val (namedFVEnumerationLP, bVarMap, usedSymbolsUpdated) = clauseVars2LP(cl.implicitlyBound, sig, usedSymbols)
      quantifiedVars = quantifiedVars ++ namedFVEnumerationLP
      // With this we now encode the actual clause
      val (encClause, usedSymbolsClause) = clause2LP0(cl, bVarMap, sig, usedSymbolsUpdated)
      //print(s"done ! ${encClause.pretty}\n")
      usedSymbols = usedSymbolsClause
      //(lpMlDependType(quantifiedVars,encClause.prf), usedSymbols)
      (quantifiedVars,encClause,usedSymbols)
    } else {
      // otherwise we just encode the clause and lift it to a proof term
      val (encClause, usedSymbolsClause) = clause2LP0(cl, Map.empty, sig, usedSymbols)
      //print(s"done ! ${encClause.pretty}\n")
      usedSymbols = usedSymbolsClause
      //(encClause.prf,usedSymbols)
      (Seq.empty,encClause,usedSymbols)
    }
  }

  final def clause2LP(cl: Clause, usedSymbols0: Set[lpStatement], sig: Signature): (lpClause, Set[lpStatement]) = {
    val (quantifiedVars,encClause,usedSymbols) = clause2LP_unquantified(cl, usedSymbols0, sig)
    (lpClause(quantifiedVars,encClause.args),usedSymbols)
  }

  def term2LP(t: Term, bVars: Map[Int,String], sig:Signature): (lpOlTerm,Set[lpStatement]) = {
    term2LP(t,bVars,sig,Set.empty)
  }
  def term2LP(t: Term, bVars: Map[Int,String], sig:Signature, usedSymbols:Set[lpStatement]): (lpOlTerm,Set[lpStatement]) = {
    //todo: dont i need the offset? was it an oversight not to use it in term2lp?
    //print(s"encoding a term: ${t.pretty}\n")
    // modelled after toTPTP0

    t match {
      // Constant symbols
      case Symbol(id) => val name = sig(id).name
        val symbol = tptpDefinedSymbolMap.getOrElse(tptpEscapeExpression(name), lpOlConstantTerm(tptpEscapeExpression(name)))
        (symbol, usedSymbols+symbol)
      // Numbers
      case Integer(n) => throw new Error(s"integers are not encoded yet ${t.pretty}") //n.toString
      case Rational(n, d) => throw new Error(s"rationals are not encoded yet ${t.pretty}") //s"$n/$d"
      case Real(w, d, e) => throw new Error(s"reals are not encoded yet ${t.pretty}") //if (e == 0) s"$w.$d" else s"$w.${d}E$e"
      // Give Bound variables names
      case Bound(_, scope) =>
        val (encType, usedSymbolsUpdated) = type2LP(t.ty, sig, usedSymbols)
        (lpOlTypedVar(lpOlConstantTerm(bVars(scope)),encType),usedSymbolsUpdated) //throw new Error(s"bound vars are not encoded yet ${t.pretty}") //bVars(scope)

      // Unary connectives
      case Not(t2) =>
        val (encBody, usedSymbolsUpdated) = term2LP(t2, bVars, sig, usedSymbols)
        (lpOlUnaryConnectiveTerm(lpNot,encBody), usedSymbolsUpdated + lpNot)
      case Forall(_) =>
        val (bVarTys, body) = collectForall(t)
        val newBVars = makeBVarList(bVarTys, bVars.size)
        val (encBody, usedSymbolsUpdated) = term2LP(body, fusebVarListwithMap(newBVars, bVars), sig, usedSymbols)
        var usedSymbolsQuant = usedSymbolsUpdated
        var quantifiedVars: Seq[lpOlTypedVar]= Seq.empty
        newBVars foreach { s_ty =>
          val (encType, usedSymbolsTyNew) = type2LP(s_ty._2, sig, usedSymbolsQuant)
          usedSymbolsQuant = usedSymbolsTyNew
          quantifiedVars = quantifiedVars :+ lpOlTypedVar(lpOlConstantTerm(s_ty._1),encType)
        }
        (lpOlMonoQuantifiedTerm(lpOlForAll,quantifiedVars,encBody), usedSymbolsQuant+lpOlForAll)
        //throw new Error(s"quantifiers are not encoded yet 1 ${t.pretty}")
      case Exists(_) =>
        // todo: Add explicit types for quantifiers?
        val (bVarTys, body) = collectExists(t)
        val newBVars = makeBVarList(bVarTys, bVars.size)
        val (encBody, usedSymbolsUpdated) = term2LP(body, fusebVarListwithMap(newBVars, bVars), sig, usedSymbols)
        var usedSymbolsQuant = usedSymbolsUpdated
        var quantifiedVars: Seq[lpOlTypedVar] = Seq.empty
        newBVars foreach { s_ty =>
          val (encType, usedSymbolsTyNew) = type2LP(s_ty._2, sig, usedSymbolsQuant)
          usedSymbolsQuant = usedSymbolsTyNew
          quantifiedVars = quantifiedVars :+ lpOlTypedVar(lpOlConstantTerm(s_ty._1), encType)
        }
        (lpOlMonoQuantifiedTerm(lpOlExists, quantifiedVars, encBody), usedSymbolsQuant + lpOlExists)
        //throw new Error(s"quantifiers are not encoded yet 2 ${t.pretty}")
      case TyForall(_) => throw new Error(s"type quantifiers are not encoded yet 3 ${t.pretty}")
      case leo.modules.HOLSignature.Choice(_) => throw new Error(s"choice not encoded yet ${t.pretty}")

      // Binary connectives
      case tl ||| tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        (lpOlUntypedBinaryConnectiveTerm(lpOr,encodedTl,encodedTr), updatedUsedSymbolsR + lpOr)
      case tl & tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        (lpOlUntypedBinaryConnectiveTerm(lpAnd,encodedTl,encodedTr), updatedUsedSymbolsR + lpAnd)
      case tl === tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        val (encTyTl, updatedUsedSymbolsTyL) = type2LP(tl.ty,sig,updatedUsedSymbolsR)
        // todo: here i need to make changes for polymorphic types of LP TYPE Scheme
        (lpOlTypedBinaryConnectiveTerm(lpEq,encTyTl,encodedTl,encodedTr), updatedUsedSymbolsTyL + lpEq)
      case tl !=== tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        val (encTyTl, updatedUsedSymbolsTyL) = type2LP(tl.ty,sig,updatedUsedSymbolsR)
        // like equ: todo: here i need to make changes for polymorphic types of LP TYPE Scheme
        (lpOlTypedBinaryConnectiveTerm(lpInEq,encTyTl.lift2Poly,encodedTl,encodedTr), updatedUsedSymbolsTyL + lpInEq)
      case tl Impl tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL)
        (lpOlUntypedBinaryConnectiveTerm(lpImp,encodedTl,encodedTr), updatedUsedSymbolsR + lpImp)
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
          val (encBody, updatedUsedSymbols0) = term2LP(body,fusebVarListwithMap(newBVars, bVars),sig,usedSymbols)
          var updatedUsedSymbols = updatedUsedSymbols0
          //val abstractions: StringBuffer = new StringBuffer()
          var abstractions: Seq[lpOlTypedVar] = Seq.empty
          newBVars foreach { s_ty =>
            val (encType, updatedUsedSymbols0) = type2LP(s_ty._2, sig, updatedUsedSymbols)
            updatedUsedSymbols = updatedUsedSymbols0
            abstractions = abstractions :+ (lpOlTypedVar(lpOlConstantTerm(s_ty._1),encType)) //todo: for polymorphy we might also need to use Scheme types here
            // todo: summarize same types into one bracket
          }
          (lpOlLambdaTerm(abstractions,encBody), updatedUsedSymbols)
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
        //val arguments: StringBuffer = new StringBuffer()
        var arguments:Seq[lpTerm] = Seq.empty
        args foreach { arg =>
          arg match {
            case Left(termArg) =>
              val (encArg, updatedUsedSymbols0) = term2LP(termArg, bVars, sig, updatedUsedSymbols)
              updatedUsedSymbols = updatedUsedSymbols0
              arguments = arguments :+ encArg
            case Right(tyArg) =>
              val (encArg, updatedUsedSymbols0) = type2LP(tyArg, sig, updatedUsedSymbols)
              updatedUsedSymbols = updatedUsedSymbols0
              arguments = arguments :+ encArg
          }
        }
        (lpOlFunctionApp(translatedF,arguments),updatedUsedSymbols)

      // Others should be invalid
      case _ => throw new IllegalArgumentException("Unexpected term format during conversion to LP")
    }
  }


  def step2LP(cl: ClauseProxy, idClauseMap: mutable.HashMap[Long,ClauseProxy], parentInLpEncID: Seq[lpConstantTerm], sig: Signature, parameters0:(Int,Int,Int,Int)): (String,lpStatement,(Int,Int,Int,Int),Set[lpStatement]) = {

    val skripts = true

    val rule = cl.annotation.fromRule

    val continuousNumbers = true

    val parameters = if (continuousNumbers) parameters0 else (0,0,0,0)

    if (!Seq(leo.datastructures.Role_Conjecture).contains(cl.role)){ // we start our proof with the negated conjecture

      rule match {
        case leo.modules.calculus.PolaritySwitch =>
          //todo: dont forget to map to the correct formula! make special case for negated conjecture
          //val encoding = encPolaritySwitchClause(cl, cl.annotation.parents.head,parentInLpEncID.head,sig,parameters) //¿polarity switch always only has one parent, right?
          //encoding
          if (skripts) {
            val encoding = encPolaritySwitchClause_proofScript(cl, cl.annotation.parents.head, parentInLpEncID.head, sig) //¿polarity switch always only has one parent, right?
            ("PolaritySwitch",encoding._1,(0,0,0,0),encoding._2)
          } else {
            val encoding = encPolaritySwitchClause(cl, cl.annotation.parents.head, parentInLpEncID.head, sig, parameters) //¿polarity switch always only has one parent, right?
            ("PolaritySwitch",encoding._1,encoding._2, encoding._3)
          }

        case leo.modules.calculus.FuncExt =>
          if (skripts) {
            val encoding = encFuncExtPosClause_script(cl, cl.annotation.parents.head, cl.furtherInfo.edLitBeforeAfter, parentInLpEncID.head, sig, parameters)
            ("FuncExt", encoding._1, parameters, encoding._2) // no new symbols this time
          } else {
            val encoding = encFuncExtPosClause(cl, cl.annotation.parents.head, cl.furtherInfo.edLitBeforeAfter, parentInLpEncID.head, sig, parameters0)
            ("FuncExt", encoding._1, encoding._2, encoding._3)
          }

        case leo.modules.calculus.BoolExt =>
          //throw new Exception(s"${cl.furtherInfo.addInfoBoolExt}")
          //val encoding = encBoolExtClause(cl, cl.annotation.parents.head, parentInLpEncID.head, sig,parameters)
          if (skripts) {
            val encoding = encBoolExtClause_proofScript(cl, cl.annotation.parents.head, parentInLpEncID.head, cl.furtherInfo.addInfoBoolExt, sig)
            ("BoolExt", encoding._1, (0, 0, 0, 0), encoding._2)
          } else {
            val encoding = encBoolExtClause(cl, cl.annotation.parents.head, parentInLpEncID.head, sig, parameters0)
            ("BoolExt", encoding._1, encoding._2, encoding._3)
          }

        case leo.modules.calculus.OrderedEqFac =>
          //val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head,cl.furtherInfo.addInfoEqFac,parentInLpEncID.head,sig)
          //(encodings._1,(0,0,0,0),encodings._2)
          if (skripts) {
            val encodings = encEqFact_proofScript(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoEqFac,parentInLpEncID.head, sig)
            ("OrderedEqFac",encodings._1,parameters,encodings._2)
          } else {
            val encodings = encEqFactClause(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoEqFac, parentInLpEncID.head, sig, parameters0)
            //throw new Exception(s"Eq factoring info: ${cl.furtherInfo.addInfoEqFac}")
            ("OrderedEqFac",encodings._1, encodings._2, encodings._3)
          }

        case leo.modules.calculus.DefExpSimp =>
          //throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoDefExp}")
          // todo: eta expansion
          val encodingsSimp = encDefExSimp(cl, cl.annotation.parents.head,cl.furtherInfo.addInfoSimp,cl.furtherInfo.addInfoDefExp,parentInLpEncID.head,sig)
          ("DexExpand",encodingsSimp._1,(0,0,0,0),encodingsSimp._2)
        case leo.modules.calculus.Simp =>
          throw new Exception(s"expanded defs: ${cl.furtherInfo.addInfoSimp}")
          // todo: eta expansion
          val encodingsSimp = encDefExSimp(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoSimp, cl.furtherInfo.addInfoDefExp, parentInLpEncID.head, sig)
          ("?",encodingsSimp._1, (0, 0, 0, 0), encodingsSimp._2)
        case leo.modules.calculus.PreUni =>
          val encodingPreUni = encPreUni(cl, cl.annotation.parents.head, cl.furtherInfo.addInfoUni, cl.furtherInfo.addInfoUniRule, parentInLpEncID.head, sig)
          ("PreUni",encodingPreUni._1,parameters,encodingPreUni._2)
          //throw new Exception(s"${cl.furtherInfo.addInfoUni}")
        case leo.modules.calculus.RewriteSimp =>
          //throw new Exception(s"add info rewriting: ${cl.furtherInfo.addInfoRewriting}")
          val encodingRewrite = encRewrite(cl,cl.annotation.parents,cl.furtherInfo.addInfoSimp,cl.furtherInfo.addInfoRewriting,parentInLpEncID,sig)
          ("RewriteSimp",encodingRewrite._1,parameters,encodingRewrite._2)
        case _ =>
          //print(s"\n $rule not encoded yet \n\n")
          (s"Rule ${rule.name} not encoded yet",lpOlNothing,parameters,Set.empty)
      }
    }//todo: either introduce else or filter out conj before!
    else ("no role or conjecture?",lpOlNothing,parameters,Set.empty)
  }

}
