package leo.modules.output.LPoutput

import leo.datastructures.Term.{Integer, Rational, Real}
import leo.datastructures.{Clause, ClauseProxy, Literal, Signature, Term, Type}
import leo.datastructures.Type._
import leo.datastructures.Term._
import leo.modules.HOLSignature
import leo.modules.HOLSignature._
import leo.modules.output._
import leo.modules.output.LPoutput.lpDatastructures._
import leo.modules.output.ToTPTP.{collectChoice, collectForallTys}
import leo.modules.output.logger.Out

import scala.collection.mutable

////////////// ENCODING OF TYPES, TERMS, CLAUSES, DEFINITIONS AND PROOF STEPS

/** Automated translation of types and terms
  *
  * @author Melanie Taprogge
  */

object Encodings {

  ////////////////////////////////////////////////////////////////
  ////////// Leo Functinality
  ////////////////////////////////////////////////////////////////

  // adapted from ToTPTP (... for now, I will have to change to a different one/ change permissions)
  // todo: combine with the original functions
  final def collectLambdasLP(t: Term): (Seq[Type], Term) = {
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

  // ?
  protected[output] final def makeDefBVarList(tys: Seq[Type], offset: Int): Seq[(String, Type)] = {
    // Is this Leo code?
    // we calculate the indizes of the variables to name and assign names accordningly
    tys.zipWithIndex.map { case (ty, idx) => (s"$$${intToName(offset + idx)}", ty) }
  }

  ////////////////////////////////////////////////////////////////
  ////////// Automated Encoding
  ////////////////////////////////////////////////////////////////

  def polyType2Lp (ty: Type, sig: Signature):(lpOlType,Seq[lpOlType])={
    // for the time being, we only allow polymorphic types when declaring symbols
    ty match {
      case ∀(_) => val (tyAbsCount, bodyTy) = collectForallTys(0, ty)
        //s"!> [${(1 to tyAbsCount).map(i => s"T${intToName(i - 1)}: $$tType").mkString(",")}]: ${typeToTHF1(c)(sig)}"
        val variables = (1 to tyAbsCount).map(i => lpOlUserDefinedType("T" + intToName(i-1)))
        val encBody = type2LP(bodyTy,sig)
        (encBody, variables)
      case _ => (type2LP(ty,sig), Seq())
    }
  }

  def type2LP (ty: Type, sig: Signature, prefix: Boolean = true):(lpOlType)={
    ty match {
      case BaseType(id) =>
        val baseType = tptpEscapeExpression(sig(id).name)
        if (tptpDefinedTypeMap.keySet.contains(baseType)){
          (tptpDefinedTypeMap(baseType))
        }else{
          val lpSafeName = lpEscapeName(sig(id).name,sig,prefix)
          (lpOlUserDefinedType(lpSafeName))
        }
      case ComposedType(id, args) =>
        var encArgs: Seq[lpType] = Seq.empty
        args foreach{arg =>
          val encArg = type2LP(arg,sig, prefix)
          encArgs = encArgs :+ encArg
        }
        throw new Exception(s"attempting to encode composed Type, this was never tested! \ninput was ${ty.pretty}\noutput would be ${lpOlMonoComposedType(lpConstantTerm(lpEscapeName(sig(id).name,sig)),encArgs).pretty}")
        (lpOlMonoComposedType(lpConstantTerm(tptpEscapeExpression(sig(id).name)),encArgs))
      case BoundType(scope) =>
        val tyName = "T" + intToName(scope-1)
        lpOlUserDefinedType(tyName)
        //throw new Error(s"BoundType not yet encoded, unable to do ${ty.pretty}")
        //todo
      case tl -> tr =>
        val encodeTl = type2LP(tl,sig, prefix)
        val encodeTr = type2LP(tr,sig, prefix)
        lpOlFunctionType(Seq(encodeTl,encodeTr))
      case ProductType(tys) =>
        throw new Error(s"ProductType not yet encoded, unable to do ${ty.pretty}")
        //todo
      case ∀(_) =>
        throw new Error(s"Poly Type not yet encoded, unable to do ${ty.pretty}")
        //todo
    }
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
          val updatedUsedSymbols = updatedUsedSymbols0
          (encbody, updatedUsedSymbols, newBVars)
        case _ => throw new Exception(s"encountered unexpected definition format when trying to encode ${t.pretty} in LP")
      }
  }

  final def clauseVars2LP(fvs: Seq[(Int, Type)], sig: Signature, usedSymbols0: Set[lpStatement]): (Seq[lpOlTypedVar], Map[Int, String],Set[lpStatement]) = {
    val fvCount = fvs.size
    var boundVars: Seq[lpOlTypedVar] = Seq.empty
    var usedSymbols = usedSymbols0

    // A new map is created to keep track of the names of the implicitly quantfied variables
    var resultBindingMap: Map[Int, String] = Map()
    var curImplicitlyQuantified = fvs
    var i = 0
    while (i < fvCount) {
      val (scope, ty) = curImplicitlyQuantified.head
      val name = intToName(fvCount - i - 1)
      val encType = type2LP(ty,sig)
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
      val (encBot,_) = term2LP(LitFalse,bVarMap,sig,usedSymbols)
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
          val encTyTl = type2LP(left.ty,sig)
          usedSymbols = usedSymbolsR
          if (lit.polarity) {
            encLit = lpOlTypedBinaryConnectiveTerm(lpEq,encTyTl,lefEnc,rigEnc)
          } else {
            encLit = lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,encTyTl,lefEnc,rigEnc))
          }
        } else {
          val (termEnc, usedSymbolsUpdated) = term2LP(lit.left, bVarMap, sig, usedSymbols)
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

  final def clause2LP_unquantified(cl: Clause, usedSymbols0: Set[lpStatement], sig: Signature): (Seq[Either[lpOlTypedVar,lpOlTyVar]],lpOlUntypedBinaryConnectiveTerm_multi, Set[lpStatement]) = {
    val freeVarsExist = cl.implicitlyBound.nonEmpty || cl.typeVars.nonEmpty
    var usedSymbols = usedSymbols0
    if (freeVarsExist) {
      // If there are free variables, they are implicitly quantified over, in the encoding this quantification should be explicit
      // Add implicitly quantified type variables
      var quantifiedVars: Seq[Either[lpOlTypedVar,lpOlTyVar]] = Seq.empty
      // todo: add the T vars to counted here
      //  and: is it right to just make these things Set types? It should be since we can only quantify over mono types right?
      quantifiedVars = quantifiedVars ++ (cl.typeVars.reverse.map(i => Right(lpOlTyVar(s"T${intToName(i - 1)}"))))
      // Add implicitly quantified typed variables
      val (namedFVEnumerationLP, bVarMap, usedSymbolsUpdated) = clauseVars2LP(cl.implicitlyBound, sig, usedSymbols)
      quantifiedVars = quantifiedVars ++ namedFVEnumerationLP.map(Left(_))
      // With this we now encode the actual clause
      val (encClause, usedSymbolsClause) = clause2LP0(cl, bVarMap, sig, usedSymbolsUpdated)
      usedSymbols = usedSymbolsClause
      (quantifiedVars,encClause,usedSymbols)
    } else {
      // otherwise we just encode the clause and lift it to a proof term
      val (encClause, usedSymbolsClause) = clause2LP0(cl, Map.empty, sig, usedSymbols)
      usedSymbols = usedSymbolsClause
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
  def var2Lp(boundVars: Seq[(Int, Type)], bVars: Map[Int, String], sig: Signature, prefix: Boolean = true): Seq[lpOlTypedVar] = {
    boundVars.map(v => var2Lp(v._1, v._2, bVars,sig,prefix))
  }
  def var2Lp(scope: Int, typ: Type, bVars: Map[Int, String], sig: Signature, prefix: Boolean ): lpOlTypedVar = {
    val encType = type2LP(typ, sig, prefix)
    (lpOlTypedVar(lpOlConstantTerm(bVars(scope)), encType))
  }
  def term2LP(t: Term, bVars: Map[Int,String], sig:Signature, usedSymbols:Set[lpStatement], supressReduction:Boolean = false, prefix: Boolean = true): (lpOlTerm,Set[lpStatement]) = {
    //todo: dont i need the offset? was it an oversight not to use it in term2lp?

    // todo: combine cases for encoding binders

    t match {
      // Constant symbols
      case Symbol(id) => val name = sig(id).name
        val symbol = tptpDefinedSymbolMap.getOrElse(name, lpEscapeTerm(name,sig,prefix))
        (symbol, usedSymbols)
      // Numbers
      case Integer(n) =>
        val encodedInt = lpInt(n)
        (encodedInt,usedSymbols+encodedInt)
      case Rational(n, d) => throw new Error(s"rationals are not encoded yet ${t.pretty}") //s"$n/$d"
      case Real(w, d, e) => throw new Error(s"reals are not encoded yet ${t.pretty}") //if (e == 0) s"$w.$d" else s"$w.${d}E$e"
      // Give Bound variables names
      case Bound(_, scope) =>
        (var2Lp(scope,t.ty,bVars,sig,prefix),usedSymbols)

      // Unary connectives
      case Not(t2) =>
        val (encBody, usedSymbolsUpdated) = term2LP(t2, bVars, sig, usedSymbols,supressReduction,prefix)
        (lpOlUnaryConnectiveTerm(lpNot,encBody), usedSymbolsUpdated)
      case Forall(_) =>
        val (bVarTys, body) = collectForall(t)
        val newBVars = makeBVarList(bVarTys, bVars.size)
        val (encBody, usedSymbolsUpdated) = term2LP(body, fusebVarListwithMap(newBVars, bVars), sig, usedSymbols,supressReduction,prefix)
        val usedSymbolsQuant = usedSymbolsUpdated
        var quantifiedVars: Seq[lpOlTypedVar]= Seq.empty
        newBVars foreach { s_ty =>
          val encType = type2LP(s_ty._2, sig, prefix)
          quantifiedVars = quantifiedVars :+ lpOlTypedVar(lpOlConstantTerm(s_ty._1),encType)
        }
        (lpOlBoundTerm(lpOlForAll,quantifiedVars,encBody), usedSymbolsQuant)
      case Exists(_) =>
        // todo: Add explicit types for quantifiers?
        val (bVarTys, body) = collectExists(t)
        val newBVars = makeBVarList(bVarTys, bVars.size)
        val (encBody, usedSymbolsUpdated) = term2LP(body, fusebVarListwithMap(newBVars, bVars), sig, usedSymbols,supressReduction,prefix)
        val usedSymbolsQuant = usedSymbolsUpdated
        var quantifiedVars: Seq[lpOlTypedVar] = Seq.empty
        newBVars foreach { s_ty =>
          val encType = type2LP(s_ty._2, sig,prefix)
          quantifiedVars = quantifiedVars :+ lpOlTypedVar(lpOlConstantTerm(s_ty._1), encType)
        }
        (lpOlBoundTerm(lpOlExists, quantifiedVars, encBody), usedSymbolsQuant)
      case TyForall(_) => throw new Error(s"type quantifiers are not encoded yet ${t.pretty}")
      case Choice(_) =>
        val (bVarTys, body) = collectChoice(t)
        val newBVars = makeBVarList(bVarTys, bVars.size)
        val (encBody, usedSymbolsUpdated) = term2LP(body, fusebVarListwithMap(newBVars, bVars), sig, usedSymbols, supressReduction,prefix)
        var boundVars: Seq[lpOlTypedVar] = Seq.empty
        newBVars foreach { s_ty =>
          val encType = type2LP(s_ty._2, sig,prefix)
          boundVars = boundVars :+ lpOlTypedVar(lpOlConstantTerm(s_ty._1), encType)
        }
        (lpOlBoundTerm(lpChoice, boundVars, encBody), usedSymbolsUpdated)

      // Binary connectives
      case tl ||| tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols ,supressReduction,prefix)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL ,supressReduction,prefix)
        (lpOlUntypedBinaryConnectiveTerm(lpOr,encodedTl,encodedTr), updatedUsedSymbolsR)
      case tl & tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols ,supressReduction,prefix)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL ,supressReduction,prefix)
        (lpOlUntypedBinaryConnectiveTerm(lpAnd,encodedTl,encodedTr), updatedUsedSymbolsR)
      case tl === tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols ,supressReduction,prefix)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL ,supressReduction,prefix)
        val encTyTl = type2LP(tl.ty,sig,prefix)
        // todo: here i need to make changes for polymorphic types of LP TYPE Scheme
        (lpOlTypedBinaryConnectiveTerm(lpEq,encTyTl,encodedTl,encodedTr), updatedUsedSymbolsR)
      case tl !=== tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols ,supressReduction,prefix)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL ,supressReduction,prefix)
        val encTyTl = type2LP(tl.ty,sig,prefix)
        // like equ: todo: here i need to make changes for polymorphic types of LP TYPE Scheme
        (lpOlTypedBinaryConnectiveTerm(lpInEq,encTyTl.lift2Poly,encodedTl,encodedTr), updatedUsedSymbolsR)
      case tl Impl tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols ,supressReduction,prefix)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL ,supressReduction,prefix)
        (lpOlUntypedBinaryConnectiveTerm(lpImp,encodedTl,encodedTr), updatedUsedSymbolsR)
      case tr <= tl =>
        //throw new Error(s"encountered un-encoded connective <= ${t.pretty}")
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols ,supressReduction,prefix)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL ,supressReduction,prefix)
        (lpOlUntypedBinaryConnectiveTerm(lpImp, encodedTl, encodedTr), updatedUsedSymbolsR)
      case _ <=> _ => throw new Error(s"encountered un-encoded connective <=> ${t.pretty}")
      case tl ~& tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols, supressReduction,prefix)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL, supressReduction,prefix)
        (lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlUnaryConnectiveTerm(lpNot,encodedTl),lpOlUnaryConnectiveTerm(lpNot,encodedTr)),updatedUsedSymbolsR)
      case tl ~||| tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, sig, usedSymbols, supressReduction,prefix)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, sig, updatedUsedSymbolsL, supressReduction,prefix)
        (lpOlUnaryConnectiveTerm(lpNot,lpOlUntypedBinaryConnectiveTerm(lpOr,encodedTl,encodedTr)),updatedUsedSymbolsR)
      case t1 <~> t2 => throw new Error(s"encountered un-encoded connective <~> ${t.pretty}")

      // term abstraction in terms
      case _ :::> _ =>
        val t0 = if (supressReduction) t else t.etaContract
        if (t != t0) term2LP(t0, bVars, sig, usedSymbols ,supressReduction,prefix)
        else {
          val (bVarTys, body) = collectLambdasLP(t)
          val newBVars = makeBVarList(bVarTys, bVars.size)
          val (encBody, updatedUsedSymbols0) = term2LP(body,fusebVarListwithMap(newBVars, bVars),sig,usedSymbols ,supressReduction,prefix)
          var updatedUsedSymbols = updatedUsedSymbols0
          var abstractions: Seq[Either[lpOlTypedVar,lpOlTyVar]] = Seq.empty
          newBVars foreach { s_ty =>
            val encType = type2LP(s_ty._2, sig,prefix)
            abstractions = abstractions :+ Left(lpOlTypedVar(lpOlConstantTerm(s_ty._1),encType))//todo: for polymorphy we might also need to use Scheme types here
            // todo: summarize same types into one bracket
          }
          (lpOlLambdaTerm(abstractions,encBody), updatedUsedSymbols)
        }

      case TypeLambda(_) =>
        val (tyAbsCount, body) = collectTyLambdas(0, t)
        val tyVars = (1 to tyAbsCount).map(n => Right(lpOlTyVar(s"T${intToName(n -1)}")))
        val (encBody, updatedUsedSymbols) = term2LP(body,bVars,sig,usedSymbols ,supressReduction,prefix)
        // todo: not really sure how this should be encoded, check with examples
        //throw new Error(s"encountered typeLambda, this is not encoded yet ${t.pretty}")
        (lpOlLambdaTerm(tyVars,encBody),updatedUsedSymbols)

      // match pattern of application
      case _@Symbol(id) ∙ args if leo.modules.input.InputProcessing.adHocPolymorphicArithmeticConstants.contains(id) =>
        val opName = lpEscapeName(sig(id).name, sig)
        val (opType,tyVars) = polyType2Lp(sig(id)._ty,sig)
        val arithmeticOperator = lpTptpOperator(opName,opType,tyVars)
        var updatedUsedSymbols = usedSymbols+arithmeticOperator

        var arguments: Seq[Either[lpOlTerm, lpOlType]] = Seq.empty
        args foreach { arg =>
          arg match {
            case Left(termArg) =>
              val (encArg, updatedUsedSymbols0) = term2LP(termArg, bVars, sig, updatedUsedSymbols ,supressReduction,prefix)
              updatedUsedSymbols = updatedUsedSymbols0
              arguments = arguments :+ Left(encArg)
            case Right(tyArg) =>
              val encArg = type2LP(tyArg, sig,prefix)
              arguments = arguments :+ Right(encArg)
          }
        }
        (lpOlFunctionApp(arithmeticOperator,arguments), updatedUsedSymbols)

      case f ∙ args =>
        val (translatedF, updatedUsedSymbols0) = term2LP(f, bVars, sig, usedSymbols ,supressReduction,prefix)
        var updatedUsedSymbols = updatedUsedSymbols0
        var arguments:Seq[Either[lpOlTerm,lpOlType]] = Seq.empty
        args foreach { arg =>
          arg match {
            case Left(termArg) =>
              val (encArg, updatedUsedSymbols0) = term2LP(termArg, bVars, sig, updatedUsedSymbols ,supressReduction,prefix)
              updatedUsedSymbols = updatedUsedSymbols0
              arguments = arguments :+ Left(encArg)
            case Right(tyArg) =>
              val encArg = type2LP(tyArg, sig,prefix)
              arguments = arguments :+ Right(encArg)
          }
        }
        // special case: unapplied connectives as head symbols
        translatedF match {
          case con:lpOlUnappliedConnective =>
            (applyPartiallyAppliedConnective(con,arguments,Seq.empty),updatedUsedSymbols)

          case _ => (lpOlFunctionApp(translatedF,arguments),updatedUsedSymbols)
        }

      // Others should be invalid
      case _ => throw new IllegalArgumentException("Unexpected term format during conversion to LP")
    }
  }

  case class lpLiteral(
                        left: lpOlTerm,
                        right: lpOlTerm,
                        tyLhs: lpOlType,
                        term: lpOlTerm,
                        pol: Boolean,
                        eq: Boolean
                      ){
    def normPol: lpLiteral = {
      if (eq) (left, right) match {
        case (lpOlUnaryConnectiveTerm(`lpNot`,left0),lpOlUnaryConnectiveTerm(`lpNot`,right0)) => lpLiteral(left0,right0,lpOtype,pol,eq)
        case _ => this
      } else this
    }
  }
  object lpLiteral {
    def constructFullLit (encLeft: lpOlTerm, encRight: lpOlTerm, encTy: lpOlType, pol: Boolean, eq: Boolean): lpOlTerm ={
      val encTerm0 = if (eq) lpOlTypedBinaryConnectiveTerm(lpEq, encTy, encLeft, encRight) else encLeft
      if (pol) encTerm0 else lpOlUnaryConnectiveTerm(lpNot, encTerm0)
    }
    def apply(lit: Literal, bVarMap: Map[Int, String], sig: Signature): lpLiteral = {
      val encLeft = term2LP(lit.left, bVarMap, sig)._1
      val encRight = if (lit.equational) term2LP(lit.right, bVarMap, sig)._1 else lpOlTop
      val encTy = type2LP(lit.left.ty, sig)
      val encTerm = constructFullLit(encLeft,encRight,encTy,lit.polarity, lit.equational)
      lpLiteral(encLeft, encRight, encTy, encTerm, lit.polarity, lit.equational)
    }

    def apply(encLeft: lpOlTerm, encRight: lpOlTerm, encTy: lpOlType, pol: Boolean, eq: Boolean): lpLiteral = {
      val encTerm = constructFullLit(encLeft,encRight, encTy, pol, eq)
      lpLiteral(encLeft, encRight, encTy, encTerm, pol, eq)
    }

    def apply(fullLit: lpOlTerm): lpLiteral = {
      fullLit match {
        case lpOlUnaryConnectiveTerm(`lpNot`,body) =>
          body match {
            case lpOlTypedBinaryConnectiveTerm(`lpEq`,ty,lhs,rhs) =>
              lpLiteral(lhs,rhs,ty,false,true)
            case lhs =>
              lpLiteral(lhs,lpOlTop,lpOtype,false,false)
          }
        case lpOlTypedBinaryConnectiveTerm(`lpEq`, ty, lhs, rhs) =>
          lpLiteral(lhs, rhs, ty, true, true)
        case lhs =>
          lpLiteral(lhs, lpOlTop, lpOtype, true, false)
      }
    }
  }

  case class lpClauseInst(
                     term: lpOlTerm,
                     lits: Seq[lpOlTerm],
                     vars: Seq[Either[lpOlTypedVar, lpOlTyVar]]
                     ){
    /** Returns `vars` as a plain sequence of `lpOlTerm`. */
    def metaVars: Seq[lpTypedVar] = vars.map{
      case Left(typedVar) => typedVar.asMlVar
      case Right(tyVar) => tyVar.asMlVar
    }
  }

  object lpClauseInst{
    def apply(cl: Clause, sig: Signature): lpClauseInst ={
      val encClause = clause2LP_unquantified(cl,Set.empty,sig)
      lpClauseInst(encClause._2,encClause._2.args,encClause._1)
    }

    def apply_to_set(cls: Seq[Clause], sig: Signature): ( Map[Int, String],Seq[lpClauseInst]) = {
      val allImpBoundVars = cls.flatMap(_.implicitlyBound).distinct
      val fullBvarsMap = clauseVars2LP(allImpBoundVars, sig, Set.empty)._2
      val encCls = cls.map(cl => clause2LP0(cl,fullBvarsMap,sig,Set.empty)._1)
      val encVars: Seq[Seq[Either[lpOlTypedVar, lpOlTyVar]]] = cls.map(cl => var2Lp(cl.implicitlyBound,fullBvarsMap,sig).map(Left(_)))
      (fullBvarsMap, encCls.zip(encVars).map(ecnCl => lpClauseInst(ecnCl._1, ecnCl._1.args, ecnCl._2)))
    }
  }
}
