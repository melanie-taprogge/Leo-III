package leo.modules.output.LPoutput.NewLpDatastructures

import leo.datastructures.Signature.Key
import leo.datastructures.Term.{Integer, Rational, Real}
import leo.datastructures.{Clause, ClauseProxy, Literal, Signature, Term, Type}
import leo.datastructures.Type._
import leo.datastructures.Term._
import leo.datastructures.impl.TermAbstr
import leo.modules.HOLSignature
import leo.modules.HOLSignature._
import leo.modules.output.LPoutput.Encodings.collectLambdasLP
import leo.modules.output.LPoutput.LPoutput.abbreviationSignatureFile
import leo.modules.output.LPoutput.NewLpDatastructures.LogicConst.{Bot, cEq}
import leo.modules.output._
import leo.modules.output.ToTHF.{collectChoice, collectExists, collectForall, collectForallTys, collectLambdas, collectTyLambdas}
import leo.modules.output.logger.Out
import leo.modules.output.LPoutput.NewLpDatastructures.Stmt._
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm._
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{El, LpSet}
import leo.modules.output.LPoutput.NewLpDatastructures.OlType.{Base, Fun, TyVar}
import leo.modules.output.LPoutput.NewLpDatastructures.Proof._
import leo.modules.output.LPoutput.NewLpDatastructures.tptpConstMappings.leoBinders
import leo.modules.output.LPoutput.{Lifting, nameDefn, nameSkDef}

object Encoder {

  @inline def nameTyVar(scope: Int) = Name(s"T${intToName(scope - 1)}")

  def type2LP(ty: Type): (OlType) = {
    ty match {
      case BaseType(id) =>
        Base(SymRef.Leo(id))
      case ComposedType(id, args) =>
        var encArgs: Seq[OlType] = Seq.empty
        args foreach { arg =>
          val encArg = type2LP(arg)
          encArgs = encArgs :+ encArg
        }
        throw new Exception(s"attempting to encode composed Type, this was never tested! \ninput was ${ty.pretty}")
      case BoundType(scope) =>
        val tyName = nameTyVar(scope)
        throw new Exception(s"attempting to encode bound Type, this was never tested! \ninput was ${ty.pretty}")
      case tl -> tr =>
        val encodeTl = type2LP(tl)
        val encodeTr = type2LP(tr)
        Fun(Seq(encodeTl, encodeTr))
      case ProductType(tys) =>
        throw new Error(s"ProductType not yet encoded, unable to do ${ty.pretty}")
      //todo
      case ∀(_) =>
        throw new Error(s"Poly Type not yet encoded, unable to do ${ty.pretty}")
      //todo
    }
  }

  def vars2Lp(boundVars: Seq[(Int, Type)], bVars: Map[Int, String]): Seq[Var[Level.Obj]] = {
    boundVars.map(v => var2Lp(v._1, v._2, bVars))
  }

  def var2Lp(scope: Int, typ: Type, bVars: Map[Int, String]): Var[Level.Obj] = { //todo: detect type variables and handle differently?
    val encType = type2LP(typ)
    assert(bVars.contains(scope), s"Error in Lambdapi encoding: Trying to encode var of scope $scope that is not in bVars Map ($bVars)")
    (Var(Name(bVars(scope)), Some(El(encType))))
  }

  def args2LP(args: Seq[Either[Term, Type]], bVars: Map[Int, String], supressReduction: Boolean = false): (Seq[Arg[Level.Obj]], Set[QName]) = {
    // todo: Probably this can be done more niceley with folding :-)
    var updatedUsedSymbols: Set[QName] = Set.empty
    var arguments: Seq[Arg[Level.Obj]] = Seq.empty
    args foreach { arg =>
      arg match {
        case Left(termArg) =>
          val (encArg, updatedUsedSymbols0) = term2LP(termArg, bVars, supressReduction)
          updatedUsedSymbols = updatedUsedSymbols0
          arguments = arguments :+ Arg.Explicit(encArg)
        case Right(tyArg) =>
          val encArg = Arg.ExplicitTypeArg(type2LP(tyArg))
          arguments = arguments :+ encArg
      }
    }
    (arguments, updatedUsedSymbols)
  }

  // todo: do i even need to match on connectives? my unapply functions should also match stuff that is not explicitly encoded as connectices, shouldn't it?
  def term2LP(t: Term, bVars: Map[Int, String], supressReduction: Boolean = false): (LpTerm[Level.Obj], Set[QName]) = {

    t match {
      // Constant symbols
      case Symbol(id) =>
        (Const(SymRef.Leo(id)), Set.empty)
      //todo: Numbers
      /*
    case Integer(n) => 
      val encodedInt = lpInt(n)
      (encodedInt, usedSymbols + encodedInt)
    case Rational(n, d) => throw new Error(s"rationals are not encoded yet ${t.pretty}") //s"$n/$d"
    case Real(w, d, e) => throw new Error(s"reals are not encoded yet ${t.pretty}") //if (e == 0) s"$w.$d" else s"$w.${d}E$e"
     */

      // todo: Variables
      case Bound(_, scope) =>
        (var2Lp(scope, t.ty, bVars), Set.empty)


      case Forall(_) =>
        t match {
          case Forall(bVarTy :::> body) =>
            val newBVar = (intToName(bVars.size), bVarTy) //makeBVarList(Seq(bVarTys), bVars.size)
            val (encBody, usedSymbolsUpdated) = term2LP(body, fusebVarListwithMap(Seq(newBVar), bVars), supressReduction)
            val quantifiedVar = {
              val encType = type2LP(bVarTy)
              (Name(intToName(bVars.size)), El(encType))
            }
            (LogicConst.Forall(quantifiedVar, encBody), usedSymbolsUpdated)
          case Forall(_) =>
            term2LP(t.etaExpand,bVars,supressReduction)
        }

      case Exists(_) =>
        t match {
          case Exists(bVarTy :::> body) =>
            val newBVar = (intToName(bVars.size), bVarTy) //makeBVarList(Seq(bVarTys), bVars.size)
            val (encBody, usedSymbolsUpdated) = term2LP(body, fusebVarListwithMap(Seq(newBVar), bVars), supressReduction)
            val quantifiedVar = {
              val encType = type2LP(bVarTy)
              (Name(intToName(bVars.size)), El(encType))
            }
            (LogicConst.Exists(quantifiedVar, encBody), usedSymbolsUpdated)
          case Exists(_) =>
            term2LP(t.etaExpand, bVars, supressReduction)
        }

      case Choice(_) =>
        t match {
          case Choice(bVarTy :::> body) =>
            val newBVar = (intToName(bVars.size), bVarTy) //makeBVarList(Seq(bVarTys), bVars.size)
            val (encBody, usedSymbolsUpdated) = term2LP(body, fusebVarListwithMap(Seq(newBVar), bVars), supressReduction)
            val quantifiedVar = {
              val encType = type2LP(bVarTy)
              (Name(intToName(bVars.size)), El(encType))
            }
            (LogicConst.Choice(quantifiedVar, encBody), usedSymbolsUpdated)
          case Choice(_) =>
            term2LP(t.etaExpand, bVars, supressReduction)
        }
        /*
      case TyForall(_) => throw new Error(s"type quantifiers are not encoded yet ${t.pretty}")
         */

      /*
    // Unary connectives
    case Not(t2) =>
      val (encBody, usedSymbolsUpdated) = term2LP(t2, bVars, usedSymbols, supressReduction)
      (LogicConst.Not(encBody), usedSymbolsUpdated)

    // Binary connectives
    case tl ||| tr =>
      val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, usedSymbols, supressReduction)
      val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, updatedUsedSymbolsL, supressReduction)
      (LogicConst.Or(encodedTl, encodedTr), updatedUsedSymbolsR)
    case tl & tr =>
      val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, usedSymbols, supressReduction)
      val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, updatedUsedSymbolsL, supressReduction)
      (LogicConst.And(encodedTl, encodedTr), updatedUsedSymbolsR)
    case tl === tr =>
      val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, usedSymbols, supressReduction)
      val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, updatedUsedSymbolsL, supressReduction)
      val encTyTl = type2LP(tl.ty)
      // todo: here i need to make changes for polymorphic types of LP TYPE Scheme
      (lpOlTypedBinaryConnectiveTerm(lpEq, encTyTl, encodedTl, encodedTr), updatedUsedSymbolsR)
    case tl !=== tr =>
      val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, usedSymbols, supressReduction)
      val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, updatedUsedSymbolsL, supressReduction)
      val encTyTl = type2LP(tl.ty)
      // like equ: todo: here i need to make changes for polymorphic types of LP TYPE Scheme
      (lpOlTypedBinaryConnectiveTerm(lpInEq, encTyTl.lift2Poly, encodedTl, encodedTr), updatedUsedSymbolsR)
    case tl Impl tr =>
      val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, usedSymbols, supressReduction)
      val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, updatedUsedSymbolsL, supressReduction)
      (LogicConst.Imp(encodedTl, encodedTr), updatedUsedSymbolsR)

       */
      // special cases abstracted away in LP translation
      // todo: maybe handle in additional step explicitly? (i.e. add definitions and expand them)
      case tr <= tl =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, supressReduction)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, supressReduction)
        (LogicConst.Imp(encodedTl, encodedTr), updatedUsedSymbolsL ++ updatedUsedSymbolsR)
      case _ <=> _ => throw new Error(s"encountered un-encoded connective <=> ${t.pretty}")
      case tl ~& tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, supressReduction)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, supressReduction)
        (LogicConst.Or(LogicConst.Not(encodedTl), LogicConst.Not(encodedTr)), updatedUsedSymbolsL ++ updatedUsedSymbolsR)
      case tl ~||| tr =>
        val (encodedTl, updatedUsedSymbolsL) = term2LP(tl, bVars, supressReduction)
        val (encodedTr, updatedUsedSymbolsR) = term2LP(tr, bVars, supressReduction)
        (LogicConst.Not(LogicConst.Or(encodedTl, encodedTr)), updatedUsedSymbolsL ++ updatedUsedSymbolsR)
      case t1 <~> t2 => throw new Error(s"encountered un-encoded connective <~> ${t.pretty}")

      // term abstraction in terms
      case _ :::> _ =>
        val t0 = if (supressReduction) t else t.etaContract
        t0 match {
          case ty :::> body =>
            val newBVar = (intToName(bVars.size), ty)
            val (encBody, updatedUsedSymbols0) = term2LP(body, fusebVarListwithMap(Seq(newBVar), bVars), supressReduction)
            val abstraction: (Name, Option[LpType]) ={
              val encType = type2LP(newBVar._2)
              (Name(newBVar._1), Some(El(encType)))
            }
            (Lam(abstraction, encBody), updatedUsedSymbols0)
          case _ => term2LP(t0, bVars, supressReduction)
        }

      case TypeLambda(_) =>
        val (tyAbsCount, body) = collectTyLambdas(0, t)
        val tyVars = (1 to tyAbsCount).map(n => (Name(s"T${intToName(n - 1)}"), Some(LpSet)))
        val (encBody, updatedUsedSymbols) = term2LP(body, bVars, supressReduction)
        throw new Exception(s"Type Lambda")
        //(Lam(tyVars, encBody), updatedUsedSymbols)

      // match pattern of application
      //case _@Symbol(id) ∙ args if leo.modules.input.InputProcessing.adHocPolymorphicArithmeticConstants.contains(id) =>
      //  throw new Exception("polymorphic constructor!")

      case f ∙ args =>
        val (translatedF, updatedUsedSymbols0) = term2LP(f, bVars, supressReduction)
        val (arguments, updatedUsedSymbols) = args2LP(args, bVars, supressReduction)
        (App(translatedF, arguments), updatedUsedSymbols0 ++ updatedUsedSymbols)

      // Others should be invalid
      case _ => throw new IllegalArgumentException("Unexpected term format during conversion to LP")
    }
  }

  final def clauseVars2LP(fvs: Seq[(Int, Type)]): (Seq[Var[Level.Obj]], Map[Int, String]) = {
    val fvCount = fvs.size
    var boundVars: Seq[Var[Level.Obj]] = Seq.empty

    // A new map is created to keep track of the names of the implicitly quantfied variables
    var resultBindingMap: Map[Int, String] = Map()
    var curImplicitlyQuantified = fvs
    var i = 0
    while (i < fvCount) {
      val (scope, ty) = curImplicitlyQuantified.head
      val name = intToName(fvCount - i - 1)
      val encType = type2LP(ty)
      boundVars = boundVars :+ Var(Name(name), Some(El(encType)))
      resultBindingMap = resultBindingMap + (scope -> name)

      curImplicitlyQuantified = curImplicitlyQuantified.tail
      i = i + 1
    }
    (boundVars, resultBindingMap)
  }

  def lit2Lp(lit: Literal, bVarMap: Map[Int, String]): (LpTerm[Level.Obj], Set[QName]) = {
    if (lit.equational) {
      val (left, right) = (lit.left, lit.right)
      val (lefEnc, usedSymbolsL) = term2LP(left, bVarMap, false)
      val (rigEnc, usedSymbolsR) = term2LP(right, bVarMap, false)
      val encTyTl = type2LP(left.ty)
      val eqTerm = LogicConst.Eq(encTyTl, lefEnc, rigEnc)
      if (lit.polarity) {
        (eqTerm, usedSymbolsL ++ usedSymbolsR)
      } else {
        (LogicConst.Not(eqTerm),usedSymbolsL ++ usedSymbolsR)
      }
    } else {
      val (termEnc, usedSymbolsUpdated) = term2LP(lit.left, bVarMap, false)
      if (lit.polarity) {
        (termEnc, usedSymbolsUpdated)
      } else {
        (LogicConst.Not(termEnc),usedSymbolsUpdated)
      }
    }
  }

  def clauseLits2Lp(lits: Seq[Literal], bVarMap: Map[Int, String]): (Seq[LpTerm[Level.Obj]], Set[QName]) = {
    var usedSymbols = Set[QName]()
    // if the clause has no literals, we retrun bottom
    if (lits.isEmpty) {
      (Seq(Bot),usedSymbols)
    } else {
      var encLits: Seq[LpTerm[Level.Obj]] = Seq.empty
      // otherwise we encode and add the literals one by one
      val litIt = lits.iterator
      while (litIt.hasNext) {
        val lit = litIt.next()
        val (encLit, usedSymbols0) = lit2Lp(lit,bVarMap)
        // either start the clause with the encoded lit (if no lits have been added so far) or add it to the disjunction
        encLits = encLits :+ encLit
        usedSymbols = usedSymbols ++ usedSymbols0
      }
      (encLits,usedSymbols)
    }
  }

  final def clause2LP(cl: Clause): (lpClauseInst, Set[QName]) = {
    val freeVarsExist = cl.implicitlyBound.nonEmpty || cl.typeVars.nonEmpty
    if (freeVarsExist) {
      // Add implicitly quantified type variables
      var quantifiedVars: Seq[Either[Var[Level.Obj], TyVar]] = Seq.empty
      quantifiedVars = quantifiedVars ++ cl.typeVars.reverse.map(i => Right(TyVar(nameTyVar(i))))
      // Add implicitly quantified typed variables
      val (namedFVEnumerationLP, bVarMap) = clauseVars2LP(cl.implicitlyBound)
      quantifiedVars = quantifiedVars ++ namedFVEnumerationLP.map(Left(_))
      // With this we now encode the actual clause
      val (encClauseLits, usedSymbolsClause) = clauseLits2Lp(cl.lits, bVarMap)
      (lpClauseInst(encClauseLits,quantifiedVars),usedSymbolsClause)
    } else {
      // otherwise we just encode the clause and lift it to a proof term
      val (encClauseLits, usedSymbolsClause) = clauseLits2Lp(cl.lits, Map.empty)
      (lpClauseInst(encClauseLits,Seq.empty),usedSymbolsClause)
    }
  }


  def constDfn(dnfName: QName, ty: OlType, hd: LpTerm[Level.Obj], defn: LpTerm[Level.Obj], freeVars: Seq[Var[Level.Obj]]): Stmt.Declaration = {
    val defAsEq = LogicConst.Eq(ty, hd, defn)
    val bindings: Seq[(Name, LpType)] = freeVars.map(v => (v.name, v.ty.get)) //todo: ensure all have type?
    Stmt.Declaration(dnfName.local, bindings, Lifting.ProofTerm(defAsEq))
  }

  def encDfn(key: Key, sig: LpSig, isSk: Boolean): (Stmt.Declaration, Set[QName]) = {
    val symbol = sig.orig.apply(key)
    val defTermType = Encoder.type2LP(symbol._defn.ty)
    val hd = Const[Level.Obj](SymRef.Leo(key))
    if (isSk){
      val skolemDefName = nameSkDef(key, sig.orig)
      val (bVarTys, strippedDef) = collectLambdasLP(symbol._defn)
      val newBVars = makeBVarList(bVarTys, 0)
      val encBvars = newBVars.map(v => LpTerm.Var[Level.Obj](Name(v._1), Some(El(Encoder.type2LP(v._2)))))
      val appliedSk = LpTerm.App[Level.Obj](hd, encBvars.map(Arg.Explicit(_)))
      val (definition, tptpDefinedSymbols) = Encoder.term2LP(strippedDef, fusebVarListwithMap(newBVars, Map()), false)
      val encDef = constDfn(skolemDefName,defTermType,appliedSk, definition,encBvars)
      (encDef, tptpDefinedSymbols)
    }else{
      val dnfName = nameDefn(key, sig)
      val (definition, tptpDefinedSymbols) = Encoder.term2LP(symbol._defn, Map(), false)
      val encDef = constDfn(dnfName, defTermType, hd, definition,Seq.empty)
      (encDef, tptpDefinedSymbols)
    }
  }


}




