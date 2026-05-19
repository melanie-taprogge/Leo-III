package leo.modules.output.LPoutput.NewLpDatastructures

import leo.Out
import leo.datastructures.Signature.Key
import leo.datastructures.{Clause, Literal, Term, Type}
import leo.datastructures.Type._
import leo.datastructures.Term._
import leo.modules.HOLSignature._
import leo.modules.output.LPoutput.EncodeResult.NotEncodable
import leo.modules.output.LPoutput.LpLibs.ND.Terms.lpWitnessCon
import leo.modules.output.LPoutput.OldLpDatastructures.Encodings.collectLambdasLP
import leo.modules.output._
import leo.modules.output.ToTHF.{collectForallTys, collectTyLambdas}
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm._
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{El, LpSet}
import leo.modules.output.LPoutput.NewLpDatastructures.OlMonoType.{Base, Fun, TyApp, TyVar}
import leo.modules.output.LPoutput.NewLpDatastructures.OlPolyType.{LiftedMono, TyQuant}
import leo.modules.output.LPoutput.{nameDefn, nameSkDef}


//////////////////////////////////////////
// Utility for translating Leo-III
// datastrucutres to the Lambdapi encoding
//////////////////////////////////////////

object TypeEncoding {

  // ** Encoding of types

  //todo: does it really make sense to already assign a name here or should we just keep numbers?
  /** Assign name to bound type variables */
  @inline private def nameTyVar(scope: Int) = Name(s"T${intToName(scope - 1)}")

  /** Assign name to bound type variables */
  @inline def tyVar2LP(tv: Int): Name = nameTyVar(tv)

  def polyType2LP(ty: Type): OlPolyType = ty match {
    case ∀(_) =>
      val (tyAbsCount, bodyTy) = collectForallTys(0, ty)
      val encBodyTy = type2LP(bodyTy)
      val quantifiers = (1 to tyAbsCount).map(scope => OlMonoType.TyVar(tyVar2LP(scope)))
      TyQuant(quantifiers, encBodyTy)
    case _ => LiftedMono(type2LP(ty))
  }

  /** Translate (Object-logical HOL) types to the Lambdapi Encoding */
  def type2LP(ty: Type): OlMonoType = {
    ty match {
      case BaseType(id) =>
        Base(SymRef.Leo(id))
      case ComposedType(id, args) =>
        val encHd = SymRef.Leo(id)
        val encArgs = args.map(type2LP)
        TyApp(encHd,encArgs)
      case BoundType(scope) =>
        val tyName = tyVar2LP(scope)
        OlMonoType.TyVar(tyName)
      case tl -> tr =>
        val encodeTl = type2LP(tl)
        val encodeTr = type2LP(tr)
        Fun(Seq(encodeTl, encodeTr))
      case ProductType(tys) =>
        throw new Error(s"ProductType not yet encoded, unable to do ${ty.pretty}")
      //todo
      case ∀(_) =>
//        TyQuant
        throw new Error(s"Error in LP Encoding: Found quantified type outside of prefix position")
      //todo
    }
  }

  /**
    * Translate (Object-logical HOL) types with prenex-quantification to the Lambdapi Encoding
    *
    * @note This is currently only used for the sake of declaring polymorphic builtin math operators of the TPTP and will fail in the general case
    * */
  def polyType2Lp(ty: Type): LpType = {
    ty match {
      case ∀(_) => val (tyAbsCount, bodyTy) = collectForallTys(0, ty)
        val variables = (1 to tyAbsCount).map(i => Var[Level.Meta](tyVar2LP(i), Some(LpType.LpSet)))
        val encBody = type2LP(bodyTy)
        LpType.Pi(variables, LpType.El(encBody))
      case _ => LpType.El(type2LP(ty))
    }
  }

  /** Helper for Decomp steps:
    * safe encoder of types that does not throw on poly types but just regurns a Not encodable mesage
    */
  def safeEncTy(ty: Type): Either[NotEncodable, OlMonoType] = {
    ty match {
      case ComposedType(_, _) =>
        Left(NotEncodable("Error: trying to encode ComposedType"))
      case ProductType(_) =>
        Left(NotEncodable("Error: trying to encode ProductType"))
      case ∀(_) =>
        Left(NotEncodable("Error: trying to encode quantified Type"))
      case _ => Right(type2LP(ty))
    }
  }

  def safeEncTypes(tys: Seq[Type]): Either[NotEncodable, Vector[OlMonoType]] = {
    tys.foldLeft[Either[NotEncodable, Vector[OlMonoType]]](Right(Vector.empty)) {
      case (Left(err), _) => Left(err)
      // else, continue
      case (Right(acc), nextTy) =>
        safeEncTy(nextTy) match {
          case Left(error) => Left(error)
          case Right(encTy) => Right(acc :+ encTy)
        }
    }
  }
}

object TermEncoding {
  import TypeEncoding.type2LP

  // ** Encoding of terms

  /** Translate a sequence of variables to Lambdapi (assigns names and translated types) */
  @inline def vars2Lp(boundVars: Seq[(Int, Type)], bVars: Map[Int, String]): Seq[Var[Level.Obj]] = boundVars.map(v => var2Lp(v._1, v._2, bVars))

  //todo: already assign names here?

  /** Translate a single variable to Lambdapi (assigns names and translated types) */
  def var2Lp(scope: Int, typ: Type, bVars: Map[Int, String]): Var[Level.Obj] = {
    val encType = type2LP(typ)
    assert(bVars.contains(scope), s"Error in Lambdapi encoding: Trying to encode var of scope $scope that is not in bVars Map ($bVars)")
    Var(Name(bVars(scope)), Some(El(encType)))
  }

  /** Translate an individual argument to Lambdapi and mark it as explicit */
  private def arg2LP(arg: Either[Term, Type], bVars: Map[Int, String], supressReduction: Boolean = false, replaceUnknownVars: Boolean = false): Arg[Level.Obj] = {
    arg match {
      case Left(termArg) =>
        Arg.Explicit(term2LP(termArg, bVars, supressReduction, replaceUnknownVars))
      case Right(tyArg) =>
        Arg.ExplicitTypeArg(type2LP(tyArg))
    }
  }

  /** Translate a sequence of arguments to Lambdapi and marks them as explicit */
  @inline def args2LP(args: Seq[Either[Term, Type]], bVars: Map[Int, String], supressReduction: Boolean = false, replaceUnknownVars: Boolean = false): List[Arg[Level.Obj]] = {
    args.map(arg2LP(_, bVars, supressReduction, replaceUnknownVars)).toList
  }

  //todo: handle replacing unknown Vars differently... -> have a step that both does that and adjusts the numbers of the remaining variables -> check how this is done in Leo
  @inline def bVarGen(bVars: Map[Int, String], ty: Type, replaceUnknownVars: Boolean)={
    if (replaceUnknownVars && bVars.nonEmpty) (intToName(bVars.map(_._1).max), ty) else (intToName(bVars.size), ty)
  }

  /**
    * Translate (Object-logical HOL) terms to the Lambdapi Encoding
    *
    * @param t                 term to be translated
    * @param bVars             mapping of variable ids to assigned names
    * @param suppressReduction Boolean indicating weather reduction (for isntance of eta expanded terms) should be suppressed
    * @return The encoded Object-level term
    * */
  def term2LP(t: Term, bVars: Map[Int, String], suppressReduction: Boolean = false, replaceUnknownVars: Boolean = false): LpTerm[Level.Obj] = {

    t match {
      // Constant symbols
      case Symbol(id) =>
        Const(SymRef.Leo(id))

      // Numbers
      case Integer(n) =>
        val encodedInt = TptpInt[Level.Obj](n)
        encodedInt
      case Rational(n, m) =>
        val encodedRat = TptpRational[Level.Obj](n, m)
        encodedRat
      case Real(n, m, l) =>
        val encodedReal = TptpReal[Level.Obj](n, m, l)
        encodedReal

      case Bound(ty, scope) if (replaceUnknownVars && !bVars.contains(scope)) =>
        val encType = type2LP(ty)
        LpTerm.App[Level.Obj](lpWitnessCon, Seq(Arg.ExplicitTypeArg(encType))) //todo: constructor for witness

      // todo: Variables using DB indices
      case Bound(_, scope) =>
        var2Lp(scope, t.ty, bVars)

      // Handle binders explicitly as they may requrire eta-expansion
      case Forall(_) =>
        t match {
          case Forall(bVarTy :::> body) =>
            val newBVar = bVarGen(bVars,bVarTy,replaceUnknownVars)//(intToName(bVars.size), bVarTy)
            val encBody = term2LP(body, fusebVarListwithMap(Seq(newBVar), bVars), suppressReduction, replaceUnknownVars)
            val quantifiedVar = {
              val encType = type2LP(bVarTy)
              (Name(newBVar._1), El(encType))
            }
            LogicConst.Forall(quantifiedVar, encBody)
          case Forall(_) =>
            term2LP(t.etaExpand, bVars, suppressReduction, replaceUnknownVars)
        }
      case Exists(_) =>
        t match {
          case Exists(bVarTy :::> body) =>
            val newBVar = bVarGen(bVars,bVarTy,replaceUnknownVars)//(intToName(bVars.size), bVarTy) //makeBVarList(Seq(bVarTys), bVars.size)
            val encBody = term2LP(body, fusebVarListwithMap(Seq(newBVar), bVars), suppressReduction, replaceUnknownVars)
            val quantifiedVar = {
              val encType = type2LP(bVarTy)
              (Name(newBVar._1), El(encType))
            }
            LogicConst.Exists(quantifiedVar, encBody)
          case Exists(_) =>
            term2LP(t.etaExpand, bVars, suppressReduction, replaceUnknownVars)
        }
      case Choice(_) =>
        t match {
          case Choice(bVarTy :::> body) =>
            val newBVar = bVarGen(bVars,bVarTy,replaceUnknownVars)//(intToName(bVars.size), bVarTy) //makeBVarList(Seq(bVarTys), bVars.size)
            val encBody = term2LP(body, fusebVarListwithMap(Seq(newBVar), bVars), suppressReduction, replaceUnknownVars)
            val quantifiedVar = {
              val encType = type2LP(bVarTy)
              (Name(newBVar._1), El(encType))
            }
            LogicConst.Choice(quantifiedVar, encBody)
          case Choice(_) =>
            term2LP(t.etaExpand, bVars, suppressReduction, replaceUnknownVars)
        }
      /*
      case TyForall(_) => throw new Error(s"type quantifiers are not encoded yet ${t.pretty}")
         */

      // special cases abstracted away in LP translation
      // todo: maybe handle in additional step explicitly? (i.e. add definitions and expand them)
      case tr <= tl =>
        val encodedTl = term2LP(tl, bVars, suppressReduction, replaceUnknownVars)
        val encodedTr = term2LP(tr, bVars, suppressReduction, replaceUnknownVars)
        LogicConst.Imp(encodedTl, encodedTr)
      case _ <=> _ => throw new Error(s"encountered un-encoded connective <=> ${t.pretty}")
      case tl ~& tr =>
        val encodedTl = term2LP(tl, bVars, suppressReduction, replaceUnknownVars)
        val encodedTr = term2LP(tr, bVars, suppressReduction, replaceUnknownVars)
        LogicConst.Or(LogicConst.Not(encodedTl), LogicConst.Not(encodedTr))
      case tl ~||| tr =>
        val encodedTlL = term2LP(tl, bVars, suppressReduction, replaceUnknownVars)
        val encodedTrR = term2LP(tr, bVars, suppressReduction, replaceUnknownVars)
        LogicConst.Not(LogicConst.Or(encodedTlL, encodedTrR))
      case t1 <~> t2 => throw new Error(s"encountered un-encoded connective <~> ${t.pretty}")

      // term abstraction in terms
      case _ :::> _ =>
        val t0 = if (suppressReduction) t else t.etaContract
        if (t != t0) term2LP(t0, bVars, suppressReduction, replaceUnknownVars)
        else
          t0 match {
            case ty :::> body =>
              val newBVar = bVarGen(bVars,ty,replaceUnknownVars)
              val encBody = term2LP(body, fusebVarListwithMap(Seq(newBVar), bVars), suppressReduction, replaceUnknownVars)
              val abstraction: (Name, Option[LpType]) = {
                val encType = type2LP(newBVar._2)
                (Name(newBVar._1), Some(El(encType)))
              }
              Lam(abstraction, encBody)
            case _ => term2LP(t0, bVars, suppressReduction, replaceUnknownVars)
          }

      case TypeLambda(_) =>
        val (tyAbsCount, body) = collectTyLambdas(0, t)
        val tyVars = (1 to tyAbsCount).map(n => (Name(s"T${intToName(n - 1)}"), Some(LpSet)))
        val encBody = term2LP(body, bVars, suppressReduction, replaceUnknownVars)
        throw new Exception(s"Error in Lambdapi encoding: Unencoded Type Lambda")

      case f ∙ args =>
        val translatedF = term2LP(f, bVars, suppressReduction, replaceUnknownVars)
        val arguments = args2LP(args, bVars, suppressReduction, replaceUnknownVars)
        App(translatedF, arguments)

      // Others should be invalid
      case _ => throw new IllegalArgumentException("Unexpected term format during conversion to LP")
    }
  }
}

  // ** Translation of clauses

object ClauseEncoding {
  import TypeEncoding.type2LP
  import TypeEncoding.tyVar2LP
  import TermEncoding.term2LP

  /**
    * Translate clause-variables to Lambdapi
    *
    * @param fvs Sequence of free variables of the original clause
    * @return - Sequence of encoded variables
    *         - a mapping of the variable-ids to their associated names
    * */
  final def clauseVars2LP(fvs: Seq[(Int, Type)]): (Seq[Var[Level.Obj]], Map[Int, String]) = {
    val fvCount = fvs.size
    var boundVars: Seq[Var[Level.Obj]] = Seq.empty
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

  /**
    * Translate Leo-III literals to the Lambdapi Encoding.
    * Equational literals are encoded as object-level equation and negative polarity
    * of a literla is enocded asobject-level negation.
    *
    * @param lit   original literal
    * @param bVarMap mapping of variable ids to assigned names
    * @return The encoded clause as a lambdapi clause object (lpClauseInst)
    * @note Built-in equality and the meta-equality of equational literals are not
    *       differentiated in the encoding
    * */
  def lit2Lp(lit: Literal, bVarMap: Map[Int, String], surpressReduction: Boolean = false, replaceUnknownVars: Boolean = false): lpLiteralInst = {
    if (lit.equational) {
      val (left, right) = (lit.left, lit.right)
      val lefEnc = term2LP(left, bVarMap, surpressReduction,replaceUnknownVars)
      val rigEnc = term2LP(right, bVarMap, surpressReduction,replaceUnknownVars)
      val encTyTl = type2LP(left.ty)
      val eqTerm = LogicConst.Eq(encTyTl, lefEnc, rigEnc)
      if (lit.polarity) {
        lpLiteralInst(eqTerm,true,true)
      } else {
        lpLiteralInst(LogicConst.Not(eqTerm),false,true)
      }
    } else {
      val termEnc = term2LP(lit.left, bVarMap, surpressReduction,replaceUnknownVars)
      if (lit.polarity) {
        lpLiteralInst(termEnc,true,false)
      } else {
        lpLiteralInst(LogicConst.Not(termEnc),false,false)
      }
    }
  } // todo: potentially pattern match to also make literals negative that leo thinks are positive but have a leading negation?

  /** Encode a sequence of Leo-III literals to Lambdapi */
  @inline def lits2Lp(lits: Seq[Literal], bVarMap: Map[Int, String]): Seq[lpLiteralInst] = lits.map(lit2Lp(_, bVarMap))

  /**
    * Translate Leo-III clauses to the Lambdapi Encoding
    *
    * @param cl original clause
    * @return The encoded clause as a lambdapi clause object (lpClauseInst)
    * */
  final def clause2LP(cl: Clause): lpClauseInst = {
    val freeVarsExist = cl.implicitlyBound.nonEmpty || cl.typeVars.nonEmpty
    if (freeVarsExist) {
      var quantifiedVars: Seq[Either[Var[Level.Obj], TyVar]] = Seq.empty
      // Add clause-type-variables
      quantifiedVars = quantifiedVars ++ cl.typeVars.reverse.map(i => Right(TyVar(tyVar2LP(i))))
      // Add clause-term-variables
      val (namedFVEnumerationLP, bVarMap) = clauseVars2LP(cl.implicitlyBound)
      quantifiedVars = quantifiedVars ++ namedFVEnumerationLP.map(Left(_))
      // Encode the individual literals with the generated bVarMap
      val encClauseLits = lits2Lp(cl.lits, bVarMap)
      lpClauseInst(encClauseLits, quantifiedVars)
    } else {
      // Encode the individual literals
      val encClauseLits = lits2Lp(cl.lits, Map.empty)
      lpClauseInst(encClauseLits, Seq.empty)
    }
  }

}

  // ** Encode definitions
  object DefEncoding {
    import TypeEncoding.type2LP
    import TermEncoding.term2LP

    /** Helper constructing the actual equality making up the definition */
    private def constDfn(dnfName: QName, ty: OlMonoType, hd: LpTerm[Level.Obj], defn: LpTerm[Level.Obj], freeVars: Seq[Var[Level.Obj]]): Stmt.Declaration = {
      val defAsEq = LogicConst.Eq(ty, hd, defn)
      val bindings: Seq[(Name, LpType)] = freeVars.map(v => (v.name, v.ty.get)) //todo: ensure all have type?
      Stmt.Declaration(dnfName.local, bindings, Lifting.ProofTerm(defAsEq))
    }

    /** Encode definitions given in the TPTP problem or constructed throughout proof search (in case of skolem terms)
      *
      * @param key the key of the symbol to be defined in the Leo-III signature
      * @param sig Leo-III signature extended with the mappings necessary for the Lambdapi encoding
      * @param isSk Boolean indicating weather the definition to be encoded is a skolem definition
      * @return Lambdapi Declaration of the encoded definition
      * */
    def encDfn(key: Key, sig: LpSig, isSk: Boolean): Stmt.Declaration = {
      val symbol = sig.orig.apply(key)
      val defTermType = type2LP(symbol._defn.ty)
      val hd = Const[Level.Obj](SymRef.Leo(key))
      if (isSk) {
        val skolemDefName = nameSkDef(key, sig.orig)
        val (bVarTys, strippedDef) = collectLambdasLP(symbol._defn)
        val newBVars = makeBVarList(bVarTys, 0)
        val encBvars = newBVars.map(v => LpTerm.Var[Level.Obj](Name(v._1), Some(El(type2LP(v._2)))))
        val appliedSk = LpTerm.App[Level.Obj](hd, encBvars.map(Arg.Explicit(_)))
        val definition = term2LP(strippedDef, fusebVarListwithMap(newBVars, Map()), false)
        val encDef = constDfn(skolemDefName, defTermType, appliedSk, definition, encBvars)
        encDef
      } else {
        val dnfName = nameDefn(key, sig)
        val definition = term2LP(symbol._defn, Map(), false)
        val encDef = constDfn(dnfName, defTermType, hd, definition, Seq.empty)
        encDef
      }
    }

  }






