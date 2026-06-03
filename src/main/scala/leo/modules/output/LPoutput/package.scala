package leo.modules.output

import leo.Out
import leo.datastructures.Signature.Key
import leo.datastructures.Term.{:::>, TypeLambda, ∙}
import leo.datastructures.{Clause, Literal, Position, Signature, Subst, Term, Type}
import leo.modules.HOLSignature._
import leo.modules.output.LPoutput.OldLpDatastructures.Encodings.{term2LP, type2LP}
import leo.modules.output.LPoutput.LPoutput.abbreviationSignatureFile
import leo.modules.output.LPoutput.NewLpDatastructures.{Arg, Level, LpSig, LpTerm, LpType, Name, OlMonoType, Prefix, QName, lpTermBuilder}
import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures.{PrettyConfig, lpAnd, lpChoice, lpConstantTerm, lpDeclaration, lpDefinition, lpElWitness, lpEq, lpFunctionApp, lpHave, lpImp, lpInEq, lpLambdaTerm, lpNot, lpOlBinder, lpOlBot, lpOlBoundTerm, lpOlConnective, lpOlConstantTerm, lpOlExists, lpOlForAll, lpOlFunctionApp, lpOlFunctionType, lpOlLambdaTerm, lpOlMonoQuantifiedTerm, lpOlPolyType, lpOlTerm, lpOlTop, lpOlTyVar, lpOlType, lpOlTypedBinaryConnective, lpOlTypedBinaryConnectiveTerm, lpOlTypedVar, lpOlUnappliedConnective, lpOlUnaryConnective, lpOlUnaryConnectiveTerm, lpOlUntypedBinaryConnective, lpOlUntypedBinaryConnectiveTerm, lpOlUntypedBinaryConnectiveTerm_multi, lpOlUntypedVar, lpOlUserDefinedPolyType, lpOlUserDefinedType, lpOlWildcard, lpOr, lpOtype, lpProofScript, lpProofScriptStep, lpRefine, lpReflexivity, lpRewritePattern, lpScheme, lpSet, lpSet2Schme, lpTerm, lpTypedVar, lpUntypedVar, lpWildcard}

package object LPoutput {

  ////////////////////////////////////////////////////////////////
  ////////// Name Generation
  ////////////////////////////////////////////////////////////////
  def nameHypothesis(usedH: Int): lpConstantTerm = {
    lpConstantTerm(s"h${usedH + 1}")
  }

  def nameBottom(usedB: Int): lpOlConstantTerm = {
    lpOlConstantTerm(s"b${usedB + 1}")
  }

  def nameX(usedX: Int): lpOlConstantTerm = {
    lpOlConstantTerm(s"x${usedX + 1}")
  }

  def nameType(usedT: Int): lpOlPolyType = {
    lpOlUserDefinedPolyType(s"t${usedT + 1}")
  }

  def nameStep(number: Long): lpConstantTerm = {
    lpConstantTerm(s"step${number}")
  }

  def nameStep_new(number: Long): QName = {
    QName.local(s"step${number}")
  }

  def nameDefn(name: Key, sig: LpSig): QName = {
    val baseName = sig.termNames(name)
    QName.in(Prefix.Formula,s"${baseName.local.value}_def")
  }

  @inline def nameSkDef(sko: Signature.Key, sig: Signature): QName = {
    val baseName = s"${sig(sko).name}_def"
    QName.local(baseName)
  }

  ////////////////////////////////////////////////////////////////
  ////////// New LP AST helpers
  ////////////////////////////////////////////////////////////////

  /**
    * Collect the leading object-level lambda binders of an LP term.
    *
    * This keeps the AST shape intact: the returned binders are ordinary
    * `LpTerm.Var[Level.Obj]` values that can later be reused for Π lifting,
    * lambda wrapping, or object-level applications.
    */
  def collectLeadingLambdas(term: LpTerm[Level.Obj], acc: Vector[LpTerm.Var[Level.Obj]] = Vector.empty): (Vector[LpTerm.Var[Level.Obj]], LpTerm[Level.Obj]) = term match {
    case LpTerm.Lam((name, ty @ Some(LpType.El(_))), body) =>
      collectLeadingLambdas(body, acc :+ LpTerm.Var[Level.Obj](name, ty))
    case LpTerm.Lam((name, ty), _) =>
      assert(false, s"LP encoding: expected object-level binder type for lambda $name, got $ty")
      (acc, term)
    case _ =>
      (acc, term)
  }

  /**
    * Flatten a curried LP application into its head and explicit/implicit
    * argument spine.
    *
    * Lambdapi printing and construction may nest applications, e.g. `(f a) b`;
    * many encodings want to inspect this as `f` applied to `a, b`.
    */
  def flattenAppSpine(term: LpTerm[Level.Obj]): (LpTerm[Level.Obj], Seq[Arg[Level.Obj]]) = term match {
    case LpTerm.App(f, args) =>
      val (hd, prefixArgs) = flattenAppSpine(f)
      (hd, prefixArgs ++ args)
    case _ => (term, Seq.empty)
  }

  /**
    * Split the first argument type from an encoded HOL function type.
    *
    * `OlMonoType.Fun` stores a full function spine.  For a type
    * `a -> b -> c`, this returns `a` and the residual function type `b -> c`.
    */
  def splitOlFun(ty: OlMonoType): Option[(OlMonoType, OlMonoType)] = ty match {
    case OlMonoType.Fun(Seq(argTy, resultTy)) => Some((argTy,resultTy))
    case OlMonoType.Fun(argTy +: rest) if rest.nonEmpty => Some((argTy,OlMonoType.Fun(rest)))
    case _ => None
  }

  /**
    * Eta-expand two LP object terms in lockstep according to their HOL type.
    *
    * Existing matching leading lambdas are preserved and only their bodies are
    * recursively expanded.  If exactly one side is already a lambda, the pair is
    * left unchanged; this avoids manufacturing asymmetric proof obligations.
    */
  def etaExpandTermPair(ty: OlMonoType, left: LpTerm[Level.Obj], right: LpTerm[Level.Obj], namePrefix: String): (LpTerm[Level.Obj], LpTerm[Level.Obj]) = {
    def go(curTy: OlMonoType, l: LpTerm[Level.Obj], r: LpTerm[Level.Obj], depth: Int): (LpTerm[Level.Obj], LpTerm[Level.Obj]) = splitOlFun(curTy) match {
      case Some((argTy, resultTy)) =>
        (l,r) match {
          case (LpTerm.Lam(lBinder, lBody), LpTerm.Lam(rBinder, rBody)) =>
            val (newLBody, newRBody) = go(resultTy,lBody,rBody,depth + 1)
            (LpTerm.Lam(lBinder,newLBody), LpTerm.Lam(rBinder,newRBody))
          case (LpTerm.Lam(_, _), _) | (_, LpTerm.Lam(_, _)) =>
            (l,r)
          case _ =>
            val etaVar = LpTerm.Var[Level.Obj](Name(s"${namePrefix}_${depth}"), Some(LpType.El(argTy)))
            val (newLBody, newRBody) = go(resultTy,lpTermBuilder.app(l,Seq(etaVar)),lpTermBuilder.app(r,Seq(etaVar)),depth + 1)
            (LpTerm.Lam(etaVar.name -> etaVar.ty,newLBody), LpTerm.Lam(etaVar.name -> etaVar.ty,newRBody))
        }
      case None => (l,r)
    }
    go(ty,left,right,0)
  }

  val lambdapiNames = Set(
    lpOtype.pretty, lpWildcard.pretty, lpSet.pretty, lpScheme.pretty,
    lpSet2Schme.pretty, lpEq.pretty, lpElWitness.pretty) // todo:generate automatically

  val lpAllowedRegEx = """^[^\t\r\n :,;`(){}\[\]".@$|?/]+$"""
  val lpKeywords = Set(
    "require", "open", "symbol", "notation", "builtin", "opaque",
    "rule", "unif_rule", "coerce_rule", "inductive", "proof",
    "assume", "apply", "refine", "simplify", "rewrite", "have",
    "print", "proofterm", "assert", "assertnot", "compute",
    "constant", "injective", "commutative", "associative",
    "in", "notation", "reflexivity", "admit", "right", "left",
    "induction", "focus", "generalize", "orelse", "remove",
    "repeat", "set", "solve", "symmetry", "try", "why3", "with",
    "abort", "admitted", "fail", "search", "type", "as", "begin",
    "debug", "end", "flag", "infix", "off", "on", "postfix",
    "prefix", "private", "protected", "prover", "prover_timeout",
    "quantifier", "sequential", "TYPE"
  ) ++ lambdapiNames

  def findSafeName(str: String, sig: Signature): String = {
    val newName = s"${str}_"
    if (!sig.exists(newName)) newName
    else findSafeName(newName, sig)
  }

  private final val partiallyAlliedTPTPmap: Map[String, lpOlUnappliedConnective] = //Vector("=", "!=", "&", "|", "~", "!", "?")
  // symbol =_part (a : Set) ≔ λ (x y : τ a), x = y;
    Map.apply("~" -> lpNot.unapplied,
      "=" -> lpEq.unapplied,
      "!=" -> lpInEq.unapplied,
      "&" -> lpAnd.unapplied,
      "|" -> lpOr.unapplied,
      "!" -> lpOlForAll.unapplied,
      "?" -> lpOlExists.unapplied,
      "@+" -> lpChoice.unapplied)
  // todo: the other connectives

  def applyPartiallyAppliedConnective(con: lpOlUnappliedConnective, args: Seq[Either[lpOlTerm,lpOlType]], impArgs: Seq[Either[lpOlTerm,lpOlType]]): lpOlTerm ={
    //Out.lp_debug_info(s"encoding partially applied connective: ${con.pretty} with args ${args}")
    con.base match {
      case con0: lpOlUnaryConnective =>
        // if there is at leas one arguemnt, we can apply it
        assert(impArgs.isEmpty, "LP-Encoding: Encountered unexpected implicit arguments")
        args match {
          case Seq(Left(arg0)) => (lpOlUnaryConnectiveTerm(con0, arg0))
          case _ =>
            if (args.length > 0) lpOlFunctionApp(con,args)
            else con
        }
      case con0: lpOlUntypedBinaryConnective =>
        assert(impArgs.isEmpty, "LP-Encoding: Encountered unexpected implicit arguments")
        args match {
          case Seq(Left(arg0),Left(arg1)) => (lpOlUntypedBinaryConnectiveTerm(con0, arg0, arg1))
          case _ =>
            if (args.length > 0) lpOlFunctionApp(con, args)
            else con
        }
      case con0: lpOlTypedBinaryConnective =>
        impArgs ++ args match {
          case Seq(Right(arg0), Left(arg1), Left(arg2)) => (lpOlTypedBinaryConnectiveTerm(con0, arg0, arg1, arg2))
          case _ =>
            if (args.length > 0) lpOlFunctionApp(con, (impArgs ++ args).tail, Seq((impArgs ++ args).head))
            else con
        }
      case con0: lpOlBinder =>
        impArgs ++ args match {
          case Seq(Right(arg0), Left(arg1)) =>
            arg1 match {
              case lpOlLambdaTerm(vars,body0) =>
                assert(vars.length > 0)
                vars.head match {
                  case Left(typedVar) =>
                    val body = if (vars.length == 1) body0 else lpOlLambdaTerm(vars.tail,body0)
                    lpOlMonoQuantifiedTerm(con0, typedVar, body)
                }
              case _ => lpOlFunctionApp(con, Seq(Left(arg1)), Seq(Right(arg0)))
            }
          case _ =>
            if (args.length > 0) lpOlFunctionApp(con, (impArgs ++ args).tail, Seq((impArgs ++ args).head))
            else con
        }
    }
  }

  final def lpEscapeName(str: String, sig: Signature, prefix: Boolean = true): String = {
    val prefixStr = if (prefix) s"${abbreviationSignatureFile}" else ""
    if (partiallyAlliedTPTPmap.keySet.contains(str)) {
      throw new Exception(s"trying to escape name for parially applied connective $str, this should not happen")
    } //throw new Exception(s"found illegal $str")
    else if (lpKeywords.contains(str)) {
      val newName = findSafeName(str, sig)
      //Out.lp_debug_info(s"renamed $str to $newName")
      return prefixStr + newName
    }
    if (!str.matches(lpAllowedRegEx)) {
      val newName = s"{|$str|}"
      Out.lp_debug_info(s"renamed $str to $newName")
      prefixStr + newName
    }
    else (if (prefix && !str.matches("^sk\\d+(?:_def)?$")) prefixStr + str else str)
  }

  //final def lpPrefixSymbols()

  final def lpEscapeTerm(str: String,sig: Signature, prefix: Boolean = true): lpOlTerm = {
    if (partiallyAlliedTPTPmap.keySet.contains(str)) {
      // todo: eventhough lambdapi can handle reusing of variable names, we should make sure to generate some fresh variable names for our new anonomus functions
      return partiallyAlliedTPTPmap(str)
    }
    else {
      val safeName = lpEscapeName(str, sig, prefix)
      lpOlConstantTerm(safeName)
    }
  }

  def applyAnyStep(listOfTacitcs: lpOlTerm) = {
    // todo: figure out where this sould actually be
    lpOlFunctionApp(lpOlConstantTerm("applyAny"), Seq(Left(listOfTacitcs)))
  }

  def liftVarsToMeta(vars:  Seq[Either[lpOlTypedVar, lpOlTyVar]]): Seq[lpTypedVar]={
    vars.map(liftVarsToMeta((_)))
  }
  def liftVarsToMeta(var0: Either[lpOlTypedVar, lpOlTyVar]): lpTypedVar = {
    var0 match {
      case Left(tyVar) => tyVar.asMlVar
      case Right(termVar) => termVar.asMlVar
    }
  }

  def isTermVar(var0: Either[lpOlTypedVar, lpOlTyVar]): lpOlTypedVar = {
    var0 match {
      case Left(termVar) => termVar
      case Right(tyVar) => throw new Exception(s"need a term variable but found a type variable")
    }
  }


  def clauseRuleQuantification(parent: Clause, bVarMap: Map[Int, String], sig: Signature): (Seq[lpTypedVar], Seq[lpUntypedVar]) = {
    //throw new Exception("CHANGE clauseRuleQuantification")

    var clauseQuantification: Seq[lpTypedVar] = Seq.empty
    var applySymbolsToParent: Seq[lpUntypedVar] = Seq.empty
    parent.implicitlyBound foreach { name_type =>
      //clauseQuantification.append(s"(${bVarMap(name_type._1)}: $Els($uparrow ${type2LP(name_type._2, sig)._1}))")
      clauseQuantification = clauseQuantification :+ lpTypedVar(lpConstantTerm(bVarMap(name_type._1)), type2LP(name_type._2, sig).lift2Meta)
      //applySymbolsToParent = applySymbolsToParent ++ Seq(bVarMap(name_type._1))
      applySymbolsToParent = applySymbolsToParent :+ lpUntypedVar(lpConstantTerm(bVarMap(name_type._1)))
    }
    (clauseQuantification, applySymbolsToParent)

  }

  def findLitInClause(lit: Literal, parent: Clause): Seq[Int] = {
    val indicesOfOccurrence: IndexedSeq[Int] = parent.lits.indices.filter(index => parent.lits(index) == lit)
    if (indicesOfOccurrence.length == 0) throw new Exception(s"literal to transform not found in clause when attempfing to generate lp encoding")
    else indicesOfOccurrence
  }

  def generateWrapperPattern(litIndex:Int, clauseLen:Int, polarity:Boolean, lhs:Option[Boolean], eqType:Option[lpOlType], patternTerm:lpOlTerm):lpOlUntypedBinaryConnectiveTerm_multi={
    Out.lp_debug_info(s"lit indices: $litIndex, clause length: $clauseLen")
    val literal = {
      if (! lhs.isDefined) patternTerm
      else if (lhs.get) {
        assert(eqType.isDefined, "Error in Lambdapi encoidng when generating a pattern: Missing type of an euqational literal")
        lpOlTypedBinaryConnectiveTerm(lpEq,eqType.get,patternTerm,lpOlWildcard)
      } else {
        assert(eqType.isDefined, "Error in Lambdapi encoidng when generating a pattern: Missing type of an euqational literal")
        lpOlTypedBinaryConnectiveTerm(lpEq, eqType.get, lpOlWildcard, patternTerm)
      }
    }
    generateClausePattern(Seq(litIndex),clauseLen, polarity, literal)
  }

  def generateClausePattern(termPosSeq:Seq[Int],clauseLen:Int, polarity:Boolean = true, patternTerm:lpOlTerm = lpOlUntypedVar(lpOlConstantTerm("x"))): lpOlUntypedBinaryConnectiveTerm_multi ={
    assert(termPosSeq.max <= clauseLen, s"Error in Lambdapi encoidng when generating a pattern: Literal index (${termPosSeq.max} out of bounds for clause of length $clauseLen)")
    val litPol = if (polarity) patternTerm else lpOlUnaryConnectiveTerm(lpNot,patternTerm)
    var args : Seq[lpOlTerm] = Seq.fill(clauseLen)(lpOlWildcard)
    termPosSeq foreach {pos =>
      args = args.updated(pos, litPol)
    }
    lpOlUntypedBinaryConnectiveTerm_multi(lpOr, args)
  }


  def generateClausePatternTerm(varPos: Seq[Int], clauseLen: Int, eqPos: Option[Int] = None, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpOlConstantTerm("x")), polarity: Boolean = true): Option[lpRewritePattern] = {
    // given the position of the literal that a rule should be applied to in a clause and weather or not this clause in embedded in an equality to be proven,
    // generate a rewrite pattern
    // todo: change encoding to take true/false as argument for equality position

    val maybeNegatedPatternVar = {
      if (polarity) patternVar
      else lpOlUnaryConnectiveTerm(lpNot, patternVar)
    }

    val clausePattern = if (clauseLen > 1) {
      generateClausePattern(varPos,clauseLen,true,maybeNegatedPatternVar)
    } else {
      maybeNegatedPatternVar
    }

    eqPos match {
      case Some(pos) =>
        val patternEq = {
          if (pos == 0) lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, clausePattern, lpOlWildcard)
          else if (pos == 1) lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlWildcard, clausePattern)
          else throw new Exception(s"position $pos provided to encode position in equality")
        }
        Some(lpRewritePattern(patternEq, patternVar))
      case None =>
        if (clausePattern == maybeNegatedPatternVar) None
        else Some(lpRewritePattern(clausePattern, patternVar))
    }
  }

  def acessSubterm(t: Term, position: Seq[Int], sig: Signature, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x"))): (lpOlTerm, Term) = {
    // generate a pattern
    // todo: rahter than using this function, use leoPosition2LpPattern and rely on the leo encodings of positions for a unified approach

    // if the length of position is 1, we arrived at the last step and want to provide a proof
    if (position.length == 0) (patternVar, t)

    else {
      val currentPosition = position.head
      t match {
        case tl ||| tr =>
          if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(tr, position.tail, sig, patternVar)
            (lpOlUntypedBinaryConnectiveTerm(lpOr, intermediatePattern, lpOlWildcard), intermediateTerm)
          }
          else if (currentPosition == 2) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(tl, position.tail, sig, patternVar)
            (lpOlUntypedBinaryConnectiveTerm(lpOr, lpOlWildcard, intermediatePattern), intermediateTerm)
          }
          else throw new Exception(s"invalid position $currentPosition vor connective ${lpOr.pretty}")
        case Not(t2) =>
          if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(t2, position.tail, sig, patternVar)
            (lpOlUnaryConnectiveTerm(lpNot, intermediatePattern), intermediateTerm)
          }
          else throw new Exception(s"invalid position $currentPosition vor connective ${lpOr.pretty}")
        case tl === tr =>
          val ty = type2LP(tl.ty, sig)
          if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(tr, position.tail, sig, patternVar)
            (lpOlTypedBinaryConnectiveTerm(lpEq, ty, intermediatePattern, lpOlWildcard), intermediateTerm)
          }
          else if (currentPosition == 2) {
            val (intermediatePattern, intermediateTerm) = acessSubterm(tl, position.tail, sig, patternVar)
            (lpOlTypedBinaryConnectiveTerm(lpEq, ty, lpOlWildcard, intermediatePattern), intermediateTerm)
          }
          else throw new Exception(s"invalid position $currentPosition for connective ${lpOr.pretty}")
        //case f ∙ args =>
          //val (intermediatePattern, intermediateTerm) = acessSubterm(args(currentPosition +1), position.tail, sig, patternVar)
          //throw new Exception(s"this is an application to ${f.pretty}")

        case _ => throw new Exception(s"connective ${t.pretty} not encoded?")
      }
    }
  }
  def findRWTerm(rwMap:Map[lpOlTerm, lpOlTerm], searchIn:lpOlTerm, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x"))): (lpRewritePattern, lpOlTerm) = {
    val (patternTerm, rewrittenTerm,counter, rwUnderBinder) = findRWTerm0(rwMap,searchIn, false, patternVar,0)
    if (counter != 1) throw new Exception(s"when trying to locate ${rwMap.keySet.map(_.pretty)} in ${searchIn.pretty}, ${counter} occurrences were found")
    val rewritePattern = lpRewritePattern(patternTerm,patternVar)
    (rewritePattern,rewrittenTerm)
  }

  // todo: implement type substitution
  //def lpTySubst(tyRwMap:Map[lpOlTerm,lpOlType],)

  def findRWTerm0(termRwMap:Map[lpOlTerm, lpOlTerm], searchIn:lpOlTerm, rwUnderBinder:Boolean = false, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x")), currentX:Int = 0): (lpOlTerm, lpOlTerm, Int, Boolean) = {
    // todo: introduce type rw as well
    // find a specific subterm for the application of a rewrite operation
    // this function returns: The rewrite-pattern, the term modulo rewriting and an integer signaling how often the pattern was found.
    if (termRwMap.keySet.contains(searchIn)) (patternVar,termRwMap(searchIn), currentX + 1, rwUnderBinder)
    //else if (tyRwMap.keySet.contains(searchIn)) (patternVar,tyRwMap(searchIn), currentX + 1, rwUnderBinder)
    else {
      searchIn match {
        case `lpOlTop` =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case `lpOlBot` =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case _: lpOlUnappliedConnective => (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case lpOlConstantTerm(_) =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case lpOlTypedVar(_,_) =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      //case lpOlTyVar(_) =>
          //(lpOlWildcard, searchIn, 0, rwUnderBinder)
      case lpOlUntypedVar(lpConstantTerm(_)) =>
        (lpOlWildcard, searchIn, 0, rwUnderBinder)
      case lpOlLambdaTerm(vars,body) =>
        val (patternbody, rewrittenbody0, counter, _) = findRWTerm0(termRwMap, body, rwUnderBinder, patternVar, 0)
        val pattern = if (counter == 0) lpOlWildcard else lpOlLambdaTerm(vars, patternbody)
        val rewrittenTerm = lpOlLambdaTerm(vars, rewrittenbody0)
        (pattern, rewrittenTerm, counter, true)
      case lpOlBoundTerm(quantifier, vars, body) =>
        val (patternbody, rewrittenbody0, counter, _) = findRWTerm0(termRwMap, body, rwUnderBinder, patternVar, 0)
        val pattern = if (counter == 0) lpOlWildcard else lpOlBoundTerm(quantifier, vars, patternbody)
        val rewrittenTerm = lpOlBoundTerm(quantifier, vars, rewrittenbody0)
        (pattern, rewrittenTerm, counter, true)
      case lpOlUnaryConnectiveTerm(con, term) =>
          val (patternTerm, rewrittenTerm0, counter, rwUnderBinder0) = findRWTerm0(termRwMap, term, rwUnderBinder, patternVar, 0)
          // to make sure patterns are not longer than necessary, we check weather rewriting at a specific position happend and - if this is not the case - just give "-"
          val pattern = if (counter == 0) lpOlWildcard else lpOlUnaryConnectiveTerm(con, patternTerm)
          val rewrittenTerm = lpOlUnaryConnectiveTerm(con, rewrittenTerm0)
          (pattern, rewrittenTerm, counter, rwUnderBinder0)
      case lpOlUntypedBinaryConnectiveTerm(con,lhs,rhs) =>
        val (patternLhs, rewrittenLhs, counterLhs, rwUnderBinderLhs) = findRWTerm0(termRwMap, lhs, rwUnderBinder, patternVar, 0)
        val (patternRhs, rewrittenRhs, counterRhs, rwUnderBinderRhs) = findRWTerm0(termRwMap, rhs, rwUnderBinder, patternVar, 0)
        // to make sure patterns are not longer than necessary, we check weather rewriting at a specific position happend and - if this is not the case - just give "-"
        val newCounter = counterLhs + counterRhs
        val pattern = if (newCounter == 0) lpOlWildcard else lpOlUntypedBinaryConnectiveTerm(con,patternLhs,patternRhs)
        val rewrittenTerm = lpOlUntypedBinaryConnectiveTerm(con,rewrittenLhs,rewrittenRhs)
        (pattern, rewrittenTerm, newCounter, rwUnderBinderLhs || rwUnderBinderRhs)
      case lpOlUntypedBinaryConnectiveTerm_multi(con, args) =>
        val intermediateResult = args.map(arg => findRWTerm0(termRwMap, arg, rwUnderBinder, patternVar, 0))
        // to make sure patterns are not longer than necessary, we check weather rewriting at a specific position happend and - if this is not the case - just give "-"
        val newCounter = intermediateResult.map(_._3).sum
        val pattern = if (newCounter == 0) lpOlWildcard else lpOlUntypedBinaryConnectiveTerm_multi(con, intermediateResult.map(_._1))
        val rewrittenTerm = lpOlUntypedBinaryConnectiveTerm_multi(con, intermediateResult.map(_._2))
        val rwUnderBinder0 = intermediateResult.map(_._4).contains(true)
        (pattern, rewrittenTerm, newCounter, rwUnderBinder0)
      case lpOlTypedBinaryConnectiveTerm(con, ty, lhs, rhs) =>
        val (patternLhs, rewrittenLhs, counterLhs, rwUnderBinderLhs) = findRWTerm0(termRwMap, lhs, rwUnderBinder, patternVar, 0)
        val (patternRhs, rewrittenRhs, counterRhs, rwUnderBinderRhs) = findRWTerm0(termRwMap, rhs, rwUnderBinder, patternVar, 0)
        // to make sure patterns are not longer than necessary, we check weather rewriting at a specific position happend and - if this is not the case - just give "-"
        val newCounter = counterLhs + counterRhs
        val pattern = if (newCounter == 0) lpOlWildcard else lpOlTypedBinaryConnectiveTerm(con, ty, patternLhs, patternRhs)
        val rewrittenTerm = lpOlTypedBinaryConnectiveTerm(con, ty, rewrittenLhs, rewrittenRhs)
        (pattern, rewrittenTerm, newCounter, rwUnderBinderLhs || rwUnderBinderRhs)
      case lpOlFunctionApp(head,args,_) =>
        val (patternHead, termHead, counterHead, rwUnderBinderHead) = findRWTerm0(termRwMap, head, rwUnderBinder, patternVar, 0)
        var patternsArgs: Seq[Either[lpOlTerm,lpOlType]] = Seq.empty
        var termsArgs: Seq[Either[lpOlTerm,lpOlType]] = Seq.empty
        var rwUnderBinderArg = false
        var countersArgs = 0
        args foreach{ arg =>
          arg match {
            case Left(term) =>
              val (patternArg0, termArg, counterArg, rwUnderBinderArg0) = findRWTerm0(termRwMap, term, rwUnderBinder, patternVar, 0)
              val patternArg = if (counterArg == 0) lpOlWildcard else patternArg0
              patternsArgs = patternsArgs :+ Left(patternArg)
              termsArgs = termsArgs :+ Left(termArg)
              countersArgs = countersArgs + counterArg
              if (rwUnderBinderArg0) rwUnderBinderArg = true
            case Right(ty) =>
              patternsArgs = patternsArgs :+ Left(lpOlWildcard)
              termsArgs = termsArgs :+ Right(ty)
          }
        }
        val pattern = if (counterHead + countersArgs == 0) lpOlWildcard else lpOlFunctionApp(patternHead, patternsArgs)
        val rewtrittenTerm = lpOlFunctionApp(termHead, termsArgs)
        (pattern,rewtrittenTerm,countersArgs, rwUnderBinderArg || rwUnderBinderHead)

        // just for testing
      case _ => throw new Exception(s"encountered unexptcted term $searchIn when trying to find terms ${termRwMap.keySet.map(_.pretty)} in ${searchIn.pretty}")
    }
    }
  }


  def leoPosition2LpPattern (t:Term, p:Position, sig:Signature, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x"))) : (lpOlTerm, Term, Option[String]) ={

    Out.lp_debug_info(s"posVector: ${p.pretty} (term: ${t.pretty})")
    val underBinderError = Some("Rewriting under binders not possible")

    // todo: do i need to also output the term or does it not matter in my use-cases?
    if (p.seq.length == 0) (patternVar, t, None)

    else {
      val currentPosition = p.posHead
      t match {
        case tl ||| tr =>
          if (currentPosition == 0) throw new Exception(s"when generating a rewrite pattern for Lambdapi, encountered position $currentPosition indicating ${lpOr.pretty}")
          else if (currentPosition == 1) {
          val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(tl, p.tail, sig, patternVar)
          (lpOlUntypedBinaryConnectiveTerm (lpOr, intermediatePattern, lpOlWildcard), intermediateTerm, cantEncode)}
          else if (currentPosition == 2) {
          val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(tr, p.tail, sig, patternVar)
          (lpOlUntypedBinaryConnectiveTerm (lpOr, lpOlWildcard, intermediatePattern), intermediateTerm, cantEncode)}
          else throw new Exception (s"invalid position $currentPosition for connective ${lpOr.pretty}")

        case lt & rt =>
          if (currentPosition == 0) throw new Exception(s"when generating a rewrite pattern for Lambdapi, encountered position $currentPosition indicating ${lpAnd.pretty}")
          else if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(lt, p.tail, sig, patternVar)
            (lpOlUntypedBinaryConnectiveTerm(lpAnd, intermediatePattern, lpOlWildcard), intermediateTerm, cantEncode)
          }
          else if (currentPosition == 2) {
            val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(rt, p.tail, sig, patternVar)
            (lpOlUntypedBinaryConnectiveTerm(lpAnd, lpOlWildcard, intermediatePattern), intermediateTerm, cantEncode)
          }
          else throw new Exception(s"invalid position $currentPosition for connective ${lpAnd.pretty}")

        case Impl(lt, rt) =>
          if (currentPosition == 0) throw new Exception(s"when generating a rewrite pattern for Lambdapi, encountered position $currentPosition indicating ${lpImp.pretty}")
          else if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(lt, p.tail, sig, patternVar)
            (lpOlUntypedBinaryConnectiveTerm(lpImp, intermediatePattern, lpOlWildcard), intermediateTerm, cantEncode)
          }
          else if (currentPosition == 2) {
            val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(rt, p.tail, sig, patternVar)
            (lpOlUntypedBinaryConnectiveTerm(lpImp, lpOlWildcard, intermediatePattern), intermediateTerm, cantEncode)
          }
          else throw new Exception(s"invalid position $currentPosition for connective ${lpImp.pretty}")

        case tl === tr =>
          val encTy = type2LP(tl.ty,sig)
            if (currentPosition == 2) {
              val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(tl, p.tail, sig, patternVar)
              (lpOlTypedBinaryConnectiveTerm(lpEq,encTy, intermediatePattern, lpOlWildcard), intermediateTerm, cantEncode)
            }
            else if (currentPosition == 3) {
              val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(tr, p.tail, sig, patternVar)
              (lpOlTypedBinaryConnectiveTerm(lpEq,encTy, lpOlWildcard, intermediatePattern), intermediateTerm, cantEncode)
            }
            else throw new Exception(s"invalid position $currentPosition for connective ${lpEq.pretty}")

        case tl !=== tr =>
            val encTy = type2LP(tl.ty, sig)
            if (currentPosition == 2) {
              val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(tl, p.tail, sig, patternVar)
              (lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, encTy, intermediatePattern, lpOlWildcard)), intermediateTerm, cantEncode)
            }
            else if (currentPosition == 3) {
              val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(tr, p.tail, sig, patternVar)
              (lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, encTy, lpOlWildcard, intermediatePattern)), intermediateTerm, cantEncode)
            }
            else throw new Exception(s"invalid position $currentPosition for connective ${lpNot.pretty} ${lpEq.pretty}")

        case Not(t) =>
          if (currentPosition == 0) throw new Exception(s"when generating a rewrite pattern for Lambdapi, encountered position $currentPosition indicating ${lpNot.pretty}")
          else if (currentPosition == 1) {
            val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(t, p.tail, sig, patternVar)
            (lpOlUnaryConnectiveTerm(lpNot, intermediatePattern), intermediateTerm, cantEncode)
          } else throw new Exception (s"invalid position $currentPosition for connective ${lpNot.pretty}")

        case _ :::> _  => (lpOlWildcard, t, underBinderError)
        case Forall(_) => (lpOlWildcard, t, underBinderError)
        case Exists(_) => (lpOlWildcard, t, underBinderError)
        case TyForall(_) => (lpOlWildcard, t, underBinderError)
        case TypeLambda(_) => (lpOlWildcard, t, underBinderError)

        case f ∙ args =>
          val wildcardSeq = Seq.fill(args.length)(Left(lpOlWildcard))
          if (currentPosition == 0) {
            val (intermediatePattern, intermediateTerm, cantEncode) = leoPosition2LpPattern(f, p.tail, sig, patternVar)
            (lpOlFunctionApp(intermediatePattern,wildcardSeq),intermediateTerm,cantEncode)
          } else {
            assert(currentPosition <= (args.length + 1), s"Error generating Lambdpai Pattern: Found position $currentPosition out of bounds")
            val (newArgs, newTerm, cantEncode) =
              args(currentPosition - 1) match {
                case Left(lTerm) =>
                  val (intermediatePattern, intermediateTerm,cantEncode0) = leoPosition2LpPattern(lTerm, p.tail, sig, patternVar)
                  (wildcardSeq.updated(currentPosition -1,Left(intermediatePattern)),intermediateTerm,cantEncode0)
                case Right(rType) =>
                  val encType = type2LP(rType,sig)
                  throw new Exception(s"Error generating Lambdpai Pattern: Patterns in types not encoded yet (trying to generate pattern in ${encType.pretty} (${rType.pretty}) with ${p.tail})")
              }
            (lpOlFunctionApp(lpOlWildcard,newArgs),newTerm,cantEncode)
          }
      case _ => throw new Exception (s"generating pattern for LP but ${t.pretty} not encodedable?")
      }
      }
  }

//todo: in order to implmement this I need proper type substitution implementation
  def betaReduceLpApplication(term0:lpOlTerm):lpOlTerm ={
    term0 match {
      // only in this case can we reduce
      case lpOlFunctionApp(lpOlLambdaTerm(vars,body), args, _) =>
        assert(vars.length >= args.length)
        Out.lp_debug_info(s"Beta-reduction occurring for ${term0.pretty}")

        val pairs = vars.zip(args)
        val (termPairs, typePairs) = pairs.partition {
          case (_, e) => e.isLeft
        }
        val termSubstDict: Map[lpOlTerm, lpOlTerm] = termPairs.map {
          case (Left(v), Left(term)) => (v, term)
          case _ => throw new Exception("unexpected case")
        }.toMap
        val tySubstDict: Map[lpOlTyVar, lpOlType] = typePairs.map {
          case (Right(v), Right(ty)) => (v, ty)
          case _ => throw new Exception("unexpected case")
        }.toMap

        Out.lp_debug_info(s"terms to rewrite: $termSubstDict")
        if (tySubstDict.nonEmpty) Out.lp_debug_info(s"Can not currently substitute types but found type subst: $tySubstDict")

        val reducedBody = findRWTerm0(termSubstDict,body)._2
        // todo: actually, I should probably search the body for reducable terms again?
        val remainingVars = vars.drop(args.length)
        val reduced = if (remainingVars.nonEmpty) lpOlLambdaTerm(remainingVars,reducedBody) else reducedBody
        Out.lp_debug_info(s"reduced to ${reduced.pretty}")
        reduced

      // in all other cases we need to search substructures for reducable terms
      case lpOlLambdaTerm(vars,body) =>
        lpOlLambdaTerm(vars,betaReduceLpApplication(body))
      case lpOlBoundTerm(quantifier, vars, body) =>
        lpOlBoundTerm(quantifier, vars, betaReduceLpApplication(body))
      case lpOlUnaryConnectiveTerm(con, term) =>
        lpOlUnaryConnectiveTerm(con, betaReduceLpApplication(term))
      case lpOlUntypedBinaryConnectiveTerm(con,lhs,rhs) =>
        lpOlUntypedBinaryConnectiveTerm(con,betaReduceLpApplication(lhs),betaReduceLpApplication(rhs))
      case lpOlUntypedBinaryConnectiveTerm_multi(con, args) =>
        val reducedArgs = args.map(betaReduceLpApplication(_))
        lpOlUntypedBinaryConnectiveTerm_multi(con, reducedArgs)
      case lpOlTypedBinaryConnectiveTerm(con, ty, lhs, rhs) =>
        lpOlTypedBinaryConnectiveTerm(con, ty, betaReduceLpApplication(lhs), betaReduceLpApplication(rhs))
      case lpOlFunctionApp(head,args,innerArgs) =>
        val reducedArgs = args.map {
          case Left(term) => Left(betaReduceLpApplication(term))
          case other => other
        }
        val reducedInnerArgs = innerArgs.map {
          case Left(term) =>
            Out.lp_debug_info(s"l: ${term.pretty}")
            Left(betaReduceLpApplication(term))
          case other =>
            other
        }
        head match {
          case con: lpOlUnappliedConnective =>
            applyPartiallyAppliedConnective(con,reducedArgs, reducedInnerArgs)
          case _ =>
            lpOlFunctionApp(head,reducedArgs,reducedInnerArgs)
        }
      // all other possible terms should be constants
      case _ => term0
    }
  }

  def alphaEquivalent(t1: Option[lpOlTerm], t2: Option[lpOlTerm]): Boolean = {
    if (t1 == t2) true
    else if (t1.isDefined && t2.isDefined) alphaEquivalent(t1.get, t2.get, Map.empty)
    else false
  }
  def alphaEquivalent(t1: lpOlTerm, t2: lpOlTerm): Boolean = {
    Out.lp_debug_info(s"testing alpha equivalence of ${t1.pretty} and ${t2.pretty}")
    if (t1 == t2) true
    else alphaEquivalent(t1, t2, Map.empty)
  }

  private def alphaEquivalent(t1: lpTerm, t2: lpTerm, env: Map[lpTerm, lpTerm]): Boolean = {
    // Checks whether two lpTerms are equal modulo renaming of bound variables.
    //Out.lp_debug_info(s"comparing \n${t1} and \n${t2} with mapping $env")
    (t1, t2) match {
    // First, we handle terms with binders:
    case (lam1: lpOlLambdaTerm, lam2: lpOlLambdaTerm) =>
      if (lam1.vars.length != lam2.vars.length) false
      else {
        val newEnv = lam1.vars.zip(lam2.vars).foldLeft(env) { case (acc, (v1, v2)) =>
          v1 match {
            case Left(otv1) =>
              v2 match {
                case Left(otv2) =>
                  if (otv1.ty != otv2.ty) return false// todo: Once polymorhic types are implemented, also include them
                  acc + (otv1 -> otv2)
                case _ => acc
              }
            // only typed vars are allowed
            case _ => throw new Exception(s"LP-Encoding: found unallowed untyped vars in Ol-lambda term")
          }
        }
        alphaEquivalent(lam1.body, lam2.body, newEnv)
      }
    case (q1: lpOlBoundTerm, q2: lpOlBoundTerm) =>
      if (q1.quantifier != q2.quantifier) false
      else {
        (q1.variables, q2.variables) match {
          case (vars1: Seq[`lpOlTypedVar`], vars2: Seq[`lpOlTypedVar`]) =>
            val newEnvOpt = vars1.zip(vars2).foldLeft(Option(env)) { (maybeEnv, v1v2) =>
              maybeEnv.flatMap { currentEnv =>
                if (v1v2._1.ty != v1v2._2.ty) None
                else {
                  Some(currentEnv + (v1v2._1 -> v1v2._2))
                }
              }
            }
            newEnvOpt match {
              case Some(newEnv) => alphaEquivalent(q1.body, q2.body, newEnv)
              case None => false
            }
          // only typed vars are allowed in mono-quantified terms
          case _ => false
        }
      }

    // Variables themselves
    case (v1: lpOlTypedVar, v2: lpOlTypedVar) =>
      env.getOrElse(v1, v1) == v2
    case (v1: lpOlUntypedVar, v2: lpOlUntypedVar) =>
      env.getOrElse(v1, v1) == v2
    case (u1: lpOlUnaryConnectiveTerm, u2: lpOlUnaryConnectiveTerm) =>
      u1.connective == u2.connective && alphaEquivalent(u1.body, u2.body, env)

    // All other terms that may contain variables
    case (app1: lpOlFunctionApp, app2: lpOlFunctionApp) =>
      app1.args.length == app2.args.length &&
        alphaEquivalent(app1.f, app2.f, env) &&
        app1.args.zip(app2.args).forall {
          case (Left(t1), Left(t2)) => alphaEquivalent(t1, t2, env)
          case (Right(ty1), Right(ty2)) => alphaEquivalent(ty1, ty2, env)
          case _ => false
        }
    case (b1: lpOlUntypedBinaryConnectiveTerm, b2: lpOlUntypedBinaryConnectiveTerm) =>
      b1.connective == b2.connective &&
        alphaEquivalent(b1.lhs, b2.lhs, env) &&
        alphaEquivalent(b1.rhs, b2.rhs, env)
    case (b1: lpOlTypedBinaryConnectiveTerm, b2: lpOlTypedBinaryConnectiveTerm) =>
      b1.connective == b2.connective &&
        b1.ty == b2.ty &&
        alphaEquivalent(b1.lhs, b2.lhs, env) &&
        alphaEquivalent(b1.rhs, b2.rhs, env)
    case (m1: lpOlUntypedBinaryConnectiveTerm_multi, m2: lpOlUntypedBinaryConnectiveTerm_multi) =>
      m1.connective == m2.connective &&
        m1.args.length == m2.args.length &&
        m1.args.zip(m2.args).forall { case (a, b) => alphaEquivalent(a, b, env) }

    // other cases can not contain variables and can thus be handled by usual ==
    case _ => t1 == t2
  }
  }

  def doubleIndexList[A](xs: Seq[A]): Seq[Int] = {
    // generate an index list where identical elements have identical indices
    val (_, _, rev) = xs.foldLeft((Map.empty[A, Int], 0, List.empty[Int])) {
      case ((m, next, acc), x) =>
        m.get(x) match {
          case Some(id) =>
            (m, next, id :: acc)
          case None =>
            (m + (x -> next), next + 1, next :: acc)
        }
    }
    rev.reverse
  }

  /*
  def wholeHaveRewriteStep(rewriteSteps: Seq[lpProofScriptStep], nameStep: String, nameSubStep: String, before: lpOlTerm, sourceBefore: lpTerm, after: lpOlTerm): lpHave = {
    //todo: use this in my simplification steps?

    // In many cases, we want to generate Sub-Steps for rewritings in proofs that first prove the equality of Term A and B (when for instance B is a simplified version of A)
    // And then prove B given A. This function generates such steps.

    // 1. Proof equality
    val equalityToProve = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, after, before)
    val withAddedReflexivity = lpProofScript(rewriteSteps :+ lpReflexivity())
    val subStep = lpHave(nameSubStep, equalityToProve.prf, withAddedReflexivity)

    // 2. Proof the "after" given the equality
    //val stepProof = lpProofScript(Seq(subStep,lpRefine(lpFunctionApp(lpConstantTerm(nameSubStep),Seq(lpUseful.Identity,sourceBefore)))))
    //val stepProof = lpProofScript(Seq(subStep,lpRefine(lpUseful.applyToEqualityTerm(lpOtype,after,before,lpOlConstantTerm(nameSubStep),lpOlLambdaTerm(Seq(lpOlTypedVar(lpOlConstantTerm("x"),lpOtype)),lpOlConstantTerm("x")),Some(sourceBefore)))))
    val stepProof = lpProofScript(Seq(subStep, lpRefine(NaturalDeductionRules.eqDef().instanciate(lpOtype.lift2Poly, after, before, Some(lpOlConstantTerm(nameSubStep)), Some(lpOlLambdaTerm(Seq(lpOlTypedTermVar(lpOlConstantTerm("x"), lpOtype)), lpOlConstantTerm("x"))), Some(sourceBefore)))))

    // the whole Have step:
    lpHave(nameStep, after.prf, stepProof)
  }

   */

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

  def shiftClause (cls: Seq[Clause]) = {
    // check if ther are gaps in the variable identifiers and if so, close them
    // check for "holes" in the variable-numbers
    val allVars = cls.flatMap(cl => cl.lits.flatMap(l => l.fv)).distinct
    val fvs = allVars.map(_._1).distinct.sortWith { case (a, b) => a > b }

    //val prefvs = newLits.flatMap(_.fv).distinct
    //val fvs = prefvs.map(_._1).distinct.sortWith { case (a, b) => a > b }
    //val tyFVs = lits.flatMap(_.tyFV).distinct.sortWith { case (a, b) => a > b }
    Out.lp_debug_info(s"fvs: $fvs")
    val derivedClauses: Seq[Clause] = if (fvs.nonEmpty && fvs.size != fvs.head) {
      Out.lp_debug_info(s"FV Optimization : \t${fvs.mkString(",")}")
      // gaps in fvs
      val newFvs = Seq.range(fvs.size, 0, -1)
      val subst = Subst.fromShiftingSeq(fvs.zip(newFvs))
      Out.finest(s"New: \t${newFvs.mkString("-")} ... subst: ${subst.pretty}")
      cls.map(cl => Clause(cl.lits.map(l => l.applyRenamingSubstitution(subst))))
    } else cls
  }

  def extendBvarMap(bV: Map[Int, String], extBy: Int): Map[Int, String] = {
    // ensure that the current map is formed as expected
    val startK = bV.size
    assert(bV.keySet == (1 to startK).toSet, s"Error in LP encoding: Trying to extend bVars map, but current map is mal-formed (Key set: ${bV.keySet}, expected ${(1 to startK).toSet})")
    if (extBy == 0) return bV

    val used = bV.values.toSet

    // find fresh candidate names produced by intToName, skipping those already used
    val freshNames = Iterator.from(startK).map(intToName).filterNot(used.contains).take(extBy).toVector
    val newBindings = freshNames.zipWithIndex.map { case (nm, i) => (startK + 1 + i) -> nm }

    bV ++ newBindings
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// USEFUL TERMS //////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  object Identity extends lpTerm {
    val x1 = lpUntypedVar(lpConstantTerm("x"))
    val definition = lpLambdaTerm(Seq(x1), x1)

    override def pretty (implicit prefix : PrettyConfig) : String = definition.pretty
  }

}
