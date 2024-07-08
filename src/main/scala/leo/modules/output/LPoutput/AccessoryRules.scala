package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._
import scala.collection.mutable

object AccessoryRules {


  ////////////////////////////////////////////////////////////////
  ////////// Transform from non-eauational to equational literals and back
  ////////////////////////////////////////////////////////////////

  case class mkNegPropPosLit_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(¬ a) → Prf(= [o] (¬ a) ⊤)

    override def name: lpConstantTerm = lpConstantTerm("negPropPosEq_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm(patternVarName)), lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm(patternVarName)), lpOlTop)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def transformLit(x0: lpOlTerm): (lpOlTerm,lpOlTerm,lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop),lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop)

    def origLit(x0: lpOlTerm): (lpOlTerm) =  lpOlUnaryConnectiveTerm(lpNot, x0)

  }

  case class mkNegPropNegLit_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [o] (¬ a) (¬ (= [o] a ⊤)))

    override def name: lpConstantTerm = lpConstantTerm("negPropNegEq_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName)), lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlTop))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def transformLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop)), x0, lpOlTop)

    def origLit(x0: lpOlTerm): (lpOlTerm) = lpOlUnaryConnectiveTerm(lpNot, x0)

  }

  case class mkPosPropNegLit_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [o] a (¬(= [o] (¬ a) ⊤)))

    override def name: lpConstantTerm = lpConstantTerm("posPropNegEq_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName)), lpOlTop))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    //def instanciate():lpFunctionApp =
    def transformLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)), lpOlUnaryConnectiveTerm(lpNot, x0), lpOlTop)

    def origLit(x0: lpOlTerm): (lpOlTerm) = x0
  }

  case class mkPosPropPosLit_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [o] a (= [o] a ⊤))

    override def name: lpConstantTerm = lpConstantTerm("mkPosPropPosEq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlTop)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosPropPosLit_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    //def instanciate():lpFunctionApp =
    def transformLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop), x0, lpOlTop)

    def origLit(x0: lpOlTerm): (lpOlTerm) = x0
  }

  case class mkNegLitPosProp_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [o] (¬ (= [o] (¬ a) ⊤)) a)

    override def name: lpConstantTerm = lpConstantTerm("negEqPosProp_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm(patternVarName)),lpOlTop)),lpOlConstantTerm(patternVarName)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkNegLitPosProp_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def instanciate(x0: lpOlTerm) = lpFunctionApp(name, Seq(x0))

    def transformLit(x0: lpOlTerm): (lpOlTerm) = x0

    def origLit(x0: lpOlTerm): (lpOlTerm,lpOlTerm,lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop)),lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop)

  }

  case class mkNegLitNegProp_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [o] (¬ (= [o] a ⊤)) (¬ a))

    override def name: lpConstantTerm = lpConstantTerm("negEqNegProp_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlConstantTerm(patternVarName), lpOlTop)), lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkNegLitPosProp_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def instanciate(x0: lpOlTerm) = lpFunctionApp(name, Seq(x0))

    def transformLit(x0: lpOlTerm): (lpOlTerm) = lpOlUnaryConnectiveTerm(lpNot, x0)

    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop)), x0, lpOlTop)


  }

  case class mkPosLitNegProp_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [o] (= [o] (¬ a) ⊤) (¬ a))

    override def name: lpConstantTerm = lpConstantTerm("posEqNegProp_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName)), lpOlTop), lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosLitNegProp_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def instanciate(x0: lpOlTerm) = lpFunctionApp(name, Seq(x0))

    def transformLit(x0: lpOlTerm): (lpOlTerm) =  lpOlUnaryConnectiveTerm(lpNot, x0)

    def origLit(x0: lpOlTerm): (lpOlTerm,lpOlTerm,lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype.lift2Poly,lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop),lpOlUnaryConnectiveTerm(lpNot,x0),lpOlTop)


  }

  case class mkPosLitPosProp_script(patternVarName: String = "x") extends lpDefinedRules {
    // Provide a proof of the type Prf(= [o] (= [o] (a) ⊤) (a))

    override def name: lpConstantTerm = lpConstantTerm("posEqPosProp_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly,lpOlConstantTerm(patternVarName), lpOlTop), lpOlConstantTerm(patternVarName)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkPosLitPosPropEq not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty

    def instanciate(x0: lpOlTerm) = lpFunctionApp(name, Seq(x0))

    def transformLit(x0: lpOlTerm): (lpOlTerm) = x0

    def origLit(x0: lpOlTerm): (lpOlTerm, lpOlTerm, lpOlTerm) = (lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x0, lpOlTop), x0, lpOlTop)


  }

  case class mkNegPropEqBot_script(patternVarName: String = "x") extends lpDefinedRules {

    override def name: lpConstantTerm = lpConstantTerm("PropBotNeg_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName)), lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlConstantTerm(patternVarName), lpOlBot)).prf

    override def proof: lpProofScript = throw new Exception("proof for mkNegPropEqBot_script not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty
  }

  case class mkBotEqNegProp_script(patternVarName: String = "x") extends lpDefinedRules {

    override def name: lpConstantTerm = lpConstantTerm("botNegProp_eq")

    override def ty: lpMlType = lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlBot, lpOlConstantTerm(patternVarName)), lpOlUnaryConnectiveTerm(lpNot, lpOlConstantTerm(patternVarName))).prf

    override def proof: lpProofScript = throw new Exception("proof for mkBotEqNegProp not encoded yet")

    override def dec: lpDeclaration = lpDeclaration(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty)

    override def pretty: String = lpDefinition(name, Seq(lpUntypedVar(lpConstantTerm(patternVarName))), ty, proof).pretty
  }

  def makeLiteralEquational_proofSkript(lits: Seq[lpOlTerm], origClause: lpClause, sourceBefore: lpTerm, desiredEquational: Boolean, desiredPolarity: Boolean, nameStept: lpConstantTerm): (lpProofScriptStep, Map[lpOlTerm, (lpOlTerm, lpOlTerm, lpOlTerm)], Seq[lpOlTerm], Set[lpStatement]) = {

    // takes a literal and an desired polarity and returns:
    // - the encoded version of the literal itself and the equational version
    // - the lambda term of type Prf lit -> Prf eqLit as well as Prf eqLit -> Prf lit
    // - the left and right side of the new equational literal

    var usedSymbols: Set[lpStatement] = Set.empty

    // order the literals according to their occourence in the clause
    var orderedLits: Seq[lpOlTerm] = Seq.empty
    var litsToFind = origClause.lits
    val positionsInClause: mutable.HashMap[lpOlTerm, Int] = mutable.HashMap.empty
    var litsAfter: Seq[lpOlTerm] = Seq.empty
    //if (!lits.forall(lit => litsToFind.contains(lit))) throw new Exception("not all lits were found in clause")
    litsToFind foreach { lit =>
      if (lits.contains(lit)) { //todo: check that each literal was actually found too.
        orderedLits = orderedLits :+ lit
        positionsInClause.update(lit, origClause.lits.indexOf(lit))
        litsAfter = litsAfter :+ lpOlNothing
      } else litsAfter = litsAfter :+ lit
      litsToFind = litsToFind.filterNot(_ != lit)
    }
    if (litsToFind.nonEmpty) throw new Exception("not all literals could be found")

    var rewriteSteps: Seq[lpRewrite] = Seq.empty
    val transformations: mutable.HashMap[lpOlTerm, (lpOlTerm, lpOlTerm, lpOlTerm)] = mutable.HashMap.empty

    orderedLits foreach { lit =>

      val rewritePattern = generateClausePatternTerm(positionsInClause(lit), origClause.lits.length, None)

      if (desiredEquational) {
        lit match {
          case lpOlUnaryConnectiveTerm(lpNot, t) =>
            if (desiredPolarity == true) {
              //throw new Exception("1")
              // hier müsste bestimmt z.t. statt lit t stehen^
              //val instRule = lpFunctionApp(mkNegPropPosLit_script().name, Seq(t))
              usedSymbols = usedSymbols + mkPosLitNegProp_script()
              rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkPosLitNegProp_script().name)
              val transformedLit = mkPosLitNegProp_script().origLit(t)
              litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit._1)
              transformations.update(lit, transformedLit)
            } else {
              val instRule = lpFunctionApp(mkNegLitNegProp_script().name, Seq(t))
              usedSymbols = usedSymbols + mkNegLitNegProp_script()
              rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, instRule)
              val transformedLit = mkNegLitNegProp_script().origLit(t)
              litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit._1)
              transformations.update(lit, transformedLit)

            }
          case _ =>
            if (desiredPolarity == true) {
              //throw new Exception("3")
              val instRule = lpFunctionApp(mkPosLitPosProp_script().name, Seq(lit))
              usedSymbols = usedSymbols + mkPosLitPosProp_script()
              rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, instRule)
              val transformedLit = mkPosLitPosProp_script().origLit(lit)
              litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit._1)
              transformations.update(lit, transformedLit)

            } else {
              val instRule = lpFunctionApp(mkNegLitPosProp_script().name, Seq(lit))
              usedSymbols = usedSymbols + mkNegLitPosProp_script()
              rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, instRule)
              val transformedLit = mkNegLitPosProp_script().origLit(lit)
              litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit._1)
              transformations.update(lit, transformedLit)
            }
        }

      } else {
        lit match {
          case lpOlTypedBinaryConnectiveTerm(lpotype, lpEq, lhs, lpTop) =>
            lhs match {
              case lpOlUnaryConnectiveTerm(lpNot, t) =>
                //val instRule = mkPosLitNegProp_script().instanciate(t)
                usedSymbols = usedSymbols + mkNegPropPosLit_script()
                rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkNegPropPosLit_script().name)
                val transformedLit = mkNegPropPosLit_script().origLit(t)
                litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)
                transformations.update(lit, (transformedLit, lpOlNothing, lpOlNothing))

              case _ =>
                throw new Exception("2")
            }
          case lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpotype, lpEq, lhs, lpTop)) =>
            lhs match {
              case lpOlUnaryConnectiveTerm(lpNot, t) =>
                //val instRule = mkNegLitPosProp_script().instanciate(t)
                usedSymbols = usedSymbols + mkPosPropNegLit_script()
                rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkPosPropNegLit_script().name)
                val transformedLit = mkPosPropNegLit_script().origLit(t)
                litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)
                transformations.update(lit, (transformedLit, lpOlNothing, lpOlNothing))
              case _ =>
                //val instRule = mkNegLitNegProp_script().instanciate(lhs)
                usedSymbols = usedSymbols + mkNegPropNegLit_script()
                rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, mkNegPropNegLit_script().name)
                val transformedLit = mkNegPropNegLit_script().origLit(lhs)
                litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)
                transformations.update(lit, (transformedLit, lpOlNothing, lpOlNothing))
            }


          case _ => throw new Exception(s"trying to convert equational literal but wrong format was given: ${lit.pretty}")

        }
      }


    }
    // Combine into a have step
    val clauseAfter = lpClause(origClause.impBoundVars, litsAfter)
    //val haveStep = wholeHaveRewriteStep(rewriteSteps, nameStept.name, "hjhjlk", origClause.withoutQuant, sourceBefore, clauseAfter.withoutQuant)
    val haveStep = lpHave(nameStept.name, clauseAfter.withoutQuant.prf, lpProofScript(rewriteSteps :+ lpRefine(lpFunctionApp(sourceBefore, Seq()))))
    (haveStep, transformations.toMap, clauseAfter.lits, usedSymbols)
  }


  ////////////////////////////////////////////////////////////////
  ////////// Change order within literals
  ////////////////////////////////////////////////////////////////

  case class flipLiteral(polarity: Boolean) extends lpDefinedRules {
    // Prf(= [o] (= [T] x y) (= [T] y x))

    val x = lpOlConstantTerm("x")
    val y = lpOlConstantTerm("y")

    override def name: lpConstantTerm = lpConstantTerm("eqSym_eq")

    override def ty: lpMlType = {
      if (polarity) lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x, y), lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, y, x)).prf
      else lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype, lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, x, y)), lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, lpOtype.lift2Poly, y, x))).prf
    }

    override def dec: lpDeclaration = lpDeclaration(name, Seq(x, y), ty)

    override def proof: lpProofScript = lpProofScript(Seq(lpProofScriptCommentLine("    assume T x y;\n    have H1: Prf(= [T] x y) → Prf(= [T] y x)\n        {assume h;\n        symmetry;\n        refine h};\n    have H2: Prf(= [T] y x) → Prf(= [T] x y)\n        {assume h;\n        symmetry;\n        refine h};\n    refine propExt (= [T] x y) (= [T] y x) H1 H2")))

    override def pretty: String = lpDefinition(name, Seq(x, y), ty, proof).pretty

    def instanciate(x0: lpOlTerm, y0: lpOlTerm, prfXeqY0: Option[lpTerm]): lpFunctionApp = {
      val prfXeqY = prfXeqY0 match {
        case Some(prfTerm) => Seq(prfTerm)
        case None => Seq()
      }
      lpFunctionApp(name, Seq(x0, y0) ++ prfXeqY)
    }

    def res(T0: lpOlPolyType, x0: lpOlTerm, y0: lpOlTerm) = { // todo unite encoding with type
      if (polarity) lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, x0)
      else lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpEq, T0, y0, x0))
    }
  }


  def flipEqLiteralsProofScript(lits: Seq[(lpOlTerm, lpOlType)], origClause: lpClause, sourceBefore: lpTerm, nameStept: lpConstantTerm): (lpProofScriptStep, Seq[lpOlTerm], Set[lpStatement]) = {

    var usedSymbols: Set[lpStatement] = Set.empty

    val litsTypeMap = lits.toMap

    if (lits.isEmpty) throw new Exception(s"Function flipEqLiteralsProofScript called but no literals to flip were provided.")

    // order the literals according to their occourence in the clause
    var orderedLits: Seq[(lpOlTerm, lpOlType)] = Seq.empty
    var litsToFind = origClause.lits
    val positionsInClause: mutable.HashMap[lpOlTerm, Int] = mutable.HashMap.empty
    var litsAfter: Seq[lpOlTerm] = Seq.empty
    litsToFind foreach { lit =>
      if (lits.map(pair => pair._1).contains(lit)) {
        orderedLits = orderedLits :+ (lit, litsTypeMap(lit))
        positionsInClause.update(lit, origClause.lits.indexOf(lit))
        litsAfter = litsAfter :+ lpOlNothing
      } else litsAfter = litsAfter :+ lit
      litsToFind = litsToFind.filterNot(_ != lit)
    }
    //if (litsToFind.nonEmpty) throw new Exception("not all literals could be found")

    var rewriteSteps: Seq[lpRewrite] = Seq.empty

    orderedLits foreach { pair =>

      val lit = pair._1
      val litType = pair._2


      val (lhs0, rhs0, ty0, ispos) = lit match { //todo: summarize

        case lpOlUnaryConnectiveTerm(lpNot, lpOlTypedBinaryConnectiveTerm(lpeq, ty, rhs, lhs)) =>
          (rhs, lhs, ty, false)

        case lpOlTypedBinaryConnectiveTerm(lpeq, ty, rhs, lhs) =>
          (rhs, lhs, ty, true)

        case _ => throw new Exception(s"ERRRRRROOOOOORRRR")

      }

      val rewritePattern = generateClausePatternTerm(positionsInClause(lit), origClause.lits.length, None, lpOlUntypedVar(lpConstantTerm("x")), ispos)

      //val instRule = lpUseful.flipLiteral(ispos).instanciate(ty0.lift2Poly, lhs0, rhs0, None)
      usedSymbols = usedSymbols + flipLiteral(ispos)
      rewriteSteps = rewriteSteps :+ lpRewrite(rewritePattern, lpFunctionApp(flipLiteral(ispos).name, Seq(), Seq(litType)))
      val transformedLit = flipLiteral(ispos).res(ty0.lift2Poly, lhs0, rhs0)
      litsAfter = litsAfter.updated(positionsInClause(lit), transformedLit)

    }

    val nameSubStep = if (nameStept.name == "H1") "H1_1" else "H1"

    // Combine into a have step
    val clauseAfter = lpClause(origClause.impBoundVars, litsAfter)
    //val haveStep = wholeHaveRewriteStep(rewriteSteps, nameStept.name, nameSubStep, origClause.withoutQuant, sourceBefore, clauseAfter.withoutQuant)
    val haveStep = lpHave(nameStept.name, clauseAfter.withoutQuant.prf, lpProofScript(rewriteSteps :+ lpRefine(lpFunctionApp(sourceBefore, Seq()))))
    (haveStep, litsAfter, usedSymbols)
  }


  ////////////////////////////////////////////////////////////////
  ////////// Change order of literals
  ////////////////////////////////////////////////////////////////

  def changePositions(positions: Seq[Int], proofNames: String): (lpHave, Set[lpStatement]) = {
    // given is a sequence of integers, this represent the position of the literal at the index of the integer in the positions sequence in the clause we want to prove

    //todo: check that the positions vector has the right format, otherwise just order the variables
    // the first step is the generation of the type representing the reordering we are trying to prove
    var clause0: Seq[lpOlUntypedVar] = Seq.empty
    var clause1: Seq[lpOlUntypedVar] = Seq.fill(positions.length)(lpOlUntypedVar(lpOlNothing))
    val origPosMap: mutable.HashMap[lpOlUntypedVar, Int] = mutable.HashMap.empty

    var varCount = 0
    var hypCount = 0

    positions foreach { pos =>
      val variable = lpOlUntypedVar(lpConstantTerm(s"x$varCount"))
      clause0 = clause0 :+ variable
      clause1 = clause1.updated(pos, variable)
      origPosMap += (variable -> pos)
      varCount = varCount + 1
    }

    // with this we can construct the type of the rule we proof and can begin the proof script
    val clause0enc = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause0)
    val clause1enc = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1)

    // the las hypothesis we assume is clause0
    val hypothesis = lpUntypedVar(lpConstantTerm(s"h$hypCount"))
    hypCount = hypCount + 1

    // we add these two as prf terms to the type we are trying to proof
    val typeOfRule = lpMlDependType(clause0.map(var0 => lpUntypedVar(var0.name)), lpMlFunctionType(Seq(clause0enc.prf, clause1enc.prf)))


    def generate(clause0Unprocessed0: Seq[lpOlUntypedVar], clause0Processed0: Seq[lpOlUntypedVar], clause1Gen: Seq[lpOlUntypedVar], hCountGen0: Int, currentAssumtion: lpUntypedVar, origPosMap: mutable.HashMap[lpOlUntypedVar, Int]): (lpProofScriptStep, Set[lpStatement]) = {

      var hCountGen = hCountGen0
      var usedSymols: Set[lpStatement] = Set.empty

      if (clause0Unprocessed0.length == 1) {
        // first we need to find out where in the new clause the variable shall go and find out what variables are left of it and what are right
        val posInNewCl = origPosMap(clause0Unprocessed0.head)
        val (lhs, rhs) = clause1Gen.splitAt(posInNewCl)
        val rhsPrf = if (rhs.length == 1) currentAssumtion else NaturalDeductionRules.orIl().instanciate(rhs.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, rhs.tail), Some(currentAssumtion))
        //print(s"rhs proof: ${nestedLorIlApp(lhs, rhs, rhsPrf).pretty}\n")
        val prf = {
          if (lhs.nonEmpty) lpProofScript(Seq(lpRefine(nestedLorIlApp(lhs, rhs, rhsPrf))))
          else lpProofScript(Seq(lpRefine(lpFunctionApp(rhsPrf, Seq()))))
        }
        (prf, usedSymols)

      } else {
        val orElInstantiation = NaturalDeductionRules.orE().instanciate(clause0Unprocessed0.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause0Unprocessed0.tail), lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Gen), Some(lpOlWildcard), Some(lpOlWildcard), Some(currentAssumtion))
        val newHyp = lpUntypedVar(lpConstantTerm(s"h$hCountGen"))
        val newAssumeStep = lpAssume(Seq(newHyp))
        hCountGen = hCountGen + 1
        val prfLhs = {
          // first we need to find out where in the new clause the variable shall fo and find out what variables are left of it and what are right
          val posInNewCl = origPosMap(clause0Unprocessed0.head)
          val (lhsLhs, lhsRhs) = clause1Gen.splitAt(posInNewCl)
          if (lhsLhs.length == 0) lpProofScript(Seq(newAssumeStep, lpRefine(NaturalDeductionRules.orIl().instanciate(lhsRhs.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, lhsRhs.tail), Some(newHyp)))))
          else {
            val lhsRhsPrf = if (lhsRhs.length == 1) newHyp else NaturalDeductionRules.orIl().instanciate(lhsRhs.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, lhsRhs.tail), Some(newHyp))
            lpProofScript(Seq(newAssumeStep, lpRefine(nestedLorIlApp(lhsLhs, lhsRhs, lhsRhsPrf))))
          }
        }
        val prfRhs = {
          val clause0Unprocessed = clause0Unprocessed0.tail
          val clause0Processed = clause0Processed0 :+ clause0Unprocessed0.head
          val (prfRhs0, newUsedSymbols) = generate(clause0Unprocessed, clause0Processed, clause1Gen, hCountGen, newHyp, origPosMap)
          usedSymols = usedSymols ++ newUsedSymbols
          lpProofScript(Seq(newAssumeStep, prfRhs0))
        }
        val proofScript = lpProofScript(Seq(lpRefine(orElInstantiation, Seq(prfLhs, prfRhs))))
        (proofScript, usedSymols)
      }
    }

    // now we can construct the overall proof!
    val assumeStep = lpAssume(clause0 :+ hypothesis)
    val (proof, usedSymbols) = generate(clause0, Seq.empty, clause1, hypCount, hypothesis, origPosMap)
    val haveStep = lpHave(proofNames, typeOfRule, lpProofScript(Seq(assumeStep, proof)))


    //print(haveStep.pretty)

    (haveStep, usedSymbols)
  }


  ////////////////////////////////////////////////////////////////
  ////////// Transform rule
  ////////////////////////////////////////////////////////////////

  def generateClorRule(positions: Seq[Boolean], proofNames: String): (lpHave, Set[lpStatement]) = {
    // generate a proof script to only transform single literals in clauses and still proof the entire clause
    // the positions vector then encodes how many literals the remaining clause has and for positions a clause application has to be proven

    // first we generate a list of variables and stuff
    // in this step we also construct the transformtion to be prooven and start assuming variables and hypothesis
    var clause0: Seq[lpOlUntypedVar] = Seq.empty
    var clause1: Seq[lpOlUntypedVar] = Seq.empty

    // To construct the type of the rule we are proving here, we need to require the proofs for the transforamtions of the individual literals
    var trnsformationProofs: Seq[lpMlType] = Seq.empty

    // we track the variable and hypothesis names we need to assume in the proof script
    var varsToBeAssumed: Seq[lpOlUntypedVar] = Seq.empty
    var hypothesisToBeAssumed: Seq[lpUntypedVar] = Seq.empty
    var quantifiedVars: Seq[lpTypedVar] = Seq.empty

    // map each variable that is transformed to the hypothesis representing this transfomration
    val transHypName: mutable.HashMap[lpOlUntypedVar, lpUntypedVar] = mutable.HashMap.empty

    var varCount = 0
    var hypCount = 0
    positions foreach { pos =>
      val variableOrig = lpOlUntypedVar(lpConstantTerm(s"x$varCount"))
      clause0 = clause0 :+ variableOrig
      varsToBeAssumed = varsToBeAssumed :+ variableOrig
      quantifiedVars = quantifiedVars :+ lpTypedVar(lpConstantTerm(s"x$varCount"), lpOtype)
      if (pos) {
        // we add the changed variable to the new clause
        varCount = varCount + 1
        val variableNew = lpOlUntypedVar(lpConstantTerm(s"x$varCount"))
        varsToBeAssumed = varsToBeAssumed :+ variableNew
        quantifiedVars = quantifiedVars :+ lpTypedVar(lpConstantTerm(s"x$varCount"), lpOtype)
        clause1 = clause1 :+ variableNew
        // since we want to transform this literal, we need to provide a proof that we can indeed do so. We assume it in the script as a hypothesis.
        trnsformationProofs = trnsformationProofs :+ lpMlFunctionType(Seq(variableOrig.prf, variableNew.prf))
        val newHypo = lpUntypedVar(lpConstantTerm(s"h$hypCount"))
        hypCount = hypCount + 1
        hypothesisToBeAssumed = hypothesisToBeAssumed :+ newHypo
        // and we add it to the map
        transHypName += (variableOrig -> newHypo)
      } else {
        clause1 = clause1 :+ lpOlUntypedVar(lpConstantTerm(s"x$varCount"))
      }
      varCount = varCount + 1
    }

    // whith this we can construct the type of the rule we proof and can begin the proof script
    val clause0enc = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause0)
    val clause1enc = lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1)

    // the las hypothesis we assume is clause0
    val newHypo = lpUntypedVar(lpConstantTerm(s"h$hypCount"))
    hypCount = hypCount + 1
    hypothesisToBeAssumed = hypothesisToBeAssumed :+ newHypo

    // we add these two as prf terms to the type we are trying to proof
    val typeOfRule = lpMlDependType(quantifiedVars, lpMlFunctionType(trnsformationProofs ++ Seq(clause0enc.prf, clause1enc.prf)))

    def generate(positionsGen: Seq[Boolean], clause0Gen: Seq[lpOlUntypedVar], clause1Unprocessed0: Seq[lpOlUntypedVar], clause1Processed0: Seq[lpOlUntypedVar], hCountgenerate: Int, currentAssumtion: lpUntypedVar): (lpProofScriptStep, Set[lpStatement]) = {

      var usedSymbols: Set[lpStatement] = Set.empty
      var hCountGen = hCountgenerate

      val clause1Unprocessed = clause1Unprocessed0.tail
      val clause1Processed = clause1Processed0 :+ clause1Unprocessed0.head

      if (positionsGen.length == 1) {
        val refLhs = if (positionsGen.head) lpFunctionApp(transHypName.getOrElse(clause0Gen.head, throw new Exception("key not found generateClorRule")), Seq(currentAssumtion)) else currentAssumtion
        // in this case the current hypothesis should be the proof for we are looking for //todo ?
        //(lpProofScript(Seq(lpRefine(lpFunctionApp(refLhs, Seq())))), usedSymbols)
        val proofRhs = lpFunctionApp(refLhs, Seq())
        val completeProof = nestedLorIlApp(clause1Processed0, clause1Unprocessed0, proofRhs)
        ((lpProofScript(Seq(lpRefine(completeProof))), Set()))

      } else {
        // the clause is longer than 0 => we need to apply ∨E
        val orElInstantiation = NaturalDeductionRules.orE().instanciate(clause0Gen.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause0Gen.tail), lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Processed ++ clause1Unprocessed), Some(lpOlWildcard), Some(lpOlWildcard), Some(currentAssumtion))
        usedSymbols = usedSymbols + NaturalDeductionRules.orE()
        // then we need two proofs: that the lhs of clause0 implies clause1 and the same for the rhs.
        val (lhs, rhs): (lpProofScript, lpProofScript) = {
          // the lhs does not have to be transformed
          val newHyp = lpUntypedVar(lpConstantTerm(s"h$hCountGen"))
          val newAssumeStep = lpAssume(Seq(newHyp))
          hCountGen = hCountGen + 1
          // depending on weather or not the lhs was transformed, we need either a hypothesis represnting a proof of itself or one representing the proof of its transformatons
          val refLhs = if (positionsGen.head) lpFunctionApp(transHypName.getOrElse(clause0Gen.head, throw new Exception("key not found generateClorRule")), Seq(newHyp)) else newHyp
          val lhsRefineStep = {
            if (clause1Processed.length == 1) {
              usedSymbols = usedSymbols + NaturalDeductionRules.orIl()
              lpRefine(NaturalDeductionRules.orIl().instanciate(clause1Processed.head, lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed), Some(refLhs)))
            }
            else {
              lpRefine(NaturalDeductionRules.orIr().instanciate(lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Processed0), lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed0), Some(NaturalDeductionRules.orIl().instanciate(clause1Unprocessed0.head, (lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed0.tail)), Some(refLhs)))))
              val proofrhs = NaturalDeductionRules.orIl().instanciate(clause1Unprocessed0.head, (lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed0.tail)), Some(refLhs))
              val completeProof = nestedLorIlApp(clause1Processed0, clause1Unprocessed0, proofrhs)
              usedSymbols = usedSymbols + NaturalDeductionRules.orIl() + NaturalDeductionRules.orIr()
              lpRefine(completeProof)
            }
          }
          usedSymbols = usedSymbols + NaturalDeductionRules.orIl()
          if (!positionsGen.tail.forall(_ == false)) {
            // some of the other literals yet have to be transformed
            val (rhsProof, newUsedSymbols) = generate(positionsGen.tail, clause0Gen.tail, clause1Unprocessed, clause1Processed, hCountGen, newHyp)
            usedSymbols = usedSymbols ++ newUsedSymbols
            (lpProofScript(Seq(newAssumeStep, lhsRefineStep)), lpProofScript(Seq(newAssumeStep, rhsProof)))
          } else {
            // no transformations left to proof! So we can simply assume both sides and refine with the application of the assumption to the right lor-introduction
            //val rhsRefineStep = lpRefine(lpUseful.orIr().instanciate(lpOlUntypedBinaryConnectiveTerm_multi(lpOr,clause1Processed), lpOlUntypedBinaryConnectiveTerm_multi(lpOr, clause1Unprocessed), Some(newHyp)))
            val completeProof = nestedLorIlApp(clause1Processed, clause1Unprocessed, newHyp)
            usedSymbols = usedSymbols + NaturalDeductionRules.orIr() + NaturalDeductionRules.orIr()
            //(lpProofScript(Seq(newAssumeStep, lhsRefineStep)), lpProofScript(Seq(newAssumeStep, rhsRefineStep)))
            (lpProofScript(Seq(newAssumeStep, lhsRefineStep)), lpProofScript(Seq(newAssumeStep, lpRefine(completeProof))))
          }
        }
        val proofScript = lpProofScript(Seq(lpRefine(orElInstantiation, Seq(lhs, rhs))))
        (proofScript, usedSymbols)
      }
    }

    // now we can construct the overall proof!
    val assumeStep = lpAssume(varsToBeAssumed ++ hypothesisToBeAssumed)
    val (proof, usedSymbols) = generate(positions, clause0, clause1, Seq.empty, hypCount, hypothesisToBeAssumed.last)
    val haveStep = lpHave(proofNames, typeOfRule, lpProofScript(Seq(assumeStep, proof)))

    (haveStep, usedSymbols)
  }


}
