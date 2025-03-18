package leo.modules.output.LPoutput

import leo.datastructures.{Int0, termArgs}

/**
  *
  * @author Melanie Taprogge
  */

object lpDatastructures {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// LP SYNTAX /////////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val monomorphic = true

  abstract class lpStatement {
    def pretty: String
  }

  abstract class lpKeyword extends lpStatement

  case object lpOpaque extends lpKeyword {
    override def pretty: String = "opaque"
  }

  abstract class lpTerm extends lpStatement

  abstract class lpConstants {
    def pretty: String
  }

  case object lpLambda extends lpConstants {
    override def pretty: String = "λ"
  }

  case object lpPi extends lpConstants {
    override def pretty: String = "Π"
  }

  case object lpArrow extends lpConstants {
    override def pretty: String = "→"
  }

  case object lpWildcard extends lpTerm {
    override def pretty: String = "_"
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// KINDS OF STATEMENTS ///////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  case class lpDeclaration(name: lpStatement, variables: Seq[lpTerm], typing: lpType, implicitArgs: Seq[lpTerm]= Seq.empty) extends lpStatement{
    override def pretty: String = {

      val typedImpArgs = implicitArgs.map {
        case lpTypedVar(term, ty) => s"[${term.pretty} : ${ty.pretty}]"
        case others => s"[${others.pretty}]"
      }

      val typedVars = variables.map {
        case lpOlTypedVar(term, ty) => s"(${term.pretty} : ${ty.lift2Meta.pretty})"
        case lpOlTyVar(name) => s"($name : ${lpSet.pretty})"
        case others => s"${others.pretty}"
      }

      val gap1 = if (implicitArgs.isEmpty) "" else " "
      val gap2 = if (variables.isEmpty) "" else " "
      s"symbol ${name.pretty}$gap1${typedImpArgs.mkString(" ")}$gap2${typedVars.mkString(" ")}: ${typing.pretty};\n"
    }
  }

  case class lpDefinition(name: lpConstantTerm, variables: Seq[lpTerm], typing: Option[lpMlType], proof: lpStatement, implicitArgs: Seq[lpTerm]= Seq.empty, modifier0: Seq[lpKeyword]= Seq.empty) extends lpStatement {
    override def pretty: String = {

      var modifier = modifier0
      if (!modifier.contains(lpOpaque)) modifier = modifier :+ lpOpaque

      val proofEnc = proof match {
        case _ : lpTerm =>
          s"${proof.pretty}"
        case proofScript : lpProofScript =>
          s"begin\n${proofScript.addTab(1).pretty}\nend"
      }

      val typedImpArgs = implicitArgs.map {
        case lpTypedVar(term,ty) => s"[${term.pretty} : ${ty.pretty}]"
        case others => s"[${others.pretty}]"
      }

      val typedVars = variables.map {
        case lpOlTypedVar(term, ty) => s"(${term.pretty} : ${ty.lift2Meta.pretty})"
        case lpOlTyVar(name) => s"($name : ${lpSet.pretty})"
        case others => s"${others.pretty}"
      }

      val gap1 = if (implicitArgs.isEmpty) "" else " "
      val gap2 = if (variables.isEmpty) "" else " "
      s"${modifier.map(mod => s"${mod.pretty} ").mkString("")}symbol ${name.pretty}$gap1${typedImpArgs.mkString(" ")}$gap2${typedVars.mkString(" ")}:${if (typing.isDefined) typing.get.pretty} ≔\n${proofEnc};\n"
    }
  }

  case class lpRule(symbol: lpTerm, variableIdentifier: Seq[lpOlUntypedVar], lambdaTerm: lpTerm) extends lpStatement {
    override def pretty: String = s"rule ${symbol.pretty} ${variableIdentifier.map(var0 => var0.pretty).mkString(" ")} ↪ ${lambdaTerm.pretty};\n"
  }
  abstract class lpDefinedRules extends lpStatement {

    def proofIsDefined: Boolean = false

    def proofRWfree: Boolean = true

    def name: lpConstantTerm

    def ty: lpMlType

    def proof: lpProofScript

    def dec: lpDeclaration

  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// LP META LOGIC /////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  ////////////////////////// META LOGIC TYPES
  abstract class lpType extends lpTerm{
    def lift2Meta: lpMlType
  }

  abstract class lpMlType extends lpType {
    def pretty: String
  }

  case class lpMlDependType(vars: Seq[lpVariable], body: lpMlType) extends lpMlType {
    override def pretty: String = {
      val decVars = vars.map {
        case v: lpTypedVar => v.tyDec
        case v => v.pretty
      }
      val quantification = if (vars.nonEmpty) s"${lpPi.pretty} ${decVars.mkString(s", ${lpPi.pretty} ")}, " else ""
      s"$quantification${body.pretty}"
    }
    //change nothing when lifting to meta type
    override def lift2Meta: lpMlType = lpMlDependType(vars, body)
  }

  case class lpMlFunctionType(objects :Seq[lpMlType]) extends lpMlType {
    override def pretty: String = {
      s"(${objects.map(ty => ty.pretty).mkString(s" ${lpArrow.pretty} ")})"
    }

    //change nothing when lifting to meta type
    override def lift2Meta: lpMlType = lpMlFunctionType(objects)
  }

  case class lpClause(impBoundVars: Seq[Either[lpOlTypedVar, lpOlTyVar]], lits: Seq[lpOlTerm]) extends lpMlType {
    override def pretty: String = {
      val metaVars = impBoundVars.map{
        case Left(tyVar) => tyVar.asMlVar
        case Right(termVar) => termVar.asMlVar

      }
      lpMlDependType(metaVars,lpOlUntypedBinaryConnectiveTerm_multi(lpOr,lits).prf).pretty
    }

    def withoutQuant: lpOlUntypedBinaryConnectiveTerm_multi = lpOlUntypedBinaryConnectiveTerm_multi(lpOr,lits)

    override def lift2Meta: lpMlType = throw new Exception("error: trying to lift lpClause to meta")
  }

  ////////////////////////// META LOGIC TERMS

  abstract class lpVariable extends lpTerm

  case class lpTypedVar(name: lpTerm, ty: lpType) extends lpVariable {
    override def pretty: String = name.pretty

    def tyDec: String = s"(${name.pretty} : ${ty.lift2Meta.pretty})"

    def untyped: lpUntypedVar = lpUntypedVar(name)
  }

  case class lpUntypedVar(name: lpTerm) extends lpVariable {
    override def pretty: String = name.pretty
  }

  case class lpConstantTerm(name: String) extends lpTerm {
    override def pretty: String = name
  }

  case class lpLambdaTerm(vars: Seq[lpVariable], body: lpTerm) extends lpTerm {
    override def pretty: String = {
      if (vars.isEmpty){
        s"${body.pretty}"
      }else{
        val decVars = vars.map {
          case v: lpTypedVar => v.tyDec
          case v: lpOlTypedVar => v.tyDec
          case v: lpOlTyVar =>
            v.tyDec
          case v => v.pretty
        }
        s"(${lpLambda.pretty} ${decVars.mkString(" ")}, ${body.pretty})"
      }
      }
  }

  case class lpFunctionApp(f: lpTerm, args: Seq[lpTerm], implicitArgs: Seq[lpTerm]= Seq.empty) extends lpTerm {
    override def pretty: String = {
      val gap1 = if(implicitArgs.isEmpty) "" else " "
      val gap2 = if(args.isEmpty) "" else " "
      s"(${f.pretty}$gap1${implicitArgs.map(arg => s"[${arg.pretty}]").mkString(" ")}$gap2${args.map(_.pretty).mkString(" ")})"
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// OBJECT LOGIC //////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  ////////////////////////// OBJECT LOGIC TYPES

  abstract class lpOlTypeConstants extends lpType

  case object lpOlTypeConstructor extends lpOlTypeConstants {
    override def pretty: String = "⤳"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpOlTypeConstructor.pretty} to meta level")
  }

  case object lpSet extends lpMlType {
    override def pretty: String = "Set"
    override def lift2Meta: lpMlType = lpSet

    //override def lift2Poly: lpOlPolyType = throw new Exception(s"attempting to lift ${lpSet.pretty} to poly")
  }

  case object lpScheme extends lpOlTypeConstants {
    override def pretty: String = "PolySet"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpScheme.pretty} to meta level")
  }

  case object lpPrf extends lpOlTypeConstants {
    override def pretty: String = "π"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpPrf.pretty} to meta level")
  }

  case object lpSet2Schme extends lpOlTypeConstants {
    override def pretty: String = "mono"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpScheme.pretty} to meta level")
  }

  case object lpEl extends lpMlType {
    override def pretty: String = "τ"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpEl.pretty} to meta level")
  }

  case object lpEls extends lpMlType {
    override def pretty: String = "τ"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpEls.pretty} to meta level")
  }

  abstract class lpOlType extends lpType {
    def lift2Poly: lpOlPolyType
  }

  abstract class lpOlPolyType extends lpOlType

  abstract class lpOlMonoType extends lpOlType

  case class lpliftedObjectType(ty: lpOlType) extends lpMlType {
    def pretty: String = {
      ty match {
        case _ :lpOlMonoType => s"${lpEl.pretty} ${ty.pretty}"
        case _ :lpOlPolyType => s"${lpEls.pretty} ${ty.pretty}"
        case _ => throw new Exception(s"failed to print lpliftedObjectType, $ty has wrong format")
      }
    }
    // change nothing when encoding as meta type
    override def lift2Meta: lpMlType = lpliftedObjectType(ty)
  }

  case class lpliftedMonoType(ty: lpOlMonoType) extends lpOlPolyType {
    def pretty: String = {
      if (monomorphic) s"${ty.pretty}"
      else s"${lpSet2Schme.pretty} ${ty.pretty}"
    }
    override def lift2Meta: lpMlType = {
      lpliftedObjectType(lpliftedMonoType(ty))
    }
    override def lift2Poly: lpOlPolyType = {
      // changes nothing
      lpliftedMonoType(ty)
    }
  }

  abstract class lpOlSimpleType extends lpOlMonoType

  case class lpOlUserDefinedType(t: String) extends lpOlSimpleType{
    def pretty: String = t
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType(t))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlUserDefinedType(t))
  }

  case class lpOlUserDefinedPolyType(t: String) extends lpOlPolyType {
    def pretty: String = t

    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedPolyType(t))

    override def lift2Poly: lpOlPolyType = lpOlUserDefinedPolyType(t)
  }

  case class lpOlUserDefinedMonoType(t: String) extends lpOlMonoType {
    def pretty: String = t

    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType(t))

    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlUserDefinedMonoType(t))
  }

  case object lpOtype extends lpOlSimpleType {
    def pretty: String = "o"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType("o"))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOtype)
  }

  case object lpItype extends lpOlSimpleType {
    def pretty: String = "ι"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType("ι"))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpItype)
  }

  val tptpDefinedTypeMap: Map[String, lpOlMonoType] = Map(
    "$o" -> lpOtype,
    "$i" -> lpItype,
    "$int" -> lpIntType)

  case class lpOlFunctionType(args: Seq[lpOlType]) extends lpOlMonoType {
    def pretty: String = s"(${args.map(t => t.pretty).mkString(s" ${lpOlTypeConstructor.pretty} ")})"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlFunctionType(args))
    override def lift2Poly: lpOlPolyType = (lpliftedMonoType(lpOlFunctionType(args)))
  }

  case class lpOlMonoComposedType(name: lpConstantTerm, args: Seq[lpType]) extends lpOlMonoType { //todo ?
    def pretty: String = s"(${name.pretty} ${args.map(arg => arg.pretty).mkString(" ")})"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlMonoComposedType(name, args))

    override def lift2Poly: lpOlPolyType = {
      // changes nothing
      lpliftedMonoType(lpOlMonoComposedType(name, args))
    }
  }


  ////////////////////////// OBJECT LOGIC TERMS

  abstract class lpOlTerm extends lpTerm {
    def prf: lpMlType
  }

  case class liftedProp(t: lpOlTerm) extends lpMlType {
    override def pretty: String = s"${lpPrf.pretty} ${t.pretty}"

    // change nothing when encoding as meta type
    override def lift2Meta: lpMlType = liftedProp(t)
  }

  ///////////// TPTP dedined symbols
  case class lpInt(n: Int0) extends lpOlTerm {
    override def pretty: String = s"int_$n"

    override def prf: lpMlType = throw new Exception(s"trying to provide proof of an integer in LP encoding")
  }

  case object lpIntType extends lpOlMonoType {
    override def pretty: String = s"tptp_int"

    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpIntType)
    override def lift2Meta: lpMlType = lpliftedObjectType(lpIntType)
  }


  case class lpTptpOperator(name: String, ty: lpOlType, tyVars: Seq[lpOlType]) extends lpOlTerm{

    override def pretty: String = name
    def dec : lpDeclaration = lpDeclaration(lpConstantTerm(name),tyVars,ty.lift2Meta)

    override def prf: lpMlType = throw new Exception(s"trying to provide proof of an integer operator in LP encoding")
  }



  ///////////// CONNECTIVES
  abstract class lpOlConnective extends lpTerm {
    def pretty: String
  }

  abstract class lpOlUnaryConnective extends lpOlConnective

  final case object lpNot extends lpOlUnaryConnective {override def pretty: String = "¬"}

  abstract class lpOlBinaryConnective extends lpOlConnective

  final case object lpOr extends lpOlBinaryConnective {override def pretty: String = "∨"}

  final case object lpAnd extends lpOlBinaryConnective {override def pretty: String = "∧"}

  final case object lpImp extends lpOlBinaryConnective {override def pretty: String = "⇒"}

  final case object lpEq extends lpOlBinaryConnective {
    override def pretty: String = "="
    def definitionName(): lpConstantTerm = lpConstantTerm("ind_eq")
  }

  final case object lpInEq extends lpOlBinaryConnective {override def pretty: String = "≠"}

  abstract class lpOlQuantifier extends lpOlConnective

  final case object lpOlExists extends lpOlQuantifier {override def pretty: String = "∃"}

  final case object lpOlForAll extends lpOlQuantifier {override def pretty: String = "∀"}


  ///////////// NATS

  case class lpNum(n: Int) extends lpOlTerm {
    override def pretty: String = n.toString

    override def prf: liftedProp = throw new Exception(s"attempting to lift number encoding to meta level")
  }

  ///////////// LISTS

  case object lpListConst extends lpTerm {
    override def pretty: String = "⸬"
  }

  case object lpListLast extends lpTerm {
    override def pretty: String = "□"
  }

  case class lpList(els : Seq[lpOlTerm]) extends lpOlTerm {

    val listEnd = els match {
      case Seq() =>
        lpListLast.pretty
      case _ =>
        f" ${lpListConst.pretty} ${lpListLast.pretty}"
    }
    override def pretty: String = s"(${els.map(el => el.pretty).mkString(f" ${lpListConst.pretty} ")}${listEnd})"

    override def prf: liftedProp = throw new Exception(s"attempting to lift list encoding to meta level")
  }

  ///////////// CONSTANTS

  case object lpOlWildcard extends lpOlTerm {
    override def pretty: String = "_"

    override def prf: liftedProp = liftedProp(lpOlWildcard)
  }

  case object lpOlTop extends lpOlTerm {
    override def pretty: String = "⊤"
    override def prf: liftedProp = liftedProp(lpOlTop)
  }

  case object lpOlTop_i extends lpOlTerm {
    override def pretty: String = "⊤ᵢ"

    override def prf: liftedProp = throw new Exception("trying to print prf for ⊤ᵢ")
  }

  case object lpOlBot extends lpOlTerm {
    override def pretty: String = "⊥"
    override def prf: liftedProp = liftedProp(lpOlBot)
  }

  case object lpElWitness extends lpOlTerm {
    override def pretty: String = "el"

    override def prf: liftedProp = throw new Exception(s"trying to lift ${lpElWitness.pretty} to meta")
  }

  /*case class lpWitness(ty: lpType) extends lpOlTerm {

    if (! ty.isInstanceOf[lpOlType]) {throw new Exception(s"trying to create a witness of meta-level type ${ty.pretty}")}
    override def pretty: String = s"(${lpElWitness.pretty} ${ty.pretty})"
    override def prf: liftedProp =
      if (ty == lpOtype) liftedProp(lpWitness(ty))
      else throw new Exception(s"trying to encode ${lpWitness(ty).pretty} as a proof")
  }

   */
  case class lpWitness(ty: lpOlType) extends lpOlTerm {
    override def pretty: String =
      s"(${lpElWitness.pretty} ${ty.pretty})"

    override def prf: liftedProp = {
      if (ty == lpOtype) liftedProp(lpWitness(ty))
      else throw new Exception(s"trying to encode ${lpWitness(ty).pretty} as a proof")
    }
  }
  object lpWitness {
    def fromAnyType(ty: lpType): lpWitness = ty match {
      case t: lpOlType => lpWitness(t)
      case lpliftedObjectType(t0) => lpWitness(t0)
      case _ => throw new Exception(s"trying to generate witness term for a type that is not an encoded HOL type: ${ty.pretty}")
    }
  }

  case object lpOlNothing extends lpOlTerm {
    override def pretty: String = ""

    override def prf: liftedProp = liftedProp(lpOlNothing)
  }

  val tptpDefinedSymbolMap: Map[String, lpOlTerm] = Map(
    "$false" -> lpOlBot,
    "$true" -> lpOlTop)

  case class lpOlConstantTerm(a : String) extends lpOlTerm{
    override def pretty: String = a
    override def prf: liftedProp = liftedProp(lpOlConstantTerm(a))
  }


  ///////////// VARIABLES

  case class lpRuleVariable(v: lpOlConstantTerm) extends lpVariable {
    override def pretty: String = s"(${v.pretty})"
  }

  case class lpOlTypedVar(name: lpOlConstantTerm, ty: lpOlType) extends lpOlTerm {

    def tyDec: String = s"(${name.pretty}: ${ty.lift2Meta.pretty})"
    override def pretty: String = name.pretty
    def asMlVar: lpTypedVar = lpTypedVar(lpConstantTerm(name.pretty),ty.lift2Meta)

    /*
    def lift2Meta: lpTypedVar = {
      val metaType = ty match {
        case ty0:lpOlType => ty0.lift2Meta
        case ty0:lpMlType =>
          if (ty0 == lpSet) lpSet
          else throw new Exception(s"attempting to type OL variable ${name.pretty} with meta-level type ${ty.pretty} in LP encoding")
      }
      lpTypedVar(lpConstantTerm(name.pretty),metaType)
    }
     */

    override def prf: liftedProp = liftedProp(lpOlTypedVar(name,ty))

  }

  case class lpOlTyVar(name:String) extends lpOlMonoType {

    def tyDec: String = s"($name: ${lpSet.pretty})"
    override def pretty: String = name
    
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlTyVar(name:String))

    def asMlVar: lpTypedVar = lpTypedVar(lpConstantTerm(name),lpSet.lift2Meta)

    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlTyVar(name:String))
  }

  case class lpOlUntypedVar(name: lpTerm) extends lpOlTerm {
    override def pretty: String = name.pretty

    def lift2Meta: lpUntypedVar = lpUntypedVar(lpConstantTerm(name.pretty))

    override def prf: liftedProp = liftedProp(lpOlUntypedVar(name))
  }

  ///////////// TERMS

  case class lpOlLambdaTerm(vars: Seq[Either[lpOlTypedVar,lpOlTyVar]], body: lpOlTerm) extends lpOlTerm {
    override def pretty: String = {
      val decVars = vars.map{
        case Left(tyVar) => tyVar.tyDec
        case Right(termVar) => termVar.tyDec
      }
      s"(${lpLambda.pretty} ${decVars.mkString(" ")}, ${body.pretty})"
    }
    override def prf: liftedProp = liftedProp(lpOlLambdaTerm(vars, body))
  }

  case class lpOlFunctionApp(f: lpOlTerm, args: Seq[Either[lpOlTerm,lpOlType]]) extends lpOlTerm{
    override def pretty: String = {
      val prettyArgs = args.map(arg => arg match {
        case Left(term) => term.pretty
        case Right(ty) => ty.pretty
      })
      if (args.isEmpty) f.pretty else s"(${f.pretty} ${prettyArgs.mkString(" ")})"
    }
    override def prf: liftedProp = liftedProp(lpOlFunctionApp(f, args))
  }

  object lpOlFunctionApp {
    def apply(f: lpOlTerm, args: Seq[Either[lpOlTerm, lpOlType]]): lpOlFunctionApp = f match {
      case lpOlFunctionApp(f0, innerArgs) =>
        new lpOlFunctionApp(f0, innerArgs ++ args)
      case _ =>
        new lpOlFunctionApp(f, args)
    }
  }

  abstract class lpOlConnectiveTerm extends lpOlTerm

  case class lpOlUnaryConnectiveTerm(connective: lpOlUnaryConnective, body: lpOlTerm) extends lpOlConnectiveTerm{
    override def pretty: String = s"(${connective.pretty} ${body.pretty})"
    override def prf: liftedProp = liftedProp(lpOlUnaryConnectiveTerm(connective, body))
  }

  case class lpOlUntypedBinaryConnectiveTerm(connective: lpOlBinaryConnective, lhs: lpOlTerm, rhs: lpOlTerm) extends lpOlConnectiveTerm {
    override def pretty: String = s"(${lhs.pretty} ${connective.pretty} ${rhs.pretty})"
    override def prf: liftedProp = liftedProp(lpOlUntypedBinaryConnectiveTerm(connective, lhs, rhs))
  }

  case class lpOlUntypedBinaryConnectiveTerm_multi(connective: lpOlBinaryConnective, args: Seq[lpOlTerm]) extends lpOlConnectiveTerm {
    override def pretty: String = {
      val term = s"${args.map(arg => arg.pretty).mkString(s" ${connective.pretty} ")}"
      if (args.length == 1) term else s"($term)"
    }
    override def prf: liftedProp = liftedProp(lpOlUntypedBinaryConnectiveTerm_multi(connective, args))
  }

  case class lpOlTypedBinaryConnectiveTerm(connective: lpOlBinaryConnective, ty: lpOlType, lhs: lpOlTerm, rhs: lpOlTerm) extends lpOlConnectiveTerm {
    override def pretty: String = {
      if (monomorphic) {
        //if (connective == lpInEq) lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,ty, lhs, rhs)).pretty
        //else s"(${lhs.pretty} ${connective.pretty} ${rhs.pretty})"
        s"(${lhs.pretty} ${connective.pretty} ${rhs.pretty})"
      }
      else {
        val encodedType = ty match {
          case _ :lpOlMonoType => s"${ty.lift2Poly.pretty}"
          case _ => throw new Exception(s"failed to print lpTypedBinaryConnectiveTerm($connective,$ty,$lhs,$rhs), $ty has wrong format")
        }
        s"(${connective.pretty} [$encodedType] ${lhs.pretty} ${rhs.pretty})"
      }
    }
    override def prf: liftedProp = liftedProp(lpOlTypedBinaryConnectiveTerm(connective, ty, lhs, rhs))
  }

  case class lpOlMonoQuantifiedTerm(quantifier: lpOlQuantifier, variable: lpOlTypedVar, body: lpOlTerm, explicitlyType:Boolean = false) extends lpOlTerm {
    override def pretty: String = {
      // if partially applied, the variable is a function
      if (explicitlyType) {
        val ty0 = variable.ty match {
          case lpOlFunctionType(Seq(a,`lpOtype`)) => a
          case _ => throw new Exception(s"unextected type when encoding quantification")
        }
        s"(${quantifier.pretty} [${ty0.pretty}] ${variable.name.pretty})"
      }
      else s"(${quantifier.pretty}${lpLambdaTerm(Seq(variable.asMlVar),body).pretty})"
    }
    override def prf: liftedProp = liftedProp(lpOlMonoQuantifiedTerm(quantifier, variable, body))
  }

  case class lpOlQuantifiedTerm(quantifier: lpOlQuantifier, variables: Seq[lpOlTypedVar], body: lpOlTerm) extends lpOlTerm {

    def quantEachVar(quantifier: lpOlQuantifier, variables: Seq[lpOlTypedVar], body: lpOlTerm): lpOlTerm = {
      if (variables.isEmpty) throw new Exception("trying to encode Lambdapi quanification without variables")
      else if (variables.length == 1) lpOlMonoQuantifiedTerm(quantifier, variables.head, body)
      else {
        var quantifiedTerm = body
        variables foreach { variable =>
          quantifiedTerm = lpOlMonoQuantifiedTerm(quantifier, variable, quantifiedTerm)
        }
        quantifiedTerm
      }
    }

    override def pretty: String = {
      quantEachVar(quantifier, variables, body).pretty
    }

    override def prf: liftedProp = liftedProp(lpOlQuantifiedTerm(quantifier, variables, body))
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// LP PROOF SCRIPTS //////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class lpProofScriptStep(tab: Int) extends lpStatement{

    if (tab < 0) throw new Exception(s"Error: Trying to add negative tabulator in proof scripts of lambdapi encoding")

    def addTab(i:Int) : lpProofScriptStep

    def toProofScrips : lpProofScript

    private[lpDatastructures] def openCurlyBracket : String

  }

  case class lpProofScriptCommentLine(comment: String,tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    val tabs = "\t" * tab
    override def addTab(i: Int): lpProofScriptStep = lpProofScriptCommentLine(comment, tab + i)

    override def toProofScrips: lpProofScript = throw new Exception(s"Error: trying to convert the single comment `$comment` to a proof script")

    override def pretty: String = s"$tabs// $comment"
    override private[lpDatastructures] def openCurlyBracket : String = s"$tabs{// $comment"
  }

  case class lpProofScriptStringProof(proof: String, tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    val tabs = "\t" * tab

    override def addTab(i: Int): lpProofScriptStep = lpProofScriptStringProof(proof, tab + i)

    override def toProofScrips: lpProofScript = throw new Exception(s"Error: trying to convert the single comment `$proof` to a proof script")

    override def pretty: String = s"$tabs$proof"

    override private[lpDatastructures] def openCurlyBracket: String = s"$tabs{$proof"
  }

  case class lpProofScriptAdmit(tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    val tabs = "\t" * tab

    override def addTab(i: Int): lpProofScriptStep = lpProofScriptAdmit(tab + i)

    override def toProofScrips: lpProofScript = throw new Exception(s"Error: trying to convert the single comment `admit` to a proof script")

    override def pretty: String = s"${tabs}admit"

    override private[lpDatastructures] def openCurlyBracket: String = s"$tabs{admit"
  }

  case class lpSimplify(symbolsToUnfold: Set[lpConstantTerm], tab: Int = 0)  extends lpProofScriptStep(tab: Int) {
    override def addTab(i: Int): lpProofScriptStep = lpSimplify(symbolsToUnfold, tab + i)

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpSimplify(symbolsToUnfold, tab)))

    val tabs = "\t" * tab
    override def pretty: String = s"${tabs}simplify ${symbolsToUnfold.map(sym => sym.pretty).mkString(" ")}"

    override def openCurlyBracket: String = s"${tabs}{simplify ${symbolsToUnfold.map(sym => sym.pretty).mkString(" ")}"
  }

  case class lpProofScript(steps: Seq[lpProofScriptStep], tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    val tabs = "\t" * tab

    def addTab(i: Int): lpProofScript = lpProofScript(steps, tab + i)

    override def pretty: String = {
      s"${steps.map(step => s"${step.addTab(tab).pretty}").mkString(";\n")}"
    }

    override private[lpDatastructures] def openCurlyBracket: String = {
      if (steps.length == 1) s"${steps.head.addTab(tab).openCurlyBracket}"
      else if (steps.length == 0) "there shoudl be nothing here" //throw new Exception(s"trying to give curly brackets to empty list")
      else s"${steps.head.addTab(tab).openCurlyBracket};\n${steps.tail.map(step => s"${step.addTab(tab).pretty}").mkString(";\n")}"
    }

    def prettyCurlyBrackets: String = {
      if (steps.length == 1) s"${steps.head.addTab(tab).openCurlyBracket}}"
      else if (steps.length == 0) "there shoudl be nothing here" //throw new Exception(s"trying to give curly brackets to empty list")
      else s"${steps.head.addTab(tab).openCurlyBracket};\n${steps.tail.map(step => s"${step.addTab(tab).pretty}").mkString(";\n")}}"
    }

    override def toProofScrips: lpProofScript = lpProofScript(steps, tab)

  }

  case class lpRefine(t: lpFunctionApp, subproofs: Seq[lpProofScript] = Seq.empty, tab: Int = 0) extends lpProofScriptStep(tab: Int){
    def addTab(i : Int): lpRefine = lpRefine(t, subproofs, tab + i)
    override def pretty: String = {
      val tabs = "\t"*tab
      //s"${tabs}have $name : ${ty.pretty}\n${proofScript.addTab(tab + 1).prettyCurlyBrackets}"
      s"${tabs}refine ${t.pretty}${subproofs.map(prf => s"\n${prf.addTab(tab+1).prettyCurlyBrackets}").mkString("")}"
    }

    val tabs = "\t" * tab

    override private[lpDatastructures] def openCurlyBracket: String = {
      // s"$tabs{${lpRefine(t).pretty}" (old version)
      // s"${tabs}{have $name : ${ty.pretty}\n${proofScript.addTab(tab + 1).prettyCurlyBrackets}" (haveStep for reference)
      s"${tabs}{refine ${t.pretty}${subproofs.map(prf => s"\n${prf.addTab(tab+1).prettyCurlyBrackets}").mkString("")}"
    }

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpRefine(t, subproofs, tab)))

  }

  case class lpHave(name: String, ty: lpMlType, proofScript: lpProofScript,tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    def addTab(i : Int): lpHave = lpHave(name,ty, proofScript, tab + i)
    override def pretty: String = {
      val tabs: String = "\t"*tab
      s"${tabs}have $name : ${ty.pretty}\n${proofScript.addTab(tab + 1).prettyCurlyBrackets}"
    }

    val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket: String = s"${tabs}{have $name : ${ty.pretty}\n${proofScript.addTab(tab + 1).prettyCurlyBrackets}" //s"$tabs{${lpHave(name,ty, proofScript).pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpHave(name,ty, proofScript, tab)))
  }

  case class lpEval(tacticTerm: lpTerm, tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    def addTab(i: Int): lpEval = lpEval(tacticTerm, tab + i)

    override def pretty: String = {
      val tabs: String = "\t" * tab
      s"${tabs}eval ${tacticTerm.pretty}"
    }

    val tabs = "\t" * tab

    override private[lpDatastructures] def openCurlyBracket: String = s"${tabs}{eval ${tacticTerm.pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpEval(tacticTerm: lpTerm, tab)))
  }

  case class lpRewritePattern (pattern: lpTerm, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x"))) extends lpTerm {
    override def pretty: String = {
      s".[${patternVar.pretty} in ${pattern.pretty}]"
    }
  }

  case class lpRewrite(rewritePattern0: Option[lpRewritePattern], rewriteTerm: lpTerm, tab: Int = 0) extends lpProofScriptStep(tab: Int){
    def addTab(i : Int): lpRewrite =lpRewrite(rewritePattern0, rewriteTerm, tab + i)
    override def pretty: String = {
      val tabs: String = "\t" * tab
      val rewritePattern = if (rewritePattern0.isDefined) s"${rewritePattern0.get.pretty} " else ""
      s"${tabs}rewrite $rewritePattern${rewriteTerm.pretty}"
    }

    val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket: String = s"$tabs{${lpRewrite(rewritePattern0, rewriteTerm).pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpRewrite(rewritePattern0, rewriteTerm, tab)))
  }

  case class lpReflexivity(tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    def addTab(i : Int): lpReflexivity = lpReflexivity(tab + i)
    override def pretty: String = {
      val tabs: String = "\t" * tab
      s"${tabs}reflexivity"
    }

    val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket: String = s"$tabs{${lpReflexivity()}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpReflexivity(tab)))
  }

  case class lpAssume(vars: Seq[lpTerm], tab: Int = 0) extends lpProofScriptStep(tab: Int){
    def addTab(i : Int): lpAssume = lpAssume(vars, tab + i)

    val tabs: String = "\t" * tab
    override def pretty: String = {
      s"${tabs}assume ${vars.map(var0 => var0.pretty).mkString(" ")}"
    }

    override private[lpDatastructures] def openCurlyBracket: String = s"$tabs{${lpAssume(vars).pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpAssume(vars, tab)))
  }
}
