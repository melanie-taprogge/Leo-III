package leo.modules.output.LPoutput

import leo.datastructures.{Int0, termArgs}
import leo.modules.output.LPoutput.LPoutput.abbreviationSignatureFile

/**
  *
  * @author Melanie Taprogge
  */

object lpDatastructures {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// LP SYNTAX /////////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val monomorphic = true

  final case class PrettyConfig(sigPrefix: Boolean = true, formulaPrefix: Boolean = true)

  abstract class lpStatement {
    def pretty (implicit prefix : PrettyConfig = PrettyConfig(false,false)): String
  }

  abstract class lpModifier extends lpStatement

  case object lpOpaque extends lpModifier {
    override def pretty (implicit prefix : PrettyConfig): String = "opaque"
  }

  abstract class lpTerm extends lpStatement

  abstract class lpConstants extends  lpTerm

  case object lpLambda extends lpConstants {
    override def pretty (implicit prefix : PrettyConfig): String = "λ"
  }

  case object lpPi extends lpConstants {
    override def pretty (implicit prefix : PrettyConfig): String = "Π"
  }

  case object lpArrow extends lpConstants {
    override def pretty (implicit prefix : PrettyConfig): String = "→"
  }

  case object lpWildcard extends lpTerm {
    override def pretty (implicit prefix : PrettyConfig): String = "_"
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// KINDS OF STATEMENTS ///////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  case class lpDeclaration(name: lpStatement, variables: Seq[lpTerm], typing: lpType, implicitArgs: Seq[lpTerm]= Seq.empty) extends lpStatement{
    override def pretty (implicit prefix : PrettyConfig): String = {

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

  case class lpDefinition(name: lpConstantTerm, variables: Seq[lpTerm], maybeTyping: Option[lpMlType], proof: lpStatement, implicitArgs: Seq[lpTerm]= Seq.empty, modifier: Seq[lpModifier]= Seq.empty) extends lpStatement {
    override def pretty (implicit prefix : PrettyConfig): String = {

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

      val typing = if (maybeTyping.isDefined) s": ${maybeTyping.get.pretty}" else ""

      val gap1 = if (implicitArgs.isEmpty) "" else " "
      val gap2 = if (variables.isEmpty) "" else " "
      s"${modifier.map(mod => s"${mod.pretty} ").mkString("")}symbol ${name.pretty}$gap1${typedImpArgs.mkString(" ")}$gap2${typedVars.mkString(" ")}$typing ≔${if (maybeTyping.isDefined) "\n" else " "}${proofEnc};\n"
    }
  }

  case class lpRule(symbol: lpTerm, variableIdentifier: Seq[lpOlUntypedVar], lambdaTerm: lpTerm) extends lpStatement {
    override def pretty (implicit prefix : PrettyConfig): String = s"rule ${symbol.pretty} ${variableIdentifier.map(var0 => var0.pretty).mkString(" ")} ↪ ${lambdaTerm.pretty};\n"
  }
  abstract class lpDefinedRules extends lpStatement {

    def proofIsDefined: Boolean = false

    def proofRWfree: Boolean = true

    def name: lpConstantTerm

    def ty: lpMlType

    def proof: lpProofScript

    def dec: lpDeclaration

  }

  abstract class lpSimpRuleVersion extends lpStatement {
    def term: lpTerm
    def rwLeft: Boolean

    override def pretty (implicit prefix : PrettyConfig): String = term.pretty
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// LP META LOGIC /////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  ////////////////////////// META LOGIC TYPES
  abstract class lpType extends lpTerm{
    def lift2Meta: lpMlType
  }

  abstract class lpMlType extends lpType {
  }

  case class lpMlDependType(vars: Seq[lpVariable], body: lpMlType) extends lpMlType {
    override def pretty (implicit prefix : PrettyConfig): String = {
      val decVars = vars.map {
        case v: lpTypedVar =>
          val tyDec: String = s"(${v.name.pretty} : ${v.ty.lift2Meta.pretty})"
          tyDec
        case v => v.pretty
      }
      val quantification = if (vars.nonEmpty) s"${lpPi.pretty} ${decVars.mkString(s", ${lpPi.pretty} ")}, " else ""
      s"$quantification${body.pretty}"
    }
    //change nothing when lifting to meta type
    override def lift2Meta: lpMlType = lpMlDependType(vars, body)
  }

  case class lpMlFunctionType(objects :Seq[lpMlType]) extends lpMlType {
    override def pretty (implicit prefix : PrettyConfig): String = {
      s"(${objects.map(ty => ty.pretty).mkString(s" ${lpArrow.pretty} ")})"
    }

    //change nothing when lifting to meta type
    override def lift2Meta: lpMlType = lpMlFunctionType(objects)
  }

  case class lpClause(impBoundVars: Seq[Either[lpOlTypedVar, lpOlTyVar]], lits: Seq[lpOlTerm]) extends lpMlType {
    override def pretty (implicit prefix : PrettyConfig): String = {
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
    override def pretty (implicit prefix : PrettyConfig): String = name.pretty

    //def tyDec: String = s"(${name.pretty()} : ${ty.lift2Meta.pretty})"

    def untyped: lpUntypedVar = lpUntypedVar(name)
  }

  case class lpUntypedVar(name: lpTerm) extends lpVariable {
    override def pretty (implicit prefix : PrettyConfig): String = name.pretty
  }

  case class lpConstantTerm(name: String) extends lpTerm {
    override def pretty (implicit prefix : PrettyConfig): String = name
  }

  case class lpLambdaTerm(vars: Seq[lpVariable], body: lpTerm) extends lpTerm {
    override def pretty (implicit prefix : PrettyConfig): String = {
      if (vars.isEmpty){
        s"${body.pretty}"
      }else{
        val decVars = vars.map {
          case v: lpTypedVar =>
            val tyDec: String = s"(${v.name.pretty} : ${v.ty.lift2Meta.pretty})"
            tyDec
          case v: lpOlTypedVar => v.tyDec
          case v: lpOlTyVar =>
            v.tyDec
          case v => v.pretty
        }
        s"(${lpLambda.pretty} ${decVars.mkString(" ")}, ${body.pretty})"
      }
      }
  }

  case class lpFunctionApp(f: lpTerm, args: Seq[lpTerm]= Seq.empty, implicitArgs: Seq[lpTerm]= Seq.empty) extends lpTerm {
    override def pretty (implicit prefix : PrettyConfig): String = {
      val gap1 = if(implicitArgs.isEmpty) "" else " "
      val gap2 = if(args.isEmpty) "" else " "
      s"(${f.pretty}$gap1${implicitArgs.map(arg => s"[${arg.pretty}]").mkString(" ")}$gap2${args.map(_.pretty).mkString(" ")})"
    }
  }
  object lpFunctionApp{
    def toDefName(headSymbolName: String, args: Seq[lpTerm] = Seq.empty, implicitArgs: Seq[lpTerm] = Seq.empty): lpFunctionApp =
      lpFunctionApp(lpConstantTerm(headSymbolName), args, implicitArgs)

    def mk(f: lpTerm, args: Seq[lpTerm]= Seq.empty, implicitArgs: Seq[lpTerm]= Seq.empty): lpTerm =
      (args, implicitArgs) match {
        case (Nil,Nil) => f
        case _ => lpFunctionApp(f, args, implicitArgs)
      }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// OBJECT LOGIC //////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  ////////////////////////// OBJECT LOGIC TYPES

  abstract class lpOlTypeConstants extends lpType

  case object lpOlTypeConstructor extends lpOlTypeConstants {
    override def pretty (implicit prefix : PrettyConfig): String = "⤳"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpOlTypeConstructor.pretty(PrettyConfig(false,false))} to meta level")
  }

  case object lpSet extends lpMlType {
    override def pretty (implicit prefix : PrettyConfig): String = "Set"
    override def lift2Meta: lpMlType = lpSet

    //override def lift2Poly: lpOlPolyType = throw new Exception(s"attempting to lift ${lpSet.pretty} to poly")
  }

  case object lpScheme extends lpOlTypeConstants {
    override def pretty (implicit prefix : PrettyConfig): String = "PolySet"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpScheme.pretty(PrettyConfig(false,false))} to meta level")
  }

  case object lpPrf extends lpOlTypeConstants {
    override def pretty (implicit prefix : PrettyConfig): String = "π"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpPrf.pretty(PrettyConfig(false,false))} to meta level")
  }

  case object lpSet2Schme extends lpOlTypeConstants {
    override def pretty (implicit prefix : PrettyConfig): String = "mono"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpScheme.pretty(PrettyConfig(false,false))} to meta level")
  }

  case object lpEl extends lpMlType {
    override def pretty (implicit prefix : PrettyConfig): String = "τ"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpEl.pretty(PrettyConfig(false,false))} to meta level")
  }

  case object lpEls extends lpMlType {
    override def pretty (implicit prefix : PrettyConfig): String = "τ"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpEls.pretty(PrettyConfig(false,false))} to meta level")
  }

  abstract class lpOlType extends lpType {
    def lift2Poly: lpOlPolyType
  }

  abstract class lpOlPolyType extends lpOlType

  abstract class lpOlMonoType extends lpOlType

  case class lpliftedObjectType(ty: lpOlType) extends lpMlType {
    override def pretty (implicit prefix : PrettyConfig): String = {
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
    override def pretty (implicit prefix : PrettyConfig): String = {
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
    override def pretty(implicit prefix: PrettyConfig): String = t
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType(t))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlUserDefinedType(t))
  }

  case class lpOlUserDefinedPolyType(t: String) extends lpOlPolyType {
    override def pretty (implicit prefix : PrettyConfig): String = t

    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedPolyType(t))

    override def lift2Poly: lpOlPolyType = lpOlUserDefinedPolyType(t)
  }

  case class lpOlUserDefinedMonoType(t: String) extends lpOlMonoType {
    override def pretty (implicit prefix : PrettyConfig): String = t

    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType(t))

    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlUserDefinedMonoType(t))
  }

  case object lpOtype extends lpOlSimpleType {
    override def pretty (implicit prefix : PrettyConfig): String = "o"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType("o"))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOtype)
  }

  case object lpItype extends lpOlSimpleType {
    override def pretty (implicit prefix : PrettyConfig): String = "ι"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType("ι"))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpItype)
  }

  val lpDefOlTypes: Map[String, lpOlMonoType] = Map(
    "$o" -> lpOtype,
    "$i" -> lpItype
  )

  val tptpDefinedTypeMap: Map[String, lpOlMonoType] = Map(
    "$int" -> lpIntType
  )

  case class lpOlFunctionType(args: Seq[lpOlType]) extends lpOlMonoType {
    override def pretty (implicit prefix : PrettyConfig): String = s"(${args.map(t => t.pretty).mkString(s" ${lpOlTypeConstructor.pretty} ")})"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlFunctionType(args))
    override def lift2Poly: lpOlPolyType = (lpliftedMonoType(lpOlFunctionType(args)))
  }

  case class lpOlMonoComposedType(name: lpConstantTerm, args: Seq[lpType]) extends lpOlMonoType { //todo ?
    override def pretty (implicit prefix : PrettyConfig): String = s"(${name.pretty} ${args.map(arg => arg.pretty).mkString(" ")})"
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
    override def pretty (implicit prefix : PrettyConfig): String = s"${lpPrf.pretty} ${t.pretty}"

    // change nothing when encoding as meta type
    override def lift2Meta: lpMlType = liftedProp(t)
  }

  ///////////// TPTP dedined symbols
  case class lpInt(n: Int0) extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = {
      val baseName = s"int_$n"
      if (prefix.sigPrefix) s"$abbreviationSignatureFile$baseName" else baseName
    }

    override def prf: lpMlType = throw new Exception(s"trying to provide proof of an integer in LP encoding")
  }

  case object lpIntType extends lpOlMonoType {
    val baseName = "tptp_int"
    override def pretty (implicit prefix : PrettyConfig): String = if (prefix.sigPrefix) s"${abbreviationSignatureFile}$baseName" else baseName
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpIntType)
    override def lift2Meta: lpMlType = lpliftedObjectType(lpIntType)
  }


  case class lpTptpOperator(name: String, ty: lpOlType, tyVars: Seq[lpOlType]) extends lpOlTerm{

    override def pretty (implicit prefix : PrettyConfig): String = name
    def dec : lpDeclaration = lpDeclaration(lpConstantTerm(name),tyVars,ty.lift2Meta)

    override def prf: lpMlType = throw new Exception(s"trying to provide proof of an integer operator in LP encoding")
  }



  ///////////// CONNECTIVES

  abstract class lpOlUnappliedConnective(val base: lpOlConnective) extends lpOlTerm {
    def unapplied: lpOlUnappliedConnective = this

    override def pretty (implicit prefix : PrettyConfig): String = s"(${base.pretty})"

    override def prf: lpMlType = throw new Exception("trying to output proof for unapplied connective")
  }

  abstract class lpOlConnective extends lpTerm {
    //override def pretty (implicit prefix : PrettyConfig): String

    def firstArgImp: Boolean

    def unapplied: lpOlUnappliedConnective =
      new lpOlUnappliedConnective(this) {}
  }

  abstract class lpOlUnaryConnective extends lpOlConnective

  final case object lpNot extends lpOlUnaryConnective {override def pretty (implicit prefix : PrettyConfig): String = "¬"; override def firstArgImp: Boolean = false}

  abstract class lpOlUntypedBinaryConnective extends lpOlConnective

  abstract class lpOlTypedBinaryConnective extends lpOlConnective

  final case object lpOr extends lpOlUntypedBinaryConnective {override def pretty (implicit prefix : PrettyConfig): String = "∨"; override def firstArgImp: Boolean = false}

  final case object lpAnd extends lpOlUntypedBinaryConnective {override def pretty (implicit prefix : PrettyConfig): String = "∧"; override def firstArgImp: Boolean = false}

  final case object lpImp extends lpOlUntypedBinaryConnective {override def pretty (implicit prefix : PrettyConfig): String = "⇒"; override def firstArgImp: Boolean = false}

  final case object lpEq extends lpOlTypedBinaryConnective {override def pretty (implicit prefix : PrettyConfig): String = "="; override def firstArgImp: Boolean = true}

  final case object lpInEq extends lpOlTypedBinaryConnective {override def pretty (implicit prefix : PrettyConfig): String = "≠"; override def firstArgImp: Boolean = true}

  abstract class lpOlBinder extends lpOlConnective

  final case object lpOlExists extends lpOlBinder {override def pretty (implicit prefix : PrettyConfig): String = "∃"; override def firstArgImp: Boolean = true}

  final case object lpOlForAll extends lpOlBinder {override def pretty (implicit prefix : PrettyConfig): String = "∀"; override def firstArgImp: Boolean = true}

  final case object lpChoice extends lpOlBinder {override def pretty (implicit prefix : PrettyConfig): String = "ε"; override def firstArgImp: Boolean = false}


  ///////////// NATS

  case class lpNum(n: Int) extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = n.toString

    override def prf: liftedProp = throw new Exception(s"attempting to lift number encoding to meta level")
  }

  ///////////// LISTS

  case object lpListConst extends lpTerm {
    override def pretty (implicit prefix : PrettyConfig): String = "⸬"
  }

  case object lpListLast extends lpTerm {
    override def pretty (implicit prefix : PrettyConfig): String = "□"
  }

  case class lpList(els : Seq[lpOlTerm]) extends lpOlTerm {

    override def pretty (implicit prefix : PrettyConfig): String ={
      val listEnd = els match {
        case Seq() =>
          lpListLast.pretty
        case _ =>
          f" ${lpListConst.pretty} ${lpListLast.pretty}"
      }
      s"(${els.map(el => el.pretty).mkString(f" ${lpListConst.pretty} ")}${listEnd})"
    }

    override def prf: liftedProp = throw new Exception(s"attempting to lift list encoding to meta level")
  }

  ///////////// CONSTANTS

  case object lpOlWildcard extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = "_"

    override def prf: liftedProp = liftedProp(lpOlWildcard)
  }

  case object lpOlTop extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = "⊤"
    override def prf: liftedProp = liftedProp(lpOlTop)
  }

  case object lpOlTop_i extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = "⊤ᵢ"

    override def prf: liftedProp = throw new Exception("trying to print prf for ⊤ᵢ")
  }

  case object lpOlBot extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = "⊥"
    override def prf: liftedProp = liftedProp(lpOlBot)
  }

  case object lpElWitness extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = "el"

    override def prf: liftedProp = throw new Exception(s"trying to lift ${lpElWitness.pretty(PrettyConfig(false,false))} to meta")
  }

  /*case class lpWitness(ty: lpType) extends lpOlTerm {

    if (! ty.isInstanceOf[lpOlType]) {throw new Exception(s"trying to create a witness of meta-level type ${ty.pretty}")}
    override def pretty (implicit prefix : PrettyConfig): String = s"(${lpElWitness.pretty} ${ty.pretty})"
    override def prf: liftedProp =
      if (ty == lpOtype) liftedProp(lpWitness(ty))
      else throw new Exception(s"trying to encode ${lpWitness(ty).pretty} as a proof")
  }

   */
  case class lpWitness(ty: lpOlType) extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String =
      s"(${lpElWitness.pretty} ${ty.pretty})"

    override def prf: liftedProp = {
      if (ty == lpOtype) liftedProp(lpWitness(ty))
      else throw new Exception(s"trying to encode ${lpWitness(ty).pretty(PrettyConfig(false,false))} as a proof")
    }
  }
  object lpWitness {
    def fromAnyType(ty: lpType): lpWitness = ty match {
      case t: lpOlType => lpWitness(t)
      case lpliftedObjectType(t0) => lpWitness(t0)
      case _ => throw new Exception(s"trying to generate witness term for a type that is not an encoded HOL type: ${ty.pretty(PrettyConfig(false,false))}")
    }
  }

  case object lpOlNothing extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = ""

    override def prf: liftedProp = liftedProp(lpOlNothing)
  }

  val tptpDefinedSymbolMap: Map[String, lpOlTerm] = Map(
    "$false" -> lpOlBot,
    "$true" -> lpOlTop)

  case class lpOlConstantTerm(name : String) extends lpOlTerm{
    override def pretty (implicit prefix : PrettyConfig): String = name
    override def prf: liftedProp = liftedProp(lpOlConstantTerm(name))
  }


  ///////////// VARIABLES

  case class lpRuleVariable(v: lpOlConstantTerm) extends lpVariable {
    override def pretty (implicit prefix : PrettyConfig): String = s"(${v.pretty})"
  }

  case class lpOlTypedVar(name: lpOlConstantTerm, ty: lpOlType) extends lpOlTerm {

    def tyDec (implicit prefix : PrettyConfig): String = s"(${name.pretty}: ${ty.lift2Meta.pretty})"
    override def pretty (implicit prefix : PrettyConfig): String = name.pretty
    def asMlVar: lpTypedVar = lpTypedVar(lpConstantTerm(name.name),ty.lift2Meta)

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

    def tyDec (implicit prefix : PrettyConfig): String = s"($name: ${lpSet.pretty})"
    override def pretty (implicit prefix : PrettyConfig): String = name
    
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlTyVar(name:String))

    def asMlVar: lpTypedVar = lpTypedVar(lpConstantTerm(name),lpSet.lift2Meta)

    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlTyVar(name:String))
  }

  case class lpOlUntypedVar(name: lpTerm) extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = name.pretty

    def lift2Meta (implicit prefix : PrettyConfig): lpUntypedVar = lpUntypedVar(lpConstantTerm(name.pretty))

    override def prf: liftedProp = liftedProp(lpOlUntypedVar(name))
  }

  ///////////// TERMS

  case class lpOlLambdaTerm(vars: Seq[Either[lpOlTypedVar,lpOlTyVar]], body: lpOlTerm) extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = {
      val decVars = vars.map{
        case Left(tyVar) => tyVar.tyDec
        case Right(termVar) => termVar.tyDec
      }
      s"(${lpLambda.pretty} ${decVars.mkString(" ")}, ${body.pretty})"
    }
    override def prf: liftedProp = liftedProp(lpOlLambdaTerm(vars, body))
  }
  case class lpOlFunctionApp(f: lpOlTerm, args: Seq[Either[lpOlTerm,lpOlType]], implicitArgs: Seq[Either[lpOlTerm,lpOlType]] = Seq.empty) extends lpOlTerm{
    override def pretty (implicit prefix : PrettyConfig): String = {
      val prettyArgs = args.map(arg => arg match {
        case Left(term) => term.pretty
        case Right(ty) => ty.pretty
      })
      val prettyImpArgs = implicitArgs.map(arg => arg match {
        case Left(term) => s"[${term.pretty}]"
        case Right(ty) => s"[${ty.pretty}]"
      })

      val gap0 = if (implicitArgs.isEmpty) "" else " "
      val gap1 = if (args.isEmpty) "" else " "
      s"(${f.pretty}$gap0${prettyImpArgs.mkString(" ")}$gap1${prettyArgs.mkString(" ")})"
    }
    override def prf: liftedProp = liftedProp(lpOlFunctionApp(f, args))
  }

  object lpOlFunctionApp {
    def apply(f: lpOlTerm, args: Seq[Either[lpOlTerm, lpOlType]], impArgs: Seq[Either[lpOlTerm, lpOlType]] = Seq.empty): lpOlFunctionApp = f match {
      case lpOlFunctionApp(f0, innerArgs, innerImpArgs) =>
        new lpOlFunctionApp(f0, innerArgs ++ args, impArgs ++ innerImpArgs)
      case _ =>
        new lpOlFunctionApp(f, args, impArgs)
    }
  }

  abstract class lpOlConnectiveTerm extends lpOlTerm

  case class lpOlUnaryConnectiveTerm(connective: lpOlUnaryConnective, body: lpOlTerm) extends lpOlConnectiveTerm{
    override def pretty (implicit prefix : PrettyConfig): String = s"(${connective.pretty} ${body.pretty})"
    override def prf: liftedProp = liftedProp(lpOlUnaryConnectiveTerm(connective, body))
  }

  case class lpOlUntypedBinaryConnectiveTerm(connective: lpOlUntypedBinaryConnective, lhs: lpOlTerm, rhs: lpOlTerm) extends lpOlConnectiveTerm {
    override def pretty (implicit prefix : PrettyConfig): String = s"(${lhs.pretty} ${connective.pretty} ${rhs.pretty})"
    override def prf: liftedProp = liftedProp(lpOlUntypedBinaryConnectiveTerm(connective, lhs, rhs))
  }

  final case class lpOlUntypedBinaryConnectiveTerm_multi(connective: lpOlUntypedBinaryConnective, args: Seq[lpOlTerm]) extends lpOlConnectiveTerm {
    override def pretty (implicit prefix : PrettyConfig): String = {
      val term = s"${args.map(arg => arg.pretty).mkString(s" ${connective.pretty} ")}"
      if (args.length == 1) term else s"($term)"
    }
    override def prf: liftedProp = liftedProp(lpOlUntypedBinaryConnectiveTerm_multi(connective, args))
  }

  object lpOlUntypedBinaryConnectiveTerm_multi {

    /** Smart constructor for binary conjunctions/ disjunctions: handles 0/1-ary cases. */
    def mk(connective: lpOlUntypedBinaryConnective, terms: Seq[lpOlTerm]): lpOlTerm = {
      terms match {
        case Nil => identity(connective)
        case t +: Nil => t
        case many => new lpOlUntypedBinaryConnectiveTerm_multi(connective, many)
      }
    }

    /** Convenience constructors for common connectives. */
    def conjunction(terms: Seq[lpOlTerm]): lpOlTerm =
      mk(lpAnd, terms)

    def disjunction(terms: Seq[lpOlTerm]): lpOlTerm =
      mk(lpOr, terms)

    /** helper */
    private def identity(conn: lpOlUntypedBinaryConnective): lpOlTerm = conn match {
      case `lpAnd` => lpOlTop
      case `lpOr` => lpOlBot
      case _ => throw new Exception(s"Error in LP-Encoding: Trying to construct a binary connective term for 0 elements and connective ${conn.pretty}")
    }
  }

  case class lpOlTypedBinaryConnectiveTerm(connective: lpOlTypedBinaryConnective, ty: lpOlType, lhs: lpOlTerm, rhs: lpOlTerm) extends lpOlConnectiveTerm {
    override def pretty (implicit prefix : PrettyConfig): String = {
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

  case class lpOlMonoQuantifiedTerm(quantifier: lpOlBinder, variable: lpOlTypedVar, body: lpOlTerm, explicitlyType:Boolean = false) extends lpOlTerm {
    override def pretty (implicit prefix : PrettyConfig): String = {
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

  case class lpOlBoundTerm(quantifier: lpOlBinder, variables: Seq[lpOlTypedVar], body: lpOlTerm) extends lpOlTerm {

    def quantEachVar(quantifier: lpOlBinder, variables: Seq[lpOlTypedVar], body: lpOlTerm): lpOlTerm = {
      if (variables.isEmpty) throw new Exception(s"trying to encode Lambdapi quanification without variables (body : ${body.pretty})")
      else if (variables.length == 1) lpOlMonoQuantifiedTerm(quantifier, variables.head, body)
      else {
        var quantifiedTerm = body
        variables.reverse foreach { variable =>
          quantifiedTerm = lpOlMonoQuantifiedTerm(quantifier, variable, quantifiedTerm)
        }
        quantifiedTerm
      }
    }

    override def pretty (implicit prefix : PrettyConfig): String = {
      quantEachVar(quantifier, variables, body).pretty
    }

    override def prf: liftedProp = liftedProp(lpOlBoundTerm(quantifier, variables, body))
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// LP PROOF SCRIPTS //////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class lpProofScriptStep(tab: Int) extends lpStatement{

    if (tab < 0) throw new Exception(s"Error: Trying to add negative tabulator in proof scripts of lambdapi encoding")

    def addTab(i:Int) : lpProofScriptStep

    def toProofScrips : lpProofScript

    private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig) : String

  }

  case class lpProofScriptCommentLine(comment: String,tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    val tabs = "\t" * tab
    override def addTab(i: Int): lpProofScriptStep = lpProofScriptCommentLine(comment, tab + i)

    override def toProofScrips: lpProofScript = throw new Exception(s"Error: trying to convert the single comment `$comment` to a proof script")

    override def pretty (implicit prefix : PrettyConfig): String = s"$tabs// $comment"
    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"$tabs{// $comment"
  }

  case class lpProofScriptStringProof(proof: String, tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    val tabs = "\t" * tab

    override def addTab(i: Int): lpProofScriptStep = lpProofScriptStringProof(proof, tab + i)

    override def toProofScrips: lpProofScript = throw new Exception(s"Error: trying to convert the single comment `$proof` to a proof script")

    override def pretty (implicit prefix : PrettyConfig): String = s"$tabs$proof"

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"$tabs{$proof"
  }

  case class lpProofScriptAdmit(tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    val tabs = "\t" * tab

    override def addTab(i: Int): lpProofScriptStep = lpProofScriptAdmit(tab + i)

    override def toProofScrips: lpProofScript = throw new Exception(s"Error: trying to convert the single comment `admit` to a proof script")

    override def pretty (implicit prefix : PrettyConfig): String = s"${tabs}admit"

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"$tabs{admit"
  }

  case class lpSimplify(symbolsToUnfold: Set[lpConstantTerm], tab: Int = 0)  extends lpProofScriptStep(tab: Int) {
    override def addTab(i: Int): lpProofScriptStep = lpSimplify(symbolsToUnfold, tab + i)

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpSimplify(symbolsToUnfold, tab)))

    val tabs = "\t" * tab
    override def pretty (implicit prefix : PrettyConfig): String = s"${tabs}simplify ${symbolsToUnfold.map(sym => sym.pretty).mkString(" ")}"

    override def openCurlyBracket (implicit prefix : PrettyConfig): String = s"${tabs}{simplify ${symbolsToUnfold.map(sym => sym.pretty).mkString(" ")}"
  }

  case class lpProofScript(steps: Seq[lpProofScriptStep], tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    val tabs = "\t" * tab

    def addTab(i: Int): lpProofScript = lpProofScript(steps, tab + i)

    override def pretty (implicit prefix : PrettyConfig): String = {
      s"${steps.map(step => s"${step.addTab(tab).pretty}").mkString(";\n")}"
    }

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = {
      if (steps.length == 1) s"${steps.head.addTab(tab).openCurlyBracket}"
      else if (steps.length == 0) "there shoudl be nothing here" //throw new Exception(s"trying to give curly brackets to empty list")
      else s"${steps.head.addTab(tab).openCurlyBracket};\n${steps.tail.map(step => s"${step.addTab(tab).pretty}").mkString(";\n")}"
    }

    def prettyCurlyBrackets (implicit prefix : PrettyConfig): String = {
      if (steps.length == 1) s"${steps.head.addTab(tab).openCurlyBracket}}"
      else if (steps.length == 0) "there shoudl be nothing here" //throw new Exception(s"trying to give curly brackets to empty list")
      else s"${steps.head.addTab(tab).openCurlyBracket};\n${steps.tail.map(step => s"${step.addTab(tab).pretty}").mkString(";\n")}}"
    }

    override def toProofScrips: lpProofScript = lpProofScript(steps, tab)

  }

  case class lpRefine(t: lpTerm, subproofs: Seq[lpProofScript] = Seq.empty, tab: Int = 0) extends lpProofScriptStep(tab: Int){
    def addTab(i : Int): lpRefine = lpRefine(t, subproofs, tab + i)
    override def pretty (implicit prefix : PrettyConfig): String = {
      val tabs = "\t"*tab
      //s"${tabs}have $name : ${ty.pretty}\n${proofScript.addTab(tab + 1).prettyCurlyBrackets}"
      s"${tabs}refine ${t.pretty}${subproofs.map(prf => s"\n${prf.addTab(tab+1).prettyCurlyBrackets}").mkString("")}"
    }

    val tabs = "\t" * tab

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = {
      // s"$tabs{${lpRefine(t).pretty}" (old version)
      // s"${tabs}{have $name : ${ty.pretty}\n${proofScript.addTab(tab + 1).prettyCurlyBrackets}" (haveStep for reference)
      s"${tabs}{refine ${t.pretty}${subproofs.map(prf => s"\n${prf.addTab(tab+1).prettyCurlyBrackets}").mkString("")}"
    }

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpRefine(t, subproofs, tab)))

  }

  case class lpHave(name: String, ty: lpMlType, proofScript: lpProofScript,tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    def addTab(i : Int): lpHave = lpHave(name,ty, proofScript, tab + i)
    override def pretty (implicit prefix : PrettyConfig): String = {
      val tabs: String = "\t"*tab
      s"${tabs}have $name : ${ty.pretty}\n${proofScript.addTab(tab + 1).prettyCurlyBrackets}"
    }

    val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"${tabs}{have $name : ${ty.pretty}\n${proofScript.addTab(tab + 1).prettyCurlyBrackets}" //s"$tabs{${lpHave(name,ty, proofScript).pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpHave(name,ty, proofScript, tab)))
  }

  case class lpEval(tacticTerm: lpStatement, tab: Int = 0) extends lpProofScriptStep(tab: Int) {

    def addTab(i: Int): lpEval = lpEval(tacticTerm, tab + i)

    override def pretty (implicit prefix : PrettyConfig): String = {
      val tabs: String = "\t" * tab
      s"${tabs}eval ${tacticTerm.pretty}"
    }

    val tabs = "\t" * tab

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"${tabs}{eval ${tacticTerm.pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpEval(tacticTerm, tab)))
  }

  abstract class lpUserTactic extends lpOlTerm {
    override def prf: lpMlType = throw new Exception(s"Error in LP encoding: Trying to generate proof for user tactic")
  }

  case class lpRewritePattern (pattern: lpTerm, patternVar: lpOlUntypedVar = lpOlUntypedVar(lpConstantTerm("x"))) extends lpTerm {
    override def pretty (implicit prefix : PrettyConfig): String = {
      s".[${patternVar.pretty} in ${pattern.pretty}]"
    }
  }

  case class lpRewrite(rewritePattern0: Option[lpRewritePattern], rewriteTerm: lpTerm, rwRhs: Boolean = false, tab: Int = 0) extends lpProofScriptStep(tab: Int){
    def addTab(i : Int): lpRewrite =lpRewrite(rewritePattern0, rewriteTerm, rwRhs, tab + i)

    val asOlTerm = "#rewrite"

    lazy val olTermApp = {
      rewriteTerm match {
        case t:lpOlTerm =>
          val patternStr = if (rewritePattern0.isDefined) s"\"${rewritePattern0.get}\"" else s"\"\""
          val sideStr = if (rwRhs) s"\"left\"" else s"\"\""
          lpOlFunctionApp(lpOlConstantTerm(asOlTerm),Seq(Left(lpOlConstantTerm(sideStr)), Left(lpOlConstantTerm(patternStr)),Left(t)))
        case _ => throw new Exception(s"LP-Encoding: Trying to apply meta level term ${rewriteTerm.pretty(PrettyConfig(false,false))} to $asOlTerm")
      }
    }

    lazy val olUsrTac : lpProofScriptStep = {
      rewriteTerm match {
        case t: lpOlTerm =>
          val patternStr = if (rewritePattern0.isDefined) s"\"${rewritePattern0.get}\"" else s"\"\""
          val sideStr = if (rwRhs) s"\"left\"" else s"\"\""
          lpUserTacApp(lpConstantTerm(asOlTerm),Seq(lpOlConstantTerm(sideStr), lpOlConstantTerm(patternStr), t))
        case _ => throw new Exception(s"LP-Encoding: Trying to apply meta level term ${rewriteTerm.pretty(PrettyConfig(false, false))} to $asOlTerm")
      }
    }

    override def pretty (implicit prefix : PrettyConfig): String = {
      val tabs: String = "\t" * tab
      val maybeLeft: String = if(rwRhs) " left " else ""
      val rewritePattern = if (rewritePattern0.isDefined) s"${rewritePattern0.get.pretty} " else ""
      s"${tabs}rewrite$maybeLeft $rewritePattern${rewriteTerm.pretty}"
    }

    val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"$tabs{${lpRewrite(rewritePattern0, rewriteTerm, rwRhs).pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpRewrite(rewritePattern0, rewriteTerm, rwRhs, tab)))
  }

  case class lpReflexivity(tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    def addTab(i : Int): lpReflexivity = lpReflexivity(tab + i)
    override def pretty (implicit prefix : PrettyConfig): String = {
      val tabs: String = "\t" * tab
      s"${tabs}reflexivity"
    }

    val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"$tabs{${lpReflexivity()}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpReflexivity(tab)))
  }

  case class lpAssume(vars: Seq[lpTerm], tab: Int = 0) extends lpProofScriptStep(tab: Int){
    def addTab(i : Int): lpAssume = lpAssume(vars, tab + i)

    val asOlTerm = "#assume"

    def olTermApp = {
      lazy val processedVars: Seq[String] = vars.map {
        case lpOlTypedVar(n,t) => n.pretty
        case other => throw new Exception(s"Error in LP encoding: Attempting to instanciate $asOlTerm with ${other}")
      }
      lpOlFunctionApp(lpOlConstantTerm(asOlTerm), Seq(Left(lpOlConstantTerm(s"\"${processedVars.mkString(" ")}\""))))
    }

    val tabs: String = "\t" * tab
    override def pretty (implicit prefix : PrettyConfig): String = {
      s"${tabs}assume ${vars.map(var0 => var0.pretty).mkString(" ")}"
    }

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"$tabs{${lpAssume(vars).pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpAssume(vars, tab)))
  }

  case class lpSetTac(name: String, dfn: lpStatement, tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    def addTab(i: Int): lpSetTac = lpSetTac(name, dfn, tab + i)

    val tabs: String = "\t" * tab

    def pretty0 (implicit prefix : PrettyConfig): String = {
      s"set ${name} ≔ ${dfn.pretty}"
    }

    override def pretty (implicit prefix : PrettyConfig): String = {
      s"${tabs}${lpSetTac(name, dfn, tab).pretty0}"
    }

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"${tabs}{${lpSetTac(name, dfn, tab).pretty0}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpSetTac(name, dfn, tab)))
  }

  case class lpTacSimplify(tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    def addTab(i: Int): lpTacSimplify = lpTacSimplify(tab + i)

    override def pretty (implicit prefix : PrettyConfig): String = {
      val tabs: String = "\t" * tab
      s"${tabs}simplify"
    }

    val tabs = "\t" * tab

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"${tabs}{simplify"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpTacSimplify(tab)))
  }

  case class lpRepeat(stepToRepeat: lpStatement, tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    def addTab(i: Int): lpRepeat = lpRepeat(stepToRepeat, tab + i)

    val asOlTerm = "#repeat"

    lazy val olTermApp = {
      stepToRepeat match {
        case t: lpOlTerm => lpOlFunctionApp(lpOlConstantTerm(asOlTerm), Seq(Left(t)))
        case _ => throw new Exception(s"LP-Encoding: Trying to apply meta level term ${stepToRepeat.pretty(PrettyConfig(false, false))} to $asOlTerm")
      }
    }

    val asUserTac = {
      lpUserTacApp(lpConstantTerm(asOlTerm),Seq(stepToRepeat))
    }
    override def pretty (implicit prefix : PrettyConfig): String = {
      val tabs: String = "\t" * tab
      s"${tabs}repeat ${stepToRepeat.pretty}"
    }

    val tabs = "\t" * tab

    override private[lpDatastructures] def openCurlyBracket (implicit prefix : PrettyConfig): String = s"$tabs{repeat ${stepToRepeat.pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpRepeat(stepToRepeat, tab)))
  }

  case class lpTacBinaryConnectiveTerm(connective: lpTacBinaryConnective, lhs: lpProofScriptStep, rhs: lpProofScriptStep, tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    override def addTab(i: Int): lpTacBinaryConnectiveTerm = lpTacBinaryConnectiveTerm(connective, lhs, rhs, tab + i)

    override def toProofScrips: lpProofScript = throw new Exception(s"Error in LP encoidng: trying to convert instance of ${connective.pretty} to proof script")

    //val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket(implicit prefix: PrettyConfig): String = throw new Exception(s"Error in LP encoidng: trying to convert instance of ${connective.pretty} to proof script")

    override def pretty(implicit prefix: PrettyConfig): String = s"(${lhs.pretty} ${connective.pretty} ${rhs.pretty})"
  }

  case class lpUserTacApp(tacConst: lpStatement, tacs: Seq[lpStatement], tab: Int = 0) extends lpProofScriptStep(tab: Int) {
    override def addTab(i: Int): lpUserTacApp = lpUserTacApp(tacConst, tacs, tab + i)

    override def toProofScrips: lpProofScript = throw new Exception(s"Error in LP encoidng: trying to convert instance of ${tacConst.pretty} to proof script")

    //val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket(implicit prefix: PrettyConfig): String = throw new Exception(s"Error in LP encoidng: trying to convert instance of ${tacConst.pretty} to proof script")

    override def pretty(implicit prefix: PrettyConfig): String = {
      if (tacs.isEmpty) throw new Exception(s"Error in LP Encoidng: no tactics given to constructor ${tacConst.pretty}")
      val prettyArgs = tacs.map(_.pretty)
      s"(${tacConst.pretty} ${prettyArgs.mkString(" ")})"
    }
  }

  abstract class lpTacBinaryConnective extends lpStatement

  final case object lpOrElseTac extends lpTacBinaryConnective {
    override def pretty(implicit prefix: PrettyConfig): String = "#orelse";

    val nonInfix: String = s"($pretty)"
  }


  /*
  case class lpOrElse(termA: lpProofScriptStep, termB: lpProofScriptStep, tab: Int = 0) extends lpTacBinaryConnectiveTerm {
    def addTab(i: Int): lpOrElse = lpOrElse(termA, termB, tab + i)

    val asOlTerm = "#orelse"

    val olTermApp = {
      (termA, termB) match {
        case (tA: lpProofScriptStep, tB: lpProofScriptStep) => lpFunctionApp(lpConstantTerm(lpOrElseTac.nonInfix),Seq(tA,tB))
        case _ => throw new Exception(s"LP-Encoding: Trying to apply meta level terms ${termA.pretty(PrettyConfig(false, false))} and ${termB.pretty(PrettyConfig(false, false))} to $asOlTerm")
      }
    }

    override def pretty(implicit prefix: PrettyConfig): String = {
      throw new Exception(s"Error in LP encoding: trying to use $asOlTerm outside of eval")
    }

    val tabs = "\t" * tab

    override private[lpDatastructures] def openCurlyBracket(implicit prefix: PrettyConfig): String = throw new Exception(s"Error in LP encoding: trying to use $asOlTerm outside of eval")

    override def toProofScrips: lpProofScript = throw new Exception(s"Error in LP encoding: trying to use $asOlTerm outside of eval")
  }

   */

}
