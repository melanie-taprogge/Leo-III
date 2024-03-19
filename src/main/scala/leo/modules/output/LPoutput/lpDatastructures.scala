package leo.modules.output.LPoutput

object lpDatastructures {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// KINDS OF STATEMENTS ///////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class lpStatement{
    def pretty: String
  }

  case class lpDeclaration(name: lpConstantTerm, typing: lpMlType) extends lpStatement{
    override def pretty: String = s"symbol ${name.pretty}: ${typing.pretty};\n"
  }

  case class lpDefinition(name: lpConstantTerm, typing: lpMlType, lambdaTerm: lpTerm) extends lpStatement {
    override def pretty: String = s"symbol ${name.pretty}: ${typing.pretty} ≔\n${lambdaTerm.pretty};"
  }

  case class lpRule(symbol: lpTerm, variableIdentifier: Seq[lpRuleVariable], lambdaTerm: lpTerm) extends lpStatement {
    override def pretty: String = s"rule ${symbol.pretty} ${variableIdentifier.map(var0 => var0.pretty).mkString(" ")} ↪ ${lambdaTerm.pretty};"
  }
  


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// LP META LOGIC /////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  abstract class lpTerm {
    def pretty: String
  }

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

  ////////////////////////// META LOGIC TYPES

  abstract class lpMlType extends lpTerm {
    def pretty: String
  }

  case object lpMetaType extends lpMlType {
    override def pretty: String = "TYPE"
  }

  case class lpMlDependType(vars: Seq[lpTypedVar], body: lpMlType) extends lpMlType {
    override def pretty: String = {
      s"(${lpPi.pretty} ${vars.map(name_ty => s"(${name_ty.pretty} : ${name_ty.ty.pretty})").mkString(s", ${lpPi.pretty}")}, ${body.pretty})"
    }
  }

  case class lpMlFunctionType(objects :Seq[lpMlType]) extends lpMlType {
    override def pretty: String = {
      objects.map(ty => ty.pretty).mkString(s" ${lpArrow.pretty} ")
    }
  }

  ////////////////////////// META LOGIC TERMS
  case class lpTypedVar(name: lpConstantTerm, ty: lpMlType) extends lpTerm {
    override def pretty: String = name.pretty
  }

  case class lpConstantTerm(name: String) extends lpTerm {
    override def pretty: String = name
  }

  case class lpLambdaTerm(vars: Seq[lpTypedVar], body: lpTerm) extends lpTerm {
    override def pretty: String = {
      s"(${lpLambda.pretty} ${vars.map(name_ty => s"(${name_ty.pretty} : ${name_ty.ty.pretty})").mkString(" ")}, ${body.pretty})"
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// OBJECT LOGIC //////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  ////////////////////////// OBJECT LOGIC TYPES

  ///////////// CONSTANTS
  abstract class lpOlTypeConstants extends lpConstants
  case object lpOlTypeConstructor extends lpOlTypeConstants {override def pretty: String = "⤳"}
  case object lpSet extends lpOlTypeConstants {override def pretty: String = "Set"}
  case object lpScheme extends lpOlTypeConstants {override def pretty: String = "Scheme"}
  case object lpPrf extends lpOlTypeConstants {override def pretty: String = "Prf"}
  case object lpSet2Schme extends lpOlTypeConstants {override def pretty: String = "↑"}
  case object lpEl extends lpMlType {override def pretty: String = "El"}
  case object lpEls extends lpMlType {override def pretty: String = "Els"}


  ///////////// TYPES
  //todo: Polymorphy
  abstract class lpOlType extends lpTerm {
    def lift2Meta: lpMlType
  }
  abstract class lpOlPolyType extends lpOlType
  abstract class lpOlMonoType extends lpOlType {
    def lift2Poly: lpOlPolyType
  }

  case class lpliftedObjectType(ty: lpOlType) extends lpMlType {
    def pretty: String = {
      ty match {
        case lpOlMonoType => s"(${lpEl.pretty} ${ty.pretty})"
        case lpOlPolyType => s"(${lpEls.pretty} ${ty.pretty})"
        case _ => throw new Exception(s"failed to print lpliftedObjectType, $ty has wrong format")
      }
    }
  }
  case class lpliftedMonoType(ty: lpOlMonoType) extends lpOlPolyType {
    def pretty: String = {
      s"(${lpSet2Schme.pretty} ${ty.pretty})"
    }
    override def lift2Meta: lpMlType = {
      lpliftedObjectType(lpliftedMonoType(ty))
    }
  }

  abstract class lpOlSimpleType extends lpOlMonoType
  case class lpOlUserDefinedType(t: String) extends lpOlSimpleType{
    def pretty: String = t
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType(t))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlUserDefinedType(t))
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
  case class lpOlFunctionType(args: Seq[lpOlMonoType]) extends lpOlMonoType {
    def pretty: String = s"(${args.map(t => t.pretty).mkString(s" ${lpOlTypeConstructor.pretty} ")})"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlFunctionType(args))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlFunctionType(args))
  }


  ////////////////////////// OBJECT LOGIC TERMS

  ///////////// CONNECTIVES
  abstract class lpOlConnective {
    def pretty: String
  }

  abstract class lpOlUnaryConnective extends lpOlConnective
  final case object lpNot extends lpOlUnaryConnective {override def pretty: String = "¬"}

  abstract class lpOlBinaryConnective extends lpOlConnective
  final case object lpOr extends lpOlBinaryConnective {override def pretty: String = "∨"}
  final case object lpAnd extends lpOlBinaryConnective {override def pretty: String = "∧"}
  final case object lpImp extends lpOlBinaryConnective {override def pretty: String = "⇒"}
  final case object lpEq extends lpOlBinaryConnective {override def pretty: String = "eq"}
  final case object lpInEq extends lpOlBinaryConnective {override def pretty: String = "inEq"}

  abstract class lpOlQuantifier extends lpOlConnective
  final case object lpExists extends lpOlQuantifier {override def pretty: String = "∃"}
  final case object lpOlForAll extends lpOlQuantifier {override def pretty: String = "∀"}

  abstract class lpOlTerm extends lpTerm{
    def prf: lpMlType
  }

  case class liftedProp(t: lpOlTerm) extends lpMlType {
    override def pretty: String = s"(${lpPrf.pretty} ${t.pretty})"
  }
  case object lpOlTop extends lpOlTerm {
    override def pretty: String = "⊤"

    override def prf: liftedProp = liftedProp(lpOlTop)
  }
  case object lpOlBot extends lpOlTerm {
    override def pretty: String = "⊥"
    override def prf: liftedProp = liftedProp(lpOlBot)
  }
  case class lpOlConstantTerm(a : String) extends lpOlTerm{
    override def pretty: String = a
    override def prf: liftedProp = liftedProp(lpOlConstantTerm(a))
  }

  case class lpRuleVariable(v: lpOlConstantTerm) extends lpOlTerm {
    override def pretty: String = s"($$$v)"
    override def prf: liftedProp = liftedProp(lpRuleVariable(v))
  }
  case class lpOlTypedVar(name: lpOlConstantTerm,ty: lpOlType) extends lpOlTerm {
    override def pretty: String = name.pretty
    def lift2Meta: lpTypedVar = lpTypedVar(lpConstantTerm(name.pretty),ty.lift2Meta)
    override def prf: liftedProp = liftedProp(lpOlTypedVar(name,ty))
  }
  case class lpOlFunctionTerm(f: lpOlConstantTerm, args: Seq[lpOlTerm]) extends lpOlTerm{
    override def pretty: String = {
      if (args.isEmpty) f.pretty else s"($f ${args.map(_.pretty).mkString(" ")})"
    }
    override def prf: liftedProp = liftedProp(lpOlFunctionTerm(f, args))
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
  case class lpOlTypedBinaryConnectiveTerm(connective: lpOlBinaryConnective, ty: lpOlType, lhs: lpOlTerm, rhs: lpOlTerm) extends lpOlConnectiveTerm {
    override def pretty: String = {
      val encodedType = ty match{
        case lpOlMonoType => s"${lpSet2Schme.pretty} ${ty.pretty}"
        case _ => throw new Exception(s"failed to print lpTypedBinaryConnectiveTerm($connective,$ty,$lhs,$rhs), $ty has wrong format")
      }
      s"(${connective.pretty} [$encodedType] ${lhs.pretty} ${rhs.pretty})"
    }
    override def prf: liftedProp = liftedProp(lpOlTypedBinaryConnectiveTerm(connective, ty, lhs, rhs))
  }

  case class lpOlMonoQuantifiedTerm(quantifier: lpOlQuantifier, variables: Seq[lpOlTypedVar], body: lpOlTerm) extends lpOlTerm {
    override def pretty: String = {
      s"(${quantifier.pretty}${lpLambdaTerm(variables.map(var0 => lpTypedVar(var0.lift2Meta.name,var0.lift2Meta.ty)),body).pretty})"
    }
    override def prf: liftedProp = liftedProp(lpOlMonoQuantifiedTerm(quantifier, variables, body))
  }



  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// TEST TEST TEST  ///////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def main(args: Array[String]):Unit = {
    print(s"${lpOlFunctionTerm(lpOlConstantTerm("test"), Seq.empty).pretty}\n")
    print(s"${lpOlFunctionType(Seq(lpOtype,lpItype,lpOlUserDefinedType("h"))).pretty}\n")
    print(s"${lpOlMonoQuantifiedTerm(lpOlForAll, Seq(lpOlTypedVar(lpOlConstantTerm("a"), lpOtype), lpOlTypedVar(lpOlConstantTerm("b"), lpItype)), lpOlBot).pretty}\n")
    print(s"${lpLambdaTerm(Seq(lpTypedVar(lpConstantTerm("a"),lpliftedObjectType(lpOtype)),lpTypedVar(lpConstantTerm("b"),lpliftedObjectType(lpItype))),lpOlBot).pretty}\n")
  }

}
