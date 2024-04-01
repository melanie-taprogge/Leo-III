package leo.modules.output.LPoutput

object lpDatastructures {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// KINDS OF STATEMENTS ///////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val reducedLogic = true

  abstract class lpStatement{
    def pretty: String
  }

  abstract class lpDefinedRules extends lpStatement{

    def name: String
    def ty: lpMlType

    def proof: lpProofScript

    def dec: lpDeclaration

  }

  case class lpDeclaration(name: lpConstantTerm, variables: Seq[lpVariable], typing: lpType) extends lpStatement{
    override def pretty: String = {
      if (variables.isEmpty){
        s"symbol ${name.pretty}: ${typing.pretty};\n"
      } else {
        s"symbol ${name.pretty} ${variables.map(var0 => var0.pretty).mkString(" ")}: ${typing.pretty};\n"
      }
    }
  }

  case class lpDefinition(name: lpConstantTerm, variables: Seq[lpVariable], typing: lpMlType, proof: lpStatement) extends lpStatement {
    override def pretty: String = {

      val proofEnc = proof match {
        case _ : lpTerm =>
          s"${proof.pretty}"
        case proofScript : lpProofScript =>
          s"begin\n${proofScript.addTab(1).pretty}\nend"
      }

      if (!variables.isEmpty){
        s"symbol ${name.pretty} ${variables.map(var0 => var0.pretty).mkString(" ")}: ${typing.pretty} ≔\n${proofEnc};\n"
      }else{
      s"symbol ${name.pretty}: ${typing.pretty} ≔\n${proofEnc};"
    }
    }
  }

  case class lpRule(symbol: lpTerm, variableIdentifier: Seq[lpVariable], lambdaTerm: lpTerm) extends lpStatement {
    override def pretty: String = s"rule ${symbol.pretty} ${variableIdentifier.map(var0 => var0.pretty).mkString(" ")} ↪ ${lambdaTerm.pretty};\n"
  }
  


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// LP META LOGIC /////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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
  case object lpWildcard extends lpTerm{
    override def pretty: String = "_"
  }

  ////////////////////////// META LOGIC TYPES

  abstract class lpType extends lpTerm{
    def lift2Meta: lpMlType
  }
  abstract class lpMlType extends lpType {
    def pretty: String
  }

  case object lpMetaType extends lpMlType {
    override def pretty: String = "TYPE"

    //change nothing when lifting to meta type
    override def lift2Meta: lpMlType = lpMetaType
  }

  case class lpMlDependType(vars: Seq[lpVariable], body: lpMlType) extends lpMlType {
    override def pretty: String = {
      s"(${lpPi.pretty} ${vars.map(var0 => var0.pretty).mkString(s", ${lpPi.pretty}")}, ${body.pretty})"
    }
    //change nothing when lifting to meta type
    override def lift2Meta: lpMlType = lpMlDependType(vars, body)
  }

  case class lpMlFunctionType(objects :Seq[lpMlType]) extends lpMlType {
    override def pretty: String = {
      objects.map(ty => ty.pretty).mkString(s" ${lpArrow.pretty} ")
    }

    //change nothing when lifting to meta type
    override def lift2Meta: lpMlType = lpMlFunctionType(objects)
  }

  ////////////////////////// META LOGIC TERMS
  abstract class lpVariable extends lpTerm
  case class lpTypedVar(name: lpTerm, ty: lpType) extends lpVariable {
    override def pretty: String = s"(${name.pretty} : ${ty.lift2Meta.pretty})"

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
        s"(${lpLambda.pretty} ${vars.map(var0 => var0.pretty).mkString(" ")}, ${body.pretty})"
      }
      }
  }

  case class lpFunctionApp(f: lpTerm, args: Seq[lpTerm]) extends lpTerm {
    override def pretty: String = {
      if (args.isEmpty) f.pretty else s"(${f.pretty} ${args.map(_.pretty).mkString(" ")})"
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// OBJECT LOGIC //////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  ////////////////////////// OBJECT LOGIC TYPES

  ///////////// CONSTANTS
  abstract class lpOlTypeConstants extends lpType
  case object lpOlTypeConstructor extends lpOlTypeConstants {
    override def pretty: String = "⤳"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpOlTypeConstructor.pretty} to meta level")
  }
  case object lpSet extends lpOlTypeConstants {
    override def pretty: String = "Set"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpSet.pretty} to meta level")
  }
  case object lpScheme extends lpOlTypeConstants {
    override def pretty: String = "Scheme"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpScheme.pretty} to meta level")
  }
  case object lpPrf extends lpOlTypeConstants {
    override def pretty: String = "Prf"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpPrf.pretty} to meta level")
  }
  case object lpSet2Schme extends lpOlTypeConstants {
    override def pretty: String = "↑"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpScheme.pretty} to meta level")
  }
  case object lpEl extends lpMlType {
    override def pretty: String = "El"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpEl.pretty} to meta level")
  }
  case object lpEls extends lpMlType {
    override def pretty: String = "Els"
    override def lift2Meta: lpMlType = throw new Exception(s"attempting to lift ${lpEls.pretty} to meta level")
  }


  ///////////// TYPES
  //todo: Polymorphy
  abstract class lpOlType extends lpType {
    def lift2Poly: lpOlPolyType
  }
  abstract class lpOlPolyType extends lpOlType
  abstract class lpOlMonoType extends lpOlType

  case class lpliftedObjectType(ty: lpOlType) extends lpMlType {
    def pretty: String = {
      ty match {
        case lpOlMonoType => s"(${lpEl.pretty} ${ty.pretty})"
        case lpOlPolyType => s"(${lpEls.pretty} ${ty.pretty})"
        case _ => throw new Exception(s"failed to print lpliftedObjectType, $ty has wrong format")
      }
    }
    // change nothing when encoding as meta type
    override def lift2Meta: lpMlType = lpliftedObjectType(ty)
  }
  case class lpliftedMonoType(ty: lpOlMonoType) extends lpOlPolyType {
    def pretty: String = {
      s"(${lpSet2Schme.pretty} ${ty.pretty})"
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

    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlUserDefinedType(t))

    override def lift2Poly: lpOlPolyType = lpOlUserDefinedPolyType(t)
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
    "$i" -> lpItype)

  case class lpOlFunctionType(args: Seq[lpOlType]) extends lpOlMonoType {
    def pretty: String = s"(${args.map(t => t.pretty).mkString(s" ${lpOlTypeConstructor.pretty} ")})"
    override def lift2Meta: lpMlType = lpliftedObjectType(lpOlFunctionType(args))
    override def lift2Poly: lpOlPolyType = lpliftedMonoType(lpOlFunctionType(args))
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
    override def pretty: String = if (reducedLogic) "=" else "eq"
    def definitionName(): lpConstantTerm = {
      if (reducedLogic) (lpConstantTerm(s"=def"))

      else throw new Exception(s"trying to use =def in non-reduced logic")
    }
  }
  final case object lpInEq extends lpOlBinaryConnective {override def pretty: String = "inEq"}

  abstract class lpOlQuantifier extends lpOlConnective
  final case object lpOlExists extends lpOlQuantifier {override def pretty: String = "∃"}
  final case object lpOlForAll extends lpOlQuantifier {override def pretty: String = "∀"}


  abstract class lpOlTerm extends lpTerm{
    def prf: lpMlType
  }

  case class liftedProp(t: lpOlTerm) extends lpMlType {
    override def pretty: String = s"(${lpPrf.pretty} ${t.pretty})"

    // change nothing when encoding as meta type
    override def lift2Meta: lpMlType = liftedProp(t)
  }

  case object lpOlWildcard extends lpOlTerm {
    override def pretty: String = "_"

    override def prf: liftedProp = liftedProp(lpOlWildcard)
  }
  case object lpOlTop extends lpOlTerm {
    override def pretty: String = "⊤"
    override def prf: liftedProp = liftedProp(lpOlTop)
  }
  case object lpOlBot extends lpOlTerm {
    override def pretty: String = "⊥"
    override def prf: liftedProp = liftedProp(lpOlBot)
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


  case class lpRuleVariable(v: lpOlConstantTerm) extends lpVariable {
    override def pretty: String = s"(${v.pretty})"
  }

  case class lpOlTypedVar(name: lpOlConstantTerm,ty: lpOlType) extends lpOlTerm {
    override def pretty: String = name.pretty
    def lift2Meta: lpTypedVar = lpTypedVar(lpConstantTerm(name.pretty),ty.lift2Meta)
    override def prf: liftedProp = liftedProp(lpOlTypedVar(name,ty))
  }

  case class lpOlUntypedVar(name: lpTerm) extends lpOlTerm {
    override def pretty: String = name.pretty

    def lift2Meta: lpUntypedVar = lpUntypedVar(lpConstantTerm(name.pretty))

    override def prf: liftedProp = liftedProp(lpOlUntypedVar(name))
  }
  case class lpOlLambdaTerm(vars: Seq[lpOlTypedVar], body: lpOlTerm) extends lpOlTerm {
    override def pretty: String = {
      s"(${lpLambda.pretty} ${vars.map(name_ty => s"(${name_ty.pretty} : ${name_ty.ty.lift2Meta.pretty})").mkString(" ")}, ${body.pretty})"
    }
    override def prf: liftedProp = liftedProp(lpOlLambdaTerm(vars, body))
  }
  case class lpOlFunctionApp(f: lpOlTerm, args: Seq[lpTerm]) extends lpOlTerm{
    override def pretty: String = {
      if (args.isEmpty) f.pretty else s"(${f.pretty} ${args.map(_.pretty).mkString(" ")})"
    }
    override def prf: liftedProp = liftedProp(lpOlFunctionApp(f, args))
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
    override def pretty: String = s"(${args.map(arg => arg.pretty).mkString(s" ${connective.pretty} ")})"
    override def prf: liftedProp = liftedProp(lpOlUntypedBinaryConnectiveTerm_multi(connective, args))
  }
  case class lpOlTypedBinaryConnectiveTerm(connective: lpOlBinaryConnective, ty: lpOlType, lhs: lpOlTerm, rhs: lpOlTerm) extends lpOlConnectiveTerm {
    override def pretty: String = {
      if (reducedLogic) {
        if (connective == lpInEq) lpOlUnaryConnectiveTerm(lpNot,lpOlTypedBinaryConnectiveTerm(lpEq,ty, lhs, rhs)).pretty
        else s"( ${connective.pretty} ${lhs.pretty} ${rhs.pretty})"
      }
      else {
        val encodedType = ty match {
          case lpOlMonoType => s"${ty.lift2Poly.pretty}"
          case _ => throw new Exception(s"failed to print lpTypedBinaryConnectiveTerm($connective,$ty,$lhs,$rhs), $ty has wrong format")
        }
        s"(${connective.pretty} [$encodedType] ${lhs.pretty} ${rhs.pretty})"
      }
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

    override private[lpDatastructures] def openCurlyBracket: String = s"{${steps.head.addTab(tab).openCurlyBracket};\n${steps.tail.map(step => s"${step.addTab(tab).pretty}").mkString(";\n")}"

    def prettyCurlyBrackets: String = {
      if (steps.length == 1) s"${steps.head.addTab(tab).openCurlyBracket}}"
      else s"${steps.head.addTab(tab).openCurlyBracket};\n${steps.tail.map(step => s"${step.addTab(tab).pretty}").mkString(";\n")}}"
    }

    override def toProofScrips: lpProofScript = lpProofScript(steps, tab)

  }

  case class lpRefine(t: lpFunctionApp, tab: Int = 0) extends lpProofScriptStep(tab: Int){
    def addTab(i : Int): lpRefine = lpRefine(t, tab + i)
    override def pretty: String = {
      val tabs = "\t"*tab
      s"${tabs}refine ${t.pretty}"
    }

    val tabs = "\t" * tab
    override private[lpDatastructures] def openCurlyBracket: String = s"$tabs{${lpRefine(t).pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpRefine(t, tab)))

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

  case class lpAssume(vars: Seq[lpUntypedVar], tab: Int = 0) extends lpProofScriptStep(tab: Int){
    def addTab(i : Int): lpAssume = lpAssume(vars, tab + i)

    val tabs: String = "\t" * tab
    override def pretty: String = {
      s"${tabs}assume ${vars.map(var0 => var0.pretty).mkString(" ")}"
    }

    override private[lpDatastructures] def openCurlyBracket: String = s"$tabs{${lpAssume(vars).pretty}"

    override def toProofScrips: lpProofScript = lpProofScript(Seq(lpAssume(vars, tab)))
  }





  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  ////////////////////////// TEST TEST TEST  ///////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def main(args: Array[String]):Unit = {
    print(s"${lpOlFunctionApp(lpOlConstantTerm("test"), Seq.empty).pretty}\n")
    print(s"${lpOlFunctionType(Seq(lpOtype,lpItype,lpOlUserDefinedType("h"))).pretty}\n")
    print(s"${lpOlMonoQuantifiedTerm(lpOlForAll, Seq(lpOlTypedVar(lpOlConstantTerm("a"), lpOtype), lpOlTypedVar(lpOlConstantTerm("b"), lpItype)), lpOlBot).pretty}\n")
    print(s"${lpLambdaTerm(Seq(lpTypedVar(lpConstantTerm("a"),lpliftedObjectType(lpOtype)),lpTypedVar(lpConstantTerm("b"),lpliftedObjectType(lpItype))),lpOlBot).pretty}\n")

    print(s"${lpOlUntypedBinaryConnectiveTerm_multi(lpOr,Seq(lpOlConstantTerm("a"),lpOlConstantTerm("a"),lpOlConstantTerm("a"))).pretty}")
  }

}
