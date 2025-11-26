
package leo.modules.output.LPoutput.NewLpDatastructures

import leo.modules.HOLSignature
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Var
import leo.modules.output.LPoutput.OldLpDatastructures.lpDatastructures.lpProofScriptStep


//////////////////////////////////////////
// CORE-AST
//////////////////////////////////////////

// ** Prelim

sealed trait Level
object Level { sealed trait Meta extends Level; sealed trait Obj extends Meta }

/** Prefix used to qualify names by the Lambdapi files the symbols are declared in */
sealed trait Prefix
object Prefix {
  case object Sig extends Prefix // file containing the signature of the TPTP problem
  case object Formula extends Prefix // file containing all formulae given in the TPTP problem and used in the proof (axioms and definitions)
}

final case class Name(value: String)
/** Name and potential Prefix */
final case class QName(file: Option[Prefix], local: Name)
object QName {
  /** Symbol used only in the file it is declared in -> no prefix */
  def local(n: String): QName = QName(None, Name(n))
  def in(file: Prefix, n: String): QName = QName(Some(file), Name(n))
}

/**
  * Reference to the name of a symbol
  *
  * A SymRef can refer to
  *  - the integer of a symbol of the TPTP signature (Leo)
  *  - a Qname associated with a symbol exclusive to the Lambdapi encoding (LP)
  */
sealed trait SymRef
object SymRef {
  /**
    * Symbol of the underlying HOL signature, or symbol introduced in the TPTP problem
    *
    * @param id the key in the Leo signature
    */
  final case class Leo(id: Int) extends SymRef      // Leo's signature key
  final case class LP(qn: QName) extends SymRef
}

/** Meta logical types in the Lambdapi encoding */
sealed trait LpType
object LpType {
  /** Meta universe */
  case object LpSet extends LpType
  /** encoded HOL Types as ML Types */
  final case class El(ol: OlType) extends LpType
  /** HOL propositions as ML Types */
  final case class Prf(tm: LpTerm[Level.Obj]) extends LpType
  /** Dependant types */
  final case class Pi(binders: Seq[Var[Level.Meta]], body: LpType) extends LpType
  /** ML function types */
  final case class Arrow(dom: LpType, cod: LpType) extends LpType
  /** for compatibility: until fully migrated to new DS, allow stirngs here */
  final case class Old(ty: String) extends LpType
}

/** Object-logic (HOL) types */
sealed trait OlType
object OlType {
  final case class Base(sym: SymRef) extends OlType
  /** Object level function types */
  final case class Fun(args: Seq[OlType]) extends OlType
  /** Type variables */
  final case class TyVar(name: Name) extends OlType
}

/** LpTerms (parametric in Level) */
sealed trait LpTerm[L <: Level]
object LpTerm {
  final case class Var[L <: Level](name: Name, ty: Option[LpType]) extends LpTerm[L]
  final case class Const[L <: Level](sym: SymRef) extends LpTerm[L]
  final case class Lam[L <: Level](binder: (Name, Option[LpType]), body: LpTerm[L]) extends LpTerm[L]
  final case class App[L <: Level](f: LpTerm[L], args: Seq[Arg[L]]) extends LpTerm[L]
  /** Placeholder in Lambdapi */
  final case class Wildcard[L <: Level]() extends LpTerm[L]
  final case class Obj(t: LpTerm[Level.Obj]) extends LpTerm[Level.Meta] // todo: change?
  final case class TptpInt[L <: Level](n: BigInt) extends LpTerm[L]

  final case class TptpRational[L <: Level](n0: BigInt, n1: BigInt) extends LpTerm[L]
  final case class TptpReal[L <: Level](n0: BigInt, n1: BigInt, n2: BigInt) extends LpTerm[L]
}
/** Argument supplied in an application, can either be a term or a type argument and can either be explicit or implicit */
sealed trait Arg[L <: Level]
object Arg {
  final case class Implicit[L <: Level](t: LpTerm[L]) extends Arg[L]
  final case class Explicit[L <: Level](t: LpTerm[L]) extends Arg[L]
  final case class ImplicitTypeArg[L <: Level](ty: OlType) extends Arg[L]
  final case class ExplicitTypeArg[L <: Level](ty: OlType) extends Arg[L]
}

/** Statements in Lambdapi can be Declarations, Definitions or Rewrite Rules */
sealed trait Stmt
object Stmt {
  final case class Declaration(name: Name, params: Seq[(Name, LpType)], result: LpType, implicitParams: Seq[(Name, LpType)] = Nil) extends Stmt
  final case class Definition( name: Name, params: Seq[(Name, LpType)], ty: Option[LpType], body: DefBody, implicitParams: Seq[(Name, LpType)] = Nil, modifiers: Seq[Modifier] = Nil) extends Stmt
  final case class Rule(head: LpTerm[Level.Meta], binders: Seq[Name], rhs: LpTerm[Level.Meta]) extends Stmt // rewrite rules

  /** Definitions can either be declarations and rewrite rule in one, or define an encoded proposition by providing a proof */
  sealed trait DefBody
  object DefBody {
    final case class LpTermBody(t: LpTerm[Level.Meta]) extends DefBody
    final case class ProofBody(proofScript: Seq[LpProofScript]) extends DefBody
  }

  /** Modifiers of the declared/ defined Lambdapi symbols */
  sealed trait Modifier
  case object Opaque extends Modifier
}

/** Lambdapi proof-scripts are (sequences of) applications of the various tactics the system offers*/
sealed trait LpProofScript
object LpProofScript {
  // ** Tactics

  /** Instantiate the proof term */
  final case class Refine(t: LpTerm[Level.Meta], proofScript: Seq[LpProofScript] = Nil) extends LpProofScript
  /** Define a sub-proof */
  final case class Have(name: Name, ty: LpType, proofScript: Seq[Either[LpProofScript,lpProofScriptStep]]) extends LpProofScript // for compatibility: until fully migrated to new DS, allow stirngs here
  /**
    * Use the proof of an equality to replace occurrences of the LHS with the RHS
    * @param pattern Apply (only) at a specified position
    * @param side "left" allows to instead rewrite occurrences of the RHS with the LHS
    * */
  final case class Rewrite(pattern: Option[RewritePattern], rule: LpTerm[Level.Meta], side: Side = Side.Any) extends LpProofScript
  /** Resolve goals of the shape `x=x` */
  case object Reflexivity extends LpProofScript
  /**
    * Exhaustiveley use ß-reduction and rewrite rules to simplify the goal
    * @param unfold Only unfold specific symbols
    * @param onlyBeta Only ß-reduce, do not apply rewrite rules
    * */
  final case class Simplify(unfold: Seq[Name] = Seq.empty, onlyBeta: Boolean = false) extends LpProofScript
  /** Repeat a given tactic until the goal is resolved or does not change anymore */
  final case class Repeat(step: LpProofScript) extends LpProofScript
  /** Evaluate a tactic defined in the term language of Lambdapi */
  final case class Eval(tactic: LpTerm[Level.Meta]) extends LpProofScript
  /** Give up ad assume the current goal as an axiom */
  final case object Admit extends LpProofScript
  /** Instantiate the dependant types/ the arguments of function types of the current goals with variables */
  final case class Assume(MetaVars: Seq[Name]) extends LpProofScript

  // ** Misc
  /** Add a comment in the proof-script */
  final case class Comment(com: String) extends LpProofScript
  // additional Information providable for rewrite tactic
  /** Direction to apply the rewrite tactic */
  sealed trait Side
  object Side { case object Left extends Side; case object Right extends Side; case object Any extends Side }
  final case class RewritePattern(LpTerm: LpTerm[Level.Obj], hole: Name = Name("x"))
}


//////////////////////////////////////////
// SHORTHANDS, CONSTRUCTORS AND EXTRACTORS
//////////////////////////////////////////

// ** Types
/**
  * Access to the pre-defined basetypes in the TPTP
  * - the SymRefs to the keys in the Leo Signature
  * - the encodings as Lambdapi Types
  * */
object HolBaseTypes {
  // ** canonical names for o and i
  private val oTyN: SymRef.Leo = SymRef.Leo(HOLSignature.oKey)
  private val iTyN: SymRef.Leo = SymRef.Leo(HOLSignature.iKey)
  // ** TPTP types for numbers
  val intTyN: SymRef.Leo = SymRef.Leo(HOLSignature.intKey)
  val rationalTyN: SymRef.Leo = SymRef.Leo(HOLSignature.ratKey)
  val realTyN: SymRef.Leo = SymRef.Leo(HOLSignature.realKey)

  // ** encoding as Lambdapi types
  val O: OlType.Base = OlType.Base(oTyN)
  val I: OlType.Base = OlType.Base(iTyN)
  val Int: OlType.Base = OlType.Base(intTyN)
  val Rat: OlType.Base = OlType.Base(rationalTyN)
  val Real: OlType.Base = OlType.Base(realTyN)
}

// ** HOL Constants
/**
  * Access to the pre-defined HOL Constants of the TPTP
  * - the SymRefs to the keys in the Leo Signature
  * - the encodings as Lambdapi OL Terms
  * - Smart constructors + extractors for terms using the connectives
  * */
object LogicConst {
  // ** canonical names for surface symbols
  private val topN = SymRef.Leo(HOLSignature.LitTrue.key)
  private val botN = SymRef.Leo(HOLSignature.LitFalse.key)
  private val notN = SymRef.Leo(HOLSignature.Not.key)
  private val andN = SymRef.Leo(HOLSignature.&.key)
  private val orN  = SymRef.Leo(HOLSignature.|||.key)
  private val impN = SymRef.Leo(HOLSignature.Impl.key)
  private val eqN  = SymRef.Leo(HOLSignature.===.key)
  private val allN = SymRef.Leo(HOLSignature.Forall.key)
  private val exN  = SymRef.Leo(HOLSignature.Exists.key)
  private val chN  = SymRef.Leo(HOLSignature.Choice.key)

  val Top:LpTerm.Const[Level.Obj] = LpTerm.Const[Level.Obj](topN)
  val Bot:LpTerm.Const[Level.Obj] = LpTerm.Const[Level.Obj](botN)
  val cNot:LpTerm.Const[Level.Obj] = LpTerm.Const[Level.Obj](notN)
  val cAnd:LpTerm.Const[Level.Obj] = LpTerm.Const[Level.Obj](andN)
  val cOr:LpTerm.Const[Level.Obj]  = LpTerm.Const[Level.Obj](orN)
  val cImp:LpTerm.Const[Level.Obj] = LpTerm.Const[Level.Obj](impN)
  val cEq:LpTerm.Const[Level.Obj]  = LpTerm.Const[Level.Obj](eqN)
  val cAll:LpTerm.Const[Level.Obj] = LpTerm.Const[Level.Obj](allN)
  val cEx:LpTerm.Const[Level.Obj]  = LpTerm.Const[Level.Obj](exN)
  val cCh:LpTerm.Const[Level.Obj]  = LpTerm.Const[Level.Obj](chN)

  private def E(t: LpTerm[Level.Obj]) = Arg.Explicit(t)

  // ** Smart constructors + extractors

  /** Negation */
  object Not {
    private val head = cNot
    def apply(t: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(E(t)))

    def unapply(t: LpTerm[Level.Obj]): Option[LpTerm[Level.Obj]] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(x))) => Some(x)
      case _ => None
    }
  }

  /** Conjunction */
  object And {
    private val head = cAnd
    def apply(l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(l), Arg.Explicit(r))) => Some((l,r))
      case _ => None
    }
  }

  /** Disjunction */
  object Or {
    private val head = cOr
    def apply(l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(l), Arg.Explicit(r))) => Some((l,r))
      case _ => None
    }
  }

  /** Implication */
  object Imp {
    private val head = cImp
    def apply(l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(l), Arg.Explicit(r))) => Some((l,r))
      case _ => None
    }
  }

  /** Equality */
  object Eq {
    private val head = cEq
    def apply(ty: OlType, l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(Arg.ExplicitTypeArg(ty), E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(OlType, LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, List(Arg.ExplicitTypeArg(t), Arg.Explicit(l), Arg.Explicit(r))) => Some((t,l,r))
      case _ => None
    }
  }

  /** Universal quantification */
  object Forall {
    private val head = cAll
    def apply(binder: (Name, LpType), body: LpTerm[Level.Obj]): LpTerm[Level.Obj] = {
      val (n, bTy) = binder
      LpTerm.App(head, Seq(E(LpTerm.Lam(n -> Some(bTy), body))))
    }

    def unapply(t: LpTerm[Level.Obj]): Option[((Name, LpType), LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(LpTerm.Lam(bs, body)))) =>
        val (n, Some(bty)) = bs
        val typed = (n, bty)
        Some((typed, body))
      case _ => None
    }
  }

  /** Existential quantification */
  object Exists {
    private val head = cEx
    def apply(binder: (Name, LpType), body: LpTerm[Level.Obj]): LpTerm[Level.Obj] = {
      val (n, bTy) = binder
      LpTerm.App(head, Seq(E(LpTerm.Lam(n -> Some(bTy), body))))
    }

    def unapply(t: LpTerm[Level.Obj]): Option[((Name, LpType), LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(LpTerm.Lam(bs, body)))) =>
        val (n, Some(bty)) = bs
        val typed = (n, bty)
        Some((typed, body))
      case _ => None
    }
  }

  /** Choice instances */
  object Choice {
    private val head = cCh

    def apply(binder: (Name, LpType), body: LpTerm[Level.Obj]): LpTerm[Level.Obj] = {
      val (n, bTy) = binder
      LpTerm.App(head, Seq(E(LpTerm.Lam(n -> Some(bTy), body))))
    }

    def unapply(t: LpTerm[Level.Obj]): Option[((Name, LpType), LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(LpTerm.Lam(bs, body)))) =>
        val (n, Some(bty)) = bs
        val typed = (n, bty)
        Some((typed, body))
      case _ => None
    }
  }

  // ** TPTP connectives abstracted away in the translation
  // todo: either handle other connectives like this too or abstract away ineq during encoding process
  /** Inequality */
  object InEq {
    private val inEqN = SymRef.Leo(HOLSignature.!===.key)
    private val cInEq = LpTerm.Const[Level.Obj](inEqN)
    private val head = cInEq

    def apply(ty: OlType, l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(Arg.ExplicitTypeArg(ty), E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(OlType, LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, List(Arg.ExplicitTypeArg(t), Arg.Explicit(l), Arg.Explicit(r))) => Some((t, l, r))
      case _ => None
    }
  }
}

