
package leo.modules.output.LPoutput.NewLpDatastructures

import leo.modules.HOLSignature
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Var


// ── Levels prevent object/meta mixing ──────────────────────────────────────────
sealed trait Level
object Level { sealed trait Obj extends Level; sealed trait Meta extends Level }

// ── Names ─────────────────────────────────────────────────────────────────────
final case class Name(value: String) //todo: add checks for safetey of names, rename if necessary
final case class Prefix(name: Name) // if you later want namespaces/prefixes

final case class QName(file: Option[Prefix], local: Name)

object QName {
  def local(n: String): QName = QName(None, Name(n))
  def in(file: Prefix, n: String): QName = QName(Some(file), Name(n))
}

sealed trait SymRef
object SymRef {
  final case class Leo(id: Int) extends SymRef      // Leo's signature key
  final case class LP(qn: QName) extends SymRef
}

// ── Types (LP meta level + encoded HOL types) ─────────────────────────────────
sealed trait LpType
object LpType {
  case object LpSet extends LpType                    // meta universe
  final case class El(ol: OlType) extends LpType    // ⟦OL type⟧ at meta level
  final case class Prf(tm: LpTerm[Level.Obj]) extends LpType
  final case class Pi(binders: Seq[Var[Level.Meta]], body: LpType) extends LpType
  final case class Arrow(dom: LpType, cod: LpType) extends LpType
}

// ── Object-logic (HOL) types only ─────────────────────────────────────────────
sealed trait OlType
object OlType {
  final case class Base(sym: SymRef) extends OlType
  final case class Fun(args: Seq[OlType]) extends OlType  // right-assoc arrow
  final case class TyVar(name: Name) extends OlType        // type variable
}

// ── LpTerms (parametric in Level) ───────────────────────────────────────────────
sealed trait LpTerm[L <: Level]
object LpTerm {
  final case class Var[L <: Level](name: Name, ty: Option[LpType]) extends LpTerm[L]
  final case class Const[L <: Level](sym: SymRef) extends LpTerm[L]
  final case class Lam[L <: Level](binder: (Name, Option[LpType]), body: LpTerm[L]) extends LpTerm[L]
  final case class App[L <: Level](f: LpTerm[L], args: Seq[Arg[L]]) extends LpTerm[L]
}
sealed trait Arg[L <: Level]
object Arg {
  final case class Implicit[L <: Level](t: LpTerm[L]) extends Arg[L]
  final case class Explicit[L <: Level](t: LpTerm[L]) extends Arg[L]

  final case class ImplicitTypeArg(ty: OlType) extends Arg[Level.Obj]
  final case class ExplicitTypeArg(ty: OlType) extends Arg[Level.Obj]
}

// ── Statements ────────────────────────────────────────────────────────────────
sealed trait Stmt
object Stmt {
  final case class Declaration(name: Name, params: Seq[(Name, LpType)], result: LpType, implicitParams: Seq[(Name, LpType)] = Nil) extends Stmt
  final case class Definition(
                               name: Name,
                               params: Seq[(Name, LpType)],
                               ty: Option[LpType],
                               body: DefBody,
                               implicitParams: Seq[(Name, LpType)] = Nil,
                               modifiers: Seq[Modifier] = Nil
                             ) extends Stmt
  final case class Rule(head: LpTerm[Level.Obj], binders: Seq[Name], rhs: LpTerm[Level.Obj]) extends Stmt

  sealed trait DefBody
  object DefBody {
    final case class LpTermBody(t: LpTerm[Level.Obj]) extends DefBody
    final case class ProofBody(p: Proof) extends DefBody
  }

  sealed trait Modifier
  case object Opaque extends Modifier
}

// ── Proof scripts DSL (no side effects, no raw Stringly) ─────────────────────
sealed trait Proof
object Proof {
  final case class Refine(t: LpTerm[Level.Meta], sub: Seq[Proof] = Nil) extends Proof
  final case class Have(name: Name, ty: LpType, proof: Proof) extends Proof
  final case class Rewrite(pattern: Option[RewritePattern], rule: LpTerm[Level.Meta], side: Side = Side.Any) extends Proof
  case object Reflexivity extends Proof
  final case class Simplify(unfold: Seq[Name]) extends Proof
  final case class Repeat(step: Proof) extends Proof
  final case class Eval(tactic: LpTerm[Level.Meta]) extends Proof

  sealed trait Side
  object Side { case object Left extends Side; case object Right extends Side; case object Any extends Side }

  final case class RewritePattern(LpTerm: LpTerm[Level.Meta], hole: Name = Name("x"))
}

object HolBaseTypes {
  // canonical names for o and i
  val oTyN = SymRef.Leo(HOLSignature.oKey)
  val iTyN = SymRef.Leo(HOLSignature.iKey)

  val O = OlType.Base(oTyN)
  val I = OlType.Base(iTyN)
}

object LogicConst {
  // canonical names for surface symbols
  val topN = SymRef.Leo(HOLSignature.LitTrue.key)
  val botN = SymRef.Leo(HOLSignature.LitFalse.key)
  val notN = SymRef.Leo(HOLSignature.Not.key)
  val andN = SymRef.Leo(HOLSignature.&.key)
  val orN  = SymRef.Leo(HOLSignature.|||.key)
  val impN = SymRef.Leo(HOLSignature.Impl.key)
  val eqN  = SymRef.Leo(HOLSignature.===.key)
  val allN = SymRef.Leo(HOLSignature.Forall.key)
  val exN  = SymRef.Leo(HOLSignature.Exists.key)
  val chN  = SymRef.Leo(HOLSignature.Choice.key)

  val Top = LpTerm.Const[Level.Obj](topN)
  val Bot = LpTerm.Const[Level.Obj](botN)
  val cNot = LpTerm.Const[Level.Obj](notN)
  val cAnd = LpTerm.Const[Level.Obj](andN)
  val cOr  = LpTerm.Const[Level.Obj](orN)
  val cImp = LpTerm.Const[Level.Obj](impN)
  val cEq  = LpTerm.Const[Level.Obj](eqN)
  val cAll = LpTerm.Const[Level.Obj](allN)
  val cEx  = LpTerm.Const[Level.Obj](exN)
  val cCh  = LpTerm.Const[Level.Obj](chN)

  private def E(t: LpTerm[Level.Obj]) = Arg.Explicit(t)

  // ---- Smart constructors + extractors (one object each!) -------------------
  object Not {
    val head = cNot
    def apply(t: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(E(t)))

    def unapply(t: LpTerm[Level.Obj]): Option[LpTerm[Level.Obj]] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(x))) => Some(x)
      case _ => None
    }
  }

  object And {
    val head = cAnd
    def apply(l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(l), Arg.Explicit(r))) => Some((l,r))
      case _ => None
    }
  }

  object Or {
    val head = cOr
    def apply(l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(l), Arg.Explicit(r))) => Some((l,r))
      case _ => None
    }
  }

  object Imp {
    val head = cImp
    def apply(l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, Seq(Arg.Explicit(l), Arg.Explicit(r))) => Some((l,r))
      case _ => None
    }
  }

  object Eq {
    val head = cEq
    def apply(ty: OlType, l: LpTerm[Level.Obj], r: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
      LpTerm.App(head, Seq(Arg.ExplicitTypeArg(ty), E(l), E(r)))

    def unapply(t: LpTerm[Level.Obj]): Option[(OlType, LpTerm[Level.Obj], LpTerm[Level.Obj])] = t match {
      case LpTerm.App(`head`, List(Arg.ExplicitTypeArg(t), Arg.Explicit(l), Arg.Explicit(r))) => Some((t,l,r))
      case _ => None
    }
  }

  object Forall {
    val head = cAll
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

  object Exists {
    val head = cEx
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

  object Choice {
    val head = cCh

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

  // Optional: flatteners for nicer n-ary handling
  def flattenAnd(t: LpTerm[Level.Obj]): Seq[LpTerm[Level.Obj]] = t match {
    case And(l, r) => flattenAnd(l) ++ flattenAnd(r)
    case x         => Seq(x)
  }
  def flattenOr(t: LpTerm[Level.Obj]): Seq[LpTerm[Level.Obj]] = t match {
    case Or(l, r) => flattenOr(l) ++ flattenOr(r)
    case x        => Seq(x)
  }
}

