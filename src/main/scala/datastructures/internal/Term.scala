package datastructures.internal

import datastructures.Pretty
import scala.language.implicitConversions

/**
 * Abstract interface for generation of various terms that can be
 * displayed in the internal language.
 * Terms are generated by
 *
 * {{{s,t ::= c (Atom)
 *       | \c.t (term abstraction)
 *       | s t (term application)
 *       | /\a.t (type abstraction)
 *       | s tau (type application)}}}
 *
 * where `c` is some symbol (constant) and `tau` is a type (see `HOLType`).
 *
 * @author Alexander Steen
 * @since 21.05.2014
 */
abstract sealed class Term extends Pretty {
  // Predicates on terms
  val isAtom: Boolean
  val isTermApp: Boolean
  val isTermAbs: Boolean
  val isTypeApp: Boolean
  val isTypeAbs: Boolean
  def isApplicable(arg: Term): Boolean

  // Queries on terms
  def getType: Option[Type]
  def _getType: Type = getType.get
  def freeVars: Set[Signature#Key]
  def herbrandUniverse: Set[Term]
  // Substitutions
  def substitute(what: Term, by: Term): Term = substitute0(what,by,0)
  def substitute(what: List[Term], by: List[Term]): Term = {
    require(what.length == by.length, "Substitution list do not match in length.")
    what.zip(by).foldRight(this)({case ((w,b), t:Term) => t.substitute(w,b)})
  }
  protected[internal] def substitute0(what: Term, by: Term, scope: Int): Term

  protected[internal] def inc(scope: Int): Term = this
  protected[internal] def dec(scope: Int): Term = this

  // Other operations
  def betaNormalize: Term = normalize0(0)
  protected[internal] def normalize0(scope: Int): Term
  // compare, order...
}

protected[internal] case class Atom(id: Signature#Key) extends Term {
  // Pretty printing
  import Signature.{get => signature}
  val sig = signature
  def pretty = sig.getMeta(id).getName

  // Predicates on terms
  val isAtom = true
  val isTermApp = false
  val isTermAbs = false
  val isTypeApp = false
  val isTypeAbs = false
  def isApplicable(arg: Term): Boolean = sig.getMeta(id).getType match {
    case Some(ty) if ty.isFunType  => ty._funDomainType == arg._getType
    case _ => false
  }

  // Queries
  def getType: Option[Type] = sig.getMeta(id).getType
  def freeVars: Set[Signature#Key] = Set(id)
  def herbrandUniverse: Set[Term] = Set.empty

  // Substitutions
  def substitute0(what: Term, by: Term, scope: Int): Term = what match {
    case Atom(a) if a == id => by
    case _                  => this
  }
  def normalize0(scope: Int) = this  // atoms are in β-nf
}

protected[internal] case class TermAbs(paramType: Type, body: Term) extends Term {
  // Pretty printing
//  def pretty = "(\\" + paramType.pretty + ". " + body.pretty + ")"
  def pretty = "(\\. " + body.pretty + ")"
  // Predicates on terms
  val isAtom = false
  val isTermApp = false
  val isTermAbs = true
  val isTypeApp = false
  val isTypeAbs = false
  def isApplicable(arg: Term): Boolean = arg.getType match {
    case None     => true // was machen wir hier?
    case Some(ty) => ty == paramType
  }

  // Queries
  def getType: Option[Type] = Some(Type.mkFunType(paramType, body._getType))
  def freeVars: Set[Signature#Key] = body.freeVars
  def herbrandUniverse: Set[Term] = ???

  // Substitutions
  def substitute0(what: Term, by: Term, scope: Int): Term = what match {
    case _ => TermAbs(paramType, body.substitute(what.inc(scope),by.inc(scope+1)))
  }

  override def dec(scope: Int) = TermAbs(paramType, body.dec(scope+1))
  override def inc(scope: Int) = TermAbs(paramType, body.inc(scope+1))

  def normalize0(scope: Int): Term = {
    TermAbs(paramType, body.normalize0(scope+1))
  }
}

protected[internal] case class TermApp(left: Term, right: Term) extends Term {
  // Pretty printing
  def pretty = "(" + left.pretty + " " + right.pretty + ")"

  // Predicates on terms
  val isAtom = false
  val isTermApp = true
  val isTermAbs = false
  val isTypeApp = false
  val isTypeAbs = false
  def isApplicable(arg: Term): Boolean = betaNormalize._getType match {
    case ty if ty.isFunType => arg._getType == ty._funDomainType
    case _ => false
  }

  // Queries
  def getType: Option[Type] = Some(left._getType._funCodomainType)

  def freeVars: Set[Signature#Key] = left.freeVars ++ right.freeVars
  def herbrandUniverse: Set[Term] = ???

  // Substitutions
  def substitute0(what: Term, by: Term, scope: Int): Term = TermApp(left.substitute0(what, by,scope), right.substitute0(what, by, scope))

  override def dec(scope: Int) = TermApp(left.dec(scope), right.dec(scope))
  override def inc(scope: Int) = TermApp(left.inc(scope), right.inc(scope))

  def normalize0(scope: Int): Term = {
    val leftNF = left.betaNormalize
    val rightNF = right.betaNormalize
    leftNF match {
      case TermAbs(ty, body) => body.dec(scope+1).substitute(DeBruijnIndex(ty, 1), rightNF)
      case _ => TermApp(leftNF, rightNF)
    }
  }

}

protected[internal] case class DeBruijnIndex(boundType: Type, i: Int) extends Term {
  // Pretty printing
  def pretty = i.toString

  // Predicates on terms
  val isAtom = false
  val isTermApp = true
  val isTermAbs = false
  val isTypeApp = false
  val isTypeAbs = false
  def isApplicable(arg: Term): Boolean = arg.getType match {
    case Some(ty) if boundType.isFunType => boundType._funDomainType == ty
    case _ => false
  }

  // Queries
  def getType: Option[Type] = Some(boundType)

  def freeVars: Set[Signature#Key] = Set.empty
  def herbrandUniverse: Set[Term] = ???

  // Substitutions
  def substitute0(what: Term, by: Term, scope: Int): Term = what match {
    case DeBruijnIndex(_,j) if i == j => by
    case _ => this
  }

  override def dec(scope: Int) = scope match {
    case s if s <= i => DeBruijnIndex(boundType, i-1)
    case _ => this
  }
  override def inc(scope: Int) = scope match {
    case s if s <= i => DeBruijnIndex(boundType, i+1)
    case _ => this
  }

  def normalize0(scope: Int): Term = this
}


object Term {
  def mkAtom = Atom(_)
  def mkBound = DeBruijnIndex(_,_)
  def mkTermApp = TermApp(_,_)
  def mkTermAbs = TermAbs(_, _)
  def mkTypeApp(left: Type, right: Type): Term = ???
  def mkTypeAbs(hd: Variable, body: Term): Term = ???

  def \(hd: Type, body: Term): Term = ???

  def /\(hd: Variable, body: Term): Term = ???

  implicit def intToBoundVar(i: Int, t: Type): Term = mkBound(t,i)
}
