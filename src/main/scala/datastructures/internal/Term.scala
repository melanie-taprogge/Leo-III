package datastructures.internal

import datastructures.Pretty


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
 * @note Updated 02.06.2014 Cleaned up method set, lambda terms always have types
 */
abstract class Term extends Pretty {
  // Predicates on terms
  val isAtom: Boolean
  val isTermApp: Boolean
  val isTermAbs: Boolean
  val isTypeApp: Boolean
  val isTypeAbs: Boolean


  // Queries on terms
  def ty: Type
  def freeVars: Set[Term]
  def herbrandUniverse: Set[Term]
  // Substitutions
  def substitute(what: Term, by: Term): Term
  def substitute(what: List[Term], by: List[Term]): Term = {
    require(what.length == by.length, "Substitution list do not match in length.")
    what.zip(by).foldRight(this)({case ((w,b), t:Term) => t.substitute(w,b)})
  }

  // Other operations
  def betaNormalize: Term

  protected[internal] def inc(scopeIndex: Int): Term
}


object Term {
  def mkAtom = SymbolNode(_)
  def mkBound = BoundNode(_,_)
  def mkTermApp = ApplicationNode(_,_)
  def mkTermAbs = AbstractionNode(_, _)
  def mkTypeApp(left: Type, right: Type): Term = ???
  def mkTypeAbs(hd: Variable, body: Term): Term = ???

  def \(hd: Type, body: Term): Term = ???

  def /\(hd: Variable, body: Term): Term = ???
}

