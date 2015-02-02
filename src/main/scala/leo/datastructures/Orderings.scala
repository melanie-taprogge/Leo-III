package leo.datastructures

import leo.datastructures.impl.Signature
import leo.{ClauseOrdering, TermOrdering, TypeOrdering}
import leo.datastructures.term.Term
import leo.datastructures.term.Term.{:::>, TypeLambda,∙,Symbol}

/**
 * Collection of Ordering relations of terms, clauses, etc.
 *
 * @author Alexander Steen
 * @since 20.08.14
 */



/////////////////////
// Clause Orderings
/////////////////////

/** Lexicographic clause ordering on the 3-tuple (clause weight, clause age, clause origin). */
object CLOrdering_Lex_Weight_Age_Origin extends ClauseOrdering {
  import scala.math.Ordered.orderingToOrdered
  def compare(a: Clause, b: Clause) = ((a.weight, a.id, a.origin)) compare ((b.weight, b.id, b.origin))
}

///////////////////////
/// Term Orderings
///////////////////////

/** Only for debugging and compiling purposes. Will be removed soon. */
object SenselessOrdering extends TermOrdering {
  def compare(a: Term, b: Term) = Some(0)
}

/** Polymorphic higher-order recursive path ordering on terms of same type, as given by Jouannaud and Rubio
  * in "The Higher-Order Recursive Path Ordering",1999, doi: 10.1109/LICS.1999.782635  */
object PolyHORecPathOrdering extends TermOrdering {
  def compare(a: Term, b: Term) = {
    // Only terms with equivalent type can be compared
    if (a.ty != b.ty)
      None
    else if (a == b)
      Some(0)
    else {
      compare0(a,b)
    }
  }

  private def compare0(a: Term, b: Term): Option[Int] = {
    assert(a.ty == b.ty)

    if (a == b) {
      Some(0)
    } else if (a.isVariable || b.isVariable) {
      // Variables cannot be compared since orderings are only defined on ground terms.
      None
    } else if (a.isTypeAbs && !b.isTypeAbs || !a.isTypeAbs && b.isTypeAbs) {
      // adapted: If only one term is a type abstraction but the other is not,
      // the terms are not comparable
      None
    } else if (a.isTypeAbs && b.isTypeAbs) {
      // adapted: both terms are type abstractions, compare recursively
      val body1 = TypeLambda.unapply(a).get
      val body2 = TypeLambda.unapply(b).get
      compare0(body1, body2)
    } else if (a.isTermAbs && !b.isTermAbs || !a.isTermAbs && b.isTermAbs) {
      // If only one term is an abstraction but the other is not,
      // the terms are not comparable
      None
    } else if (a.isTermAbs && b.isTermAbs) {
      // Case (7), both terms are abstractions, compare recursively
      val (_, body1) = :::>.unapply(a).get
      val (_, body2) = :::>.unapply(b).get
      compare0(body1, body2)
    } else {
      lazy val (head1, spine1) = ∙.unapply(a).get
      lazy val (head2, spine2) = ∙.unapply(b).get

      lazy val argList1 = filterTermArgs(spine1)
      lazy val argList2 = filterTermArgs(spine2)
      head1 match {
        case Symbol(k1) => {
          // Case (1), > direction
          val it = argList1.iterator
          var stop = false
          while (it.hasNext && !stop) {
            compare0(it.next(), b) match {
              case Some(res) if res >= 0 => {stop = true}
              case _ => ;
            }
          }
          if (stop) { // subterm greater than b was found, return result > 0
            Some(1)
          } else { // continue serach
            head2 match {
              case Symbol(k2) => {
                // Cases 2,3,4, both directions

                if (k1 > k2) {
                  // Case 2, > direction
                  if ((argList2).forall(arg =>
                    compare0(a, arg).getOrElse(Int.MinValue) > 0 || argList1.exists(compare0(_,arg).getOrElse(Int.MinValue) >= 0))) {
                    Some(1)
                  } else {
                    None
                  }
                } else if (k2 < k1) {
                  // Case 2, < direction
                  if ((argList1).forall(arg =>
                    compare0(a, arg).getOrElse(Int.MaxValue) < 0 || argList2.exists(compare0(_,arg).getOrElse(Int.MaxValue) <= 0))) {
                    Some(-1)
                  } else {
                    None
                  }
                } else {
                  // Case 3,4
                  val sig = Signature.get
                  val status = sig(k1).status

                  if (status == 0) { // Multiset
                    mult(argList1, argList2)
                  } else if (status == 1) { // Lexicographic
                    lex(argList1, argList2) match {
                      case None => None
                      case Some(r) if r == 0 => None
                      case Some(r) if r > 0 => if ((argList2).forall(arg =>
                        compare0(a, arg).getOrElse(Int.MinValue) > 0 || argList1.exists(compare0(_,arg).getOrElse(Int.MinValue) >= 0))) {
                        Some(1)
                      } else {
                        None
                      }
                      case Some(r) if r < 0 => if ((argList1).forall(arg =>
                        compare0(a, arg).getOrElse(Int.MaxValue) < 0 || argList2.exists(compare0(_,arg).getOrElse(Int.MaxValue) <= 0))) {
                        Some(-1)
                      } else {
                        None
                      }
                    }
                  } else {
                    assert(false)
                    throw new IllegalArgumentException("this should not happen")
                  }
                }
              }
              case _ => { // Case 5, > direction
                if ((head2 +: argList2).forall(arg =>
                  compare0(a, arg).getOrElse(Int.MinValue) > 0 || argList1.exists(compare0(_,arg).getOrElse(Int.MinValue) >= 0))) {
                  Some(1)
                } else {
                  None
                }
              }
            }
          }
        }
        case _ => {
          //head2 could be signature constant
          //some application (either i.S or t'.S)
          head2 match {
            case Symbol(k2) => {
              // Case 1, < direction
              val it = argList2.iterator
              var stop = false
              while (it.hasNext && !stop) {
                compare0(it.next(), a) match {
                  case Some(res) if res <= 0 => {
                    stop = true
                  }
                  case _ => ;
                }
              }
              if (stop) {
                Some(-1)
              } else {
                // case 5, < direction
                if ((head1 +: argList1).forall(arg =>
                  compare0(a, arg).getOrElse(Int.MaxValue) < 0 || argList2.exists(compare0(_,arg).getOrElse(Int.MaxValue) <= 0))) {
                  Some(-1)
                } else {
                  None
                }
              }
            }
            case _ => mult((head1 +: argList1),(head2 +: argList2)) // case 6 both directions, adopted
          }
        }
      }
    }
  }

  private def filterTermArgs(args: Seq[Either[Term, Type]]): Seq[Term] = args match {
    case Seq() => Seq()
    case Seq(h, rest@_*) => h match {
      case Left(term) => term +: filterTermArgs(rest)
      case Right(_) => filterTermArgs(rest)
    }
  }

  private def lex(a: Seq[Term], b: Seq[Term]): Option[Int] = a match {
    case Seq() if b.isEmpty => Some(0)
    case Seq() => Some(-1)
    case Seq(_, rest@_*) if b.isEmpty => Some(1)
    case Seq(t1, tn@_*) => compare0(t1, b.head) match {
      case None => None
      case Some(r) if r == 0 => lex(tn, b.tail)
      case r => r
    }
  }

  private def mult(a: Seq[Term], b: Seq[Term]): Option[Int] = {
    a match {
      case Seq() if b.isEmpty => Some(0)
      case Seq() => Some(-1)
      case _ if b.isEmpty => Some(1)
      case _ => {
        val aMax = maximalElement(a)
        val bMax = maximalElement(b)

        compare(aMax, bMax)match {
          case None => None
          case Some(r) if r == 0 => mult(a.diff(Seq(aMax)), b.diff(Seq(bMax)))
          case r => r
        }
      }
    }
  }

  private def maximalElement(a: Seq[Term]): Term = {
    val it = a.iterator
    var curMax = a.head
    while(it.hasNext) {
      val cur = it.next()
      compare(curMax, cur) match {
        case None => ;
        case Some(r) if r < 0 => curMax = cur
      }
    }
    curMax
  }
}

/**
 * `HORPO` as given by "Polymorphic higher-order recursive path ordering" by Jouannaud and Rubio in
 * Journal of the ACM, Vol 54. No 1. Article 2, March 2007.
 *
 * Since we only work on beta-normalized terms, we remove the functionality
 * property requirement from the ordering, i.e. we do not follow/track possible beta-
 * and eta-normalization steps during the comparison. More concretely, we drop cases (11) and (12) of
 * the original definition.
 */
object RPO extends TermOrdering {
  val GT = Some(1)
  val LT = Some(-1)
  val tyO: TypeOrdering = ???
  val prec: QuasiOrdering[Signature#Key] = ???

  def compare(a: Term, b: Term) = {
    if (a == b)
      Some(0)
    else
      tyO.compare(a.ty, b.ty).flatMap(doCompare(a,b,_))
  }

  private def compare0(a: Term, b: Term, cmpTo: Int): Option[Int] = {
    val tyCmp = tyO.compare(a.ty, b.ty)

    // Either the type order is still compatible, or the terms cannot be ordered
    // (i.e. type incomparable or ordering not compatible to root type ordering result).
    if (tyCmp.isDefined && Math.abs(tyCmp.get - cmpTo) <= 1) {
      doCompare(a,b,cmpTo)
    } else {
      None
    }

  }

  private def doCompare(a: Term, b: Term, cmp: Int): Option[Int] = {
    var res: Option[Int] = None


    if (res.isEmpty && isFuncSymbApp(a) && cmp >= 0) {
      val (_, spineA) = ∙.unapply(a).get

      // Case (1) >-Direction
      if (spineA.exists(_ match {
        case Left(t) => gteq(t, b)
        case Right(_) => false
      })) {
        res = GT
      }

      // Case (7) >-Direction
      if (res.isEmpty && isAppWithoutFuncSymb(b)) {
        val (headB, spineB) = ∙.unapply(b).get
        
        if ( A(a, spineA, Left(headB) +: spineB, cmp)) {
          res = GT
        }
      }

      // Case (8) >-Direction
      if (res.isEmpty && b.isTermAbs) {
        val (_, bodyB) = :::>.unapply(b).get

        if (!bodyB.looseBounds.contains(1)) {
          res = compare0(a, bodyB, cmp)
        }
      }
    }


    if (res.isEmpty && isFuncSymbApp(b) && cmp <= 0) {
      val (_, spineB) = ∙.unapply(b).get

      // Case (1) <-Direction
      if (spineB.exists(_ match {
        case Left(t) => lteq(a, t)
        case Right(_) => false
      })) {
        res = LT
      }

      // Case (7) <-Direction
      if (res.isEmpty && isAppWithoutFuncSymb(a)) {
        val (headA, spineA) = ∙.unapply(a).get

        if (A(b,spineB, (Left(headA) +: spineA), cmp)) {
          res = LT
        }
      }

      // Case (8) <-Direction
      if (res.isEmpty && a.isTermAbs) {
        val (_, bodyA) = :::>.unapply(a).get

        if (!bodyA.looseBounds.contains(1)) {
          res = compare0(bodyA, b, cmp)
        }
      }
    }

    // Cases (2),(3),(4)
    if (res.isEmpty && isFuncSymbApp(a) && isFuncSymbApp(b)) {
      lazy val (headA, spineA) = ∙.unapply(a).get
      lazy val (headB, spineB) = ∙.unapply(b).get



    }

    /** Implements case (10) */
    if (res.isEmpty && a.isTermAbs && b.isTermAbs) {
      val (varTyA, bodyA) = :::>.unapply(a).get
      val (varTyB, bodyB) = :::>.unapply(b).get

      if (tyO.eq(varTyA, varTyB)) {
        res = compare0(bodyA, bodyB, cmp)
      }
    }

    if (res.isEmpty && a.isTermAbs) {
      val (_, bodyA) = :::>.unapply(a).get
      if (cmp >= 0) {
        /** Implements case (6), >=-direction */
        res = compare0(bodyA, b, cmp)
      }
      if (cmp <= 0) {
        /** Implements case (12), <=-direction */
        // eta contract a to `a2`
        val a2 = a.topEtaContract
        if (a != a2)
          res = join(res,compare0(a2, b, cmp))
      }
    }

    if (res.isEmpty && b.isTermAbs) {
      if (cmp >= 0) {
        /** Implements case (12), >-direction */
        // eta contract b to `b2`
        val b2 = b.topEtaContract
        if (b != b2)
          res = compare0(a, b2, cmp)
      }
      if (cmp <= 0) {
        /** Implements case (6), <-direction */
        val (_, bodyB) = :::>.unapply(b).get
        res = join(res,compare0(a, bodyB, cmp))
      }
    }



    // if a is type abstraction and b is type abstraction
    // if a

    res
  }
  // wenn cmp < 0, dann a < b, sonst wenn cmp > 0 dann a > b
  private def nextCase(res: Option[Int]): Boolean = res.isEmpty

  private def join(a: Option[Int], b: => Option[Int]): Option[Int] = if (a.isDefined) a else b
//  s (6),(8) and

  private def isFuncSymbApp(a: Term): Boolean = {
    if (!a.isApp) false
    else {
      val (head1, _) = ∙.unapply(a).get
      head1.isConstant
    }
  }

  private def isAppWithoutFuncSymb(a: Term): Boolean = {
    if (!a.isApp) false
    else {
      val (head1, _) = ∙.unapply(a).get
      !head1.isConstant
    }
  }

  def A(a: Term, argsA: Seq[Either[Term,Type]], argsB: Seq[Either[Term,Type]], cmp: Int): Boolean = {
    (argsB).forall(_ match {
      case Left(t) => (compare0(a, t,cmp).getOrElse(-4711) > 0 || argsB.exists(_.fold(compare0(_,t,cmp).getOrElse(-4711) > 0, _ => false)))
      case _ => false
    })
  }



}

///////////////////////
/// Type Orderings
///////////////////////



///////////////////////
/// Generic Orderings
///////////////////////

/** `SimpleOrdering`s are orderings that are induced by a weighting. */
class SimpleOrdering[A](weighting: Weight[A]) extends Ordering[A] {
  def compare(a: A, b: A) = weighting.weightOf(a) - weighting.weightOf(b)
}

//////////////////////
// Associated traits
//////////////////////

/**
 * A trait for representing quasi-orderings.
 * A quasi-ordering is a
 *
 * - reflexive
 * - transitive
 *
 * binary relation.
 */
trait QuasiOrdering[A] {
  /** Result of comparing `x` with operand `y`.
    *
    * Returns `Some(res)` where:
    *   - `res < 0` when `x < y`
    *   - `res == 0` when `x == y`
    *   - `res > 0` when  `x > y`
    *
    * Returns `None` if the objects cannot be compared.
    * This is due to the fact that this object represents a partial ordering;
    * it is possible that neither `compare(x,y) < 0` or `compare(y,x) < 0`
    * holds for `x != y`.
    */
  def compare(x: A, y: A): Option[Int]

  /** Returns `true` iff `x` and `y` are comparable w.r.t. the underlying ordering. */
  def canCompare(x: A, y: A): Boolean = if (x == y) true
                                        else compare(x,y).isDefined|| compare(y,x).isDefined

  /** Strict comparison `x < y` w.r.t. the underlying ordering. */
  def lt (x: A, y: A): Boolean = compare(x,y).getOrElse(Int.MaxValue) < 0
  /** Comparison `x <= y` w.r.t. the underlying ordering. */
  def lteq (x: A, y: A): Boolean = compare(x,y).getOrElse(Int.MaxValue) <= 0
  /** Strict comparison `x > y` w.r.t. the underlying ordering. */
  def gt (x: A, y: A): Boolean = compare(x,y).getOrElse(Int.MinValue) > 0
  /** Comparison `x >= y` w.r.t. the underlying ordering. */
  def gteq (x: A, y: A): Boolean = compare(x,y).getOrElse(Int.MinValue) >= 0
  /** Comparison `x = y` w.r.t. the underlying ordering .*/
  def eq (x: A, y: A): Boolean = compare(x,y).getOrElse(-4711) == 0
}

/** Trait for quasi-ordered data.
  * @see [[QuasiOrdering]]
  */
trait QuasiOrdered[A] {
  /** Result of comparing `this` with operand `that`.
    *
    * Returns `Some(res)` where:
    *   - `res < 0` when `this < that`
    *   - `res == 0` when `this == that`
    *   - `res > 0` when  `this > that`
    *
    * Returns `None` if the objects cannot be compared.
    * This is due to the fact that this object represents a partial ordering;
    * it is possible that neither `this compareTo that < 0` or `that compareTo this < 0`
    * holds for `this != that`.
    */
  def compareTo(that: A): Option[Int]

  /** Returns true iff `this` and `that`  are comparable w.r.t. the underlying quasi-ordering. */
  def comCompareTo(that: A): Boolean = compareTo(that).isDefined

  /** Returns true iff (this compareTo that) < 0, i.e. if `this` is strictly smaller than `that`. */
  def <  (that: A): Boolean = (this compareTo that).getOrElse(Int.MaxValue) < 0
  /** Returns true iff (this compareTo that) <= 0, i.e. if `this` is smaller than (or equal to) `that`. */
  def <= (that: A): Boolean = (this compareTo that).getOrElse(Int.MaxValue) <= 0
  /** Returns true iff (this compareTo that) > 0, i.e. if `this` is strictly larger than `that`. */
  def >  (that: A): Boolean = (this compareTo that).getOrElse(Int.MinValue) > 0
  /** Returns true iff (this compareTo that) >= 0, i.e. if `this` is larger than (or equal to) `that`. */
  def >= (that: A): Boolean = (this compareTo that).getOrElse(Int.MinValue) >= 0
}

