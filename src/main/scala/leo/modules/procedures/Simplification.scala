package leo.modules.procedures

import leo.datastructures.{Literal, Rat, Real, Term, Type}
import leo.datastructures.Term.local._

import scala.annotation.{switch, tailrec}

/**
  * Applies simplification transformations to formulas/terms.
  * The simplification result is given by the exhaustive (recursive) application of
  * the following rules (where Π denotes universal type quantification):
  *
  *   - `s \/ s -> s`
  *   - `~s \/ s -> T`
  *   - `s \/ T -> T`
  *   - `s \/ F -> s`
  *   - `s /\ s -> s`
  *   - `~s /\ s -> F`
  *   - `s /\ T -> s`
  *   - `s /\ F -> F`
  *   - `~ ~s -> s`
  *   - `~F -> T`
  *   - `~T -> F`
  *   - `t = t -> T`
  *   - `s = T -> s` *
  *   - `s = F -> ~s` *
  *   - `t != t -> F`
  *   - `s != T -> ~s` *
  *   - `s != F -> s` *
  *   - `∀x. s -> s` if `x` not free in `s`
  *   - `∃x. s -> s` if `x` not free in `s`
  *   - `Πx. s -> s` if `x` is not free in `s`
  *   - `n/m -> n'/m'` where `n/m` is a rational number and `n'/m'` is its canonical rational representation
  *   - `(w,d,e) -> (w',d',e')` where `r = (w,d,e)` is a real number and `r' = (w',d',e')` is its canonical representation
  *   - `$difference(x,y) -> $sum(x,$uminus(y))` where `x` and `y` are arbitrary terms
  *   - `$greatereq(x,y) -> $less(y,x) \/ x = y`
  *   - `$greater(x,y) -> $less(y,x)`
  *   - `$lesseq(x,y) -> $less(x,y) \/ x = y`
  *
  * The four cases marked with (*) are only applied if simplifying extensionally, cf. [[Simplification.apply]].
  *
  * @author Alexander Steen
  */
object Simplification extends Function1[Term, Term] {

  /**
    * Applies simplification to `term` using the transformation rules given in
    * the description of [[Simplification]].
    *
    * @param term The term to be simplified
    * @param extensional If set to `true`, the term will be simplified using the additional four extensional simplification rules.
    *
    * @return The term that is created by exhaustively applying all the rewriting rules given in [[Simplification]].
    */
  final def apply(term: Term, extensional: Boolean): Term = {
    val term0 = term.betaNormalize
    apply0(term0, extensional).betaNormalize
  }

  /**
    * Applies simplification to `term` using the transformation rules given in
    * the description of [[Simplification]], including the extensional ones.
    *
    * @param term The term to be simplified
    * @return The term that is created by exhaustively applying all the rewriting rules given in [[Simplification]].
    */
  final def apply(term: Term): Term = apply(term, extensional = true)

  // TODO: Check if the four simplifications are really "extensional" and not just straight-forward
  // Boolean (with equality) identities

  private[this] final def apply0(term: Term, extensional: Boolean): Term = {
    val (t,_) = applyAndTrack (term, extensional)
    t
  }

  final def track(term: Term): (Term, Seq[(Seq[Int], String, Term, Term)]) = {
    val (restult, addInfo) = applyAndTrack(term, true)
    // we want to reverse the order of the positional encoding sequence so that the first step is the first integer
    val addInfoReverseOrder = addInfo.map(tuple => (tuple._1.reverse,tuple._2,tuple._3,tuple._4))
    (restult,addInfoReverseOrder)
  }
  private[this] final def applyAndTrack(term: Term, extensional: Boolean): (Term, Seq[(Seq[Int], String, Term, Term)]) = {
    import leo.datastructures.Term.{:::>, TypeLambda, Bound, Symbol, ∙, Rational, Real}
    import leo.modules.HOLSignature.{Exists, Forall, TyForall, &, |||, LitTrue, LitFalse, ===, !===, Not, Impl, <=>,
      HOLDifference, HOLUnaryMinus, HOLSum, HOLLess, HOLLessEq, HOLGreaterEq, HOLGreater}

    //@inline def simpTermOrType(arg: Either[Term, Type]): Either[(Term,Seq[(Seq[Int],String,Term)]), (Type,Seq[(Seq[Int],String,Term)])] = arg match {
    @inline def simpTermOrType(arg: Either[Term, Type]): (Either[Term, Type],Seq[(Seq[Int],String,Term, Term)]) = arg match {
      case Left(arg0) =>
        val intermediate = applyAndTrack(arg0, extensional)
        (Left(intermediate._1),intermediate._2)
      case Right(arg0) => (Right(arg0),Seq.empty)
    }

    term match {
      case Bound(_, _) => (term,Seq.empty)
      case Symbol(_) => (term,Seq.empty)
      case ty :::> body =>
        val (simpBody, addInfo) = applyAndTrack(body, extensional)
        (mkTermAbs(ty, simpBody), addInfo.map(tuple => (tuple._1 :+ 1,tuple._2, tuple._3, tuple._4)))
      case TypeLambda(body) =>
        val (simpBody, addInfo) = applyAndTrack(body, extensional)
        (mkTypeAbs(simpBody), addInfo.map(tuple => (tuple._1 :+ 1,tuple._2, tuple._3, tuple._4)))
      case Rational(n, d) => ((mkRational _).tupled(normalizeRat(n, d)), Seq.empty)
      case Real(w,d,e) => ((mkReal _).tupled(normalizeReal(w,d,e)), Seq.empty)
      case f ∙ args if f.isConstant && args.length <= 3 =>
        (f: @unchecked) match {
          case Symbol(id) =>
            (id: @switch) match {
              case |||.key =>
                val (left,right) = |||.unapply(term).get
                val (simpLeft,addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight,addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                (simpLeft, simpRight) match {
                  // - `s \/ s -> s`
                  case (l, r) if l == r       => (l,newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp1", term, l))
                  // - `~s \/ s -> T`
                  case (l, Not(r)) if l == r  => (LitTrue,newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp3_r", term, LitTrue))
                  case (Not(l), r) if l == r  => (LitTrue,newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp3_l", term, LitTrue))
                  // - `s \/ T -> T`
                  case (_, LitTrue())         => (LitTrue,newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp5_l", term, LitTrue))
                  case (LitTrue(), _)         => (LitTrue,newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp5_r", term, LitTrue))
                  // - `s \/ F -> s`
                  case (l, LitFalse())        => (l,newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp7_l", term, l))
                  case (LitFalse(), r)        => (r,newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp7_r", term, r))
                  case (l, r)                 => (mkTermApp(f, Seq(l,r)),newAddInfoL ++ newAddInfoR)
                }
              case &.key =>
                val (left,right) = &.unapply(term).get
                val (simpLeft,addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight,addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                (simpLeft, simpRight) match {
                  // - `s /\ s -> s`
                  case (l, r) if l == r       => (l,newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp2", term, l))
                  //  - `~s /\ s -> F`
                  case (l, Not(r)) if l == r  => (LitFalse, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp4_r", term, LitFalse))
                  case (Not(l), r) if l == r  => (LitFalse, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp4_l", term, LitFalse))
                  // - `s /\ T -> s`
                  case (l, LitTrue())         => (l, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp6_l", term, l))
                  case (LitTrue(), r)         => (r, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp6_r", term, r))
                  // - `s /\ F -> F`
                  case (_, LitFalse())        => (LitFalse, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp8_l", term, LitFalse))
                  case (LitFalse(), _)        => (LitFalse, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp8_r", term, LitFalse))
                  case (l, r)                 => (mkTermApp(f, Seq(l,r)), newAddInfoL ++ newAddInfoR)
                }
              case Impl.key =>
                val (left,right) = Impl.unapply(term).get
                val (simpLeft, addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight, addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                (simpLeft, simpRight) match {
                  case (_, LitTrue())   => (LitTrue, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE1", term, LitTrue))
                  case (LitFalse(), _)  => (LitTrue, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE2", term, LitTrue))
                  case (LitTrue(), r) =>  (r, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE3", term, r))
                  case (_, LitFalse()) =>
                    val intermediate = mkTermApp(mkAtom(Not.key, Not.ty), simpLeft) // todo: I think i do not have to track this for lp since this is the lp encoding but make sure
                    applyAndTrack(intermediate, extensional)
                  case (l, r) if l == r => (LitTrue(), newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE5", term, LitTrue()))
                  case (l, r)           => (mkTermApp(f, Seq(l,r)), newAddInfoL ++ newAddInfoR)
                }
              case <=>.key =>
                val (left,right) = <=>.unapply(term).get
                val (simpLeft, addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight, addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                (simpLeft, simpRight) match {
                  case (l, LitTrue())   => (l, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE6_l", term, l))
                  case (LitTrue(), r)   =>  (r, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE6_r", term, r))
                  case (LitFalse(), _)  =>
                    val intermediate = mkTermApp(mkAtom(Not.key, Not.ty), simpRight)
                    val (simpIntermediate, addInfoInt) = applyAndTrack(intermediate, extensional)
                    val newAddInfoInt = addInfoInt.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                    (simpIntermediate, newAddInfoInt :+ (Seq.empty, "Simp7_r", term, simpIntermediate))
                  case (_, LitFalse())  =>
                    val intermediate = mkTermApp(mkAtom(Not.key, Not.ty), simpLeft)
                    val (simpIntermediate, addInfoInt) = applyAndTrack(intermediate, extensional)
                    val newAddInfoInt = addInfoInt.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                    (simpIntermediate, newAddInfoInt :+ (Seq.empty, "Simp7_l", term, simpIntermediate))
                  case (l, r) if l == r => (LitTrue(), newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE9", term, l))
                  case (l, r)           => (mkTermApp(f, Seq(l,r)), newAddInfoL ++ newAddInfoR)
                }
              case Not.key =>
                val body = Not.unapply(term).get
                val (simpBody, addInfo) = applyAndTrack(body, extensional)
                val newAddInfo = addInfo.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                simpBody match {
                  // - `~T -> F`
                  case LitTrue()  => (LitFalse, newAddInfo :+ (Seq.empty, "Simp16", term, LitFalse))
                  // - `~F -> T`
                  case LitFalse() => (LitTrue, newAddInfo :+ (Seq.empty, "Simp15", term, LitTrue))
                  // - `~ ~s -> s`
                  case Not(body0) => (body0, newAddInfo :+ (Seq.empty, "Simp17", term, body0))
                  case _          => (mkTermApp(f, simpBody), newAddInfo)
                }
              case ===.key =>
                val (left,right) = ===.unapply(term).get
                val (simpLeft, addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight, addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                if (extensional) {
                  (simpLeft, simpRight) match {
                    // - `s = T -> s`
                    case (_, LitTrue()) => (simpLeft, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp11_l", term, simpLeft))
                    case (LitTrue(), _) => (simpRight, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp11_r", term, simpRight))
                    // - `s = F -> ~s`
                    case (_, LitFalse()) =>
                      val intermediate = mkTermApp(mkAtom(Not.key, Not.ty), simpLeft)
                      val (simpIntermediate, addInfoInt) = applyAndTrack(intermediate, extensional)
                      val newAddInfoInt = addInfoInt.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                      (simpIntermediate, newAddInfoInt :+ (Seq.empty, "SimpE10_l", term, simpIntermediate))
                    case (LitFalse(), _) =>
                      val intermediate = mkTermApp(mkAtom(Not.key, Not.ty), simpRight)
                      val (simpIntermediate, addInfoInt) = applyAndTrack(intermediate, extensional)
                      val newAddInfoInt = addInfoInt.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                      (simpIntermediate, newAddInfoInt :+ (Seq.empty, "SimpE10_r", term, simpIntermediate))
                    // - `t = t -> T`
                    case (l, r) if l == r => (LitTrue, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp9", term, LitTrue))
                    case (l, r) => (mkApp(f, Seq(Right(l.ty), Left(l), Left(r))), newAddInfoL ++ newAddInfoR)
                  }
                } else {
                  (simpLeft, simpRight) match {
                    // - `t = t -> T`
                    case (l, r) if l == r => (LitTrue, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp9_ne", term, LitTrue))
                    case (l, r) => (mkApp(f, Seq(Right(l.ty), Left(l), Left(r))), newAddInfoL ++ newAddInfoR)
                  }
                }
              case !===.key =>
                val (left,right) = !===.unapply(term).get
                val (simpLeft, addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight, addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                if (extensional) {
                  (simpLeft, simpRight) match {
                    // - `s != F -> s`
                    case (_, LitFalse()) => (simpRight, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE12_l", term, simpRight))
                    case (LitFalse(), _) => (simpLeft, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"SimpE12_r", term, simpLeft))
                    // - `s != T -> ~s`
                    case (_, LitTrue()) =>
                      val intermediate = (mkTermApp(mkAtom(Not.key, Not.ty), simpLeft))
                      val (simpIntermediate, addInfoInt) = applyAndTrack(intermediate, extensional)
                      val newAddInfoInt = addInfoInt.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                      (simpIntermediate, newAddInfoInt :+ (Seq.empty, "SimpE13_l", term, simpIntermediate))
                    case (LitTrue(), _) =>
                      val intermediate = mkTermApp(mkAtom(Not.key, Not.ty), simpRight)
                      val (simpIntermediate, addInfoInt) = applyAndTrack(intermediate, extensional)
                      val newAddInfoInt = addInfoInt.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                      (simpIntermediate, newAddInfoInt :+ (Seq.empty, "SimpE13_r", term, simpIntermediate))
                    // - `t != t -> F`
                    case (l, r) if l == r => (LitFalse, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp10", term, LitFalse))
                    case (l, r) =>( mkApp(f, Seq(Right(l.ty), Left(l), Left(r))),newAddInfoL ++ newAddInfoR)
                  }
                } else {
                  (simpLeft, simpRight) match {
                    // - `t != t -> F`
                    case (l, r) if l == r => (LitFalse, newAddInfoL ++ newAddInfoR :+ (Seq.empty,"Simp10_ne", term, LitFalse))
                    case (l, r) => (mkApp(f, Seq(Right(l.ty), Left(l), Left(r))), newAddInfoL ++ newAddInfoR)
                  }
                }
              case Forall.key =>
                val body = Forall.unapply(term).get
                val (simpBody, addInfo) = applyAndTrack(body, extensional)
                val newAddInfo = addInfo.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                simpBody match {
                  // - ∀x. s -> s if x not free in s
                  // - ∃x. s -> s if x not free in s
                  case _ :::> absBody if !absBody.looseBounds.contains(1) => (absBody.lift(-1), newAddInfo :+ (Seq.empty,"Simp13", term,absBody.lift(-1)))
                  case _ => (mkApp(f, Seq(Right(simpBody.ty._funDomainType), Left(simpBody))), newAddInfo)
                }
              case Exists.key =>
                val body = Exists.unapply(term).get
                val (simpBody, addInfo) = applyAndTrack(body, extensional)
                val newAddInfo = addInfo.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                simpBody match {
                  // - ∀x. s -> s if x not free in s
                  // - ∃x. s -> s if x not free in s
                  case _ :::> absBody if !absBody.looseBounds.contains(1) => (absBody.lift(-1), newAddInfo :+ (Seq.empty,"Simp14", term,absBody.lift(-1)))
                  case _ => (mkApp(f, Seq(Right(simpBody.ty._funDomainType), Left(simpBody))), newAddInfo)
                }
              case TyForall.key =>
                val body = TyForall.unapply(term).get
                val (simpBody, addInfo) = applyAndTrack(body, extensional)
                val newAddInfo = addInfo.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                simpBody match {
                  // - Πx. s -> s if x is not free in s
                  case TypeLambda(absBody) if !absBody.tyFV.contains(1) => (absBody.lift(0, -1), newAddInfo :+ (Seq.empty,"SimpE16", term,absBody.lift(0, -1)))
                  case _ => (mkTermApp(f, simpBody), newAddInfo)
                }
              case HOLDifference.key =>
                val (left, right) = HOLDifference.unapply(term).get
                val (simpLeft, addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight, addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                (mkTermApp(mkTypeApp(HOLSum, simpLeft.ty), Seq(simpLeft, mkTermApp(mkTypeApp(HOLUnaryMinus, simpRight.ty), simpRight))), newAddInfoL ++ newAddInfoR)
              case HOLLessEq.key =>
                val (left, right) = HOLLessEq.unapply(term).get
                val (simpLeft, addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight, addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                (mkTermApp(mkAtom(|||.key, |||.ty), Seq(mkTermApp(mkTypeApp(HOLLess, simpLeft.ty), Seq(simpLeft, simpRight)), ===(simpLeft, simpRight))), newAddInfoL ++ newAddInfoR)
              case HOLGreater.key =>
                val (left, right) = HOLGreater.unapply(term).get
                val (simpLeft, addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight, addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                (mkTermApp(mkTypeApp(HOLLess, simpLeft.ty), Seq(simpRight, simpLeft)), newAddInfoL ++ newAddInfoR)
              case HOLGreaterEq.key =>
                val (left, right) = HOLGreaterEq.unapply(term).get
                val (simpLeft, addInfoL) = applyAndTrack(left, extensional)
                val newAddInfoL = addInfoL.map(tuple => (tuple._1 :+ 1, tuple._2, tuple._3, tuple._4))
                val (simpRight, addInfoR) = applyAndTrack(right, extensional)
                val newAddInfoR = addInfoR.map(tuple => (tuple._1 :+ 2, tuple._2, tuple._3, tuple._4))
                (mkTermApp(mkAtom(|||.key, |||.ty), Seq(mkTermApp(mkTypeApp(HOLLess, simpLeft.ty), Seq(simpRight, simpLeft)), ===(simpLeft, simpRight))), newAddInfoL ++ newAddInfoR)
              case _ =>
                val simpArgs0 = args.map(simpTermOrType) //.map(tuple => (tuple._1 :+ 1,tuple._2, tuple._3))
                (mkApp(f, simpArgs0.map(arg => arg._1)), simpArgs0.map(arg0 => arg0._2.map(arg => (arg._1 :+ simpArgs0.indexOf(arg0), arg._2, arg._3, arg._4))).flatten)
            }
        }
      case f ∙ args =>
        // f is a variable or a constant because `term` is in beta nf.
        val simpArgs0 = args.map(simpTermOrType)
        //var simpArgs: Seq[Either[Term,Type]] = Seq.empty
        //var addInfoArgs: Seq[(Seq[Int],String,Term)] = Seq.empty
        /*
        simpArgs0 foreach( arg => arg match {
          case Left((te, addInfoTe)) =>
            simpArgs = simpArgs :+ te
          case Right((ty, addInfoTy)) =>
        })

         */
        //val simpArgs: ((Term,(Seq[Int],String,Term))) = simpArgs0.map {
        //  case Left((te, addInfoTe)) => (te, addInfoTe)
        //  case Right((ty, addInfoTy)) => (ty, addInfoTy)})
        //(mkApp(f, simpArgs), addInfoArgs)

        //(mkApp(f, simpArgs0.map(arg => arg._1)), simpArgs0.map(arg => arg._2).flatten)
        (mkApp(f, simpArgs0.map(arg => arg._1)), simpArgs0.map(arg0 => arg0._2.map(arg => (arg._1 :+ simpArgs0.indexOf(arg0), arg._2, arg._3, arg._4))).flatten)
    }
  }

  @tailrec private[this] final def gcd(a: BigInt, b: BigInt): BigInt = if (b == 0) a.abs else gcd(b, a % b)
  final def normalizeRat(n: BigInt, d: BigInt): Rat = {
    val sign: BigInt = d.sign
    val greatestCommonDivisor: BigInt = gcd(n ,d).abs * sign
    (n / greatestCommonDivisor, d / greatestCommonDivisor)
  }
  final def normalizeReal(wholePart: BigInt, decimalPlaces: BigInt, exponent: BigInt): Real = { // TODO
    //    val decimalPlacesWithoutTrailingZeroes = if (decimalPlaces != 0) decimalPlaces.toString.reverse.dropWhile(_ == '0').reverse.toInt else 0
    //    val decimalPlacesWithoutTrailingZeroesLength = decimalPlacesWithoutTrailingZeroes.toString.length
    //    val wholePartAsString = wholePart.toString
    //    if (wholePartAsString.length > 3) {
    //      val (newWholePart, newRest) = wholePartAsString.splitAt(3)
    //      val newDecimalPlaces = decimalPlaces.toString.prependedAll(newRest)
    //    }
    (wholePart, decimalPlaces, exponent)
  }
}
