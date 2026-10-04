package leo.datastructures

/**
  * A literal representation that preserves its syntactic shape.
  *
  * Unlike [[Literal]], constructing a raw equational literal with `$true` or
  * `$false` on either side does not turn it into a non-equational literal.
  * Raw literals are intended for additional proof metadata that must describe
  * a clause before Leo's literal ordering and normalization.
  */
sealed trait RawLiteral {
  def polarity: Boolean
  def terms: Seq[Term]

  final lazy val fv: Seq[(Int, Type)] = terms.flatMap(_.fv).distinct
  final lazy val tyFV: Seq[Int] = terms.flatMap(_.tyFV).distinct
}

final case class RawEqLiteral(left: Term,
                              right: Term,
                              polarity: Boolean) extends RawLiteral {
  require(left.ty == right.ty, "Raw equality sides must have the same type")

  override val terms: Seq[Term] = Seq(left, right)
}

final case class RawNonEqLiteral(term: Term,
                                 polarity: Boolean) extends RawLiteral {
  override val terms: Seq[Term] = Seq(term)
}

object RawLiteral {
  /** Preserve the distinction between equational and non-equational literals. */
  def apply(literal: Literal): RawLiteral = {
    if (literal.equational) RawEqLiteral(literal.left, literal.right, literal.polarity)
    else RawNonEqLiteral(literal.left, literal.polarity)
  }
}

/** A sequence of raw literals together with its implicitly bound variables. */
final case class RawClause(lits: Seq[RawLiteral]) {
  lazy val implicitlyBound: Seq[(Int, Type)] =
    lits.flatMap(_.fv).distinct.toVector.sortWith { case ((left, _), (right, _)) => left > right }

  lazy val typeVars: Seq[Int] =
    lits.flatMap(_.tyFV).distinct.toVector.sortWith(_ > _)
}

object RawClause {
  /** Capture the current shape of an ordinary clause without later rebuilding it through Literal. */
  def apply(clause: Clause): RawClause = RawClause(clause.lits.map(RawLiteral(_)).toVector)
}
