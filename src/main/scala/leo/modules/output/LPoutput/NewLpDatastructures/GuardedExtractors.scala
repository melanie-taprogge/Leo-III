package leo.modules.output.LPoutput.NewLpDatastructures

import leo.modules.output.LPoutput.EncodeResult.NotEncodable

//////////////////////////////////////////
// Guarded extractors
//////////////////////////////////////////

object Arguments {

  /** Helper for safe extraction of terms from term arguments */
  private def extractTermArg(arg: Arg[Level.Obj]): Either[NotEncodable, LpTerm[Level.Obj]] = arg match {
    case Arg.Implicit(t) => Right(t)
    case Arg.Explicit(t) => Right(t)
    case Arg.ImplicitTypeArg(_) => Left(NotEncodable("DetUniSimp: unexpected type argument in term application (implicit type arg)"))
    case Arg.ExplicitTypeArg(_) => Left(NotEncodable("DetUniSimp: unexpected type argument in term application (explicit type arg)"))
  }

  /** Helper for safe extraction of a Vector of terms from a Vector of term arguments */
  def extractTermArgs(args: Seq[Arg[Level.Obj]]): Either[NotEncodable, Vector[LpTerm[Level.Obj]]] = {
    args.foldLeft[Either[NotEncodable, Vector[LpTerm[Level.Obj]]]](Right(Vector.empty)) {
      case (Left(err), _) => Left(err)
      case (Right(acc), a) =>
        extractTermArg(a) match {
          case Left(err) => Left(err)
          case Right(t) => Right(acc :+ t)
        }
    }
  }
}
