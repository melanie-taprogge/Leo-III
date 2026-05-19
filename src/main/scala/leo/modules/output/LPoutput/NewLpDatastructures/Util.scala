package leo.modules.output.LPoutput.NewLpDatastructures

/** Carry out substitutions */
object Substitution {
  import leo.modules.output.LPoutput.NewLpDatastructures.OlMonoType._
  import leo.modules.output.LPoutput.NewLpDatastructures.OlPolyType._

  /** Substitute type variables in a monomorphic type. */
  def substMonoType(ty: OlMonoType, subst: Map[Name, OlMonoType]): OlMonoType = ty match {
    case v @ TyVar(name) =>
      subst.getOrElse(name, v)

    case b @ Base(_) =>
      b

    case Fun(args) =>
      Fun(args.map(arg => substMonoType(arg, subst)))

    case TyApp(hd, args) =>
      TyApp(hd, args.map(arg => substMonoType(arg, subst)))
  }

  /**
    * Instantiate as many prefix type quantifiers as there are supplied arguments.
    *
    * Behavior mirrors Leo's instantiate(by: Seq[Type]):
    * - if fewer args than binders are given, only that many binders are instantiated
    * - if more args than binders are given, extras are ignored
    * - if the input is already monomorphic, it is returned unchanged
    */
  def instantiatePrefix(polyTy: OlPolyType, args: Seq[OlMonoType]): OlPolyType = polyTy match {
    case LiftedMono(ty) => LiftedMono(ty)

    case TyQuant(binders, body) =>
      val (instBinders, remainingBinders) = binders.splitAt(args.size)

      val subst: Map[Name, OlMonoType] =
        instBinders.iterator.map(_.name).zip(args.iterator).toMap

      val instantiatedBody = substMonoType(body, subst)

      if (remainingBinders.isEmpty) LiftedMono(instantiatedBody)
      else TyQuant(remainingBinders, instantiatedBody)
  }

  /** Fully instantiate and return the monomorphic body. */
  def instantiateToMono(polyTy: OlPolyType, args: Seq[OlMonoType]): OlMonoType =
    instantiatePrefix(polyTy, args) match {
      case LiftedMono(ty)       => ty
      case TyQuant(_, body)     => body
    }

  /** Drop all prefix type arguments and keep the remaining term arguments. */
  def removeLeadingTypeArgs(args: Seq[Arg[Level.Obj]]): Seq[Arg[Level.Obj]] =
    args.dropWhile {
      case Arg.ImplicitTypeArg(_) => true
      case Arg.ExplicitTypeArg(_) => true
      case _ => false
    }
}
