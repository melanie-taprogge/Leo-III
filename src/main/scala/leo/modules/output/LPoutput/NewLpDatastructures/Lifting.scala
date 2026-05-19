package leo.modules.output.LPoutput.NewLpDatastructures

import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm.Var
import leo.modules.output.LPoutput.NewLpDatastructures.LpType.{LpSet, Prf}
import leo.modules.output.LPoutput.NewLpDatastructures.OlMonoType.TyVar

/** Constructors for Lambdapi meta-level Types and Terms based on object-level instances **/
object Lifting {
  // ** Variables 
  private object TyVarM {
    def apply(v: TyVar): Var[Level.Meta] =
      Var(v.name,Some(LpSet))

    def unapply(v: Var[Level.Meta]): Option[TyVar] = v match {
      case `Var`(n,Some(LpSet)) => Some(TyVar(n))
      case _ => None
    }
  }

  object OlVarM {
    def apply(v: Var[Level.Obj]): Var[Level.Meta] = {
      Var(v.name, v.ty)
    }

    def unapply(v: Var[Level.Meta]): Option[Var[Level.Obj]] = v match {
      case `Var`(n, t) => Some(Var[Level.Obj](n, t))
      case _ => None
    }
  }

  def liftOlVars(v: Either[Var[Level.Obj], TyVar]): Var[Level.Meta] = v match {
    case Left(olVar) => OlVarM(olVar)
    case Right(tyVar) => TyVarM(tyVar)
  }

  // ** Propositions
  object ProofTerm {
    def apply(t: LpTerm[Level.Obj]): LpType = {
      Prf(t)
    }

    def unapply(t: LpType): Option[LpTerm[Level.Obj]] = t match {
      case Prf(t) => Some(t)
      case _ => None
    }
  }
}
