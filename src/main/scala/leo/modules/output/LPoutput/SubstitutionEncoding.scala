package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures._
import leo.modules.output.LPoutput.LpLibs.ND.Terms.lpWitnessCon
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures._

/** Shared encoding of proof-term instantiation by Leo substitutions. */
object SubstitutionEncoding {

  /**
    * Translate the term-variable part of a raw Leo substitution into the
    * structured representation consumed by the Lambdapi proof encoder.
    *
    * `sourceVars` must describe the variables in the same index space as
    * `termSubst`. In particular, callers reconstructing RewriteSimp steps must
    * pass the shifted rewrite-rule variables used by Leo's matcher.
    */
  def trackTermSubstitution(termSubst: Subst,
                            typeSubst: Subst,
                            sourceVars: Seq[(Int, Type)]): Either[String, Seq[UniTermSubst]] = {
    val result = Vector.newBuilder[UniTermSubst]

    sourceVars.foreach { case (sourceIndex, _) =>
      termSubst.substBndIdx(sourceIndex) match {
        case BoundFront(targetIndex) if targetIndex == sourceIndex =>
          ()
        case BoundFront(targetIndex) =>
          result += UniTermSubst(sourceIndex, UniTermByBoundVar(targetIndex))
        case TermFront(term) =>
          result += UniTermSubst(
            sourceIndex,
            UniTermByTerm(term.typeSubst(typeSubst), tyVarCount = 0, varmap = Map.empty)
          )
        case TypeFront(_) =>
          return Left(s"Encountered a type entry while reconstructing the term substitution for variable $sourceIndex")
      }
    }

    Right(result.result())
  }

  /**
    * Apply a quantified proof to the arguments described by `termSubst`.
    *
    * Variables retained in `currentVars` are passed through. Variables that are
    * neither substituted nor available in the current clause are instantiated
    * with the standard Lambdapi witness, matching the existing unification
    * encoding behavior.
    */
  def instantiateProofTerm(parentVars: Seq[(Int, Type)],
                           currentVars: Seq[(Int, Type)],
                           termSubst: Seq[UniTermSubst],
                           sharedVarMap: Map[Int, String],
                           parentProof: LpTerm[Level.Obj]): LpTerm[Level.Obj] = {
    val currentBoundIndices = currentVars.map(_._1)
    val parentVarTypes = parentVars.toMap
    val termToApply = termSubst.iterator.map { subst =>
      subst.sourceIndex -> encodeSubstitutionRhs(subst.rhs, currentBoundIndices, sharedVarMap, parentVarTypes)
    }.toMap

    val orderedTerms: Seq[Arg[Level.Obj]] = parentVars.map { case parentVar @ (sourceIndex, sourceType) =>
      termToApply.getOrElse(sourceIndex,
        if (currentVars.contains(parentVar)) {
          Arg.Explicit[Level.Obj](var2Lp(sourceIndex, sourceType, sharedVarMap))
        } else {
          Arg.Explicit[Level.Obj](LpTerm.App[Level.Obj](lpWitnessCon, Seq(Arg.ExplicitTypeArg[Level.Obj](type2LP(sourceType)))))
        }
      )
    }

    if (orderedTerms.nonEmpty) LpTerm.App(parentProof, orderedTerms)
    else parentProof
  }

  /** Encode one structured term-substitution RHS as a Lambdapi argument. */
  private def encodeSubstitutionRhs(termRhs: UniTermRhs,
                                    currentBoundIndices: Seq[Int],
                                    sharedVarMap: Map[Int, String],
                                    parentVarTypes: Map[Int, Type]): Arg[Level.Obj] = {
    termRhs match {
      case UniTermByBoundVar(targetIndex) =>
        if (currentBoundIndices.contains(targetIndex)) {
          Out.lp_debug_info(s"bind by variable with index $targetIndex")
          Arg.Explicit[Level.Obj](LpTerm.Var(Name(sharedVarMap(targetIndex)), None))
        } else {
          Out.lp_debug_info(s"creating a witness term for variable of scope $targetIndex")
          val ty = parentVarTypes(targetIndex)
          Arg.Explicit[Level.Obj](LpTerm.App[Level.Obj](lpWitnessCon, Seq(Arg.ExplicitTypeArg[Level.Obj](type2LP(ty)))))
        }

      case UniTermByTerm(term, _, _) =>
        val currentVarMap = sharedVarMap.view.filterKeys(currentBoundIndices.contains).toMap
        val encTargetTerm = term2LP(term, currentVarMap, suppressReduction = false, replaceUnknownVars = true)
        Out.lp_debug_info(s"bind by term $encTargetTerm")
        Arg.Explicit[Level.Obj](encTargetTerm)
    }
  }
}
