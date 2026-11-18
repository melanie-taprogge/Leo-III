package leo.modules.output.LPoutput

import leo.Out
import leo.modules.HOLSignature
import leo.datastructures._
import leo.modules.output.LPoutput.LpLibs.ND.Terms.lpWitnessCon
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.{tyVar2LP, type2LP}
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
                           parentProof: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
    instantiateProofTerm(parentVars, currentVars, termSubst, sharedVarMap, parentProof, Map.empty[Name, OlMonoType])

  /** Instantiate a parent in a child context with the same variable scopes.
    * Type variables absent from the child are instantiated at the individual type.
    */
  def instantiateProofTerm(parent: Clause,
                           child: Clause,
                           sharedVarMap: Map[Int, String],
                           parentProof: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
    instantiateProofTerm(parent, child, Seq.empty, sharedVarMap, parentProof)

  /** Instantiate clause type parameters before applying a term substitution.
    * This carries the existing type scopes; it does not replay type substitutions.
    */
  def instantiateProofTerm(parent: Clause,
                           child: Clause,
                           termSubst: Seq[UniTermSubst],
                           sharedVarMap: Map[Int, String],
                           parentProof: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
    instantiateProofTerm(parent.implicitlyBound, parent.typeVars.reverse, child, sharedVarMap,
      parentProof, termSubst)

  /** Instantiate a pointwise proof whose type and term parameters have explicit
    * declaration order. In particular, Skolem definitions follow the recorded
    * dependency order, which need not be the clause's type-binder order.
    */
  def instantiateProofTerm(parentVars: Seq[(Int, Type)],
                           parentTypeVars: Seq[Int],
                           child: Clause,
                           sharedVarMap: Map[Int, String],
                           parentProof: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
    instantiateProofTerm(parentVars, parentTypeVars, child, sharedVarMap, parentProof, Seq.empty)

  private def instantiateProofTerm(parentVars: Seq[(Int, Type)],
                                   parentTypeVars: Seq[Int],
                                   child: Clause,
                                   sharedVarMap: Map[Int, String],
                                   parentProof: LpTerm[Level.Obj],
                                   termSubst: Seq[UniTermSubst]): LpTerm[Level.Obj] = {
    val childTypeScopes = child.typeVars.toSet
    val typeInstances = parentTypeVars.map { scope =>
      val name = tyVar2LP(scope)
      val instance = if (childTypeScopes(scope)) OlMonoType.TyVar(name) else type2LP(HOLSignature.i)
      name -> instance
    }
    val typeArgs = typeInstances.map { case (_, instance) => Arg.ExplicitTypeArg[Level.Obj](instance) }
    val instantiatedParent = if (typeArgs.nonEmpty) LpTerm.App(parentProof, typeArgs) else parentProof
    instantiateProofTerm(parentVars, child.implicitlyBound, termSubst, sharedVarMap,
      instantiatedParent, typeInstances.toMap)
  }

  private def instantiateProofTerm(parentVars: Seq[(Int, Type)],
                                   currentVars: Seq[(Int, Type)],
                                   termSubst: Seq[UniTermSubst],
                                   sharedVarMap: Map[Int, String],
                                   parentProof: LpTerm[Level.Obj],
                                   typeInstances: Map[Name, OlMonoType]): LpTerm[Level.Obj] = {
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
          val witnessType = Substitution.substMonoType(type2LP(sourceType), typeInstances)
          Arg.Explicit[Level.Obj](LpTerm.App[Level.Obj](lpWitnessCon, Seq(Arg.ExplicitTypeArg[Level.Obj](witnessType))))
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
