package leo.modules.output.LPoutput

import leo.Out
import leo.datastructures._
import leo.modules.output.LPoutput.LpLibs.ND.Terms.lpWitnessCon
import leo.modules.output.LPoutput.NewLpDatastructures.LpTerm
import leo.modules.output.LPoutput.NewLpDatastructures.TermEncoding.{term2LP, var2Lp}
import leo.modules.output.LPoutput.NewLpDatastructures.TypeEncoding.type2LP
import leo.modules.output.LPoutput.NewLpDatastructures._

/** Build proof applications from quantified parameters and recorded substitutions.
  * Callers introduce the target context and verify any literal transformations;
  * this object only supplies arguments to an existing proof term.
  */
object SubstitutionEncoding {

  /**
    * Translate the term-variable part of a raw Leo substitution into the
    * structured representation consumed by the Lambdapi proof encoder.
    *
    * `sourceVars` must describe the variables in the same index space as
    * `termSubst`. In particular, callers reconstructing RewriteSimp steps must
    * pass the shifted rewrite-rule variables used by Leo's matcher.
    * `typeSubst` is applied to term fronts here, so the returned term RHSs
    * already use the target type context and must not be specialized again.
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

  /** Instantiate only the term parameters of a proof, in their declaration order.
    * Type arguments must already have been supplied by the caller, and parameter
    * types and term RHSs must already use the current type context.
    * Recorded substitutions take precedence over retained variables; unavailable
    * parameters without a recorded replacement receive a witness of their type.
    */
  def instantiateTermParameters(parentVars: Seq[(Int, Type)],
                                currentVars: Seq[(Int, Type)],
                                termSubst: Seq[UniTermSubst],
                                sharedVarMap: Map[Int, String],
                                parentProof: LpTerm[Level.Obj],
                                typeVars: TypeVariableContext = TypeVariableContext.unrestricted): LpTerm[Level.Obj] =
    applyTermArguments(parentVars, currentVars, termSubst, sharedVarMap, parentProof, Map.empty, typeVars)

  /** Instantiate a clause proof in the child's context, applying type arguments
    * before term arguments. Clause type binders are outermost first in
    * `parent.typeVars.reverse`; term binders follow `parent.implicitlyBound`.
    *
    * `typeSubst` maps source type scopes to target types. Recorded term RHSs
    * must already use those target types: applying the source substitution to
    * them again can change the meaning of their type-variable indices.
    * `typeContext` lets replay retain extra term parameters while using the
    * final child's available types (as in RewriteWithParentVars).
    * With identity substitutions, retained parameters pass through and missing
    * parameters use the individual-type and term-witness fallbacks below.
    */
  def instantiateClauseProof(parent: Clause,
                             child: Clause,
                             sharedVarMap: Map[Int, String],
                             parentProof: LpTerm[Level.Obj],
                             termSubst: Seq[UniTermSubst] = Seq.empty,
                             typeSubst: Subst = Subst.id,
                             typeContext: Option[TypeVariableContext] = None): LpTerm[Level.Obj] =
    instantiateQuantifiedProof(parent.implicitlyBound, parent.typeVars.reverse, child, sharedVarMap,
      parentProof, termSubst, typeSubst, typeContext.getOrElse(TypeVariableContext.forClause(child)))

  /** Instantiate a pointwise proof with explicitly ordered type and term binders.
    * Both parameter lists must match the proof's declaration order. In particular,
    * Skolem definitions follow their recorded dependency order, which can differ
    * from clause order. No inference substitution is applied at this entry point;
    * disappearing parameters receive the same fallbacks as clause parameters.
    */
  def instantiatePointwiseProof(parentVars: Seq[(Int, Type)],
                                parentTypeVars: Seq[Int],
                                child: Clause,
                                sharedVarMap: Map[Int, String],
                                parentProof: LpTerm[Level.Obj]): LpTerm[Level.Obj] =
    instantiateQuantifiedProof(parentVars, parentTypeVars, child, sharedVarMap, parentProof, Seq.empty, Subst.id, TypeVariableContext.forClause(child))

  /** Resolve each source type scope to its target type, preserving the supplied
    * declaration order. Leo's raw substitution uses the same one-based scopes as
    * clauses. This does not yet replace missing target variables with the
    * individual type, so callers can also inspect the intermediate context.
    */
  def resolveTypeInstances(parentTypeVars: Seq[Int], typeSubst: Subst): Seq[(Int, Type)] =
    parentTypeVars.map(scope => scope -> Type.mkVarType(scope).substitute(typeSubst))

  /** Shared implementation for clause proofs and explicitly ordered pointwise
    * proofs. Resolve type arguments first, then use those same instances to
    * determine the expected types of the dependent term arguments.
    */
  private def instantiateQuantifiedProof(parentVars: Seq[(Int, Type)],
                                         parentTypeVars: Seq[Int],
                                         child: Clause,
                                         sharedVarMap: Map[Int, String],
                                         parentProof: LpTerm[Level.Obj],
                                         termSubst: Seq[UniTermSubst],
                                         typeSubst: Subst,
                                         typeVars: TypeVariableContext): LpTerm[Level.Obj] = {
    val resolvedTypes = resolveTypeInstances(parentTypeVars, typeSubst)
    // Resolve the recorded source substitution first. Only its remaining free
    // target parameters are candidates for the replay context's ι fallback.
    val typeInstances = resolvedTypes.map { case (scope, instance) =>
      scope -> type2LP(instance, typeVars)
    }
    // Preserve binder order in the application. The map is only for specializing
    // dependent term types; it must not determine the order of type arguments.
    val typeArgs = typeInstances.map { case (_, instance) => Arg.ExplicitTypeArg[Level.Obj](instance) }
    val instantiatedParent = if (typeArgs.nonEmpty) LpTerm.App(parentProof, typeArgs) else parentProof
    applyTermArguments(parentVars, child.implicitlyBound, termSubst, sharedVarMap,
      instantiatedParent, typeInstances.toMap, typeVars)
  }

  /** Apply the ordered term arguments after type instantiation. `typeInstances`
    * maps source type scopes to complete target types; substitution is simultaneous,
    * so names inside those target types must not be substituted a second time.
    */
  private def applyTermArguments(parentVars: Seq[(Int, Type)],
                                 currentVars: Seq[(Int, Type)],
                                 termSubst: Seq[UniTermSubst],
                                 sharedVarMap: Map[Int, String],
                                 parentProof: LpTerm[Level.Obj],
                                 typeInstances: Map[Int, OlMonoType],
                                 typeVars: TypeVariableContext): LpTerm[Level.Obj] = {
    val currentBoundIndices = currentVars.map(_._1)
    // Parameter types use source scopes, whereas recorded RHSs and retained
    // variables use target scopes. Resolve source indices to their complete
    // instances here; do not feed those instances through the substitution again.
    val sourceTypes = typeVars.copy(instances = typeVars.instances ++ typeInstances)
    val instantiatedVarTypes = parentVars.map { case (index, ty) =>
      index -> type2LP(ty, sourceTypes)
    }.toMap
    val termToApply = termSubst.iterator.map { subst =>
      subst.sourceIndex -> encodeSubstitutionRhs(subst.rhs, currentBoundIndices, sharedVarMap,
        instantiatedVarTypes(subst.sourceIndex), typeVars)
    }.toMap

    val orderedTerms: Seq[Arg[Level.Obj]] = parentVars.map { case (sourceIndex, _) =>
      val expectedType = instantiatedVarTypes(sourceIndex)
      termToApply.getOrElse(sourceIndex,
        // A retained variable must be compared at its instantiated type. Its
        // original type can differ even when its term scope is unchanged.
        currentVars.find { case (index, ty) => index == sourceIndex && type2LP(ty, typeVars) == expectedType } match {
          case Some((index, ty)) => Arg.Explicit[Level.Obj](var2Lp(index, ty, sharedVarMap, typeVars))
          case None =>
            Arg.Explicit[Level.Obj](LpTerm.App[Level.Obj](lpWitnessCon,
              Seq(Arg.ExplicitTypeArg[Level.Obj](expectedType))))
        }
      )
    }

    if (orderedTerms.nonEmpty) LpTerm.App(parentProof, orderedTerms)
    else parentProof
  }

  /** Encode a recorded replacement in the target context. Bound-variable fronts
    * carry an index rather than a typed term, so an unavailable target receives
    * a witness of `expectedType`. Term fronts retain their recorded types and
    * let term2LP replace any unavailable free variables with typed witnesses.
    */
  private def encodeSubstitutionRhs(termRhs: UniTermRhs,
                                    currentBoundIndices: Seq[Int],
                                    sharedVarMap: Map[Int, String],
                                    expectedType: OlMonoType,
                                    typeVars: TypeVariableContext): Arg[Level.Obj] = {
    termRhs match {
      case UniTermByBoundVar(targetIndex) =>
        if (currentBoundIndices.contains(targetIndex)) {
          Out.lp_debug_info(s"bind by variable with index $targetIndex")
          Arg.Explicit[Level.Obj](LpTerm.Var(Name(sharedVarMap(targetIndex)), None))
        } else {
          Out.lp_debug_info(s"creating a witness term for variable of scope $targetIndex")
          // The replacement must inhabit the instantiated source parameter's
          // type, even if the target variable has no surviving clause binder.
          Arg.Explicit[Level.Obj](LpTerm.App[Level.Obj](lpWitnessCon,
            Seq(Arg.ExplicitTypeArg[Level.Obj](expectedType))))
        }

      case UniTermByTerm(term, _, _) =>
        val currentVarMap = sharedVarMap.view.filterKeys(currentBoundIndices.contains).toMap
        val encTargetTerm = term2LP(term, currentVarMap, suppressReduction = false, replaceUnknownVars = true, typeVars = typeVars)
        Out.lp_debug_info(s"bind by term $encTargetTerm")
        Arg.Explicit[Level.Obj](encTargetTerm)
    }
  }
}
