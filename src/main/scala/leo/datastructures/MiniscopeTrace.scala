package leo.datastructures

/** Decisive source observations for one changed Miniscope result.
  *
  * Positions describe visits in the recursive source traversal. After branch
  * substitutions they need not address the original term or a reverse goal.
  * Binder ordinals are zero-based in the pending prefix, outermost first.
  */
final case class MiniscopeTrace(observations: Vector[MiniscopeObservation])

sealed trait MiniscopeObservation {
  def sourceVisit: Position
  def pendingBinderOrdinal: Int
}

final case class MiniscopeCrossNegation(sourceVisit: Position,
                                        pendingBinderOrdinal: Int) extends MiniscopeObservation

sealed trait MiniscopePush
case object MiniscopeNoPush extends MiniscopePush
case object MiniscopePushLeft extends MiniscopePush
case object MiniscopePushRight extends MiniscopePush
case object MiniscopePushBoth extends MiniscopePush

final case class MiniscopePushAtConnective(sourceVisit: Position,
                                           pendingBinderOrdinal: Int,
                                           movement: MiniscopePush) extends MiniscopeObservation

/** The first blocked binder; every outer binder in the prefix was untested. */
final case class MiniscopeStopAtConnective(sourceVisit: Position,
                                           pendingBinderOrdinal: Int) extends MiniscopeObservation

/** Producer-local pending binder, not retained in the proof object. */
final case class MiniscopeBinder(sourcePosition: Position,
                                 sourceUniversal: Boolean,
                                 storedUniversal: Boolean,
                                 typ: Type)

/** Producer-local decision returned by pushQuants. */
final case class MiniscopePushDecision(binder: MiniscopeBinder,
                                       boundIndex: Int,
                                       occursLeft: Boolean,
                                       occursRight: Boolean,
                                       movement: MiniscopePush)
