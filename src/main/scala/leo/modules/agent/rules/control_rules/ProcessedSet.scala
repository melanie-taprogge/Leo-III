package leo.modules.agent.rules.control_rules

import leo.datastructures.AnnotatedClause
import leo.datastructures.blackboard.{DataStore, DataType, Result}

import scala.collection.mutable

case object Processed extends DataType

/**
  * Stores the processed Formulas for
  * the algorithm execution in [[leo.modules.control.Control]]
  */
class ProcessedSet  extends DataStore{

  private final val set : mutable.Set[AnnotatedClause] = mutable.HashSet[AnnotatedClause]()

  /**
    * Gets the set of unprocessed clauses.
    * The returned set is immutable.
    *
    * @return Set of unprocessed clauses
    */
  def get : Set[AnnotatedClause] = synchronized(set.toSet)

  /**
    * This method returns all Types stored by this data structure.
    *
    * @return all stored types
    */
  override val storedTypes: Seq[DataType] = Seq(Processed)

  /**
    *
    * Inserts all results produced by an agent into the datastructure.
    *
    * @param r - A result inserted into the datastructure
    */
  override def updateResult(r: Result): Boolean = synchronized {
    val ins1 = r.inserts(Processed)
    val del1 = r.removes(Processed)
    val (del2, ins2) = r.updates(Processed).unzip

    val ins = (ins1 ++ ins2).iterator
    val del = (del1 ++ del2).iterator

    var change = false

    while(del.hasNext){
      del.next match {
        case c : AnnotatedClause =>
          set.remove(c)
          change |= true
        case x => leo.Out.debug(s"Tried to remove $x from Unprocessed Set, but was no clause.")
      }
    }

    while(ins.hasNext) {
      ins.next match {
        case c: AnnotatedClause =>
          set.add(c)
          change |= true
        case x => leo.Out.debug(s"Tried to add $x to Unprocessed Set, but was no clause.")
      }
    }
    change
  }

  /**
    * Removes everything from the data structure.
    * After this call the ds should behave as if it was newly created.
    */
  override def clear(): Unit = synchronized(set.clear())

  /**
    * Returns a list of all stored data.
    *
    * @param t
    * @return
    */
  override protected[blackboard] def all(t: DataType): Set[Any] = t match{
    case Processed => synchronized(set.toSet)
    case _ => Set()

  }
}
