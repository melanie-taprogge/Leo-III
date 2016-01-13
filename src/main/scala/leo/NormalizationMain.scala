package leo

import leo.datastructures.blackboard.impl.FormulaDataStore
import leo.datastructures._
import leo.datastructures.blackboard.{Store, FormulaStore}
import leo.datastructures.context.Context
import leo.datastructures.tptp.fof.Formula
import leo.modules.extraction_normalization.{Simplification, ArgumentExtraction}
import leo.modules.{SZSOutput, SZSException, CLParameterParser}
import leo.modules.Utility._
import leo.modules.output.ToTPTP
import leo.datastructures.impl.Signature

import scala.collection.mutable

/**
  * Created by mwisnie on 1/6/16.
  */
object NormalizationMain {

  /**
    * Set of clauses of the problem w/o rewrite
    */
  val clauses = mutable.Set[Clause]()

  /**
    * All positive unit clauses of the problem
    */
  val rewrite = mutable.Set[Literal]()

  /**
    * Conjecture of the problem
    */
  var conjecture : Option[Clause] = None

  var extract0r : ArgumentExtraction = ArgumentExtraction

  /**
    *
    * Reads from an input file and performs
    * <ol>
    *   <li> Argument Extraction </li>
    *   <li> Unit Clause Application </li>
    *   <li> Simplification </li>
    *   <li> ... </li>
    * </ol>
    *
    * @param args - See [[Configuration]] for argument treatment
    */
  def main(args : Array[String]): Unit ={
    try {
      Configuration.init(new CLParameterParser(args))
    } catch {
      case e: IllegalArgumentException => {
        Out.severe(e.getMessage)
        println(helpText)
        return
      }
    }
    if (Configuration.HELP) {
      println(helpText)
      return
    }

    // Begin of the normalization
    try {
      val forms = load(Configuration.PROBLEMFILE)

      Configuration.valueOf("d").foreach
      {s =>
        s.headOption.foreach
        {i =>
          try{
            val iv = i.toInt
            extract0r = new ArgumentExtraction({ x => x.size <= iv})    // NOTE : Change to modify maximal size. (Add debug output)
          } catch {
            case _ : Exception => ()
          }
        }
      }

      // -------------------------------------------
      //          Datastructures
      //-------------------------------------------


      val it : Iterator[FormulaStore] = forms.iterator
      while(it.hasNext){
        val f = it.next()
        if(f.role == Role_Conjecture) {
          conjecture = Some(f.clause)
        } else if (f.role == Role_NegConjecture) {
          conjecture = Some(f.clause.mapLit(_.flipPolarity))
        } else {
          val c = f.clause
          if (c.lits.size == 1 && c.lits.forall(_.equation) && c.lits.forall(_.oriented) && c.lits.forall(_.equational)) {
            // Rewrite Rule TODO better filter (if equational, aber left hat keine Boolschen variablen ... )
            rewrite.add(c.lits.head)
          } else {
            clauses.add(c)
          }
        }
      }

      if(Configuration.isSet("def")) {
        val s = Signature.get
        s.allUserConstants.foreach { k =>
          val m = s(k)
          m.defn.foreach { t =>
            rewrite.add(Literal(Term.mkAtom(k), t, true))
          }
        }
      }

      val argExt : Boolean = Configuration.isSet("a")
      val simpl : Boolean = Configuration.isSet("s")

      // --------------------------------------------
      //            Normalization
      // --------------------------------------------

      import leo.modules.extraction_normalization._

      var change = true

      while(change) {
        change = false

        if(simpl) change &= simplifyAll
        if(argExt) change &= extractAll
      }

      if(Configuration.isSet("e"))
        extensionalRewrite

      // ---------------------------------------------
      //          Output (nach Std.)
      // ---------------------------------------------

      //Typdefinitionen
      var counter : Int = 0
      val rewriteF : Seq[FormulaStore] = rewrite.toSeq.map{l => {counter += 1; Store(counter.toString, Clause(l), Role_Axiom, Context(), 0, NoAnnotation)}}  // TODO is definition ok?
      val clauseF : Seq[FormulaStore] = clauses.toSeq.map{c => {counter += 1; Store(counter.toString, c, Role_Axiom, Context(), 0, NoAnnotation)}}
      val conjectureF : Seq[FormulaStore] = conjecture.toSeq.map{c => Store((counter+1).toString, c, Role_Conjecture, Context(), 0, NoAnnotation)}

      //TODO Print and Format the time need for normalization
      ToTPTP((rewriteF ++(clauseF ++ conjectureF)), !Configuration.isSet("def")).foreach{o => println(o.output)}

      //println(s"Loaded:\n  ${forms.map(ToTPTP(_).output).mkString("\n  ")}")
    } catch {
      case e : SZSException =>  Out.output(SZSOutput(e.status, Configuration.PROBLEMFILE,e.getMessage))
    }
  }

  /**
    * Simplifies all clauses (clauses, rewrite, conjecutre) of the problem.
    *
    * @return true if anything changed
    */
  private def simplifyAll : Boolean = {
    var change = false
    clauses.foreach { c =>
      clauses.remove(c)
      val c1 = Simplification(c)
      clauses.add(c1)
      change &= c == c1
    }
    rewrite.foreach { l =>
      rewrite.remove(l)
      val l1 = Simplification(l)
      rewrite.add(l1)
      change &= l == l1
    }
    conjecture.foreach { c =>
      val c1 = Simplification(c)
      conjecture = Some(c1)
      change &= c == c1
    }
    change
  }

  /**
    * Extracts in one round from each Formula in the current state the arguments.
    *
    * @return
    */
  private def extractAll : Boolean = {
    var change = false

    clauses.foreach { c =>
      clauses.remove(c)
      val (c1, units) = extract0r(c)
      clauses.add(c1)
      units.foreach { case (l, r) => rewrite.add(Literal(l, r, true)) }
      change &= units.isEmpty
    }
    rewrite.foreach { l =>
      rewrite.remove(l)
      val (l1, units) = extract0r(l)
      rewrite.add(l1)
      units.foreach { case (l, r) => rewrite.add(Literal(l, r, true)) }
      change &= units.isEmpty
    }
    conjecture.foreach { c =>
      val (c1, units) = extract0r(c)
      conjecture = Some(c1)
      units.foreach { case (l, r) => rewrite.add(Literal(l, r, true)) }
      change &= units.isEmpty
    }
    change
  }

  /**
    * Performs boolean and functional extension on rewrite rules.
    */
  private def extensionalRewrite : Unit = {
    import leo.modules.calculus._
    import leo.modules.seqpproc.{FuncExt, BoolExt}
    rewrite.foreach{ l : Literal =>
      rewrite.remove(l)
      val fun_l : Literal= if(FuncExt.canApply(l)) FuncExt(freshVarGen(Clause(l)), Seq(l)).headOption.fold(l)(l1 => l1) else l
      if(BoolExt.canApply(fun_l)) {
        val (bool_t, bool_f) = BoolExt(fun_l)
        clauses.add(Clause(bool_t))
        clauses.add(Clause(bool_f))
      } else {
        clauses.add(Clause(fun_l))
      }
    }
  }

  private def helpText : String = {
    val sb = StringBuilder.newBuilder
    sb.append("Normalize -- A Higher-Order Normalization Tool\n")
    sb.append("Christoph Benzmüller, Alexander Steen, Max Wisniewski and others.\n\n")
    sb.append("Usage: ... PROBLEM_FILE [OPTIONS]\n")
    sb.append("Options:\n")

    sb.append("-e \t\tFull extensional handeling for rewrite rules.")
    sb.append("-a \t\tEnables argument extraction.")
    sb.append("-s \t\tEnables simplification")
    sb.append("--def \t\tHandles definitions as unit equations.")
    sb.append("-d N \t\t maximal depth of argument extraction\n")
    sb.append("--ne N \t\t non exhaustively.  Will iterate N(=1 std) times.\n")
    sb.append("-h \t\t display this help message\n")

    sb.toString()
  }
}
