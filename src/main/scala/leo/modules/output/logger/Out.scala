package leo.modules.output.logger

import leo.modules.output.Output
import java.util.logging.Level

/**
 * Simple implementation of the [[Logging]] trait
 * with message logging to System.err (FD 1).
 *
 * The verbosity (logging level threshold) is set
 * by the `v` flag from the command-line arguments.
 * @see [[leo.Configuration]]
 */
object Out extends Logging {
  override protected val loggerName = "Console"
  override protected val useParentLoggers = false

  import java.util.logging.{ConsoleHandler, LogRecord, Formatter}
  addLogHandler(
    new ConsoleHandler {
      setLevel(defaultLogLevel)
      setFormatter(new Formatter {
        def format(record: LogRecord) = {
          val lines = record.getMessage.linesWithSeparators
          if (lines.hasNext) {
            val msg = lines.next() + lines.map(str => "% " + str).mkString("")
            s"% [${record.getLevel.getLocalizedName}] \t $msg \n"
          } else {
            ""
          }
        }
      })

      override def publish(record: LogRecord): Unit = {
        super.publish(record)
        flush()
      }
    }
  )

  // Attach a handler specifically for lpLog
  addLpLogHandler(
    new ConsoleHandler {
      setLevel(Level.ALL)
      setFormatter(new Formatter {
        def format(record: LogRecord) = {
          val lines = record.getMessage.linesWithSeparators
          if (lines.hasNext) {
            val msg = lines.next() + lines.map(str => "% " + str).mkString("")
            s"% [LP-DEBUG: ${record.getLevel.getLocalizedName}] \t $msg \n"
          } else {
            ""
          }
        }
      })

      override def publish(record: LogRecord): Unit = {
        super.publish(record)
        flush()
      }
    }
  )


def output(msg: Output): Unit = { println(msg.apply()) }
  def output(msg: String): Unit = { println(msg) }
  def comment(msg: String): Unit = {println(msg.linesWithSeparators.map(str => "% "+str).mkString(""))}

}
