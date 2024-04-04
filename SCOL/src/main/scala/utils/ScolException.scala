package utils

// reworked class compared to original implementation so that it suits the 
// Scala paradigm more
// You shouldn't really use scol_fail nad scol_error in code instead just throw ScolFail/Error (it's more list Scala)
object ScolException extends Exception{

  // class that stores message and func name
  case class ScolFail(msg: String) extends RuntimeException(s"[SC] FAIL: $msg")

  /* fixme throw an exception probably should just stick to `throw ScolFail(func, msg)`*/
  def scol_fail(msg: String): Nothing = throw ScolFail(msg)

  case class ScolError(err: String, msg: String) extends RuntimeException(s"[SC] $err: $msg")

  // fixme throw an error again better stick to `throw ScolError(err, msg)`
  def scol_error(err: String, msg: String): Nothing = throw ScolError(err, msg)


  def internal_error(func: String): Nothing = scol_error("INTERNAL ERROR", func)

  def build_error(msg: String): Nothing = scol_error("BUILD ERROR", msg)

  case object LocalFail extends RuntimeException

  def print_exn(e: Throwable): Unit = e match {
    case ScolFail(msg) => println(s"\n[SC] FAIL: $msg")
    case ScolError(err, msg) => println(s"\n[SC] $err: $msg")
    case _ => println(e.toString)
  }

}
