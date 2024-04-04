package utils

class ScolException(func : String, msg : String) extends Exception(msg){

  // class that stores message and func name
  case class ScolFail(func: String, msg: String) extends RuntimeException(s"[SC] FAIL: $func - $msg")

  // fixme throw an exception probably should just stick to `throw ScolFail(func, msg)`
  def scol_fail(func: String, msg: String): Nothing = throw ScolFail(func, msg)

  case class ScolError(err: String, msg: String) extends RuntimeException(s"[SC] $err: $msg")

  // fixme throw an error again better stick to `throw ScolError(err, msg)`
  def scol_error(err: String, msg: String): Nothing = throw ScolError(err, msg)


  def internal_error(func: String): Nothing = scol_error("INTERNAL ERROR", func)

  def build_error(msg: String): Nothing = scol_error("BUILD ERROR", msg)

  case object LocalFail extends RuntimeException

  def print_exn(e: Throwable): Unit = e match {
    case ScolFail(func, msg) => println(s"\n[SC] FAIL: $func - $msg")
    case ScolError(err, msg) => println(s"\n[SC] $err: $msg")
    case _ => println(e.toString)
  }

}
