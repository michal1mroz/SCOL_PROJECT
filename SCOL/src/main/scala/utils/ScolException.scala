package main.scala.utils

// reworked class compared to original implementation so that it suits the 
// Scala paradigm more
// You shouldn't really use scol_fail nad scol_error in code instead just throw ScolFail/Error (it's more list Scala)
object ScolException extends Exception{

  // class that stores message and func name
  case class ScolFail(msg: String) extends RuntimeException(s"[SC] FAIL: $msg")
  case class ReaderFail(msg: String) extends RuntimeException(s"[SC] ReaderFail: $msg")
  case class LexFail(msg: String) extends RuntimeException(s"[SC] LexFail: $msg")
  case class TypeFail(msg: String) extends RuntimeException(s"[SC] TypeFail: $msg")
  case class NatLocalFail() extends RuntimeException(s"[SC] NatLocalFail")
  case class EnumLocalFail() extends RuntimeException(s"[SC] EnumLocalFail")
  case class LocalFail() extends RuntimeException(s"[SC] LocalFail")

  /* fixme throw an exception probably should just stick to `throw ScolFail(func, msg)`*/
  def scolFail(msg: String): Nothing = throw ScolFail(msg)

  case class ScolError(err: String, msg: String) extends RuntimeException(s"[SC] $err: $msg")

  // fixme throw an error again better stick to `throw ScolError(err, msg)`
  def scolError(err: String, msg: String): ScolError = ScolError(err, msg)

  def scolWarn(msg : String) : Unit = println("WARNING: " + msg)
  def scolReport(msg : String) : Unit = println("REPORT: " + msg)
  def assertScol(b : Boolean, msg : String): Unit = if !b then throw ScolFail(msg)
  def try0[A, B](f : A => B, x : A, exn : Exception) : B = {
    try {
      f(x)
    }catch
      case _ : Throwable => throw exn
  }


  def internalError(func: String): ScolError = scolError("INTERNAL ERROR", func)

  def buildError(msg: String): ScolError = scolError("BUILD ERROR", msg)

  case object LocalFail extends RuntimeException

  def printExn(e: Throwable): Unit = e match {
    case ScolFail(msg) => println(s"\n[SC] FAIL: $msg")
    case ScolError(err, msg) => println(s"\n[SC] $err: $msg")
    case _ => println(e.toString)
  }

}
