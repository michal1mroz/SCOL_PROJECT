package main.scala.utils

import main.scala.Reader.Reader

import scala.annotation.targetName

object HelperType {

  type func[A, B] = A => B

  extension[A, B] (f : func[A, B]) {
    @targetName("@:")
    infix def @:[C](readFn : Reader[C, A]) : Reader[C, B] = {
      src =>
        val (x1, src1) = readFn(src)
        (f(x1), src1)
    }
  }

}
