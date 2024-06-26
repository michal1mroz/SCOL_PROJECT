package main.scala

import Reader.{Reader, |||}
import main.scala.Lexer.Token
import main.scala.Parser.syntaxError
import main.scala.utils.ScolException.{ReaderFail, ScolError}

import scala.annotation.targetName


//noinspection DuplicatedCode
object Reader {

    type Reader[A, B] = A => (B, A)

    def readList[A, B](n : Int, readFn : Reader[A, B]) : Reader[A, List[B]] = {
      src =>
          try {
            val (x, src1) = readFn(src)
            val (xs, src2) = readList(n - 1, readFn)(src1)
            (x :: xs, src2)
          } catch {
            case _: ReaderFail =>
              if (n <= 0) (Nil, src)
              else throw ReaderFail("Reader Failed to finish readList")
          }
    }

    @targetName("@:")
    def @:[A, B, C](f : B => C, readFn : Reader[A, B]): Reader[A, C] = {
      src =>
        val (x1, src1) = readFn(src)
        (f(x1), src1)
    }

    @targetName("@!:")
    infix def @!:[A, B](f: B => String, readFn: Reader[A, B]): A => String = {
      (src : A) => 
        val (x1, src1) = readFn(src)
        f(x1)
    }

    def lookahead[A, B](readFn : Reader[A, B]) : Reader[A, B] = {
      src =>
        val (x1, _) = readFn(src)
        (x1, src)
    }

    def readWith[A, B](readFn : Reader[A, B], f : B => Boolean) : Reader[A, B] = {
      src =>
        val (x1, src1) = readFn(src)
        if f (x1) then (x1, src1)
        else throw ReaderFail("Test function in readWith failed")
    }

    def readElem[A] : Reader[List[A], A] = {
      case e :: srcTail => (e, srcTail)
      case _ => throw ReaderFail("readElem found no element to read")
    }

    def readElemWith[A](testFn: A => Boolean): Reader[List[A], A] =
      src =>
        readWith(readElem, testFn)(src)

    def readElemIn[A](es: List[A]): Reader[List[A], A] = {
        def testFn(e: A): Boolean = es.contains(e)
        readElemWith(testFn)
    }

    def readElemNotIn[A](es: List[A]): Reader[List[A], A] = {
      def testFn(e: A): Boolean = !es.contains(e)

      readElemWith(testFn)
    }

    def readStart[A] : Reader[List[A], Unit] = src =>
      if (src.nonEmpty) ((), src) else throw ReaderFail("ReadStart failed there is nothing to read")

    def readEnd[A] : Reader[List[A], Unit] = src =>
      if (src.isEmpty) ((), src) else throw ReaderFail("ReadEnd failed there is more to read")


    extension[A, B](readFn1 : Reader[A, B]) {
      @targetName("|||")
      infix def |||(readFn2: Reader[A, B]): Reader[A, B] = {
        src =>
          try {
            readFn1(src)
          } catch {
            case _: ReaderFail => readFn2(src)
          }
      }
      @targetName(">>>")
      infix def >>>[C](readFn2: Reader[A, C]): Reader[A, (B, C)] = {
        src =>
          val (x1, src1) = readFn1(src)
          val (x2, src2) = readFn2(src1)
          ((x1, x2), src2)
      }

      @targetName("*>>")
      infix def *>>[C](readFn2: Reader[A, C]): Reader[A, C] = {
        src =>
          val (x1, src1) = readFn1(src)
          val (x2, src2) = readFn2(src1)
          (x2, src2)
      }

      @targetName(">>*")
      infix def >>*[C](readFn2: Reader[A, C]): Reader[A, B] = {
        src =>
          val (x1, src1) = readFn1(src)
          val (x2, src2) = readFn2(src1)
          (x1, src2)
      }

      @targetName("|@|")
      infix def |@|(readFn2: B => Reader[A, B]): Reader[A, B] = {
        src =>
          val (x1, src1) = readFn1(src)
          try {
            val (x2, src2) = readFn2(x1)(src1)
            (x2, src2)
          } catch {
            case _: ReaderFail => (x1, src1)
          }
      }

      @targetName(">@>")
      infix def >@>[C](readFn2: B => Reader[A, C]): Reader[A, (B, C)] = {
        src =>
          val (x1, src1) = readFn1(src)
          val (x2, src2) = readFn2(x1)(src1)
          ((x1, x2), src2)
      }

      @targetName("*@>")
      infix def *@>[C](readFn2: B => Reader[A, C]): Reader[A, C] = {
        src =>
          val (x1, src1) = readFn1(src)
          val (x2, src2) = readFn2(x1)(src1)
          (x2, src2)
      }

      @targetName("/!")
      infix def /![C](msg: String, src : A): (B, A)  = {
        try {
          readFn1(src)
        }
        catch
          case _ : ReaderFail => throw syntaxError(msg)
      }


//      @targetName("/!!")
//      infix def /!![C](errFn: A => A): Reader[A , B | ScolError] = {
////        val x = syntaxError
////        readFn1 |||
////          syntaxError[A] @: (src : A) => (errFn(src), src)
//      }
    }

  }