import Reader.{Reader, |||}
import utils.ScolException.ReaderFail

import scala.annotation.targetName


//noinspection DuplicatedCode
object Reader {

    type Reader[A, B] = A => (B, A)
//
//      @targetName("|||")
//      infix def |||[A, B](readFn1: Reader[A, B], readFn2: Reader[A, B]): Reader[A, B] = {
//        src =>
//          try {
//            readFn1(src)
//          } catch {
//            case _: ReaderFail => readFn2(src)
//          }
//      }
//
//    @targetName(">>>")
//    infix def >>>[A, B, C](readFn1: Reader[A, B], readFn2: Reader[A, C]): Reader[A, (B, C)] = {
//      src =>
//        val (x1, src1) = readFn1(src)
//        val (x2, src2) = readFn2(src1)
//        ((x1, x2), src2)
//    }
//
//    @targetName("*>>")
//    infix def *>>[A, B, C](readFn1: Reader[A, B], readFn2: Reader[A, C]): Reader[A, C] = {
//      src =>
//        val (x1, src1) = readFn1(src)
//        val (x2, src2) = readFn2(src1)
//        (x2, src2)
//    }
//
//    @targetName(">>*")
//    infix def >>*[A, B, C](readFn1: Reader[A, B], readFn2: Reader[A, C]): Reader[A, B] = {
//      src =>
//        val (x1, src1) = readFn1(src)
//        val (x2, src2) = readFn2(src1)
//        (x1, src2)
//    }
//
//    @targetName("|@|")
//    infix def |@|[A, B](readFn1 : Reader[A, B], readFn2 : B => Reader[A, B]) : Reader[A, B] = {
//      src =>
//        val (x1, src1) = readFn1(src)
//        try{
//          val (x2, src2) = readFn2(x1)(src1)
//          (x2, src2)
//        }catch{
//          case _: ReaderFail => (x1, src1)
//        }
//    }
//
//    @targetName(">@>")
//    infix def >@>[A, B, C](readFn1: Reader[A, B], readFn2: B => Reader[A, C]): Reader[A, (B, C)] = {
//      src =>
//        val (x1, src1) = readFn1(src)
//        val (x2, src2) = readFn2(x1)(src1)
//        ((x1, x2), src2)
//    }
//
//    @targetName("*@>")
//    infix def *@>[A, B, C](readFn1: Reader[A, B], readFn2: B => Reader[A, C]): Reader[A, C] = {
//      src =>
//        val (x1, src1) = readFn1(src)
//        val (x2, src2) = readFn2(x1)(src1)
//        (x2, src2)
//    }

    def readList[A, B](n : Int, readFn : Reader[A, B]) : Reader[A, List[B]] = {
      src =>
        def innerReadList(m: Int, reader: Reader[A, B], source: A): (List[B], A) = {
          try {
            val (x, src1) = reader(source)
            val (xs, src2) = innerReadList(m - 1, reader, src1)
            (x :: xs, src2)
          } catch {
            case _: ReaderFail =>
              if (m == 0) (Nil, source)
              else throw ReaderFail("Reader Failed to finish readList")
          }
        }
        innerReadList(n, readFn, src)
    }

    @targetName("@:")
    infix def @:[A, B, C](f : B => C, readFn : Reader[A, B]): Reader[A, C] = {
      src =>
        val (x1, src1) = readFn(src)
        (f(x1), src1)
    }

    @targetName("@!:")
    infix def @!:[A, B](f: B => String, readFn: Reader[A, B], src : A): String = {
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

    def readElemWith[A](testFn: A => Boolean): Reader[List[A], A] = {
      src => {
        val (x, srcRest) = readElem(src)
        if (testFn(x)) (x, srcRest)
        else throw ReaderFail("Test function in readElemWith failed")
      }
    }

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
    }
}


//implicit class Reader2[A, B](private val r1: Reader1.Reader[A, B]) extends AnyVal {
//  @targetName("|||")
//  infix def |||(r2: Reader1.Reader[A, B]): Reader1.Reader[A, B] = Reader1.|||(r1, r2)
//
//  @targetName(">>>")
//  infix def >>>[C](r2: Reader[A, C]): Reader[A, (B, C)] =
//    Reader1.>>>(r1, r2)
//
//  @targetName("*>>")
//  infix def *>>[C](r2: Reader[A, C]): Reader[A, C] = Reader1.*>>(r1, r2)
//
//  @targetName(">>*")
//  infix def >>*[C](r2: Reader[A, C]): Reader[A, B] = Reader1.>>*(r1, r2)
//
//  @targetName("|@|")
//  extension def |@|(r2: B => Reader[A, B]): Reader[A, B] = Reader1.|@|(r1, r2)
//
//  @targetName(">@>")
//  infix def >@>[C](r2: B => Reader[A, C]): Reader[A, (B, C)] = Reader1.>@>(r1, r2)
//
//  @targetName("*@>")
//  infix def *@>[C](r2: B => Reader[A, C]): Reader[A, C] = Reader1.*@>(r1, r2)
//
//  @targetName("@:")
//  infix def @:[C](f: B => C): Reader[A, C] = Reader1.@:(f, r1)
//
//}
