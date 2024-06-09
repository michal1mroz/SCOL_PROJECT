import main.scala.Lexer.*
import main.scala.Parser.{parseType, parseTypeDebug}
import main.scala.Type.primNewTyconst
import main.scala.utils.ScolException.LexFail
import org.scalatest.funsuite.AnyFunSuite

class ParserTest extends AnyFunSuite {


  test("parseType basic testing") {
//    println(parseType("bool->bool"))
    primNewTyconst("->", 1)
    primNewTyconst("bool", 0)
    primNewTyconst("bool1", 1)
    println(parseType("bool->bool1"))
  }
}
