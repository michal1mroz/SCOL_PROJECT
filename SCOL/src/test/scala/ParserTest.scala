import main.scala.Lexer.*
import main.scala.Parser.{parseType, parseTypeDebug}
import main.scala.utils.ScolException.LexFail
import org.scalatest.funsuite.AnyFunSuite

class ParserTest extends AnyFunSuite {


  test("parseType basic testing") {
    printType(parseType("string"))
    parseTypeDebug("string")
  }
}
