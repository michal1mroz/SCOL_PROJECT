import Lexer.*
import Reader.*
import org.scalatest.funsuite.AnyFunSuite

class LexerTest extends AnyFunSuite {


  test("lexToken basic testing") {
    assert(lexToken(", aijdi".toList) == (ReswordTok(","), " aijdi".toList))
    assert(lexToken("123".toList) == (NumericTok(false,NoMark,"123"),List()))
    assert(lexToken(") rest".toList) == (ReswordTok(")")," rest".toList))
    assert(lexToken("_a12 123".toList) == (IdentTok(false,NoMark,"_a12"), " 123".toList))
    assert(lexToken("\"ABC\"".toList) == (IdentTok(false,NoMark,"ABC"),List()))
    assert(lexToken("\"ABC\\123\"".toList) == (IdentTok(false,NoMark,"ABC{"),List()))
    assert(lexToken("\"Test\\\"\\\\\"\"".toList) == (IdentTok(false,NoMark,"Test\"\\"),List('"')))

    println(lexToken("%123".toList))
    println(lexWhitespace("    ".toList))
//    println(lexToken("    ".toList))
//    println(lexToken("@)#(@)".toList))
//    println(lexToken("0123".toList))
//    println((lexToken >>* lexWhitespace)("1".toList))
//    println(lexList(0, (lexToken >>* lexWhitespace))("531 2".toList))
  }

  test ("lex basic testing") {

  }
}
