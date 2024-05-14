import Lexer.*
import Reader.*
import org.scalatest.funsuite.AnyFunSuite

class LexerTest extends AnyFunSuite {


  test("Lexer compiling") {
    println(lexWhitespace("    ".toList))
    println(lexToken(",".toList))
    println(lexToken(")".toList))
//    println(lexToken("    ".toList))
    println(lexToken("_a12".toList))
    println(lexToken("123".toList))
    println(lexToken("!#!#!#".toList))
    println(lexToken("@)#(@)".toList))
    println(lexToken("0123".toList))
    println((lexToken >>* lexWhitespace)("1".toList))
    println(lexList(0, (lexToken >>* lexWhitespace))("531 2".toList))
  }

}
