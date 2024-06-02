import main.scala.Lexer.*
import main.scala.utils.ScolException.LexFail
import org.scalatest.funsuite.AnyFunSuite

class LexerTest extends AnyFunSuite {


  test("lexToken basic testing") {
    assert(lexToken(", aijdi".toList) == (ReswordTok(","), " aijdi".toList))
    assert(lexToken("123".toList) == (NumericTok(false, NoMark, "123"), List()))
    assert(lexToken(") rest".toList) == (ReswordTok(")"), " rest".toList))
    assert(lexToken("_a12 123".toList) == (IdentTok(false, NoMark, "_a12"), " 123".toList))
    assert(lexToken("a12 123".toList) == (IdentTok(false, NoMark, "a12"), " 123".toList))
    assert(lexToken("\"ABC\"".toList) == (IdentTok(false, NoMark, "ABC"), List()))
    assert(lexToken("\"ABC\\123\"".toList) == (IdentTok(false, NoMark, "ABC{"), List()))
    assert(lexToken("\"Test\\\"\\\\\"\"".toList) == (IdentTok(false, NoMark, "Test\"\\"), List('"')))

    assert(lexToken("%a123".toList) == (IdentTok(false,TmvarMark,"a123"),List()))
    assert(lexToken("'a123".toList) == (IdentTok(false,TyvarMark,"a123"),List()))
    assertThrows[LexFail] {lexToken("' a123".toList)}
//    println(lexToken("$a123".toList))
  }

  test("lexWhitespace basic testing") {
    assert(lexWhitespace("    ".toList) == ("    ".toList, List.empty))
    assert(lexWhitespace(" s  ".toList) == (List(' '), "s  ".toList))
  }

  test("lex basic testing") {
    assert(lex("123 123".toList) == List(NumericTok(false, NoMark, "123"), NumericTok(false, NoMark, "123")))
    assert(lex("_a12 32, 32    'a42   \"hello\"".toList) == List(IdentTok(false, NoMark, "_a12"), NumericTok(false, NoMark, "32"), ReswordTok(","), NumericTok(false, NoMark, "32"), IdentTok(false, TyvarMark, "a42"), IdentTok(false, NoMark, "hello")))
  }
}
