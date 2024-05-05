import scala.util.{Failure, Success, Try}
import Reader.{>>>, @:, *}
import main.scala.Names.{isAlphanumChar1, isAlphanumChar2, isDigit, isEnumBracket, isKeyword, isNumeric, isPunctuationChar, isSymbolicChar, isWhitespaceChar}
import utils.ScolException.{LexFail, ReaderFail}

import scala.annotation.targetName
import scala.language.postfixOps

object Lexer {

  // Specialised lexical reader combinators
  private def lexCharWith = readElemWith[Char]
  private def lexCharIn = readElemIn[List[Char]]
  private def lexCharNotIn = readElemNotIn[List[Char]]
  private def lexList[A] = readList[List[Char], A]
  private def lexEnd = readEnd[Char]


  @targetName("/+")
  def /+[A](reader: List[Char] => (List[Char], A), msg: String)(input: List[Char]): (List[Char], A) = {
    Try(reader(input)) match {
      case Success(value) => value
      case Failure(_) => throw LexFail(msg)
    }
  }

  // Lexical token datatype
  sealed trait VarMark
  case object TyvarMark extends VarMark
  case object TmvarMark extends VarMark
  case object NoMark extends VarMark

  sealed trait Token
  case class IdentTok(isDefix: Boolean, varmark: VarMark, name: String) extends Token
  case class NumericTok(isDefix: Boolean, varmark: VarMark, value: String) extends Token
  case class ReswordTok(name: String) extends Token

  // Token name
  def tokenName(token: Token): String = token match {
    case IdentTok(_, _, x) => x
    case NumericTok(_, _, x) => x
    case ReswordTok(x) => x
  }

  // Token lexer
  private def lexToken0(dfx : Boolean, vmrk : VarMark) : Reader[List[Char], Token] = {

      // Punctuation
      def punctuationReader: Reader[List[Char], Token] = {
        @:[List[Char], Char, Token](
        (c : Char) => {
          if (dfx || vmrk != NoMark)
            throw LexFail(s"Cannot mark reserved word '$c'")
          else
            ReswordTok(c.toString)
        },  lexCharWith(isPunctuationChar))
      }

      // Alphanumeric
      def alphanumReader: Reader[List[Char], Token] = {
        @:[List[Char], (Char, List[Char]), Token ] (
          (c : Char, cs : List[Char]) => {
          val x = (c :: cs).mkString
          if (isKeyword(x) || isEnumBracket(x))
            if (dfx || vmrk != NoMark) {
              throw LexFail(s"Cannot mark reserved word '$x'")
            }else{
              ReswordTok(x)
            }
          else
            IdentTok(dfx, vmrk, x)
        },
          >>>[List[Char], Char, List[Char]]
            (lexCharWith(isAlphanumChar1), lexList(0, lexCharWith(isAlphanumChar2))))
      }

    // Numeric
      def numericReader: Reader[List[Char], Token] = {
        @:[List[Char], (Char, List[Char]), Token](
          (c: Char, cs: List[Char]) => {
            val x = (c :: cs).mkString
            if (!isNumeric(x))
              throw LexFail(s"Non numeric character $c in numeric token $x")

            else if (vmrk == TmvarMark)
              throw LexFail("Cannot mark numeric with '%'")

            else NumericTok(dfx, vmrk ,x)
          },
          >>>[List[Char], Char, List[Char]]
            (lexCharWith(isDigit), lexList(0, lexCharWith(isAlphanumChar2))))
      }

    // Symbolic
      def symbolicReader: Reader[List[Char], Token] = {
        @:[List[Char], List[Char], Token](
          (cs: List[Char]) => {
            val x = cs.mkString
            if (isKeyword(x) || isEnumBracket(x))
              if (dfx || vmrk != NoMark)
                throw LexFail(s"Cannot mark reserved word '$x'")
              else
                ReswordTok(x)
            else
              IdentTok(dfx, vmrk, x)
          },
          lexList(1, lexCharWith(isSymbolicChar)))

      }

      // Quote (You need to implement this)
      def quoteReader: Reader[List[Char], Token] =
        ???


      |||(punctuationReader ,
        |||(alphanumReader,
          |||(numericReader,
          |||(symbolicReader, quoteReader))))
  }

  private val lexToken: Reader[List[Char], Token] = lexToken0(false, NoMark)


  private val lexWhitespace: Reader[List[Char], List[Char]] = lexList(0, lexCharWith(isWhitespaceChar))

  def lex(src: List[Char]): List[Token] = {
    try {
      val (tokens, _) = >>*[List[Char], List[Token], Unit](lexList(0, >>*(lexToken ,lexWhitespace)), lexEnd)(src)
      tokens
    } catch {
      case _: ReaderFail => throw LexFail("Undiagnosed lexical error")
    }
  }

}
