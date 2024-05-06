import Lexer.{/+, lexCharWith}

import scala.util.{Failure, Success, Try}
import Reader.*
import main.scala.Lib.{charImplode, intOfString}
import main.scala.Names.{isAlphanumChar1, isAlphanumChar2, isDigit, isEnumBracket, isKeyword, isNumeric, isPunctuationChar, isSymbolicChar, isWhitespaceChar}
import utils.ScolException.{LexFail, ReaderFail}

import scala.annotation.targetName
import scala.language.postfixOps

object Lexer {

  // Specialised lexical reader combinators
  private def lexCharWith = readElemWith[Char]
  private def lexCharIn = readElemIn[Char]
  private def lexCharNotIn = readElemNotIn[Char]
  private def lexList[A] = readList[List[Char], A]
  private def lexEnd = readEnd[Char]


  @targetName("/+")
  def /+[A](reader: Reader[List[Char], A], msg: String)(input: List[Char]): (A, List[Char]) = {
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

  def helper1: Reader[List[Char], ((Char, Char), Char)] =
    (/+(lexCharWith(isDigit), "Invalid escape character - must be '\\', '\"' or ASCII code") >>>
                    /+(lexCharWith(isDigit), "Missing escape code digits - must be 3 digits")) >>>
                        /+(lexCharWith(isDigit), "Missing escape code digit - must be 3 digits")

  def helper2: (((Char, Char), Char)) => Char =
    (c1c2 : (Char, Char), c3 : Char) => {
    val (c1, c2) = c1c2 // open up the tuple
    val n : Integer = charImplode(List(c1, c2, c3)).toInt
    if (n > 255)
      throw LexFail("Character escape code out of range - must be from 0 to 255")
    else
      n.toChar
  }

  // Token lexer
  private def lexToken0(dfx : Boolean, vmrk : VarMark) : Reader[List[Char], Token] = {

      // Punctuation
      def punctuationReader: Reader[List[Char], Token] = {
        @:((c : Char) => {
          if (dfx || vmrk != NoMark)
            throw LexFail(s"Cannot mark reserved word '$c'")
          else
            ReswordTok(c.toString)
        }, lexCharWith(isPunctuationChar))
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
            lexCharWith(isAlphanumChar1) >>> lexList(0, lexCharWith(isAlphanumChar2)))
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
            lexCharWith(isDigit) >>> lexList(0, lexCharWith(isAlphanumChar2)))
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

      // Quote
      val List1 = List('\\', '"')
      val List2 = List('"')
      val List3 = List('\\')
      def quoteReader: Reader[List[Char], Token] = {
        @:(
          (cs : List[Char]) => {
            val x = cs.mkString
            IdentTok(dfx, vmrk, x)
          },
          lexCharIn(List2) *>>
            lexList(0,
              (lexCharNotIn(List1) |||
                lexCharIn(List3) *>>
                  (lexCharIn(List1) |||
                    @:(helper2, helper1))
            ) >>* /+(lexCharIn(List2), "Missing closing '\"'")))
      }


      punctuationReader ||| alphanumReader |||numericReader ||| symbolicReader ||| quoteReader
  }

  private val lexToken: Reader[List[Char], Token] = lexToken0(false, NoMark)


  private val lexWhitespace: Reader[List[Char], List[Char]] = lexList(0, lexCharWith(isWhitespaceChar))

  def lex(src: List[Char]): List[Token] = {
    try {
      val (tokens, _) = (lexList(0, lexToken >>* lexWhitespace) >>* lexEnd)(src)
      tokens
    } catch {
      case _: ReaderFail => throw LexFail("Undiagnosed lexical error")
    }
  }


  def test[A, B](r1 : Reader[A, B], r2 : Reader[A, B]) : Reader[A, B] = r1 ||| r2
}
