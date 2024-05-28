package main.scala

import main.scala.Lexer.*
import main.scala.Names.*
import main.scala.Type.*
import main.scala.Term.*
import main.scala.Reader.*
import main.scala.utils.ScolException.{ReaderFail, ScolError}

object Parser {
  
  // Token Type Tests
  def isReswordToken(tok: Token): Boolean = tok match {
    case ReswordTok(_) => true
    case _ => false
  }

  def isEqkwdToken(tok: Token): Boolean = tok match {
    case IdentTok(false, NoMark, "=") => true
    case _ => false
  }

  def isReswordTokenWith(p: String => Boolean)(tok: Token): Boolean =
    (isReswordToken(tok) || isEqkwdToken(tok)) && p(tokenName(tok))

  def isReswordTokenIn(xs0: Set[String])(tok: Token): Boolean =
    (isReswordToken(tok) || isEqkwdToken(tok)) && xs0.contains(tokenName(tok))

  def isReswordTokenNotIn(xs0: Set[String])(tok: Token): Boolean =
    isReswordToken(tok) && !xs0.contains(tokenName(tok))

  // Type Token Tests
  def isNonfixTyconstToken(tok: Token): Boolean = tok match {
    case IdentTok(dfx, NoMark, x) =>
      (dfx || hasNonfixTypeFixity(x)) && isTyconstName(x)
    case  NumericTok(dfx, NoMark, x) =>
      (dfx || hasNonfixTypeFixity(x)) && isTyconstName(x)
    case _ => false
  }

  def isInfixTyconstToken(tok: Token): Boolean = tok match {
    case IdentTok(dfx, NoMark, x)  =>
      !dfx && hasInfixTypeFixity(x) && isTyconstName(x)
    case NumericTok(dfx, NoMark, x) =>
      !dfx && hasInfixTypeFixity(x) && isTyconstName(x)
    case _ => false
  }

  def isTyvarToken(tok: Token): Boolean = tok match {
    case IdentTok(_, vmrk, x) =>
      vmrk == TyvarMark || (vmrk == NoMark && !isTyconstName(x))
    case NumericTok(_, vmrk, x) =>
      vmrk == TyvarMark || (vmrk == NoMark && !isTyconstName(x))
    case _ => false
  }

  // Term Token Tests
  def isNonfixToken(tok: Token): Boolean = tok match {
    case IdentTok(dfx, TmvarMark | NoMark, x) =>
      dfx || hasNonfixFixity(x)
    case _ => false
  }

  def isPrefixToken(tok: Token): Boolean = tok match {
    case IdentTok(dfx, TmvarMark | NoMark, x) =>
      !dfx && hasPrefixFixity(x)
    case _ => false
  }

  def isInfixToken(tok: Token): Boolean = tok match {
    case IdentTok(dfx, TmvarMark | NoMark, x) =>
      !dfx && hasInfixFixity(x)
    case _ => false
  }

  def isPostfixToken(tok: Token): Boolean = tok match {
    case IdentTok(dfx, TmvarMark | NoMark, x) =>
      !dfx && hasPostfixFixity(x)
    case _ => false
  }

  def isBinderToken(tok: Token): Boolean = tok match {
    case IdentTok(dfx, TmvarMark | NoMark, x) =>
      !dfx && hasBinderFixity(x)
    case _ => false
  }

  def isVarToken(tok: Token): Boolean = tok match {
    case IdentTok(_, vmrk, x) =>
      vmrk == TmvarMark || (vmrk == NoMark && !isConstName(x))
    case _ => false
  }

  def isConstToken(tok: Token): Boolean = tok match {
    case IdentTok(_, vmrk, x) =>
      vmrk == NoMark && isConstName(x)
    case _ => false
  }

  def isNonfixVarToken(tok: Token): Boolean =
    isVarToken(tok) && isNonfixToken(tok)

  def isNumeralToken(tok: Token): Boolean = tok match {
    case NumericTok(_, vmrk, _) => vmrk == NoMark
    case _ => false
  }

  // Specialised Syntax Reader Combinators
  def parseList[A]: (Int, Reader[List[Token], A]) => Reader[List[Token], List[A]] = readList[List[Token], A]
  val parseStart: Reader[List[Token], Unit] = readStart
  val parseEnd: Reader[List[Token], Unit] = readEnd

  def parseEqualsKwd: Reader[List[Token], String] = @:(tokenName, readElemWith(isEqkwdToken))

  def parseNameWith(testFn: Token => Boolean): Reader[List[Token], String] = @:(tokenName, readElemWith(testFn))

  def parseResword(x: String): Reader[List[Token], String] =
    parseNameWith(isReswordTokenIn(Set(x)))

  def parseReswordIn(xs: Set[String]): Reader[List[Token], String] =
    parseNameWith(isReswordTokenIn(xs))

  def parseReswordNotIn(xs: Set[String]): Reader[List[Token], String] =
    parseNameWith(isReswordTokenNotIn(xs))

  // Syntax Error Support

  // Error Raising Function
  def syntaxError(x: Any): ScolError = ScolError(s"SYNTAX ERROR:", x.toString)

  // Error Combinators
  def /![A](parseFn: Reader[List[Token], A], msg: String, src: List[Token]): (A, List[Token]) =
    try parseFn(src)
    catch {
      case _: ReaderFail => throw syntaxError(msg)
    }

  def ||![A](parseFn: Reader[List[Token], A], errFn: List[Token] => A): Reader[List[Token], A] = 
    parseFn ||| @:(syntaxError, src => (errFn(src), src))

  // Utility
  def ored(items: List[() => String]): () => String =
    () => items.map(_()).mkString(" or ")


}
