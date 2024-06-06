package main.scala

import main.scala.Lexer.*
import main.scala.Names.*
import main.scala.Type.*
import main.scala.Term.*
import main.scala.Reader.*
import main.scala.utils.HelperType.*
import main.scala.utils.ScolException.{ReaderFail, ScolError}
import main.scala.Lib.*

import scala.annotation.targetName

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

  def parseEqualsKwd: Reader[List[Token], String] = tokenName @: readElemWith(isEqkwdToken) // ?????

  def parseNameWith(testFn: Token => Boolean): Reader[List[Token], String] = tokenName @: readElemWith(testFn)

  def parseResword(x: String): Reader[List[Token], String] =
    parseNameWith(isReswordTokenIn(Set(x)))

  def parseReswordIn(xs: Set[String]): Reader[List[Token], String] =
    parseNameWith(isReswordTokenIn(xs))

  def parseReswordNotIn(xs: Set[String]): Reader[List[Token], String] =
    parseNameWith(isReswordTokenNotIn(xs))

  // Syntax Error Support

  // Error Raising Function
  def syntaxError[A](x: A): ScolError = ScolError(s"SYNTAX ERROR: ", x.toString)

  @targetName("/!")
  def /![A, B](parseFn: Reader[A, B], msg: String)(src: A): (B, A) = {
    try{
      parseFn(src)
    }catch{
      case _: ReaderFail => throw syntaxError(msg)
    }
  }

  // I have no clue how to do this one
  extension[A, B](parseFn: Reader[A, B]) {
    @targetName("/|/!")
    infix def /|/!(errFn: Reader[A, String]): Reader[A, String] = {
      src =>
        try {
          val (x, src_) = parseFn(src)
          (x.toString, src_)
        } catch {
          case _: ReaderFail =>
            val errMsg = errFn(src)
            throw syntaxError(errMsg)
        }
    }
  }
  //infix def ||![A](parseFn: Reader[List[Token], A], errFn: List[Token] => A): A=
  //  val an: List[Token] => (A, List[Token]) = src => (errFn(src), src)
  //  parseFn ||| syntaxError @! an

  // Utility
  def ored(items: List[() => String]): () => String =
    () => items.map(_()).mkString(" or ")



  def endOfQtnErr(items: List[() => String]): Reader[List[Token], String] = {
    val errFn: () => String = () => "Unexpected end of quotation instead of " + ored(items)()
    src => {
      try {
        parseEnd(src)
        throw syntaxError(errFn)
      } catch {
        case e: ScolError => (errFn(), src)
      }
    }
  }

  def earlyReswordErr(rws: Set[String], item: () => String): Reader[List[Token], String] = {
    val errorFn: () => String = () => "Missing " + item()
    src => {
      try {
        parseReswordIn(rws)(src)
        throw syntaxError(errorFn())
      }catch {
        case e: ScolError => (errorFn(), src)
      }

    }
  }

  def hitReswordErr(rws: Set[String], context: () => String): Reader[List[Token], String] = {
    val errorFn: String => String = x => "Unexpected reserved word " + quote(x) + " " + context()
    src => {
      val (res, src_) = parseReswordNotIn(rws)(src)
      (errorFn(res), src_)
    }
  }

  def hitReswordInsteadErr(rws: Set[String], items: List[() => String]): Reader[List[Token], String] = {
    val context: () => String = () => "Instead of " + ored(items)()
    hitReswordErr(rws, context)
  }

  def wrongResowrdErr(rws: Set[String]): Reader[List[Token], String] = {
    val items: List[() => String] = map((rw: String) => () => quote(rw), rws.toList)
    hitReswordInsteadErr(rws, items)
  }


  val leadingTypeReswords = List("(")

  //def noCloseErr0(n: Int, rw1: String, rw2: String )

  def leadingTermResswors: List[String] = {
    List("(", "\\", "if", "let", ":") ++ get_all_enum_info().map {case ((first, _), _) => first}
  }

  def parseItemA(item: () => String, rws: Set[String], parseFn: Reader[List[Token], String]): Reader[List[Token], String] = {
    parseFn /|/! endOfQtnErr(List(item)) /|/! earlyReswordErr(rws, item) /|/! hitReswordInsteadErr(rws, List(item))
  }

  def parseReswordA(rw: String): Reader[List[Token], String] = {
    parseResword(rw) /|/! endOfQtnErr(List(() => quote(rw))) /|/! wrongResowrdErr(Set(rw))
  }

  /*def parseListA(item: () => String, rw: String, parseFn1: Reader[List[Token], String]): Reader[List[Token], String] = {
    val items = List(item, () => quote(rw))

    (x, xs) => (x :: xs) @: (((!>>>) parseItemA(item, Set[rw], parseFn1(List(item))) (parseList(0, parseFn1(items)))))
      >>* (parseResword(".") /|/! endOfQtnErr(items) /|/! hitReswordInsteadErr(Set(rw), items))
  }*/

  def parseItemB(item: () => String, parseFn: Reader[List[Token], String]): Reader[List[Token], String] = {
    parseFn /|/! endOfQtnErr(List(item)) /|/! hitReswordInsteadErr(Set.empty, List(item))
  }

}
