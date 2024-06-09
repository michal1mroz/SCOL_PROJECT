package main.scala

import main.scala.Lexer.*
import main.scala.Names.*
import main.scala.Type.*
import main.scala.Term.*
import main.scala.Reader.*
import main.scala.utils.HelperType.*
import main.scala.utils.ScolException.{ReaderFail, ScolError, ScolFail, internalError}
import main.scala.Lib.*
import main.scala.Parser./|/!
import main.scala.Preterm.{Preterm, Pretype, Ptycomp, Ptyvar, mkBinPretype, pretermToTerm, pretypeToType}
import main.scala.TypeAnal.{checkPretype, detypePreterm, resolvePreterm}
import main.scala.utils.ScolException

import scala.annotation.{tailrec, targetName}

object Parser {
  
  // Token Type Tests
  private def isReswordToken(tok: Token): Boolean = tok match {
    case ReswordTok(_) => true
    case _ => false
  }

  private def isEqkwdToken(tok: Token): Boolean = tok match {
    case IdentTok(false, NoMark, "=") => true
    case _ => false
  }

  def isReswordTokenWith(p: String => Boolean)(tok: Token): Boolean =
    (isReswordToken(tok) || isEqkwdToken(tok)) && p(tokenName(tok))

  private def isReswordTokenIn(xs0: List[String])(tok: Token): Boolean =
    (isReswordToken(tok) || isEqkwdToken(tok)) && xs0.contains(tokenName(tok))

  private def isReswordTokenNotIn(xs0: List[String])(tok: Token): Boolean =
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
  private def isNonfixToken(tok: Token): Boolean = tok match {
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

  private def isVarToken(tok: Token): Boolean = tok match {
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
  private def parseList[A]: (Int, Reader[List[Token], A]) => Reader[List[Token], List[A]] = readList[List[Token], A]
  val parseStart: Reader[List[Token], Unit] = readStart
  val parseEnd: Reader[List[Token], Unit] = readEnd
  val parseEnd1: Reader[List[Token], String] = (src) =>
    val (_, lt) = parseEnd(src)
    ("", lt)


  def parseEqualsKwd: Reader[List[Token], String] = tokenName @: readElemWith(isEqkwdToken) // ?????

  private def parseNameWith(testFn: Token => Boolean): Reader[List[Token], String] = tokenName @: readElemWith(testFn)

  private def parseResword(x: String): Reader[List[Token], String] =
    parseNameWith(isReswordTokenIn(List(x)))

  private def parseReswordIn(xs: List[String]): Reader[List[Token], String] =
    parseNameWith(isReswordTokenIn(xs))

  private def parseReswordNotIn(xs: List[String]): Reader[List[Token], String] =
    parseNameWith(isReswordTokenNotIn(xs))

  // Syntax Error Support

  // Error Raising Function
  def syntaxError[A](x: A): ScolError = ScolError(s"SYNTAX ERROR: ", x.toString)
  def syntaxErrorTh[A](x: A): Unit = throw ScolError(s"SYNTAX ERROR: ", x.toString)
  def syntaxErrorTh2[A](x: A): String = "SYNTAX ERROR" + x.toString

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
    infix def /|/![C](errFn: C) : Reader[A, B] = {
      parseFn
//        parseFn |||
//          (syntaxErrorTh2 @: ((src : A) => (errFn(src), src)))
    }
  }

  //infix def ||![A](parseFn: Reader[List[Token], A], errFn: List[Token] => A): A=
  //  val an: List[Token] => (A, List[Token]) = src => (errFn(src), src)
  //  parseFn ||| syntaxError @! an

  // Utility
  private def ored(items: List[() => String]): () => String =
    () => items.map(_()).mkString(" or ")

  private def endOfQtnErr(items: List[() => String]): List[Token] => String = {
    @!:(_ => "Unexpected end of quotation instead of " + ored(items)(), parseEnd)
  }

  private def earlyReswordErr(rws: List[String], item: () => String): List[Token] => String = {
    @!:(_ => "Missing " + item(), parseReswordIn(rws))
  }

  private def hitReswordErr(rws: List[String], context: () => String): List[Token] => String = {
    @!:(x => "Unexpected reserved word " + x.toString + " " + context(), parseReswordIn(rws))
  }

  private def hitReswordInsteadErr(rws: List[String], items: List[() => String]): List[Token] => String = {
    hitReswordErr(rws, () => "instead of " + ored(items)())
  }

  private def wrongReswordErr(rws: List[String]): List[Token] => String = {
    hitReswordInsteadErr(rws, rws.map(rw => () => rw))
  }

  private def noCloseErr0(n : Int, rw1 : String, rw2 : String) : Reader[List[Token], Unit] = {
      if n == 0 then throw ReaderFail("noCloseErr0")
      else
        parseList(0, parseReswordNotIn(List(rw1, rw2)))
        *>> ((parseResword(rw1) *>> noCloseErr0(n + 1, rw1, rw2))
            |||
            (parseResword(rw2) *>> noCloseErr0(n - 1, rw1, rw2))
            |||
            parseEnd)
  }

  private def noCloseErr(rw1: String, rw2: String): List[Token] => String = {
    @!:((a: Unit) => "Opening " + rw1 + " but no subsequent " + rw2, noCloseErr0(1, rw1, rw2))
  }

  private val leadingTypeReswords: List[String] = List("(")


  def leadingTermResswors: List[String] = {
    List("(", "\\", "if", "let", ":") ++ get_all_enum_info().map {case ((first, _), _) => first}
  }

  def parseItemA(item: () => String, rws: List[String], parseFn: Reader[List[Token], String]): Reader[List[Token], String] = {
    parseFn /|/! endOfQtnErr(List(item)) /|/! earlyReswordErr(rws, item) /|/! hitReswordInsteadErr(rws, List(item))
  }

  def parseReswordA(rw: String): Reader[List[Token], String] = {
    parseResword(rw) /|/! endOfQtnErr(List(() => quote(rw))) /|/! wrongReswordErr(List(rw))
  }

  def parseListA(item: () => String, rw: String, parseFn1: List[() => String] => Reader[List[Token], String]): Reader[List[Token], List[String]] = {
    val items = List(item, () => rw)

    ((x : String, xs : List[String]) => x :: xs ) @:
      (parseItemA(item, List(rw), parseFn1(List(item)))
                              >>> parseList(0, parseFn1(items))
                              >>* (parseResword(".") /|/! endOfQtnErr(items)
                                                      /|/! hitReswordInsteadErr(List(rw), items)))
  }

  def parseItemB(item: () => String, parseFn: Reader[List[Token], String]): Reader[List[Token], String] = {
    parseFn /|/! endOfQtnErr(List(item)) /|/! hitReswordInsteadErr(List.empty, List(item))
  }

  def parseItemC(item: () => String, br1: String, br2: String, parseFn: Reader[List[Token], String]): Reader[List[Token], String] = {
    parseFn
      /|/! noCloseErr(br1, br2)
      /|/! earlyReswordErr(List(br2), item)
      /|/! hitReswordInsteadErr(List(br2), List(item))
  }

  def parseItemD(item: () => String, br1: String, sep: String, br2: String, parseFn: Reader[List[Token], String]): Reader[List[Token], String] = {
    parseFn
      /|/! noCloseErr(br1, br2)
      /|/! earlyReswordErr(List(sep, br2), item)
      /|/! hitReswordInsteadErr(List(sep, br2), List(item))
  }

  def parseReswordD(br1: String, sep: String, br2: String, x: String): Reader[List[Token], String] = {
    parseResword(x)
      /|/! noCloseErr(br1, br2)
      /|/! wrongReswordErr(List(sep, br2))
  }

  private def parseListD0(n: Int, item: () => String, br1: String, sep: String, br2: String, parseFn: Reader[List[Token], String]) = {
    ((xs : List[String]) => {
      if (xs.length < n)  syntaxError("Missing " + item())
      else xs
    }) @:
      ((_ => Nil) @: parseResword(br2)
      |||
      (((x, xs) => x :: xs) @:
        (parseItemD(item, br1, sep, br2, parseFn)
          >>> parseList(n-1, parseReswordD(br1, sep, br2, sep)
          *>>parseItemD(item, br1, sep, br2, parseFn))
          >>* parseResword(br2))))
  }

  def parseListD(n: Int, item: () => String, br1: String, sep: String, br2: String, parseFn: Reader[List[Token], String]) = {
    parseResword(br1) *>> parseListD0(n, item, br1, sep, br2, parseFn)
  }

  sealed trait InfixElem[+A, +B]

  case class InfixOp[A](op: A) extends InfixElem[A, Nothing]

  case class InfixArg[B](arg: B) extends InfixElem[Nothing, B]

  private def buildRevpolishStep[A, B, C, D](form: String, nameFn: C => String)(elems: List[InfixElem[A, B]], fnhs: List[(C, Int, AssocHand)])
                                      (fnh : (C, Int, AssocHand), expr : D) = {
    val (f, n, h) = fnh
    val foo = (f1: C, n1: Int, h1: AssocHand) => n < n1 || (n == n1 && (if (h == NonAssoc) {
      throw syntaxError("Missing bracket for non-associative " + form + " " + quote(nameFn(f1)))
    } else h == LeftAssoc))
    val (fnhs1, fnhs2) = fnhs.span(foo.tupled)
    val y = InfixArg(expr)
    val gs1 = fnhs1.map { case (f, _, _) => InfixOp(f) }
    val elems1 = y :: gs1.reverse ::: elems
    val fnhs3 = (f, n, h) :: fnhs2
    (elems1, fnhs3)
  }

//  private def buildRevpolish[A, B](form: String, nameFn: A => String)(expr0: B, fexprs: List[(A,A)]) = {
//    val a0 = (List(InfixArg(expr0)), List() : List[(A, Int, AssocHand)])
//    val (elems, fnhs) = fexprs.foldLeft(a0)(buildRevpolishStep(form, nameFn))
//    val gs = fnhs.map { case (f, _, _) => InfixOp(f) }
//    gs.reverse ::: elems
//  }
  def buildRevpolish[A, B, C, F, D](form: String, nameFn: A => String)(expr0: B, fexprs: List[((A,C, F), D)]) = ???

  private def buildInfixExpr[A, B](mkBinFn: (A, B, B) => B)(ys: List[InfixElem[A, B]]): (B, List[InfixElem[A, B]]) = ys match {
    case InfixOp(f) :: ys0 =>
      val (expr1, ys1) = buildInfixExpr(mkBinFn)(ys0)
      val (expr2, ys2) = buildInfixExpr(mkBinFn)(ys1)
      (mkBinFn(f, expr2, expr1), ys2)
    case InfixArg(expr) :: ys0 =>
      (expr, ys0)
    case Nil =>
      throw ReaderFail("buildInfixExpr")
  }

  private def parseInfixExpr0[A, B, C, D](form: String, nameFn: A => String)(parseFn: Reader[List[Token], B], parseOpFn: Reader[List[Token], (A, C, D)])
  : Reader[List[Token], List[((A, C, D), B)]] = {
    parseList.curried(1)(parseOpFn >@> (_ => parseFn))
  }

  def parseInfixExpr[A, B, C, D, E, F](form: String, nameFn: A => String)(parseFn: Reader[List[Token], D],
                                                              parseOpFn: Reader[List[Token], (A, E, F)], mkBinFn: (A, B, B) => B)
                          (e0: B, src: List[Token]): (B, List[Token]) = {
    val (fes, src1) = parseInfixExpr0(form, nameFn)(parseFn, parseOpFn)(src)
    val ys = buildRevpolish(form, nameFn)(e0, fes)
    val (e, ys1) = buildInfixExpr(mkBinFn)(ys)
    assert(ys1.isEmpty, "parseInfixExpr")
    (e, src1)
  }


  private def parseInfixTyconst: Reader[List[Token], (String, Int, AssocHand)] = {
    { x =>
      val (n, h) = getInfixTypeInfo(x)
      (x, n, h)
    } @: parseNameWith(isInfixTyconstToken)
  }

  private def parseNonfixTyconst: Reader[List[Token], String] =
    parseNameWith(isNonfixTyconstToken) /|/!
      @!: ({ x =>
        s"Unexpected type variable ${x.toString} instead of type constant"
      }, parseNameWith(isTyvarToken) )

//  private def parsePretype2[A] : Reader[A, (String, List[Token])] = {
//    ({ x => Ptyvar(x) } @: parseNameWith(isTyvarToken))|||
//      ( { x => Ptycomp(x, List()) } @: parseNameWith(isNonfixTyconstToken))|||
//      (parseResword("(") *>>
//         parseItemD(() => "subtype", "(", ",", ")", (parsePretype0 /|/! noCloseErr("(", ")")
//                                                                   /|/! earlyReswordErr(List(","), () => "type parameter")))
//        *@> ((pty) =>
//           ((_) => pty) @: parseReswordD("(", ",", ")", ")")
//            |||
//            ((ptys, x) => Ptycomp(x, pty::ptys)) @: (parseReswordD("(", ",", ")", ",")
//              *>> parseListD0(1, ()=>"type parameter", "(", ",", ")", parsePretype0)
//              >>> parseItemB(()=>"type constant", (parseNonfixTyconst /|/!
//              (((x) => "Type constant " + x + " is not nonfix")
//              @!: parseNameWith(isInfixTypeToken))))))
//        )
//    |||
//      ((x) =>
//        syntaxError("Term variable " + x + " encountered in type") @:
//          (parseNameWith(({
//            case IdentTok(_, TmvarMark, _) => true
//            case _ => false
//          })))
//        )
//  }


//  def parsePretype1: Reader[Pretype, (String, List[Token])] = {
//    parsePretype2 |@|
//      ((pty) =>
//        (xs : List[String]) => foldl((pty1 : Pretype, x : String) => Ptycomp(x, List(pty1)))(pty)(xs) @:
//        parseList(1, parseNonfixTyconst))
//  }

//  def parsePretype0 = {
//    (parsePretype1 /|/! (@!:((x) => "Missing LHS for infix type " + x.toString), parseNameWith(isInfixTyconstToken)))
//  }

  def parsePretype1 : Reader[List[Token], Pretype] = ???
  def parsePretype0: Reader[List[Token], Pretype] = {
    (src : List[Token]) =>
      ((parsePretype1 /|/! (@!:((x) => "Missing LHS for infix type " +  x , parseNameWith(isInfixTyconstToken))))
      |@|
      parseInfixExpr("infix type", idFn[String])(parsePretype1, parseInfixTyconst, mkBinPretype).curried)(src)
  }

  private def parsePretype(src: List[Token]): Pretype = {
    try {
      (/!(parseStart, "Empty type quotation")
        *>> (parsePretype0 /|/! hitReswordErr(leadingTypeReswords, () => "at start of type"))
        >>* (parseEnd1 /|/! hitReswordErr(Nil, () => "after syntax-correct leading subtype")))(src)._1
    } catch
      case e: ReaderFail => throw ScolFail("Undiagnosed type syntax error")
  }


  def parseType(x : String) : HolType = (pretypeToType compose checkPretype compose parsePretype compose lex compose charExplode)(x)
  def parsePreterm(src : List[Token]) : Preterm = ???
  def parseTerm(x : String) : Term = (pretermToTerm compose resolvePreterm compose detypePreterm compose parsePreterm compose lex compose charExplode)(x)

  private def stringTail(x : String, i : Int) : String = {
    x.substring(i)
  }

  @tailrec
  private def skipSpace(x : String, i : Int) : Int = {
    if (i < x.length && isWhitespaceChar(x(i))){
      skipSpace(x, i + 1)
    }else{
      i
    }
  }

  def expandHolEquation(x : String) : String = {
    val i = skipSpace(x, 0)
    if (i < x.length && x(i) == ':'){
      val i_ = skipSpace(x, i+1)
      "parse type " + (stringTail(x, i_))
    }else{
      "parse term " + (stringTail(x, i))
    }
  }
}
