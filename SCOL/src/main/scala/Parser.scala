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
import main.scala.Preterm.{Preterm, Pretype, Ptmtyped, Ptycomp, Ptyvar, atomPretermName, isPrefixPreterm, listMkAbsPreterm, listMkBinderPreterm, listMkCombPreterm, listMkPairPreterm, mkBinPreterm, mkBinPretype, mkCombPreterm, mkCondPreterm, mkEnumPreterm, mkLetPreterm, mkNatPreterm, mkNulltypeConstPreterm, mkNulltypeVarPreterm, pretermToTerm, pretypeToType}
import main.scala.TypeAnal.{checkPretype, detypePreterm, resolvePreterm}
import main.scala.utils.ScolException

import scala.::
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

  private def isConstToken(tok: Token): Boolean = tok match {
    case IdentTok(_, vmrk, x) =>
      vmrk == NoMark && isConstName(x)
    case _ => false
  }

  private def isNonfixVarToken(tok: Token): Boolean =
    isVarToken(tok) && isNonfixToken(tok)

  private def isNumeralToken(tok: Token): Boolean = tok match {
    case NumericTok(_, vmrk, _) => vmrk == NoMark
    case _ => false
  }

  private def parseList[B](n: Int, readFn: Reader[List[Token], B]): Reader[List[Token], List[B]] = {
    src =>
      try {
        val (x, src1) = readFn(src)
        val (xs, src2) = readList(n - 1, readFn)(src1)
        (x :: xs, src2)
      } catch {
        case _: ReaderFail =>
          if (n == 0) {println("here");(Nil, src)}
          else throw ReaderFail("ReadList Failed to finish readList")
      }
  }
  // Specialised Syntax Reader Combinators
//  private def parseList[A]: (Int, Reader[List[Token], A]) => Reader[List[Token], List[A]] = readList[List[Token], A]
  private val parseStart: Reader[List[Token], Unit] = readStart
  private val parseEnd: Reader[List[Token], Unit] = readEnd
  private val parseEnd1: Reader[List[Token], String] = (src) =>
    val (_, lt) = parseEnd(src)
    ("", lt)


  private def parseEqualsKwd: Reader[List[Token], String] = tokenName @: readElemWith(isEqkwdToken)

  private def parseNameWith(testFn: Token => Boolean): Reader[List[Token], String] = tokenName @: readElemWith(testFn)

  private def parseResword(x: String): Reader[List[Token], String] =
    parseNameWith(isReswordTokenIn(List(x)))

  private def parseReswordIn(xs: List[String]): Reader[List[Token], String] =
    parseNameWith(isReswordTokenIn(xs))

  private def parseReswordNotIn(xs: List[String]): Reader[List[Token], String] =
    parseNameWith(isReswordTokenNotIn(xs))

  // Syntax Error Support

  // Error Raising Function
  def syntaxError(x: String): ScolError = ScolError(s"SYNTAX ERROR: ", x)
  private def syntaxErrorTh[A](x: String): A = throw ScolError(s"SYNTAX ERROR: ", x)
  private def syntaxErrorTh2(x: String): String = "SYNTAX ERROR" + x

  @targetName("/!")
  def /![A, B](parseFn: Reader[A, B], msg: String)(src: A): (B, A) = {
    try{
      parseFn(src)
    }catch{
      case _: ReaderFail => throw syntaxError(msg)
    }
  }

  extension[A, B](parseFn: Reader[A, B]) {
    @targetName("/|/!")
    infix def /|/![C](errFn: A => String) : Reader[A, B] = {
//      try{parseFn}catch
//        case _ => throw ReaderFail("FAIL FAIL FAIL")
        parseFn |||
          (syntaxErrorTh @: ((src : A) => (errFn(src), src)))
    }
  }

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


  private def leadingTermResswors: List[String] = {
    List("(", "\\", "if", "let", ":") ++ get_all_enum_info().map {case ((first, _), _) => first}
  }

  private def parseItemA[A](item: () => String, rws: List[String], parseFn: Reader[List[Token], A]): Reader[List[Token], A] = {
    parseFn /|/! endOfQtnErr(List(item)) /|/! earlyReswordErr(rws, item) /|/! hitReswordInsteadErr(rws, List(item))
  }

  private def parseReswordA(rw: String): Reader[List[Token], String] = {
    parseResword(rw) /|/! endOfQtnErr(List(() => quote(rw))) /|/! wrongReswordErr(List(rw))
  }

  def parseListA[A](item: () => String, rw: String, parseFn1: List[() => String] => Reader[List[Token], A]): Reader[List[Token], List[A]] = {
    val items = List(item, () => rw)

    ((x : A, xs : List[A]) => x :: xs ) @:
      (parseItemA(item, List(rw), parseFn1(List(item)))
                              >>> parseList(0, parseFn1(items))
                              >>* (parseResword(".") /|/! endOfQtnErr(items)
                                                      /|/! hitReswordInsteadErr(List(rw), items)))
  }

  private def parseItemB[A](item: () => String, parseFn: Reader[List[Token], A]): Reader[List[Token], A] = {
    parseFn /|/! endOfQtnErr(List(item)) /|/! hitReswordInsteadErr(List.empty, List(item))
  }

  private def parseItemC[A](item: () => String, br1: String, br2: String, parseFn: Reader[List[Token], A]): Reader[List[Token], A] = {
    parseFn
      /|/! noCloseErr(br1, br2)
      /|/! earlyReswordErr(List(br2), item)
      /|/! hitReswordInsteadErr(List(br2), List(item))
  }

  private def parseItemD[A](item: () => String, br1: String, sep: String, br2: String, parseFn: Reader[List[Token], A]): Reader[List[Token], A] = {
    parseFn
      /|/! noCloseErr(br1, br2)
      /|/! earlyReswordErr(List(sep, br2), item)
      /|/! hitReswordInsteadErr(List(sep, br2), List(item))
  }

  private def parseReswordD(br1: String, sep: String, br2: String, x: String): Reader[List[Token], String] = {
    parseResword(x)
      /|/! noCloseErr(br1, br2)
      /|/! wrongReswordErr(List(sep, br2))
  }

  private def parseListD0[A](n: Int, item: () => String, br1: String, sep: String, br2: String, parseFn: Reader[List[Token], A]) = {
    ((xs : List[A]) => {
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

  private def parseListD[A](n: Int, item: () => String, br1: String, sep: String, br2: String, parseFn: Reader[List[Token], A]) = {
    parseResword(br1) *>> parseListD0(n, item, br1, sep, br2, parseFn)
  }

  sealed trait InfixElem[A, B]

  case class InfixOp[A, B](op: A) extends InfixElem[A, B]

  case class InfixArg[A, B](arg: B) extends InfixElem[A, B]

  private def buildRevpolishStep[A, B, C : Ordering](form: String, nameFn: A => String)(elems: List[InfixElem[A, B]], fnhs: List[(A, C, AssocHand)])
                                      (fnh : (A, C, AssocHand), expr : B): (List[InfixElem[A, B]], List[(A, C, AssocHand)]) = {
    val ordering = implicitly[Ordering[C]]
    val (f : A, n : C, h : AssocHand) = fnh
    val foo = (f1: A, n1: C, h1: AssocHand) => ordering.lt(n, n1) || (n == n1 && (if (h == NonAssoc) {
      throw syntaxError("Missing bracket for non-associative " + form + " " + nameFn(f1))
    } else h == LeftAssoc))
    val (fnhs1, fnhs2) = fnhs.span(foo.tupled)
    val y : InfixElem[A, B] = InfixArg(expr)
    val gs1 : List[InfixElem[A, B]] = fnhs1.map { case (f, _, _) => InfixOp(f) }
    val elems1 : List[InfixElem[A, B]] = y :: (gs1.reverse ::: elems)
    val fnhs3 = (f, n, h) :: fnhs2
    (elems1, fnhs3)
  }

  private def buildRevpolish[A, B, C : Ordering](form: String, nameFn: A => String)(expr0: B, fexprs: List[((A, C, AssocHand), B)]): List[InfixElem[A, B]] = {
    val a0 = (List(InfixArg(expr0)): List[InfixElem[A, B]], Nil: List[(A, C, AssocHand)])
    val (elems, fnhs) = fexprs.foldLeft(a0) { (acc, fnhexpr) =>
      buildRevpolishStep(form, nameFn)(acc._1, acc._2)(fnhexpr._1, fnhexpr._2)
    }
    val gs : List[InfixElem[A, B]] = fnhs.map { case (f, _, _) => InfixOp(f) }
    gs.reverse ::: elems
  }


  private def buildInfixExpr[A, B](mkBinFn: (A, B, B) => B)(ys: List[InfixElem[A, B]]): (B, List[InfixElem[A, B]]) = ys match {
    case InfixOp(f) :: (ys0 : List[InfixElem[A, B]]) =>
      val (expr1, ys1) = buildInfixExpr[A, B](mkBinFn).apply(ys0) // weird behaviour. I have to manually specify the type parameters for it to work.
      val (expr2, ys2 : List[InfixElem[A, B]]) = buildInfixExpr[A, B](mkBinFn)(ys1)
      (mkBinFn(f, expr2, expr1), ys2)
    case InfixArg(expr) :: ys0 =>
      (expr, ys0)
    case Nil =>
      throw ReaderFail("buildInfixExpr")
  }

  private def helper1[A, D](f1 : A, n1 : Int, item : (String, A) => String, parseOpFn : Reader[List[Token], (A, Int, D)]): List[Token] => String = {
    (@!:(
      (f2n2_ : (A, Int, D)) => {
        val (f2: A, n2: Int, _: Any) = f2n2_
        if n1 >= n2
        then "Missing " + item("RHS", f1)
        else "Missing " + item("LHS", f2)
      }, parseOpFn))
  }

  private def parseInfixExpr0[A, B, D](form: String, nameFn: A => String)(parseFn: Reader[List[Token], B], parseOpFn: Reader[List[Token], (A, Int, D)])
  : Reader[List[Token], List[((A, Int, D), B)]] = {
    parseList[((A, Int, D), B)].curried(1) apply
    (parseOpFn
      >@> ((f1n1_ : (A, Int, Any)) => {
      val (f1: A, n1: Int, _: Any) = f1n1_
      def item(h: String, f: A) = {h + " for " + form + " " + (nameFn apply f)}
      val item1 = () => item ("RHS", f1)
      parseFn /|/! endOfQtnErr(List (item1)) /|/! helper1 (f1, n1, item, parseOpFn) /|/! hitReswordInsteadErr (Nil, List (item1))
    }
      ))
  }

  // change D to AssocHand
  private def parseInfixExpr[A, B](form: String, nameFn: A => String)(parseFn: Reader[List[Token], B],
                                                                      parseOpFn: Reader[List[Token], (A, Int, AssocHand)], mkBinFn: (A, B, B) => B)
                                  (e0: B, src: List[Token]): (B, List[Token]) = {
    val pF = parseInfixExpr0(form, nameFn)(parseFn, parseOpFn)
    val (fes, src1) = pF(src)
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

  private def helper3 : Reader[List[Token], Pretype] = { x => Ptyvar(x) } @: parseNameWith(isTyvarToken)
  private def helper4 : Reader[List[Token], Pretype] = { x => Ptycomp(x, List()) } @: parseNameWith(isNonfixTyconstToken)
  private def helper5a: Reader[List[Token], Pretype] = {
    parseResword("(")
      *>>
      parseItemD(() => "subtype", "(", ",", ")", (parsePretype0 /|/! noCloseErr("(", ")") /|/! earlyReswordErr(List(","), () => "type parameter")))
    //parseItemD(() => "subtype", "(", ",", ")", parsePretype0)

    // fixme fix this one

  }

  private def helper5b : Pretype => Reader[List[Token], Pretype] = {
      def help(pty: Pretype): ((Object & Equals, String)) => Pretype = {
        //case (ptys: List[Pretype], x: String) => Ptycomp(x, pty :: ptys)
        // Match any list, check for the Pretype type and cast it to List[Pretype].
        // It should work this way
        case (ptys: List[_], x: String) if ptys.forall(_.isInstanceOf[Pretype]) =>
          Ptycomp(x, pty :: ptys.asInstanceOf[List[Pretype]])
        case _ => throw ScolFail("fail")

      }

      def help2a = {
        parseNonfixTyconst /|/!
          @!:(((x) => "Type constant " + x + " is not nonfix"), parseNameWith(isInfixTyconstToken))
      }

      def help2 = {
        parseReswordD("(", ",", ")", ",")
          *>> parseListD0(1, () => "type parameter", "(", ",", ")", parsePretype0)
          >>> parseItemB(() => "type constant", help2a)
      }

      def help3(pty: Pretype): Reader[List[Token], Pretype] = {
        ((_ => pty) @: parseReswordD("(", ",", ")", ")"))
      }

      (pty: Pretype) => {
        help3(pty) ||| (help(pty) @: help2)
      }
  }

  private def helper5 : Reader[List[Token], Pretype] = {
    helper5a *@> helper5b
  }

  private def helper6a[A]: String => A = (x : String) => syntaxErrorTh("Term variable " + x + " encountered in type")
  private def helper6b[A]: Reader[List[Token], String] = {parseNameWith(({
    case IdentTok(_, TmvarMark, _) => true
    case _ => false
    }))
  }

  def helper6 : Reader[List[Token], Pretype] = {
     helper6a @: helper6b
  }

  private def parsePretype2 : Reader[List[Token], Pretype] = {
    helper3 |||
    helper4 |||
    helper5 |||
    helper6
  }

  private def helper2(pty : Pretype): List[String] => Pretype = {
    (xs: List[String]) => {
      xs.foldLeft(pty)((pty1, x: String) => Ptycomp(x, List(pty1)))
    }
  }
  def parsePretype1 : Reader[List[Token], Pretype] = {
      parsePretype2
      |@|
      ((pty : Pretype) => helper2(pty) @: parseList(1, parseNonfixTyconst))
  }
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

  def parseAtomWith(testFn : Token => Boolean) : Reader[List[Token], Preterm] = {
    def help = {
      parseNameWith((tok : Token) => (isVarToken(tok) && testFn(tok)))
    }
    def help1 = {
      (upty : (Preterm, Pretype)) => {
        val (u, pty) = upty
        Ptmtyped(u, pty)
      }
    }
    def help4 = {
      parseAtomWith(testFn) /|/! noCloseErr("(", ")") /|/! earlyReswordErr(List(":"), ()  => "type annotation subterm")
    }
    def help3 = {
      parseResword("(")
      *>> help4
      >>* parseResword(":")
      >>> parseItemC(() => "type annotation type", "(", ")", parsePretype0)
      >>* parseResword(")")
    }


    (mkNulltypeVarPreterm @: help)
    |||
    (mkNulltypeConstPreterm @: help)
    |||
    (help1 @: help3)
  }

  private def hitPrefixErr(items : List[() => String]): List[Token] => String = {
    @!:((ptm : Preterm) => "Unexpected prefix " + quote(atomPretermName(ptm)) + " instead of " + ored(items), parseAtomWith(isPrefixToken))
  }

  private def hitInfixErr(items : List[() => String]): List[Token] => String = {
    @!:((ptm : Preterm) => "Unexpected infix " + quote(atomPretermName(ptm)) + " instead of " + ored(items), parseAtomWith(isInfixToken))
  }

  private def hitNumeralErr(items: List[() => String]): List[Token] => String = {
    @!:((x: String) => "Unexpected numeral " + quote(x) + " instead of " + ored(items), parseNameWith(isNumeralToken))
  }

  private def hitConstErr(eqkwd : Boolean, items: List[() => String]): List[Token] => String = {
    @!:((x: String) => "Unexpected const " + quote(x) + " instead of " + ored(items), parseNameWith((tok : Token) => isConstToken(tok) && !(eqkwd && isEqkwdToken(tok))))
  }

  private def parseInfixOp : Reader[List[Token], (Preterm, Int, AssocHand)] = {
    ((f : Preterm) => {
      val x = atomPretermName(f)
      val (n, h) = getInfixInfo(x)
      (f, n, h)
    }) @: parseAtomWith(isInfixToken)
  }

  def parseNonfixVar(eqkwd : Boolean, items : List[() => String]): Reader[List[Token], Preterm] = {
    parseAtomWith(isNonfixVarToken)
      /|/! (@!:((x : String) => "Variable " + quote(x) + " is not nonfix", parseNameWith(isVarToken)))
      /|/! hitConstErr(eqkwd, items)
      /|/! hitNumeralErr(items)
  }

  private def parsePreterm5 : Reader[List[Token], Preterm] = {
    def help1 = {
      ((x: String) => {
        val x0 = charImplode(charExplode(x).filter(isDigit))
        mkNatPreterm(x0.toInt)
      }) @: parseNameWith(isNumeralToken)
    }

    def help2 = {
      ((comb: ((Preterm, Preterm), Preterm)) => {
        val ((ptm0, ptm1), ptm2) = comb
        mkCondPreterm(ptm0, ptm1, ptm2)
      })
    }

    def help2a = {
      parseResword("if")
        *>> parseItemA(() => "conditional condition", List("then"), parsePreterm1)
        >>* parseResword("then")
        >>> parseItemA(() => "conditional then branch", List("else"), parsePreterm1)
        >>* parseResword("else")
        >>> parseItemB(() => "conditional else branch", parsePreterm1)
    }

    def parseLetBindingItem = {
      val item1 = () => "let-binding variable"
      parseItemA(item1, List("="), (parseNonfixVar(true, List(item1))))
        >>* help3a
        >>> parseItemA(() => "let-binding RHS", List("and", "in"), parsePreterm1)
    }

    def help3a = {
      val item2 = () => "\"=\""
      parseReswordA("=") /|/! hitNumeralErr(List(item2))
        /|/! hitConstErr(true, List(item2))
    }

    def help3b[A] : Reader[List[Token], (Object & Equals, Preterm)] = {
      parseResword("let")
        *>> parseListD0[(Preterm, Preterm)](1, () => "let-expression binding", "let", "and", "in", parseLetBindingItem)
        >>> parseItemB[Preterm](() => "let-expression body", parsePreterm1)
    }

    def help4a(br1 : String, br2 : String) : func[List[Preterm], Preterm] = {
      (ptms : List[Preterm]) => mkEnumPreterm(br1, ptms, br2)
    }

   /* def help4 = {
      (br1 : String) => {
        val z = getEnumBracketZero(br1)
        val (_, br2) = getEnumZeroBrackets(z)

        (help4a(br1, br2) @: parseListD0[Preterm](0, () => "enumeration, item", br1, ",", br2, parsePreterm0))
      }
    }*/

    def help5 : String => Preterm = {
      ((br12 : String) => {
        val z = getEnumBracketZero(br12)
        val (br1, br2) = getEnumZeroBrackets(z)
        mkEnumPreterm(br1, Nil, br2)
      })
    }

    def help6 = {
      parseResword("\\")
      *>> parseListA(() => "lambda binding variable", ".", parseNonfixVar.curried(false))
      >>> parseItemB(() => "lambda body", parsePreterm1)
    }

    def help7 = {
      parseAtomWith(isBinderToken)
        >>> parseListA (() => "binding variable", ".", parseNonfixVar.curried(false))
        >>> parseItemB(() => "binder body", parsePreterm1)
    }

    def help8a = {
      parseItemD( () => "subexpression", "(", ",", ")",
        (parsePreterm0 /|/! noCloseErr("(",")")
        /|/! earlyReswordErr(List(",") ,(()=>"pair component"))))
    }

//    def help8b = {
//      (x : Preterm) =>
//        (_ => x) @:
//        parseReswordD("(", ",", ")", ")")
//        |||
//        ((((xs : List[Preterm]) => listMkPairPreterm(x :: xs)) : func[List[Preterm], Preterm]) @:
//        (parseReswordD("(", ",", ")", ",")
//          *>> parseListD0(1, () => "pair component","(", ",", ")", parsePreterm0)))
//    }

    def help9 = {
      (tok : Token) =>
        tok match
          case IdentTok(_, TyvarMark, _) | NumericTok(_, TyvarMark, _) => true
          case _ => false

    }

    try {
      parseAtomWith(isNonfixToken)
      |||
      help1
      |||
      (help2 @: help2a)
//      |||
//      (mkLetPreterm @: help3b)
//      |||
//      (lookahead(parseNameWith(isReswordTokenWith(isEnumOpen))) *@> help4)
      |||
      help5 @: parseNameWith(isReswordTokenWith(isEnumOpenclose))
      |||
      (listMkAbsPreterm @: help6)
      |||
      (((comb : ((Preterm, List[Preterm]), Preterm)) =>
        val ((f, vs), ptm0) = comb
        listMkBinderPreterm(f, vs, ptm0)) @: help7)
      |||
      ((_ => throw RuntimeException("parsePreterm5")) @: lookahead(parseAtomWith(isInfixToken)))
//      |||
//      (parseResword("(") *>> help8a *@> help8b)
      |||
      (((x : String) => syntaxErrorTh("Type variable " + quote(x) + " encountered outside type annotation")) @:
        parseNameWith(help9))

    } catch {
      case _: Throwable => throw ReaderFail("ParsePreterm5")
    }
  }

  private def parsePreterm4 : Reader[List[Token], Preterm] = {
    def help(ptm : Preterm) = {
      ((ptms : List[Preterm]) => listMkCombPreterm(ptm, ptms)) @: (parseList[Preterm].curried(1)(parsePreterm5 /|/! hitPrefixErr(List(() => "as curried fn arg"))))
    }

    parsePreterm5
    |@|
    ((ptm : Preterm) => help(ptm))
  }
  private def parsePreterm3 : Reader[List[Token], Preterm] = {
    def help1 = {
      @!:((f : Preterm) => "Missing argument ofr postfix " + (quote compose atomPretermName)(f), parseAtomWith(isPostfixToken))
    }
    def help2(ptm : Preterm) = {
      ((f : Preterm) => mkCombPreterm(f, ptm)) @: parseAtomWith(isPostfixToken)
    }


    (parsePreterm4 /|/! help1)
    |@|
    ((ptm : Preterm) => help2(ptm))
  }
  private def parsePreterm2 : Reader[List[Token], Preterm] = {
    def help = {
      parseAtomWith(isPrefixToken)
        >@> ((f : Preterm) => {
        def item() = "argument for prefix " + quote(atomPretermName(f))
        parseItemB(item, (parsePreterm2 /|/! hitInfixErr(List(item))))
      } )
    }
    (mkCombPreterm @: help)
  }

  private def parsePreterm1 : Reader[List[Token], Preterm] = {
    def help1 : Reader[List[Token], Preterm] = {
      parsePreterm2 /|/! (@!:((ptm : Preterm) => "Missing LHS for infix " + quote(atomPretermName(ptm)), parseAtomWith(isInfixToken)))
    }
    def help2  = {
      parseInfixExpr("infix", atomPretermName)(parsePreterm2, parseInfixOp, mkBinPreterm).curried
    }
    help1 |@| help2
  }

  private def parsePreterm0 : Reader[List[Token], Preterm] = {
      ((parsePreterm1 /|/! (earlyReswordErr(List(":"), () => "type annotation subterm")))
        |@|
        ((ptm : Preterm) =>
          ((pty : Pretype) => Ptmtyped(ptm, pty)) @:
          (parseResword(":") *>> parseItemB(() => "type annotation type", parsePretype0))
        ))
  }

  private def parsePreterm(src: List[Token]): Preterm = {
    try {
      (/!(parseStart, "Empty type quotation")
        *>> (parsePreterm0 /|/! hitReswordErr(leadingTypeReswords, () => "at start of type"))
        >>* (parseEnd1 /|/! hitReswordErr(Nil, () => "after syntax-correct leading subtype")))(src)._1
    } catch
      case e: ReaderFail => throw ScolFail("Undiagnosed type syntax error")
  }


  def parseType(x : String) : HolType = (pretypeToType compose checkPretype compose parsePretype compose lex compose charExplode)(x)

  def parseTypeDebug(x : String): Unit =
    val ce = charExplode(x)
    println(ce)
    val l = lex(ce)
    println(l)
    val pp = parsePretype(l)
    println(pp)

  def parseTerm(x : String) : Term = (pretermToTerm compose resolvePreterm compose detypePreterm compose parsePreterm compose lex compose charExplode)(x)

  private def stringTail(x : String, i : Int) : String = x.substring(i)

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