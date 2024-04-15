package main.scala

import Lib.quote
import utils.ScolException.{ScolFail, scolReport, scolWarn}

import scala.collection.mutable
import scala.collection.mutable.HashMap

object Names {

  sealed trait Hand

  case object Left extends Hand

  case object Right extends Hand


  sealed trait AssocHand

  case object LeftAssoc extends AssocHand
  

  case object RightAssoc extends AssocHand

  case object NonAssoc extends AssocHand

  def isWhitespaceChar(c : Char) : Boolean = c match {
    case '\t' | '\n' | '\f' | '\r' | ' ' => true
    case _ => false
  }

  def isUnprintableChar(c : Char) : Boolean = {
    val asciiCode : Int = c.toInt;
    asciiCode < 32 | asciiCode > 126
  }

  def isLowercase(c: Char) : Boolean = c  >= 'a' && c <= 'z'
  def isUppercase(c: Char) : Boolean = c  >= 'A' && c <= 'Z'

  def isLetter(c : Char) : Boolean = isLowercase(c) || isUppercase(c)

  def isDigit(c : Char) : Boolean = c >= '0' || c <= '9'

  def isAlphanumChar1(c : Char) : Boolean = isLetter(c) || c == '_'
  def isAlphanumChar2(c : Char) : Boolean = isLetter(c) || isDigit(c) || c == '_' || c == '\''

  def isAlphanumeric(s : String) : Boolean = {
    val cs = s.toList
    cs match
      case c1 :: cs2 => isAlphanumChar1(c1) && cs2.forall(isAlphanumChar2)
      case Nil => false
  }

  def isNumeric(s : String): Boolean = {
    val cs = s.toList
    cs match
      case c1 :: cs2 => isDigit(c1) && cs2.forall((c) => isDigit(c) || c == '_')
      case Nil => false
  }

  def isSymbolicChar(c : Char) : Boolean =  c match{
    case '!' | '#' | '&' | '*' | '+' | '-' | '.' | '/'
      | ';' | '<' | '=' | '>' | '?' | '@'
      | '[' | '\\' | ']' | '^' | '{' | '|' | '}' | '~' => true
    case _ => false
  }

  def isSymbolic(s : String) : Boolean = {
    val cs = s.toList
    cs.forall(isSymbolicChar) && cs.nonEmpty
  }

  def isPunctuationChar(c: Char): Boolean = {
    c match {
      case '(' | ')' | ',' | ':' => true
      case _ => false
    }
  }

  def isKeyword(x: String): Boolean = {
    x match {
      case "\\" | "." | "|-" | "if" | "then" | "else" | "let" | "and" | "in" => true
      case _ => false
    }
  }



  sealed trait Fixity

  case object Nonfix extends Fixity

  case object Prefix extends Fixity

  case class Infix(priority: Int, associativity: AssocHand) extends Fixity {
    require(priority > 0, "Infix priority must be > 0")
  }

  case object Postfix extends Fixity

  case object Binder extends Fixity


  //FIXME Note that we still keep that function for integrity with original implementation, but it is
  // strictly not necessary since we require n > 0 in Infix constructor
  def precedenceOk(fxty : Fixity) : Boolean = fxty match {
    case Infix(n, _) => n > 0
    case _ => true
  }

  def isNonfixFixity(fxty: Fixity): Boolean = fxty == Nonfix

  def isPrefixFixity(fxty: Fixity): Boolean = fxty == Prefix

  def isInfixFixity(fxty: Fixity): Boolean = fxty match {
    case _: Infix => true
    case _ => false
  }

  def isPostfixFixity(fxty: Fixity): Boolean = fxty == Postfix

  def isBinderFixity(fxty: Fixity): Boolean = fxty == Binder

  def infixInfo(fxty: Fixity): (Int, AssocHand) = fxty match {
    case Infix(n, h) => (n, h)
    case _ => throw new IllegalArgumentException("Not an infix fixity")
  }

  val theTypeFixities: mutable.HashMap[String, Fixity] = mutable.HashMap.empty

  def getTypeFixity(x: String): Fixity = theTypeFixities.getOrElse(x, Nonfix)

  // get_all_type_fixities implementation is avoided, I think it is just some OCaml specific thing

  def getInfixTypeInfo(s : String) : (Int, AssocHand) = {
    try {
      infixInfo(getTypeFixity(s))
    }catch{
      case _ : Throwable => throw ScolFail("Provided type " + s + " does not have infix type fixity")
    }
  }

  def hasNonfixTypeFixity(s : String) : Boolean = isNonfixFixity(getTypeFixity(s))
  def hasInfixTypeFixity(s : String) : Boolean = isInfixFixity(getTypeFixity(s))

  def setTypeFixity(s : String, fxty : Fixity) : Unit = {
    require(isNonfixFixity(fxty) || isInfixFixity(fxty))

    val fxty0 = getTypeFixity(s)
      if (fxty == fxty0) scolWarn("Unnecessary setting of same fixity of " + s + ". Fixity already set for " + fxty)
      else if(fxty0 == Nonfix)
        theTypeFixities.put(s, fxty)
        scolReport("Changed type fixity of " + s + " to " + fxty)
      else scolWarn("Cannot change type fixity of " + s + ", fixity already set to " + fxty)
  }

  def resetTypeFixity(s : String) : Unit = {
    theTypeFixities.put(s, Nonfix)
    scolReport("Type fixity of " + s + " reset to Nonfix.")
  }


  private val theFixities: mutable.HashMap[String, Fixity] = mutable.HashMap.empty

  def getFixity(x: String): Fixity = theFixities.getOrElse(x, Nonfix)

  def getInfixInfo(s: String): (Int, AssocHand) = {
    try {
      infixInfo(getFixity(s))
    } catch {
      case _: Throwable => throw ScolFail("Provided type " + s + " does not have infix type fixity")
    }
  }

  def hasNonfixFixity(s : String) : Boolean = isNonfixFixity(getFixity(s))
  def hasPrefixFixity(s : String) : Boolean = isPrefixFixity(getFixity(s))
  def hasInfixFixity(s : String) : Boolean = isInfixFixity(getFixity(s))
  def hasPostfixFixity(s : String) : Boolean = isPostfixFixity(getFixity(s))
  def hasBinderFixity(s : String) : Boolean = isBinderFixity(getFixity(s))

  def setFixity(s: String, fxty: Fixity): Unit = {
    require(isNonfixFixity(fxty) || isInfixFixity(fxty))

    val fxty0 = getFixity(s)
    if (fxty == fxty0) scolWarn("Unnecessary setting of same fixity of " + s + ". Fixity already set for " + fxty)
    else if (fxty0 == Nonfix)
      theFixities.put(s, fxty)
      scolReport("Changed type fixity of " + s + " to " + fxty)
    else scolWarn("Cannot change type fixity of " + s + ", fixity already set to " + fxty)
  }

  def resetFixity(s: String): Unit = {
    theFixities.put(s, Nonfix)
    scolReport("Type fixity of " + s + " reset to Nonfix.")
  }

  val theEnumDb : mutable.HashMap[String, (String, (String, String))] = mutable.HashMap.empty

  def getEnumZeroOp(s : String) : String = theEnumDb(s) match
    case (x, _) => x

  def getEnumZeroBrackets(s : String) : (String, String) = theEnumDb(s) match
    case (_, y) => y

  def get_all_enum_info(): List[((String, String), (String, String))] = {
    val zys = theEnumDb.toList
    zys.map { case (z, (f, (br1, br2))) =>
      ((z, f), (br1, br2))
    }
  }

  val theEnumBrackets : mutable.HashMap[String, String] = mutable.HashMap.empty


  def isEnumBracket(s : String) : Boolean = theEnumBrackets.contains(s)

  def getEnumBracketZero(s : String) : String = theEnumBrackets.get(s) match
    case None => throw ScolFail("Didn't find such bracket : " + s + " in theEnumBracket.")
    case Some(x) => x

  def isEnumOpen(s : String) : Boolean = {
    try {
      val z = getEnumBracketZero(s)
      val (br1, br2) = getEnumZeroBrackets(z)
      s == br1
    }
    catch {
      case _ : Throwable => false
    }
  }

  def isEnumClose(s: String): Boolean = {
    try {
      val z = getEnumBracketZero(s)
      val (br1, br2) = getEnumZeroBrackets(z)
      s == br2
    }
    catch {
      case _: Throwable => false
    }
  }

  def isEnumOpenclose(s: String): Boolean = {
    try {
      val (br1, br2) = getEnumZeroBrackets(getEnumBracketZero(s))
      s == (br1 + br2)
    }
    catch {
      case _: ScolFail => false
    }
  }

  private def checkBracketName(s : String) : Unit = {
    assert(isSymbolic(s) || isAlphanumeric(s), s + " is not a valid bracket name.")
    assert(!isKeyword(s), s + " is a keyword.")
    assert(!isEnumBracket(s), s + " is already an enumeration bracket.")

  }

  def setEnumBrackets(f: String, zero: String)(br1: String, br2: String): Unit = {
    try {
      val br12 = br1 + br2
      assert(!theEnumDb.contains(zero), "theEnumDb doesn't contain provided `zero` element: " + zero)
      checkBracketName(br1)
      checkBracketName(br2)
      assert(br1 != br2, "Open and close brackets must be different")
      checkBracketName(br12)
      val zfs = theEnumDb.values.map{ case (z, (f, _)) => (z, f)}
      assert(zfs.forall(_._2 != f), s"${quote(f)} is already an enumeration constructor")

      println(s"Setting ${quote(br1)} and ${quote(br2)} as enumeration brackets for constructor ${quote(f)} with zero ${quote(zero)}")
      theEnumDb(zero) = (f, (br1, br2))
      theEnumBrackets(br1) = zero
      theEnumBrackets(br2) = zero
      theEnumBrackets(br12) = zero
    } catch {
      case _: Throwable =>
        val (f_, (br1_, br2_)) = theEnumDb(zero)
        assert((f == f_) && (br1 == br1_) && (br2 == br2_), s"${quote(zero)} is already an enumeration zero")
        println(s"Benign setting of same enumeration brackets for constructor ${quote(f)} with zero ${quote(zero)}")
    }
  }


}
