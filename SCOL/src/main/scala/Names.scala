

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
    case _ => throw new RuntimeException("Not an infix fixity") // FIXME using RuntimeException instead of hol_fail (don't know if it's ok)
  }



}