import main.scala.Names.*
import org.scalatest.funsuite.AnyFunSuite
import main.scala.utils.ScolException.ScolFail

class NamesTest extends AnyFunSuite {

  test("isWhitespaceChar should return true for whitespace characters") {
    assert(isWhitespaceChar(' '))
    assert(isWhitespaceChar('\t'))
    assert(isWhitespaceChar('\n'))
    assert(isWhitespaceChar('\f'))
    assert(isWhitespaceChar('\r'))
  }

  test("isWhitespaceChar should return false for non-whitespace characters") {
    assert(!isWhitespaceChar('a'))
    assert(!isWhitespaceChar('1'))
    assert(!isWhitespaceChar('_'))
    assert(!isWhitespaceChar('*'))
  }

  test("isUnprintableChar should return true for unprintable characters") {
    assert(isUnprintableChar('\u0001'))
    assert(isUnprintableChar('\u001F'))
    assert(isUnprintableChar('\u007F'))
  }

  test("isUnprintableChar should return false for printable characters") {
    assert(!isUnprintableChar('a'))
    assert(!isUnprintableChar('1'))
    assert(!isUnprintableChar('_'))
    assert(!isUnprintableChar('*'))
  }
  test("precedenceOk should return true for infix fixities with priority > 0") {
    assert(precedenceOk(Infix(1, LeftAssoc)))
    assert(precedenceOk(Infix(2, RightAssoc)))
  }

  test("precedenceOk should return true for non-infix fixities") {
    assert(precedenceOk(Nonfix))
    assert(precedenceOk(Prefix))
    assert(precedenceOk(Postfix))
    assert(precedenceOk(Binder))
  }

  test("setTypeFixity should set fixity correctly for a type") {
    setTypeFixity("Type1", Infix(2, LeftAssoc))
    assert(getTypeFixity("Type1") == Infix(2, LeftAssoc))
  }

  test("setTypeFixity should reset fixity if already set and trying to set a different one") {
    setTypeFixity("Type3", Nonfix)
    setTypeFixity("Type3", Infix(1, LeftAssoc))
    assert(getTypeFixity("Type3") == Infix(1, LeftAssoc))
  }

  test("resetTypeFixity should reset type fixity to Nonfix") {
    setTypeFixity("Type4", Infix(1, LeftAssoc))
    resetTypeFixity("Type4")
    assert(getTypeFixity("Type4") == Nonfix)
  }

  test("isEnumBracket should return true if the bracket is in the enumeration brackets") {
    theEnumBrackets.put("br1", "zero")
    assert(isEnumBracket("br1"))
  }

  test("isEnumBracket should return false if the bracket is not in the enumeration brackets") {
    assert(!isEnumBracket("br2"))
  }

  test("getEnumBracketZero should return the zero element associated with the bracket") {
    theEnumBrackets.put("br1", "zero")
    assert(getEnumBracketZero("br1") == "zero")
  }

  test("getEnumBracketZero should throw ScolFail if the bracket is not in the enumeration brackets") {
    intercept[ScolFail] {
      getEnumBracketZero("br2")
    }
  }

  test("isEnumOpen should return true if the bracket is the open bracket of an enumeration") {
    theEnumBrackets.put("br1", "zero")
    theEnumDb.put("zero", ("enum", ("br1", "br2")))
    assert(isEnumOpen("br1"))
    assert(!isEnumOpen("br2"))
  }

  test("isEnumClose should return true if the bracket is the close bracket of an enumeration") {
    theEnumBrackets.put("br2", "zero")
    theEnumDb.put("zero", ("enum", ("br1", "br2")))
    assert(isEnumClose("br2"))
    assert(!isEnumClose("br1"))
  }

  test("isEnumOpenclose should return true if the bracket is both the open and close bracket of an enumeration") {
    theEnumDb.clear()
    theEnumBrackets.clear()
    setEnumBrackets("enum", "zero")("br1", "br2")
    println(theEnumDb)
    assert(!isEnumOpenclose("br1 br2"))
    assert(!isEnumOpenclose("br2br1"))
    assert(isEnumOpenclose("br1br2"))
  }

}
