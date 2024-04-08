import main.scala.Names._
import utils.ScolException.ScolFail

object NamesTest extends App {

    // Test isWhitespaceChar method
    assert(!isWhitespaceChar('a'))
    assert(isWhitespaceChar(' '))
    assert(isWhitespaceChar('\t'))
    assert(isWhitespaceChar('\n'))
    assert(isWhitespaceChar('\f'))
    assert(isWhitespaceChar('\r'))

    // Test isUnprintableChar method
    assert(!isUnprintableChar('a'))
    assert(isUnprintableChar('\u0001'))
    assert(isUnprintableChar('\u001F'))
    assert(isUnprintableChar('\u007F'))
    assert(!isUnprintableChar('\u0080'))
    assert(!isUnprintableChar('\uFFFF'))

    // Add more test cases for other methods...

    println("All tests passed successfully!")
}
