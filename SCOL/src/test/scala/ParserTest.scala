import main.scala.Lexer.*
import main.scala.Names.*
import main.scala.Parser.{parseTerm, parseTermDebug, parseType, parseTypeDebug}
import main.scala.Term.primNewConst
import main.scala.Thm.{Thm, primNewConstDefinition}
import main.scala.Type.{HolType, mkCompType, primNewTyconst}
import main.scala.utils.ScolException.LexFail
import org.scalatest.funsuite.AnyFunSuite

class ParserTest extends AnyFunSuite {


  test("parseType basic testing") {
//    println(parseType("bool->bool"))
    primNewTyconst("->", 1)
    primNewTyconst("bool", 0)
    primNewTyconst("bool1", 1)
    println(parseType("bool->bool1"))
    println(parseType("bool"))
    println(parseTermDebug("bool"))
  }

  test("loading CoreThry"){
    setTypeFixity("->", Infix(5, RightAssoc))
    primNewTyconst("->", 2)

    primNewTyconst("bool", 0)
    val boolTy: HolType = mkCompType("bool", List.empty)

    setFixity("=", Infix(30, NonAssoc))
    primNewConst("=", parseType("'a->'a->bool")) // I'm not sure about this part

    setFixity("==>", Infix(10, RightAssoc))
    primNewConst("==>", parseType("bool->bool->bool"))

    setFixity("@", Binder)
    primNewConst("@", parseType("('a->bool)->'a"))

    setFixity("<=>", Infix(5, NonAssoc))
    primNewConst("<=>", parseType("bool->bool->bool"))

    def trueDef: Thm = {
      primNewConstDefinition("true", parseTerm("(\\(p:bool). p) = (\\p. p)"))
    }

  }
}
