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
    setTypeFixity("->", Infix(5, RightAssoc))
    primNewTyconst("->", 2)
    //
    primNewTyconst("bool", 0)
    val boolTy: HolType = mkCompType("bool", List.empty)

    println(parseTermDebug("k"))
//    println(parseType("('a->bool)->'a"))
//    println(parseTermDebug("bool"))
//    setFixity("@", Binder)
//    primNewConst("@", parseType("('a->bool)->'a"))
  }

  test("loading CoreThry"){
    setTypeFixity("->", Infix(5, RightAssoc))
    primNewTyconst("->", 2)
//
    primNewTyconst("bool", 0)
    val boolTy: HolType = mkCompType("bool", List.empty)
//
//    setFixity("=", Infix(30, NonAssoc))
//    primNewConst("=", parseType("'a->'a->bool")) // I'm not sure about this part

    setFixity("==>", Infix(10, RightAssoc))
    primNewConst("==>", parseType("bool->bool->bool"))

    setFixity("@", Binder)
    primNewConst("@", parseType("('a->bool)->'a"))

    setFixity("<=>", Infix(5, NonAssoc))
    primNewConst("<=>", parseType("bool->bool->bool"))

    def trueDef: Thm = {
      primNewConstDefinition("true", parseTerm("(\\(p:bool). p) = (\\p. p)"))
    }
    println(trueDef)

  }
}
