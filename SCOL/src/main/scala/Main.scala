package main.scala

import main.scala.Lexer.lex
import main.scala.Names.{Infix, NonAssoc, RightAssoc, isNumeric, setFixity, setTypeFixity}
import main.scala.Parser.parseType
import main.scala.Term.primNewConst
import main.scala.Type.{HolType, mkCompType, primNewTyconst}
import main.scala.TypeAnal.*


@main
def mAin(): Unit = {
    
    
    println(lex("a".toList))
    println(lex("1 12".toList))
    println(lex("(12)\\".toList))
    println(lex("\\(\"23\")\\".toList))

    setTypeFixity("->", Infix(5, RightAssoc))
    primNewTyconst("->", 2)

    primNewTyconst("bool", 0)
    val boolTy: HolType = mkCompType("bool", List.empty)
    setFixity("=", Infix(30, NonAssoc))
    primNewConst("=", parseType("'a->'a->bool"))

    println(lex("12=11".toList))

}