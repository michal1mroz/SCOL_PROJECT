package main.scala

import main.scala.Type.*
import main.scala.Term.*
import main.scala.Thm.*
import main.scala.Names.*
import main.scala.Parser.*

object CoreThry {

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

  val trueTm: Term = parseTerm("true")

  setFixity("!", Binder)
  def forallDef: Thm = {
    primNewConstDefinition("!", parseTerm("\\(P:'a->bool). P = (\\x. true)"))
  }

  setFixity("/\\", Infix(20, RightAssoc))
  def conjDef: Thm = {
    primNewConstDefinition("/\\", parseTerm("\\p1 p2. !p. (p1 ==> (p2 ==> p)) ==> p"))
  }

  setFixity("?", Binder)
  def existsDef: Thm = {
    primNewConstDefinition("?", parseTerm("\\(P:'a->bool). P ($@ P)"))
  }

  def oneOneDef: Thm = {
    primNewConstDefinition("ONE_ONE", parseTerm("\\(f:'a->'b). !x1 x2. f x1 = f x2 ==> x1 = x2"))
  }

  def typeDefinitionDef: Thm = {
    primNewConstDefinition(
      "TYPE_DEFINITION", parseTerm("\\P (rep:'b->'a). ONE_ONE rep /\\ (!x. P x <=> (?y. x = rep y))")
    )
  }

  def etaAx: Thm = {
    primNewAxiom("eta_ax", parseTerm("!(f:'a->'b). (\\x. f x) = f"))
  }

  def impAntisymAx: Thm = {
    primNewAxiom(
      "imp_antisym_ax", parseTerm("!p1 p2. (p1 ==> p2) ==> ((p2 ==> p1) ==> (p1 <=>p2))")
    )
  }

  def selectAx: Thm = {
    primNewAxiom(
      "select_ax", parseTerm("!(P:'a->bool) x. P x ==> P ($@ P)")
    )
  }

}
