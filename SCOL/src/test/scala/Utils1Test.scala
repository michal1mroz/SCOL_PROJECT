package scala

import main.scala.Utils1.*
import main.scala.Type.{Tyvar, *}
import main.scala.Term.*
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers.*

class Utils1Test extends AnyFlatSpec {
  "Destroyed type_var" should "be created successfully" in {
    destType(Tyvar("num")) should equal (TypeVarDestructed("num"))
  }

  "Destroyed comp_var" should "be created successfully" in {
    destType(Tycomp("->", List(Tyvar("num"), Tyvar("num")))) should equal (TypeCompDestructed("->", List(Tyvar("num"), Tyvar("num"))))
  }

  "Not bool type in isBoolType" should "return false" in {
    isBoolType(Tyvar("num")) shouldBe false
  }

  "Bool not compound type in isBoolType" should "return false" in {
    isBoolType(Tyvar("bool")) shouldBe false
  }

  "Compound bool type in isBoolType" should "return true" in {
    isBoolType(Tycomp("bool", List.empty)) shouldBe true
  }

  "typeTyvars test" should "be done successfully" in {
    val ty = typeTyVars(Tycomp("->", List(Tycomp("+", List(Tyvar("num"), Tyvar("num"))), Tyvar("string"))))
    ty should equal (List(Tyvar("string"), Tyvar("num")))
  }

  "Type match test" should "be done successfully" in {
    val ty = typeMatch(Tycomp("->", List(Tyvar("a"), Tyvar("a"))), Tycomp("->", List(Tyvar("b"), Tyvar("b"))))
    ty should equal (List((Tyvar("a"), Tyvar("b"))))
  }

  "DestTerm for Tmconst" should "be created successfully" in {
    val ty = destTerm(Tmconst("toString", Tycomp("->", List(Tyvar("num"), Tyvar("string")))))
    ty should equal (TmconstDestructed("toString", Tycomp("->", List(Tyvar("num"), Tyvar("string")))))
  }

  "Const name test" should "work correctly" in {
    val ty = constName(Tmconst("toString", Tycomp("->", List(Tyvar("w"), Tyvar("z")))))
    ty should equal ("toString")
  }

  "Const type test" should "work correctly" in {
    val ty = constType(Tmconst("toString", Tycomp("->", List(Tyvar("w"), Tyvar("z")))))
    ty should equal (Tycomp("->", List(Tyvar("w"), Tyvar("z"))))
  }

  "Var name test" should "work correctly" in {
    varType(Tmvar("a", Tyvar("bool"))) should equal (Tyvar("bool"))
  }

  "ListMkComb test" should "work correctly" in {
    val ty = listMkComb(Tmconst("toString", Tycomp("->", List(Tyvar("w"), Tyvar("z")))), List(Tmconst("a", Tyvar("w"))))
    ty should equal (Tmcomb((Tmconst("toString", Tycomp("->", List(Tyvar("w"), Tyvar("z"))))), Tmconst("a", Tyvar("w"))))
  }

  "mkBin test" should "work correctly" in {
    val expected = Tmcomb(Tmcomb((Tmconst("+", Tycomp("->", List(Tyvar("num"), Tycomp("->", List(Tyvar("num"), Tyvar("num"))))))), Tmconst("1", Tyvar("num"))), Tmconst("2", Tyvar("num")))
    val actual = mkBin(Tmconst("+", Tycomp("->", List(Tyvar("num"), Tycomp("->", List(Tyvar("num"), Tyvar("num")))))), Tmconst("1", Tyvar("num")), Tmconst("2", Tyvar("num")))

    expected should equal (actual)
  }

  "destBin test" should "work correctly" in {
    val actual = destBin(Tmcomb(Tmcomb((Tmconst("+", Tycomp("->", List(Tyvar("num"), Tycomp("->", List(Tyvar("num"), Tyvar("num"))))))), Tmconst("1", Tyvar("num"))), Tmconst("2", Tyvar("num"))))
    val expected = (Tmconst("+", Tycomp("->", List(Tyvar("num"), Tycomp("->", List(Tyvar("num"), Tyvar("num")))))), Tmconst("1", Tyvar("num")), Tmconst("2", Tyvar("num")))

    expected should equal(actual)
  }

  "isBin test" should "work correctly" in {
    val actual = isBin(Tmcomb(Tmcomb(Tmconst("+", Tycomp("->", List(Tyvar("num"), Tycomp("->", List(Tyvar("num"), Tyvar("num")))))), Tmconst("1", Tyvar("num"))), Tmconst("2", Tyvar("num"))))
    actual should equal (true)
  }

  "destCbin test" should "work correctly" in {
    val expect = (Tmconst("1", Tyvar("num")), Tmconst("2", Tyvar("num")))
    val got = destCbin("+")(Tmcomb(Tmcomb(Tmconst("+", Tycomp("->", List(Tyvar("num"), Tycomp("->", List(Tyvar("num"), Tyvar("num")))))), Tmconst("1", Tyvar("num"))), Tmconst("2", Tyvar("num"))))
    got should equal (expect)
  }

  "mkBinder test" should "work correctly" in {
    val f = Tmconst("f", Tycomp("->", List(Tycomp("->", List(Tyvar("num"), Tyvar("num"))), Tyvar("num"))))
    val va = Tmvar("x", Tyvar("num"))
    val trm = Tmconst("1", Tyvar("num"))
    val lambdaAbst = Tmabs(va, trm)

    val expect = Tmcomb(Tmconst("f", Tycomp("->", List(Tycomp("->", List(Tyvar("num"), Tyvar("num"))), Tyvar("num")))), lambdaAbst)
    val got = mkBinder(f, va, trm)
    expect should equal (got)
  }

  "destBinder test" should "work correctly" in {
    val f = Tmconst("f", Tycomp("->", List(Tycomp("->", List(Tyvar("num"), Tyvar("num"))), Tyvar("num"))))
    val va = Tmvar("x", Tyvar("num"))
    val trm = Tmconst("1", Tyvar("num"))
    val lambdaAbst = Tmabs(va, trm)

    val got = destBinder(Tmcomb(Tmconst("f", Tycomp("->", List(Tycomp("->", List(Tyvar("num"), Tyvar("num"))), Tyvar("num")))), lambdaAbst))
    val expect = (f, va, trm)
    expect should equal(got)
  }

  "destCbinder test" should "work correctly" in {
    val f = Tmconst("f", Tycomp("->", List(Tycomp("->", List(Tyvar("num"), Tyvar("num"))), Tyvar("num"))))
    val va = Tmvar("x", Tyvar("num"))
    val trm = Tmconst("1", Tyvar("num"))
    val lambdaAbstr = Tmabs(va, trm)

    val expect = (va, trm)
    val got = destCbinder("f")(Tmcomb(Tmconst("f", Tycomp("->", List(Tycomp("->", List(Tyvar("num"), Tyvar("num"))), Tyvar("num")))), lambdaAbstr))

    expect should equal (got)
  }

  "isBinder test" should "work correctly" in {
    val f = Tmconst("f", Tycomp("->", List(Tycomp("->", List(Tyvar("num"), Tyvar("num"))), Tyvar("num"))))
    val va = Tmvar("x", Tyvar("num"))
    val trm = Tmconst("1", Tyvar("num"))
    val lambdaAbstr = Tmabs(va, trm)

    val got = isBinder(Tmcomb(Tmconst("f", Tycomp("->", List(Tycomp("->", List(Tyvar("num"), Tyvar("num"))), Tyvar("num")))), lambdaAbstr))
    got should equal (true)
  }

  "isBoolTerm test" should "work correctly" in {
    isBoolTerm(Tmconst("True", Tycomp("bool", List.empty)))  should equal (true)
  }

  "destEq test" should "work correctly" in {
    val expect = (Tmconst("1", Tyvar("num")), Tmconst("1", Tyvar("num")))
    val got = destEq(Tmcomb(Tmcomb(Tmconst("=", Tycomp("->", List(Tyvar("num"), Tycomp("->", List(Tyvar("num"), Tycomp("bool", List.empty)))))),
      Tmconst("1", Tyvar("num"))), Tmconst("1", Tyvar("num"))))

    expect should equal (got)
  }

  "isEq test" should "give true" in {
    val got = isEq(Tmcomb(Tmcomb(Tmconst("=", Tycomp("->", List(Tyvar("num"), Tycomp("->", List(Tyvar("num"), Tycomp("bool", List.empty)))))),
      Tmconst("1", Tyvar("num"))), Tmconst("1", Tyvar("num"))))
    got should equal (true)
  }

  "destImp test" should "work correctly" in {
    val expect = (Tmconst("A", Tycomp("bool", List.empty)), Tmconst("B", Tycomp("bool", List.empty)))
    val got = destImp(Tmcomb(Tmcomb(
     Tmconst("==>", Tycomp("->", List(Tycomp("bool", List.empty), Tycomp("->", List(Tycomp("bool", List.empty))), Tycomp("bool", List.empty)))),
      Tmconst("A", Tycomp("bool", List.empty))), Tmconst("B", Tycomp("bool", List.empty))))
    expect should equal (got)
  }

  "isImp test" should "work correctly" in {
    val got = isImp(Tmcomb(Tmcomb(
      Tmconst("==>", Tycomp("->", List(Tycomp("bool", List.empty), Tycomp("->", List(Tycomp("bool", List.empty))), Tycomp("bool", List.empty)))),
      Tmconst("A", Tycomp("bool", List.empty))), Tmconst("B", Tycomp("bool", List.empty))))
    got should equal (true)
  }

  "freeVars test" should "work correctly" in {
    val f = freeVars(Tmcomb(
      Tmconst("~", Tycomp("->", List(Tycomp("bool", List.empty), Tycomp("bool", List.empty)))), Tmvar("a", Tycomp("bool", List.empty))
    ))
    f should equal (List(Tmvar("a", Tycomp("bool", List.empty))))
  }

  "varFreeIn true test" should "give true" in {
    val va = varFreeIn(Tmvar("a", Tycomp("bool", List.empty)), Tmcomb(Tmconst("~", Tycomp("->", List(Tycomp("bool", List.empty), Tycomp("bool", List.empty)))), Tmvar("a", Tycomp("bool", List.empty))))
    va should equal (true)
  }

  "varFreeIn false test" should "give false" in {
    val va = varFreeIn(Tmvar("x", Tycomp("bool", List.empty)), Tmcomb(Tmconst("~", Tycomp("->", List(Tycomp("bool", List.empty), Tycomp("bool", List.empty)))), Tmvar("a", Tycomp("bool", List.empty))))
    va should equal (false)

  }

  "variant variation test" should "work correctly" in {
    val va = variant(List(Tmvar("P", Tycomp("bool", List.empty))), Tmvar("P", Tycomp("bool", List.empty)))
    va should equal (Tmvar("P'", Tycomp("bool", List.empty)))
  }

  "variant no variation test" should "work correctly" in {
    val got = variant(List(Tmvar("Q", Tycomp("bool", List.empty))), Tmvar("P", Tycomp("bool", List.empty)))
    got should equal (Tmvar("P", Tycomp("bool", List.empty)))
  }

}
