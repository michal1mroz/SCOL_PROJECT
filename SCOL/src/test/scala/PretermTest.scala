import Preterm.*
import main.scala.Names.{Infix, LeftAssoc, setTypeFixity}
import main.scala.Type.{HolType, Tycomp, Tyvar}
import org.scalatest.funsuite.AnyFunSuite
import utils.ScolException.ScolFail

class PretermTest extends AnyFunSuite {


  test("Destructor of Ptyvar") {

    val name = "test"
    val pty = Ptyvar(name)
    val ptg = Ptygvar(name)
    val ptComp = Ptycomp("->", List(pty, ptg))

    assert(name == destTyvarPretype(pty))
    assertThrows[ScolFail](destTyvarPretype(ptg))
    assertThrows[ScolFail](destTyvarPretype(ptComp))
  }

  test("Destructor of Ptygvar") {

    val name = "test"
    val pty = Ptyvar(name)
    val ptg = Ptygvar(name)
    val ptComp = Ptycomp("->", List(pty, ptg))

    assert(name == destTygvarPretype(ptg))
    assertThrows[ScolFail](destTygvarPretype(pty))
    assertThrows[ScolFail](destTygvarPretype(ptComp))
  }

  test("Destructor of PtComp") {

    val name = "test"
    val pty = Ptyvar(name)
    val ptg = Ptygvar(name)
    val ptComp = mkFunPretype(pty, ptg)

    assert((pty, ptg) == destFunPretype(ptComp))
    assertThrows[ScolFail](destFunPretype(pty))
    assertThrows[ScolFail](destFunPretype(ptg))
  }


  test("Bin pretypes"){
    val name = "name"
    val pty = Ptyvar(name)
    val ptg = Ptygvar(name)
    val bpty = mkBinPretype(name, pty, ptg)

    // test whether or not the type fixity in destInfixType is checked correctly
    assertThrows[ScolFail](destInfixPretype(bpty))
    setTypeFixity(name, Infix(1, LeftAssoc))
    assert((name, pty, ptg) == destInfixPretype(bpty))
  }

  test("stripInfixPretype should correctly strip infix types") {
    val pretype1 = Ptycomp("+", List(Ptyvar("int"), Ptyvar("int")))
    val pretype2 = Ptycomp("->", List(Ptyvar("bool"), Ptycomp("->", List(Ptyvar("bool"), Ptyvar("bool")))))

    setTypeFixity("+", Infix(1, LeftAssoc))
    setTypeFixity("->", Infix(1, LeftAssoc))

    val (op1, args1) = stripInfixPretype(pretype1)
    val (op2, args2) = stripInfixPretype(pretype2)

    assert(op1 === "+")
    assert(args1 === List(Ptyvar("int"), Ptyvar("int")))

    assert(op2 === "->")
    assert(args2 === List(Ptyvar("bool"), Ptycomp("->", List(Ptyvar("bool"), Ptyvar("bool")))))
  }
  
  val pretype1: Pretype = Ptycomp("+", List(Ptyvar("int"), Ptyvar("int")))
  val type1: HolType = Tycomp("+", List(Tyvar("int"), Tyvar("int")))

  val pretype2: Pretype = Ptyvar("bool")
  val type2: HolType = Tyvar("bool")

  test("pretypeToType converts a Pretype to a Type correctly") {
    assert(pretypeToType(pretype1) == type1)
    assert(pretypeToType(pretype2) == type2)
  }

  test("typeToPretype converts a Type to a Pretype correctly") {
    assert(typeToPretype(type1) == pretype1)
    assert(typeToPretype(type2) == pretype2)
  }
  test("pretypeTyvars should return a list of pretype variables") {
    val pty1 = Ptyvar("a")
    val pty2 = Ptyvar("b")
    val pty3 = Ptygvar("c")
    val pty5 = Ptyvar("e")
    val pty4 = Ptycomp("d", List(pty1, pty2, pty5))

    assert(pretypeTyvars(pty1) == List(pty1))
    assert(pretypeTyvars(pty2) == List(pty2))
    assert(pretypeTyvars(pty3) == List.empty)
    assert(pretypeTyvars(pty4) === List(pty1, pty2, pty5))
  }
}
