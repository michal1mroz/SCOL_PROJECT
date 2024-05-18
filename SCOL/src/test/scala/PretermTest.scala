import Preterm.*
import main.scala.Names.{AssocHand, Infix, LeftAssoc, NonAssoc, RightAssoc, setTypeFixity}
import main.scala.Type.{HolType, Tycomp, Tyvar}
import org.scalatest.funsuite.AnyFunSuite
import utils.ScolException.ScolFail

class PretermTest extends AnyFunSuite {


  test("Destructor of Ptyvar") {

    val name = "test"
    val n = 2
    val pty = Ptyvar(name)
    val ptg = Ptygvar(n)
    val ptComp = Ptycomp("->", List(pty, ptg))

    assert(name == destTyvarPretype(pty))
    assertThrows[ScolFail](destTyvarPretype(ptg))
    assertThrows[ScolFail](destTyvarPretype(ptComp))
  }

  test("Destructor of Ptygvar") {

    val name = "test"
    val n = 2
    val pty = Ptyvar(name)
    val ptg = Ptygvar(n)
    val ptComp = Ptycomp("->", List(pty, ptg))

    assert(n == destTygvarPretype(ptg))
    assertThrows[ScolFail](destTygvarPretype(pty))
    assertThrows[ScolFail](destTygvarPretype(ptComp))
  }

  test("Destructor of PtComp") {

    val name = "test"
    val pty = Ptyvar(name)
    val ptg = Ptygvar(1111)
    val ptComp = mkFunPretype(pty, ptg)

    assert((pty, ptg) == destFunPretype(ptComp))
    assertThrows[ScolFail](destFunPretype(pty))
    assertThrows[ScolFail](destFunPretype(ptg))
  }


  test("Bin pretypes"){
    val name = "name"
    val pty = Ptyvar(name)
    val ptg = Ptygvar(1111)
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
    val pty3 = Ptygvar(1)
    val pty5 = Ptyvar("e")
    val pty4 = Ptycomp("d", List(pty1, pty2, pty5))

    assert(pretypeTyvars(pty1) == List(pty1))
    assert(pretypeTyvars(pty2) == List(pty2))
    assert(pretypeTyvars(pty3) == List.empty)
    assert(pretypeTyvars(pty4) === List(pty1, pty2, pty5))
  }

  test("Test pretypeInst") {
    // Define a substitution list theta
    val theta: List[(Pretype, Pretype)] = List(
      (Ptyvar("a"), Ptygvar(1)), // Substituting Ptyvar("a") with Ptygvar("b")
      (Ptyvar("c"), Ptyvar("d")) // Substituting Ptyvar("c") with Ptyvar("d")
    )

    assert(pretypeInst(theta, Ptyvar("a")) === Ptygvar(1)) // Substitute Ptyvar("a") with Ptygvar("b")
    assert(pretypeInst(theta, Ptyvar("c")) === Ptyvar("d")) // Substitute Ptyvar("c") with Ptyvar("d")
    assert(pretypeInst(theta, Ptyvar("x")) === Ptyvar("x")) // No substitution for Ptyvar("x")

  }

  test("Test pretype_complexity") {
    // Test cases for pretype_complexity
    assert(pretypeComplexity(Ptyvar("a")) === 1) // Complexity of Ptyvar("a") is 1
    assert(pretypeComplexity(Ptycomp("list", List(Ptyvar("a")))) === 2) // Complexity of Ptycomp("list", List(Ptyvar("a"))) is 2
    assert(pretypeComplexity(Ptygvar(2)) === 1) // Complexity of Ptygvar("b") is 1
    assert(pretypeComplexity(Ptycomp("tuple", List(Ptygvar(2)))) === 2) // Complexity of Ptycomp("tuple", List(Ptygvar("b"))) is 2
    assert(pretypeComplexity(Ptycomp("triple", List(Ptygvar(2), Ptyvar("scscs")))) === 3)
  }


  // Define sample preterms for testing
  val p1: Preterm = Ptmvar("x", Ptygvar(0))
  val p2: Preterm = Ptmvar("y", Ptygvar(0))
  val p3: Preterm = Ptmcomb(p1, p2)

  test("listMkCombPreterm") {
    val ptm: Preterm = Ptmconst("const", Ptygvar(0))
    val ptms: List[Preterm] = List(p1, p2, p3)
    val result: Preterm = listMkCombPreterm(ptm, ptms)
    assert(result == Ptmcomb(Ptmcomb(Ptmcomb(ptm, p1), p2), p3))
  }

  test("stripCombPreterm") {
    val (firstPtm, combList) = stripCombPreterm(p3)
    println(firstPtm)
    println(combList)
    assert(firstPtm :: combList == List(p1, p2))
    assert(firstPtm == Ptmvar("x", Ptygvar(0)))
  }

  test("listMkAbsPreterm") {
    val ptm: Preterm = Ptmconst("const", Ptygvar(0))
    val vs: List[Preterm] = List(p1, p2, p3)
    val result: Preterm = listMkAbsPreterm(vs, ptm)
    assert(result == Ptmabs(p1, Ptmabs(p2, Ptmabs(p3, Ptmconst("const", Ptygvar(0))))))
  }

  test("stripAbsPreterm") {
    val ptm: Preterm = Ptmabs(p1, Ptmabs(p2, Ptmabs(p3, Ptmvar("x", Ptygvar(0)))))
    val (absList, lastPtm): (List[Preterm], Preterm) = stripAbsPreterm(ptm)
    assert(absList == List(p1, p2, p3))
    assert(lastPtm == Ptmvar("x", Ptygvar(0)))
  }

  // Sample Preterm instances
  val ptm0: Preterm = Ptmvar("x", Ptyvar("0"))
  val ptm1: Preterm = Ptmvar("x", Ptyvar("0"))
  val ptm2: Preterm = Ptmvar("y", Ptyvar("0"))
  val ptm3: Preterm = Ptmconst("const1", Ptyvar("0"))
  val ptm4: Preterm = Ptmconst("const2", Ptyvar("0"))
  val ptm5: Preterm = Ptmtyped(ptm1, Ptyvar("0"))
  val ptm6: Preterm = Ptmtyped(ptm3, Ptyvar("0"))
  val ptm7: Preterm = Ptmtyped(ptm0, Ptyvar("0"))
  val f: Preterm = Ptmconst("f", Ptyvar("0"))
  val ptms: List[Preterm] = List(ptm1, ptm2)
  val ptms1: List[Preterm] = List(ptm1, ptm2, ptm3, ptm4, ptm5)

  test("atomPretermName should return the correct names for different preterms") {
    assert(atomPretermName(ptm1) === "x")
    assert(atomPretermName(ptm2) === "y")
    assert(atomPretermName(ptm3) === "const1")
    assert(atomPretermName(ptm4) === "const2")
    assert(atomPretermName(ptm5) === "x")
    assert(atomPretermName(ptm6) === "const1")
  }

  test("sameAtomPreterm should correctly determine if two preterms are the same atom") {
    assert(!sameAtomPreterm(ptm1, ptm2))
    assert(sameAtomPreterm(ptm1, ptm0))
    assert(sameAtomPreterm(ptm5, ptm7))
    assert(!sameAtomPreterm(ptm4, ptm3))
  }

  val leftAssocResult = listMkBinPreterm(LeftAssoc, f, ptms)
  val rightAssocResult = listMkBinPreterm(RightAssoc, f, ptms)
  val nonAssocResult = listMkBinPreterm(NonAssoc, f, List(ptm1, ptm2))

  test("destBinPreterm should correctly destructure binary preterms") {
    val (fResult, ptm1Result, ptm2Result) = destBinPreterm(nonAssocResult)
    assert(fResult === f)
    assert(ptm1Result === ptm1)
    assert(ptm2Result === ptm2)
    val (fResult2, ptm1Result2, ptm2Result2) = destBinPreterm(rightAssocResult)
    assert(fResult2 === f)
    assert(ptm1Result2 === ptm1)
    assert(ptm2Result2 === ptm2)
  }

  test("stripBinPreterm should correctly strip binary preterms with different associativity") {
    val leftAssocResult = listMkBinPreterm(LeftAssoc, f, ptms1)
    val rightAssocResult = listMkBinPreterm(RightAssoc, f, ptms1)
    val res = ptms1

    val stripLeftAssocResult = stripBinPreterm(LeftAssoc, f, leftAssocResult)
    assert(stripLeftAssocResult === res)

    val stripRightAssocResult = stripBinPreterm(RightAssoc, f, rightAssocResult)
    assert(stripRightAssocResult === res)

    val stripNonAssocResult = stripBinPreterm(NonAssoc, f, nonAssocResult)
    assert(stripNonAssocResult === List(ptm1, ptm2))
  }



}
