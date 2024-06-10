import main.scala.Type
import main.scala.Type.Tycomp
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers.*


class TypeTest extends AnyFlatSpec {

  "A new type constant" should "be declared successfully" in {
    Type.primNewTyconst("T1", 2)
    Type.getAllTyconsts should contain ("T1" -> 2)
  }

  it should "throw an exception if the same name is reused" in {
    assertThrows[IllegalArgumentException] {
      Type.primNewTyconst("T1", 3)
    }
  }

  "Type variables" should "be created successfully" in {
    val varType = Type.mkVarType("X")
    Type.isVarType(varType) shouldBe true
    Type.destVarType(varType) shouldBe "X"
  }

  "Type variables" should "be equall to each other" in {
    val var1 = Type.mkVarType("X")
    val var2 = Type.mkVarType("X")
    Type.typeEq(var1, var2) shouldBe true
  }

  "Type variables" should "not be equall to each other" in {
    val var1 = Type.mkVarType("X")
    val var2 = Type.mkVarType("Y")
    Type.typeEq(var1, var2) shouldBe false
  }

  "Compund types" should "be equall to each other" in {
    val t1 = Type.mkVarType("X")
    val t2 = Type.mkVarType("Y")

    Type.primNewTyconst("X", 2)
    val compType1 = Type.mkCompType("X", List(t1, t2))
    val compType2 = Type.mkCompType("X", List(t1, t2))
    Type.typeEq(compType1, compType2) shouldBe true
  }

  /**
    @FixMe
    Using constructor directly as mkCompType failes
   **/
  "Compund types" should "not be equall to each other" in {
    val t1 = Type.mkVarType("X")
    val t2 = Type.mkVarType("Y")

    val compType1 = Type.Tycomp("X", List(t1, t2))
    val compType2 = Type.Tycomp("Y", List(t1, t2))
    val compType3 = Type.Tycomp("X", List(t2, t1))

    Type.typeEq(compType1, compType2) shouldBe false
    Type.typeEq(compType1, compType3) shouldBe false
  }

  "Different types" should "not be equall to each other" in {
    val t1 = Type.mkVarType("X")
    val t2 = Type.Tycomp("X", List(t1))

    Type.typeEq(t1, t2) shouldBe false
  }

  it should "throw an exception if not a type variable" in {
    assertThrows[RuntimeException] {
      Type.destVarType(Type.Tycomp("->", List()))
    }
  }

  "Compound types" should "be created successfully" in {
    Type.primNewTyconst("T2", 1)
    val compType = Type.mkCompType("T2", List(Type.mkVarType("X")))
    Type.isCompType(compType) shouldBe true
    Type.destCompType(compType) shouldBe ("T2" -> List(Type.mkVarType("X")))
  }

  it should "throw an exception if the arity is incorrect" in {
    assertThrows[IllegalArgumentException] {
      Type.mkCompType("T2", List(Type.mkVarType("X"), Type.mkVarType("Y")))
    }
  }
}