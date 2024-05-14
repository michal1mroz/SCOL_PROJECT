import main.scala.Type
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