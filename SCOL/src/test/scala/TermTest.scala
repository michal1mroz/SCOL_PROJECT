import main.scala.Term.{getAllConsts, primNewConst}
import main.scala.Type.{HolType, Tyvar}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers.*


class TermTest extends AnyFlatSpec {

  val typ1: HolType = Tyvar("1")
  val typ2: HolType = Tyvar("2")

  "primNewConstant" should "create a new const" in {
    primNewConst("T3", typ1)
    getAllConsts should contain ("T3" -> typ1)
  }

  it should "throw an exception if the same name is reused" in {
    primNewConst("T1", typ1)

    assertThrows[Exception] {
      primNewConst("T1", typ2)
    }
  }


}