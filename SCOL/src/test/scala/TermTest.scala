import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers._
import Term._
import Type._


class TermTest extends AnyFlatSpec {

  val typ1 = Tyvar("Stupid")
  val typ2 = Tyvar("notStupid")

  "primNewConstant" should "create a new const" in {
    primNewConst("T1", typ1)
    getAllConsts should contain ("T1" -> typ1)
  }

  it should "throw an exception if the same name is reused" in {
    primNewConst("T1", typ1)
    assertThrows[Exception] {
      primNewConst("T1", typ2)
    }
  }


}