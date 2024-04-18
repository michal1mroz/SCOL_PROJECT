import main.scala.Names.{AssocHand, LeftAssoc, NonAssoc, RightAssoc, getInfixTypeInfo, hasInfixTypeFixity}
import utils.ScolException.ScolFail

object Preterm {
  sealed trait Pretype

  case class Ptyvar(name: String) extends Pretype

  case class Ptygvar(name: String) extends Pretype

  case class Ptycomp(name: String, preterms: List[Pretype]) extends Pretype


  def destTyvarPretype(p: Pretype): String = p match {
    case Ptyvar(name) => name
    case _ => throw ScolFail("Couldn't destroy type variable: Not a type variable")
  }

  def destTygvarPretype(p: Pretype): String = p match {
    case Ptygvar(name) => name
    case _ => throw ScolFail("Couldn't destroy generated type variable: Not a generated type variable")
  }

  def destPretype(p: Pretype): String = p match {
    case Ptyvar(name) => name
    case Ptygvar(name) => name
    case _ => throw ScolFail("Couldn't destroy provided preterm: Not a Ptyvar or Ptygvar")
  }

  def isTygvarPretype(p: Pretype): Boolean = p match
    case Ptygvar(_) => true
    case _ => false


  def mkBinPretype(name : String, ptm1 : Pretype, ptm2 : Pretype) : Ptycomp = Ptycomp(name, List(ptm1, ptm2))

  def destInfixPretype(p : Pretype) : (String, Pretype, Pretype) = p match {
    case Ptycomp(name, pty1 :: pty2 :: Nil) =>
      assert(hasInfixTypeFixity(name))
      (name, pty1, pty2)

    case _ => throw ScolFail("Not a Ptycomp provided to destInfixType")
  }


  def stripInfixPretype0(name : String, h : AssocHand, pty : Pretype) : List[Pretype] =
    try
      val (x, pty1, pty2) = destInfixPretype(pty)
      assert(x == name)

      h match
        case LeftAssoc => stripInfixPretype0(x, h, pty1).concat(List(pty2))
        case RightAssoc => pty1 :: stripInfixPretype0(x,h ,pty2)
        case NonAssoc => List(pty1, pty2)
    catch
      case _ : ScolFail  => List(pty)


  def stripInfixPretype(p : Pretype) : (String, List[Pretype]) =
    val (name, _, _) = destInfixPretype(p)
    val (n, h) = getInfixTypeInfo(name)
    val ptys = stripInfixPretype0(name, h, p)
    (name, ptys)


  def mkFunPretype(pty1 : Pretype, pty2 : Pretype) : Pretype = mkBinPretype("->", pty1, pty2)

  def setFunPretype(p : Pretype) : (Pretype, Pretype) = p match
    case Ptycomp(name, pty1 :: pty2 :: Nil) => (pty1, pty2)
    case _ => throw ScolFail("Failed to destroy provided function pretype! (Maybe it wasn't a function pretype?)")


  def boolPty = Ptycomp("bool", List())

  def boolBinPty = mkFunPretype(boolPty, mkFunPretype(boolPty, boolPty))



}
