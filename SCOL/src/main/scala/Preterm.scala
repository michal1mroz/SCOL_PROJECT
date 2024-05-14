import main.scala.Lib.{assoc, unfoldl, unfoldl1, unfoldr, unfoldr1, unions}
import main.scala.Names.{AssocHand, LeftAssoc, NonAssoc, RightAssoc, getInfixTypeInfo, hasInfixTypeFixity}
import main.scala.Type.{HolType, Tycomp, Tyvar, mkVarType}
import main.scala.Utils1.{TypeCompDestructed, TypeVarDestructed, destType}
import utils.ScolException.{ScolFail, scolFail}

object Preterm {

  sealed trait Pretype

  case class Ptyvar(name: String) extends Pretype

  case class Ptygvar(n: Int) extends Pretype

  case class Ptycomp(name: String, preterms: List[Pretype]) extends Pretype


  def destTyvarPretype(p: Pretype): String = p match {
    case Ptyvar(name) => name
    case _ => throw ScolFail("Couldn't destroy type variable: Not a type variable")
  }

  def destTygvarPretype(p: Pretype): Int = p match {
    case Ptygvar(name) => name
    case _ => throw ScolFail("Couldn't destroy generated type variable: Not a generated type variable")
  }

  def isTygvarPretype(p: Pretype): Boolean = p match
    case Ptygvar(_) => true
    case _ => false


  def mkBinPretype(name: String, ptm1: Pretype, ptm2: Pretype): Ptycomp = Ptycomp(name, List(ptm1, ptm2))

  def destInfixPretype(p: Pretype): (String, Pretype, Pretype) = p match {
    case Ptycomp(name, pty1 :: pty2 :: Nil) =>
      if (!hasInfixTypeFixity(name)) throw ScolFail("destInfixType used on non type of non infix fixity")
      (name, pty1, pty2)

    case _ => throw ScolFail("Not a Ptycomp provided to destInfixType")
  }


  private def stripInfixPretype0(name: String, h: AssocHand, pty: Pretype): List[Pretype] =
    try
      val (x, pty1, pty2) = destInfixPretype(pty)
      assert(x == name, "stripInfixPretype0: unexpected infix operator")

      h match
        case LeftAssoc => stripInfixPretype0(x, h, pty1) ::: List(pty2)
        case RightAssoc => pty1 :: stripInfixPretype0(x, h, pty2)
        case NonAssoc => List(pty1, pty2)
    catch
      case _: ScolFail => List(pty)


  def stripInfixPretype(p: Pretype): (String, List[Pretype]) =
    val (name, _, _) = destInfixPretype(p)
    val (n, h) = getInfixTypeInfo(name)
    val ptys = stripInfixPretype0(name, h, p)
    (name, ptys)


  def mkFunPretype(pty1: Pretype, pty2: Pretype): Pretype = mkBinPretype("->", pty1, pty2)

  def destFunPretype(p: Pretype): (Pretype, Pretype) = p match
    case Ptycomp("->", pty1 :: pty2 :: Nil) => (pty1, pty2)
    case _ => throw ScolFail("Failed to destroy provided function pretype! (Maybe it wasn't a function pretype?)")


  def boolPty = Ptycomp("bool", List())

  def boolBinPty = mkFunPretype(boolPty, mkFunPretype(boolPty, boolPty))

  def typeToPretype(ty: HolType): Pretype = destType(ty) match {
    case TypeVarDestructed(x) => Ptyvar(x)
    case TypeCompDestructed(x, tys) => Ptycomp(x, tys.map(typeToPretype))
  }

  private def pretypeToType0(nxs: List[(Pretype, String)], pty: Pretype): HolType = {
    pty match
      case Ptyvar(x) => mkVarType(x)

      case Ptygvar(n) =>
        val name = assoc(n, nxs)
        mkVarType(name)

      case Ptycomp(x, ptys) =>
        val tys = ptys.map(pretypeToType0(nxs, _))
        Tycomp(x, tys)
  }

  def pretypeToType(pty: Pretype): HolType = pretypeToType0(Nil, pty)

  // Listing pretype variables
  def pretypeTyvars(pty: Pretype): List[Pretype] = pty match {
    case Ptyvar(_) => List(pty)
    case Ptygvar(_) => List.empty
    case Ptycomp(_, ptys) => unions(ptys.map(pretypeTyvars))
  }

  def pretypeGtyvars(pty: Pretype): List[Pretype] = pty match {
    case Ptyvar(_) => List.empty
    case Ptygvar(_) => List(pty)
    case Ptycomp(_, ptys) => unions(ptys.map(pretypeGtyvars))
  }

  def pretypeHasGtyvars(pty: Pretype): Boolean = pty match {
    case Ptyvar(_) => false
    case Ptygvar(_) => true
    case Ptycomp(_, ptys) => ptys.exists(pretypeHasGtyvars)
  }

  // Instantiating pretypes
  def pretypeInst(theta: List[(Pretype, Pretype)], pty: Pretype): Pretype = pty match {
    case Ptyvar(_) | Ptygvar(_) =>
      try
        assoc(pty, theta)
      catch
        case e: ScolFail => pty

    case Ptycomp(x, ptys) =>
      val ptysPrime = ptys.map(pretypeInst(theta, _))
      if (ptys == ptys) pty else Ptycomp(x, ptysPrime)
  }

  // Pretype complexity
  def pretypeComplexity(pty: Pretype): Int = pty match {
    case Ptyvar(_) | Ptygvar(_) => 1
    case Ptycomp(_, ptys) => 1 + ptys.map(pretypeComplexity).sum
  }

  sealed trait Preterm

  case class Ptmvar(name: String, pretype: Pretype) extends Preterm

  case class Ptmconst(name: String, pretype: Pretype) extends Preterm

  case class Ptmcomb(term1: Preterm, term2: Preterm) extends Preterm

  case class Ptmabs(param: Preterm, body: Preterm) extends Preterm

  case class Ptmtyped(term: Preterm, pretype: Pretype) extends Preterm


  def mkNulltypeVarPreterm(x: String): Preterm = Ptmvar(x, Ptygvar(0))

  def destVarPreterm(ptm: Preterm): (String, Pretype) = ptm match {
    case Ptmvar(x, pty) => (x, pty)
    case _ => throw ScolFail("destVarPreterm: ?")
  }

  def mkNulltypeConstPreterm(x: String): Preterm = Ptmconst(x, Ptygvar(0))

  def constPretermName(ptm: Preterm): String = ptm match {
    case Ptmconst(x, _) => x
    case _ => throw ScolFail("constPretermName: ?")
  }


  // Function application
  def mkCombPreterm(f: Preterm, ptm: Preterm): Preterm = Ptmcomb(f, ptm)

  def listMkCombPreterm(f: Preterm, ptms: List[Preterm]): Preterm =
    ptms.foldLeft(f)(mkCombPreterm)

  def destCombPreterm(ptm: Preterm): (Preterm, Preterm) = ptm match {
    case Ptmcomb(ptm1, ptm2) => (ptm1, ptm2)
    case _ => throw ScolFail("destCombPreterm: ?")
  }

  def stripCombPreterm(ptm: Preterm): (List[Preterm], Preterm) =
    unfoldl(destCombPreterm, ptm)

  // Lambda abstractions
  def listMkAbsPreterm(vs: List[Preterm], ptm0: Preterm): Preterm =
    vs.foldRight(ptm0)((v, ptm) => Ptmabs(v, ptm))

  def destAbsPreterm(ptm: Preterm): (Preterm, Preterm) = ptm match {
    case Ptmabs(v, ptm0) => (v, ptm0)
    case _ => throw new Exception("destAbsPreterm: ?")
  }

  def stripAbsPreterm(ptm: Preterm): (List[Preterm], Preterm) =
    unfoldr(destAbsPreterm, ptm)
    
  // Type annotations
  def isTypedPreterm(ptm: Preterm): Boolean = ptm match {
    case Ptmtyped(_, _) => true
    case _ => false
  }

  // Atoms
  def isAtomPreterm(ptm: Preterm): Boolean = ptm match {
    case Ptmvar(_, _) | Ptmconst(_, _) => true
    case Ptmtyped(ptm0, _) => isAtomPreterm(ptm0)
    case _ => false
  }

  def atomPretermName(ptm: Preterm): String = ptm match {
    case Ptmvar(x, _) => x
    case Ptmconst(x, _) => x
    case Ptmtyped(ptm0, _) => atomPretermName(ptm0)
    case _ => throw ScolFail("atomPretermName : ?")
  }

  def sameAtomPreterm(ptm1: Preterm, ptm2: Preterm): Boolean = (ptm1, ptm2) match {
    case (Ptmvar(x1, pty1), Ptmvar(x2, pty2)) => x1 == x2 && pty1 == pty2
    case (Ptmconst(x1, _), Ptmconst(x2, _)) => x1 == x2
    case (Ptmtyped(ptm0, _), _) => sameAtomPreterm(ptm0, ptm2)
    case (_, Ptmtyped(ptm0, _)) => sameAtomPreterm(ptm1, ptm0)
    case (_, _) => throw ScolFail("sameAtomPreterm : ?")
  }

  // Binary function application

  def mkBinPreterm(ptmf: Preterm, ptm1: Preterm, ptm2: Preterm): Preterm =
    listMkCombPreterm(ptmf, List(ptm1, ptm2))

  def listMkBinPreterm(h: AssocHand, f: Preterm, ptms: List[Preterm]): Preterm =
    h match {
      case LeftAssoc => ptms.reduceLeft((ptm1, ptm2) => mkBinPreterm(f, ptm1, ptm2))
      case RightAssoc => ptms.reduceRight((ptm1, ptm2) => mkBinPreterm(f, ptm1, ptm2))
      case NonAssoc => ptms match {
        case List(ptm1, ptm2) => mkBinPreterm(f, ptm1, ptm2)
        case _ => throw ScolFail("listMkBinPreterm : ?")
      }
    }

  def destBinPreterm(ptm: Preterm): (Preterm, Preterm, Preterm) = {
    val (ptm01, ptm2) = destCombPreterm(ptm)
    val (f, ptm1) = destCombPreterm(ptm01)
    (f, ptm1, ptm2)
  }

  def destBinPreterm0(f0: Preterm, ptm: Preterm): (Preterm, Preterm) = {
    val (f, ptm1, ptm2) = destBinPreterm(ptm)
    assert(sameAtomPreterm(f0, f), "destBinPreterm0")
    (ptm1, ptm2)
  }

  def stripBinPreterm(h: AssocHand, f0: Preterm, ptm: Preterm): List[Preterm] = {
    try {
      h match {
        case LeftAssoc => unfoldl1(destBinPreterm0(f0, _), ptm)
        case RightAssoc => unfoldr1(destBinPreterm0(f0, _), ptm)
        case NonAssoc => val (ptm1, ptm2) = destBinPreterm0(f0, ptm)
          List(ptm1, ptm2)
      }
    } catch {
      case _: ScolFail => List(ptm)
    }
  }
}