import main.scala.Lib.{assoc, can, foldl1, foldr1, frontLast, reverseTail, unfold, unfold1, unfoldl, unfoldl1, unfoldlAlter, unfoldr, unfoldr1, unfoldrAlter, union, unions}
import main.scala.Names.{AssocHand, LeftAssoc, NonAssoc, RightAssoc, getEnumBracketZero, getEnumZeroBrackets, getEnumZeroOp, getInfixInfo, getInfixTypeInfo, hasBinderFixity, hasInfixFixity, hasInfixTypeFixity, hasPostfixFixity, hasPrefixFixity}
import main.scala.Term.{Term, Tmvar, Tmabs, Tmcomb, Tmconst}
import main.scala.Type.{HolType, Tycomp, Tyvar, mkVarType}
import main.scala.Utils1.{TypeCompDestructed, TypeVarDestructed, destType}
import utils.ScolException.{EnumLocalFail, LocalFail, NatLocalFail, ScolFail, assertScol, scolFail, try0}

import scala.annotation.tailrec

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

  def stripCombPreterm(ptm: Preterm): (Preterm, List[Preterm]) = unfoldl(destCombPreterm, ptm).swap

  // Lambda abstractions
  def listMkAbsPreterm(vs: List[Preterm], ptm0: Preterm): Preterm =
    vs.foldRight(ptm0)((v, ptm) => Ptmabs(v, ptm))

  def destAbsPreterm(ptm: Preterm): (Preterm, Preterm) = ptm match {
    case Ptmabs(v, ptm0) => (v, ptm0)
    case _ => throw ScolFail("destAbsPreterm: ?")
  }

  def stripAbsPreterm(ptm: Preterm): (List[Preterm], Preterm) =
    val (l, p) = unfoldr(destAbsPreterm, ptm)
    (l.reverse, p)
    
  // Type annotations
  def isTypedPreterm(ptm: Preterm): Boolean = ptm match {
    case Ptmtyped(_, _) => true
    case _ => false
  }

  // Atoms
  @tailrec
  def isAtomPreterm(ptm: Preterm): Boolean = ptm match {
    case Ptmvar(_, _) | Ptmconst(_, _) => true
    case Ptmtyped(ptm0, _) => isAtomPreterm(ptm0)
    case _ => false
  }

  @tailrec
  def atomPretermName(ptm: Preterm): String = ptm match {
    case Ptmvar(x, _) => x
    case Ptmconst(x, _) => x
    case Ptmtyped(ptm0, _) => atomPretermName(ptm0)
    case _ => throw ScolFail("atomPretermName : ?")
  }

  @tailrec
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
      case LeftAssoc => foldl1(mkBinPreterm.curried(f))(ptms)
      case RightAssoc => foldr1(mkBinPreterm.curried(f))(ptms)
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

  private def destBinPreterm0(f0: Preterm, ptm: Preterm): (Preterm, Preterm) = {
    val (f, ptm1, ptm2) = destBinPreterm(ptm)
    assert(sameAtomPreterm(f0, f), "destBinPreterm0")
    (ptm1, ptm2)
  }

  def stripBinPreterm(h: AssocHand, f0: Preterm, ptm: Preterm): List[Preterm] = {
    try {
      h match {
        case LeftAssoc => unfoldl1(destBinPreterm0(f0, _), ptm)
        case RightAssoc => reverseTail(unfoldr1(destBinPreterm0(f0, _), ptm).reverse).reverse
        case NonAssoc => val (ptm1, ptm2) = destBinPreterm0(f0, ptm)
          List(ptm1, ptm2)
      }
    } catch {
      case _: ScolFail => List(ptm)
    }
  }

  private val condFn = mkNulltypeConstPreterm("COND")

  def mkCondPreterm(ptm0: Preterm, ptm1: Preterm, ptm2: Preterm): Preterm = {
    listMkCombPreterm(condFn, List(ptm0, ptm1, ptm2))
  }

  def destCondPreterm(ptm: Preterm): (Preterm, Preterm, Preterm) = stripCombPreterm(ptm) match {
    case (Ptmconst("COND", _), List(ptm1, ptm2, ptm3)) => (ptm1, ptm2, ptm3)
    case _ => throw ScolFail("destCondPreterm : ?")
  }

  def isCondPreterm(ptm: Preterm): Boolean = {
    try {
      destCombPreterm(ptm)
      true
    }catch
      case _ : ScolFail => false
  }

  private val letFn: Preterm = mkNulltypeConstPreterm("LET")

  def mkLetPreterm(vptms: List[(Preterm, Preterm)], ptm0: Preterm): Preterm = {
    val (vs, ptms) = vptms.unzip
    val ptm1 = listMkAbsPreterm(vs, ptm0)
    listMkBinPreterm(LeftAssoc, letFn, ptm1 :: ptms)
  }

  def destLetPreterm(ptm: Preterm): (List[(Preterm, Preterm)], Preterm) = {
    val res = stripBinPreterm(LeftAssoc, letFn, ptm)
    val (ptm1, ptms) = (res.head, res.tail)
    assertScol(ptms.nonEmpty, "destLetPreterm: ?")
    val (vs, ptm2) = stripAbsPreterm(ptm1)
    val (vs1, vs2) = vs.splitAt(ptms.length)
    val ptm0 = listMkAbsPreterm(vs2, ptm2)
    val vptms = vs1.zip(ptms)
    (vptms, ptm0)
  }

  def isLetPreterm(ptm: Preterm): Boolean = {
    try {
      destLetPreterm(ptm)
      true
    } catch
      case _: ScolFail => false
  }


  private val pairFn : Preterm = mkNulltypeConstPreterm("PAIR")

  def mkPairPreterm(ptm1 : Preterm, ptm2 : Preterm) : Preterm = mkBinPreterm(pairFn, ptm1, ptm2)

  def listMkPairPreterm(ptms : List[Preterm]) : Preterm = listMkBinPreterm(RightAssoc, pairFn, ptms)
  def stripPairPreterm(ptm : Preterm) : List[Preterm] = stripBinPreterm(RightAssoc, pairFn, ptm)
  def isPairPreterm(ptm : Preterm) : Boolean = {
    try {
      destBinPreterm0(pairFn, ptm)
      true
    }catch
      case _: ScolFail => false
  }


  def numeralFn : Preterm = mkNulltypeConstPreterm("NUM")

  private def mkNatPreterm0(n : Int) : Preterm = n match {
    case n if n > 0 =>
      val n0 = n / 2;
      val ptmf = if n % 2 == 0 then mkNulltypeConstPreterm("BIT0") else mkNulltypeConstPreterm("BIT1")
      val ptm0 = mkNatPreterm0(n0)
      mkCombPreterm(ptmf, ptm0)

    case 0 => mkNulltypeConstPreterm("ZERO")
    case _ => throw ScolFail("mkNatPreterm: Received negative integer")
  }

  def mkNatPreterm(n : Int) : Preterm = mkCombPreterm(numeralFn, mkNatPreterm0(n))

  private def destNatPreterm0(zok : Boolean, ptm : Preterm) : Int = {
    try{
      val (ptmf, ptm0) = try0(destCombPreterm, ptm, NatLocalFail())
      val x = constPretermName(ptmf)
      if (x == "BIT0") {
        val n0 = destNatPreterm0(false, ptm0)
        2 * n0
      }else if (x == "BIT1") {
        val n0 = destNatPreterm0(true, ptm0)
        (2 * n0) + 1
      }else
        throw ScolFail("destNatPreterm0: improper preterm f name")
    }
    catch
      case _ : NatLocalFail =>
        val x = constPretermName(ptm)
        assertScol((x == "ZERO") && zok, "Assert in destNatPreterm0 failed")
        0
  }

  def destNatPreterm(ptm : Preterm) : Int = {
    val (f, ptm0) = destCombPreterm(ptm)
    assertScol(sameAtomPreterm(f, numeralFn), "destNatPreterm: wrong f signature")
    destNatPreterm0(true, ptm0)
  }

  def isNatPreterm(ptm : Preterm) : Boolean = {
    try {
      destCombPreterm(ptm)
      true
    }catch
      case _ : ScolFail => false
  }

  def mkEnumPreterm(br1 : String, ptms : List[Preterm], br2 : String) : Preterm = {
    val zero = getEnumBracketZero(br1)
    val f = getEnumZeroOp(zero)
    val (br1_, br2_) = getEnumZeroBrackets(zero)
    assertScol((br1_ == br1) && (br2_ == br2), "mkEnumPreterm: bracket problem")
    val fptm = mkNulltypeConstPreterm(f)
    val zptm = mkNulltypeConstPreterm(zero)
    listMkBinPreterm(RightAssoc, fptm, ptms :+ zptm)
  }

  def destEnumPreterm(ptm : Preterm) : (String, List[Preterm], String) = {
    try {
      val (fptm, ptm1, ptm2) = try0(destBinPreterm, ptm, EnumLocalFail())
      val x = constPretermName(fptm)
      val ptms0 = stripBinPreterm(RightAssoc, fptm, ptm)
      val (ptms, z) = frontLast(ptms0)
      val zero = constPretermName(z)
      assertScol(getEnumZeroOp(zero) == x, "destEnumPreterm: ?")
      val (br1, br2) = getEnumZeroBrackets(zero)
      (br1, ptms, br2)
    }catch
      case _ : EnumLocalFail =>
        val zero = constPretermName(ptm)
        val (br1, br2) = getEnumZeroBrackets(zero)
        (br1, Nil, br2)
  }


  def isEnumPreterm(ptm : Preterm) : Boolean = {
    try {
      destEnumPreterm(ptm)
      true
    } catch {
      case _ : ScolFail => false
    }
  }


  def stripInfixPreterm(ptm: Preterm): (Preterm, List[Preterm]) = {
    val (f, ptm1, ptm2) = destBinPreterm(ptm)
    val x = atomPretermName(f)
    val (n, h) = getInfixInfo(x)
    val ptms = stripBinPreterm(h, f, ptm)
    (f, ptms)
  }

  def isPrefixPreterm(ptm: Preterm): Boolean = {
    try {
      val (f, _) = destCombPreterm(ptm)
      val x = atomPretermName(f)
      hasPrefixFixity(x)
    } catch {
      case _: ScolFail => false
    }
  }

  def isInfixPreterm(ptm: Preterm): Boolean = {
    try {
      val (f, _, _) = destBinPreterm(ptm)
      val x = atomPretermName(f)
      hasInfixFixity(x)
    } catch {
      case _: ScolFail => false
    }
  }

  def isPostfixPreterm(ptm: Preterm): Boolean = {
    try {
      val (f, _) = destCombPreterm(ptm)
      val x = atomPretermName(f)
      hasPostfixFixity(x)
    } catch {
      case _: ScolFail => false
    }
  }

  def mkBinderPreterm(f: Preterm, v: Preterm, ptm0: Preterm): Preterm = {
    Ptmcomb(f, Ptmabs(v, ptm0))
  }


  //fixme important to test this one
  def listMkBinderPreterm(f: Preterm, vs: List[Preterm], ptm0: Preterm): Preterm = {
    vs.foldRight(ptm0)((v, ptm) => mkBinderPreterm(f, v, ptm))
  }

  def destBinderPreterm(ptm: Preterm): (Preterm, Preterm, Preterm) = {
    val (f, ptm1) = destCombPreterm(ptm)
    val x = atomPretermName(f)
    assertScol(hasBinderFixity(x), "destBinderPreterm : ?")
    val (v, ptm0) = destAbsPreterm(ptm1)
    (f, v, ptm0)
  }

  def stripBinderPreterm0(f0: Preterm, ptm: Preterm): (List[Preterm], Preterm) = {
    try {
      val (f, v, ptm0) = destBinderPreterm(ptm)
      assertScol(sameAtomPreterm(f0, f), "stripBinderPreterm0 : ?")
      val (vs, ptm00) = stripBinderPreterm0(f0, ptm0)
      (v :: vs, ptm00)
    } catch {
      case _: ScolFail | _: LocalFail => (Nil, ptm)
    }
  }

  def stripBinderPreterm(ptm: Preterm): (Preterm, List[Preterm], Preterm) = {
    val (f, v, ptm0) = destBinderPreterm(ptm)
    val (vs, ptm1) = stripBinderPreterm0(f, ptm0)
    (f, v :: vs, ptm1)
  }

  def isBinderPreterm(ptm: Preterm): Boolean = {
    try {
      destBinderPreterm(ptm)
      true
    } catch
      case _ : ScolFail => false
  }

  def termToPreterm(tm: Term): Preterm = tm match {
    case Tmvar(x, ty) =>
      val tyPrime = typeToPretype(ty)
      Ptmvar(x, tyPrime)
    case Tmconst(x, ty) =>
      val pty = typeToPretype(ty)
      val xPrime = if (x == "=" && pty == boolBinPty) "<=>" else x
      Ptmconst(xPrime, pty)
    case Tmcomb(tm1, tm2) =>
      val ptm1 = termToPreterm(tm1)
      val ptm2 = termToPreterm(tm2)
      Ptmcomb(ptm1, ptm2)
    case Tmabs(v, tm0) =>
      val pv = termToPreterm(v)
      val ptm0 = termToPreterm(tm0)
      Ptmabs(pv, ptm0)
  }

  // Listing functions

  def pretermTyvars(ptm: Preterm): List[Pretype] = ptm match {
    case Ptmvar(x, pty) =>
      pretypeTyvars(pty)
    case Ptmconst(x, pty) =>
      pretypeTyvars(pty)
    case Ptmcomb(ptm1, ptm2) =>
      union(pretermTyvars(ptm1), pretermTyvars(ptm2))
    case Ptmabs(ptm1, ptm2) =>
      union(pretermTyvars(ptm1), pretermTyvars(ptm2))
    case Ptmtyped(ptm0, pty) =>
      union(pretermTyvars(ptm0), pretypeTyvars(pty))
  }

  def pretermGtyvars(ptm: Preterm): List[Pretype] = ptm match {
    case Ptmvar(x, pty) =>
      pretypeGtyvars(pty)
    case Ptmconst(x, pty) =>
      pretypeGtyvars(pty)
    case Ptmcomb(ptm1, ptm2) =>
      union(pretermGtyvars(ptm1), pretermGtyvars(ptm2))
    case Ptmabs(ptm1, ptm2) =>
      union(pretermGtyvars(ptm1), pretermGtyvars(ptm2))
    case Ptmtyped(ptm0, pty) =>
      union(pretermGtyvars(ptm0), pretypeGtyvars(pty))
  }

  def pretermHasGtyvars(ptm: Preterm): Boolean = ptm match {
    case Ptmvar(_, pty)  => pretypeHasGtyvars(pty)
    case  Ptmconst(_, pty) => pretypeHasGtyvars(pty)
    case Ptmcomb(ptm1, ptm2)  =>
      pretermHasGtyvars(ptm1) || pretermHasGtyvars(ptm2)
    case  Ptmabs(ptm1, ptm2) =>
      pretermHasGtyvars(ptm1) || pretermHasGtyvars(ptm2)
    case Ptmtyped(ptm0, _) =>
      pretermHasGtyvars(ptm0)
  }


  
}