package main.scala

import Type.*
import Term.*
import Utils1.*
import Names.*
import Lib.*
//import Thm
import utils.ScolException.*

object Utils2 {
  def listMkFunType(tys: List[HolType], ty: HolType): HolType = foldr_(mkFunType)(ty, tys)

  def stripFunType(ty: HolType): (HolType, List[HolType]) = unfoldr(destFunType, ty)

  def rator(tm: Term): Term = fst(destComb(tm))

  def rand(tm: Term): Term = snd(destComb(tm))

  def stripComb(tm: Term): (Term, List[Term]) = unfoldl(destComb, tm)

  def listMkAbs(vs: List[Term], tm0: Term): Term = {
    try {
      foldr_(mkAbs)(tm0, vs)
    } catch {
      case _: ScolFail => throw ScolFail("Fail in listMkAbs")
    }
  }

  def bvar(tm: Term): Term = fst(destAbs(tm))

  def body(tm: Term): Term = snd(destAbs(tm))

  def stripAbs(tm: Term): (Term, List[Term]) = unfoldr(destAbs, tm)

  def isCbin(x: String, tm: Term): Boolean = can(destCbin(x), tm)

  def isCbinder(x: String, tm: Term): Boolean = can(destCbinder(x), tm)

  def eqLhs(tm: Term): Term = fst(destEq(tm))

  def eqRhs(tm: Term): Term = snd(destEq(tm))

  def listMkImp(tms: List[Term], tm: Term): Term = {
    try {
      foldr_(mkImp)(tm, tms)
    }catch{
      case _: ScolFail => throw ScolFail("Faile in listMkImp")
    }
  }

  def stripImp(tm: Term): (Term, List[Term]) = unfoldr(destImp, tm)

  def mkSelect(v: Term, tm0: Term): Term = {
    assert1(isBoolTerm(tm0), "mkSelect, Arg2 not boolean")
    val f = mkIconst("@", List((aTy, typeOf(v))))
    try{
      mkBinder(f, v, tm0)
    }catch{
      case _: ScolFail => throw ScolFail("mkBinder failed in mkSelect")
    }
  }

  def destSelect(tm: Term): (Term, Term) = try1(destCbinder("@"),tm, "destSelect, Not a selection")

  def isSelect(tm: Term): Boolean = can(destSelect, tm)

  def mkForall(v: Term, tm0: Term): Term = {
    assert1(isBoolTerm(tm0), "mkForall, Arg 2 not boolean")
    val f = mkIconst("!", List((aTy, typeOf(v))))
    try{
      mkBinder(f, v, tm0)
    }catch{
      case _: ScolFail => throw ScolFail("mkBinder failed in mkForall")
    }
  }

  def listMkForall(vs: List[Term], tm0: Term): Term = {
    try{
      foldr_(mkForall)(tm0,vs)
    }catch{
      case _: ScolFail => throw ScolFail("foldr_ failed in listMkForall")
    }
  }

  def destForall(tm: Term): (Term, Term) = try1(destCbinder("!"), tm, "destForall, not a universal")

  def isForall(tm: Term): Boolean = can(destForall, tm)

  def stripForall(tm: Term): (Term, List[Term]) = unfoldr(destForall, tm)

  def mkConj(tm1: Term, tm2: Term): Term = {
    assert1(isBoolTerm(tm1), "mkConj, Arg 1 not boolean")
    assert1(isBoolTerm(tm2), "mkConj, Arg 2 not boolean")
    val f = mkGconst("/\\")
    mkBin(f, tm1, tm2)
  }

  def listMkConj(tms: List[Term]): Term = try2(foldr1_(mkConj), tms)

  def destConj(tm: Term): (Term, Term) = try1(destCbin("/\\"), tm, "destConj, Not a conjunction")

  def isConj(tm: Term): Boolean = can(destConj,tm)

  def stripConj(tm: Term): List[Term] = unfoldr1(destConj, tm)

  def flatstripConj(tm: Term): List[Term] = unfold(destConj, tm)

  // Fixme dependent alphaEQ in Utils1 line 319 commented out
  //def termUnion(tms1:Term, tms2: Term): List[Term] = union_(alphaEq, tms1, tms2)

  /* Fixme dependent functions from utils1 commented out

  def listFreeVars(tms: List[Term]): Term =
    foldl((vs, tm) => union_(termEq, vs, freeVars(tm)))(List.empty)(tms)

  def termFreeIn(tm00: Term, tm: Term): Boolean =
    alphaEq(tm00, tm) || (destTerm(tm) match {
      case Tmcomb(tm1, tm2) => termFreeIn(tm00, tm1) || termFreeIn(tm00, tm2)
      case Tmabs(v, tm0) => !varFreeIn(v, tm00) && termFreeIn(tm00, tm0)
      case _ => false
    })
    */

    private var genvarCount = 0
    def genvar(ty: HolType): Term = {
      val x = s"_$genvarCount"
      genvarCount += 1
      mkVar(x, ty)
    }

    def listVariant(vs0: List[Term], vs: List[Term]): List[Term] = vs match {
      case v1 :: vs1 =>
        val v1_ = variant(vs0, v1)
        val vs1_ = listVariant((v1_ :: vs0), vs1)
        v1_ :: vs1_
      case Nil => List.empty
    }

    def listCvariant(vs0: List[Term], vs: List[Term]): List[Term] = vs match{
      case v1 :: vs1 =>
        val v1_ = cvariant(vs0, v1)
        val vs1_ = listCvariant((v1_ :: vs0), vs1)
        v1_ :: vs1_
      case Nil => List.empty
    }
  /*
    def allVars(tm: Term): List[Term] = destTerm(tm) match{
      case Tmvar(_, _) => List(tm)
      case Tmconst(_, _) => List.empty
      case Tmcomb(tm1, tm2) => union_(termEq, allVars(tm1), allVars(tm2))
      case Tmabs(v, tm0) => insert_(termEq, v, allVars(tm0))
    }

    def listAllVars(tms: List[Term]): Term = foldl((vs, tm) => union_(termEq, vs, allVars(tm)))(List.empty)(tms)
  */
}
