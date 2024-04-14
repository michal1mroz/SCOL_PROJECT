package main.scala

import Type.{HolType, destFunType, mkFunType, typeInst}
import utils.ScolException.ScolFail

import scala.collection.mutable
import scala.collection.mutable.HashMap

object Term {

  sealed trait Term

  case class Tmvar(name: String, ty: HolType) extends Term

  case class Tmconst(name: String, ty: HolType) extends Term

  case class Tmcomb(tm1: Term, tm2: Term) extends Term

  case class Tmabs(v: Term, tm0: Term) extends Term

  private val theConsts: mutable.HashMap[String, HolType] = mutable.HashMap.empty

  def getConstGtype(x: String): HolType =
    theConsts.getOrElse(x, throw ScolFail(s"No constant called $x"))

  def getAllConsts: List[(String, HolType)] = theConsts.toList

  def isConstName(x: String): Boolean = theConsts.contains(x)

  def primNewConst(x: String, ty: HolType): Unit = {
    require(!isConstName(x), s"Constant name $x already used")
    println(s"Declaring constant $x")
    theConsts.put(x, ty)
  }

  def typeOf(tm : Term) : HolType  = tm match {
    case Tmvar(_, x) => x
    case Tmconst(_, x) => x
    case Tmcomb(tm1, _) => destFunType(typeOf(tm1))._2
    case Tmabs(v, tm0) => mkFunType(typeOf(v), typeOf(tm0))
  }

  def mkVar(x: String, ty: HolType): Term = Tmvar(x, ty)

  def destVar(tm: Term): (String, HolType) = tm match {
    case Tmvar(x, ty) => (x, ty)
    case _ => throw ScolFail("Not a variable")
  }

  def isVar(tm: Term): Boolean = tm match {
    case Tmvar(_, _) => true
    case _ => false
  }

  def mkGconst(x: String): Term = {
    val ty0 = theConsts.getOrElse(x, throw ScolFail(s"No constant called $x"))
    Tmconst(x, ty0)
  }

  // fixme not sure if its correct or not, not really sure what it does
  def mkIconst(x: String, tytheta: List[(HolType, HolType)]): Term = {
    val ty0 = theConsts.getOrElse(x, throw ScolFail(s"No constant called $x"))
    val ty = typeInst(tytheta, ty0)
    Tmconst(x, ty)
  }

  def destConst(tm: Term): (String, HolType) = tm match {
    case Tmconst(x, ty) => (x, ty)
    case _ => throw ScolFail("Not a constant")
  }

  def isConst(tm: Term): Boolean = tm match {
    case Tmconst(_, _) => true
    case _ => false
  }

  def mkComb(tm1: Term, tm2: Term): Term = {
    val (ty1, ty2) = try{destFunType(typeOf(tm1))}
    catch
      case e : ScolFail => throw ScolFail("tm1 is not a function type")
    val ty1_ = typeOf(tm2)
    require(ty1_ == ty1, "Function domain type not equal to argument type")
    Tmcomb(tm1, tm2)
  }

  def destComb(tm: Term): (Term, Term) = tm match {
    case Tmcomb(tm1, tm2) => (tm1, tm2)
    case _ => throw ScolFail("Not a function application")
  }

  def isComb(tm: Term): Boolean = tm match {
    case Tmcomb(_, _) => true
    case _ => false
  }

  def mkAbs(v: Term, tm0: Term): Term = {
    require(isVar(v), "Arg 1 is not a variable")
    Tmabs(v, tm0)
  }

  def destAbs(tm: Term): (Term, Term) = tm match {
    case Tmabs(v, tm0) => (v, tm0)
    case _ => throw ScolFail("Not a lambda abstraction")
  }

  def isAbs(tm: Term): Boolean = tm match {
    case Tmabs(_, _) => true
    case _ => false
  }

}