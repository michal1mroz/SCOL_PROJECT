package main.scala

import utils.ScolException.ScolFail

import scala.collection.mutable
import scala.collection.mutable.HashMap
import scala.math.BigInt

object Type {

  sealed trait HolType

  case class Tyvar(name: String) extends HolType

  case class Tycomp(name: String, params: List[HolType]) extends HolType

  private val theTyconsts: mutable.HashMap[String, BigInt] = mutable.HashMap.empty

  def getTyconstArity(x: String): BigInt =
    theTyconsts.getOrElse(x, throw ScolFail(s"No type constant called $x"))

  def getAllTyconsts: List[(String, BigInt)] = theTyconsts.toList

  def isTyconstName(x: String): Boolean = theTyconsts.contains(x)

  def primNewTyconst(x: String, n: BigInt): Unit = {
    require(n >= BigInt(0), "Arity must be non-negative")
    require(!isTyconstName(x), s"Type constant name $x already used")
    println(s"Declaring type constant $x")
    theTyconsts.put(x, n)
  }

  def mkVarType(x: String): HolType = Tyvar(x)

  def destVarType(ty: HolType): String = ty match {
    case Tyvar(x) => x
    case _ => throw ScolFail("Not a type variable")
  }

  def isVarType(ty: HolType): Boolean = ty match {
    case Tyvar(_) => true
    case _ => false
  }

  def mkCompType(x: String, tys: List[HolType]): HolType = {
    val n = theTyconsts.getOrElse(x, throw ScolFail("No type constant called " + x))
    require(tys.length == n.toInt, "Type list doesn't fit arity")
    Tycomp(x, tys)
  }

  def destCompType(ty: HolType): (String, List[HolType]) = ty match {
    case Tycomp(x, tys) => (x, tys)
    case _ => throw new RuntimeException("Not a compound type" + ty)
  }

  def isCompType(ty: HolType): Boolean = ty match {
    case Tycomp(_, _) => true
    case _ => false
  }

  //fixme don't know how to define them maybe Scala compiler will figure it out
//  def typeEq(x: HolType, y: HolType): Boolean = x == y
  def typeEq(x: HolType, y: HolType): Boolean = x == y
  
  //fixme don't know how to define them
//  def typeLt(x: HolType, y: HolType): Boolean = x.toString < y.toString

  def mkFunType(ty1: HolType, ty2: HolType): HolType = Tycomp("->", List(ty1, ty2))

  def destFunType(ty: HolType): (HolType, HolType) = ty match {
    case Tycomp("->", List(ty1, ty2)) => (ty1, ty2)
    case _ => throw ScolFail("Not a function type")
  }

  def isFunType(ty: HolType): Boolean = ty match {
    case Tycomp("->", _) => true
    case _ => false
  }

  def typeInst0(tytheta: List[(HolType, HolType)], ty: HolType): HolType = ty match {
    case Tyvar(_) => tytheta.find(_._1 == ty).map(_._2).getOrElse(ty)
    case Tycomp(x, tys) =>
      val tys_ = tys.map(typeInst0(tytheta, _))
      if (tys_ == tys) ty else Tycomp(x, tys_)
  }

  def typeInst(tytheta: List[(HolType, HolType)], ty: HolType): HolType =
    if (tytheta.isEmpty) ty
    else {
      require(tytheta.forall { case (ty1, _) => isVarType(ty1) }, "Non-type-variable in instantiation domain")
      typeInst0(tytheta, ty)
    }
}