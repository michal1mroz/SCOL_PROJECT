package main.scala

import main.scala.Type.*
import main.scala.Term.*
import main.scala.Thm.*
import main.scala.Utils1.*
import main.scala.Utils2.*
import main.scala.CoreThry.*
import main.scala.Lib.{assert0, hdTl, try1, try2}
import main.scala.utils.ScolException.{LocalFail, ScolFail}

object Wrap {

  private var theAbsoluteStepTotal: Int = 0
  def stepTotal: Int = theAbsoluteStepTotal
  def incStepTotal(): Unit = {
    theAbsoluteStepTotal = theAbsoluteStepTotal + 1
  }

  private var theRelativeStepStart: Int = 0
  def resetStepCounter(): Unit = {
    theRelativeStepStart = theAbsoluteStepTotal
  }
  def stepCounter: Int = {
    theAbsoluteStepTotal - theRelativeStepStart
  }

  def eqReflConv(tm: Term): Thm = {
    val th_ = primEqReflConv(tm)
    incStepTotal()
    th_
  }

  def betaConv(tm: Term): Thm = {
    val th_ = try2(primBetaConv, tm)
    incStepTotal()
    th_
  }

  def mkCombRule(th1: Thm, th2: Thm): Thm = {
    val th_ = try2(primMkCombRule.curried(th1), th2)
    incStepTotal()
    th_
  }

  def mkAbsRule(v: Term, th: Thm): Thm = {
    val th_ = try2(primMkAbsRule.curried(v), th)
    incStepTotal()
    th_
  }

  def assumeRule(tm: Term): Thm = {
    val th_ = try2(primAssumeRule, tm)
    incStepTotal()
    th_
  }

  def dischRule(tm: Term, th: Thm): Thm = {
    val th_ = try2(primDishRule.curried(tm), th)
    incStepTotal()
    th_
  }

  def mpRule(th1: Thm, th2: Thm): Thm = {
    val th_ = try2(primMpRule.curried(th1), th2)
    incStepTotal()
    th_
  }

  def eqMpRule(th1: Thm, th2: Thm): Thm = {
    val th_ = try2(primEqMpRule.curried(th1), th2)
    incStepTotal()
    th_
  }

  def instRule(theta: List[(Term, Term)], th: Thm): Thm = {
    val th_ = try2(primInstRule.curried(theta), th)
    incStepTotal()
    th_
  }

  def instTypeRule(tytheta: List[(HolType, HolType)], th: Thm): Thm = {
    val th_ = try2(primInstTypeRule.curried(tytheta), th)
    incStepTotal()
    th_
  }

  def getTyconstArity(x: String): Int = {
    try2(primGetTyconstArity, x) // Shouldn't it work correctly?
  }

  def getAllTyconsts: List[(String, Int)] = {
    Type.getAllTyconsts
  }

  private def ntyvars(n: Int): List[HolType] = {
    List.range(1, n+1).map(i => mkVarType(i.toString))
  }

  def newTyconst(x: String, n: Int): HolType = {
    try{
      primNewTyconst(x, n)
      mkCompType(x, ntyvars(n))
    }catch {
      case _: ScolFail =>
        try{
          val n0_ = primGetTyconstArity(x)
          mkCompType(x, ntyvars(n))
        }catch{
          case _: ScolFail => throw ScolFail("new tyconst failed")
          case _: LocalFail => throw ScolFail("new tyconst failed")
        }
    }
  }

  def newConst(x: String, ty: HolType): Term = {
    try{
      primNewConst(x, ty)
      mkIconst(x, List.empty)
    }catch{
      case _: ScolFail =>
        try{
          val ty0 = getConstGtype(x)
          assert0(typeEq(ty, ty0), LocalFail)
          mkIconst(x, List.empty)
        }catch{
          case _: ScolFail => throw ScolFail("New const failed")
          case _: LocalFail => throw ScolFail("New const failed")
        }
    }
  }

  def newAxiom(x: String, tm: Term): Thm = {
    try{
      primNewAxiom(x, tm)
    }catch{
      case _: ScolFail =>
        try{
          val th0 = getAxiom(x)
          assert0(alphaEq(tm, concl(th0)), LocalFail)
          th0
        }catch{
          case _: ScolFail => throw ScolFail("New axiom failed")
          case _: LocalFail => throw ScolFail("New axiom failed")
        }
    }
  }

  def newConstDefinition(tm: Term): Thm = {
    val (lhs, rhs) = try1(destEq, tm, "Term is not an equality")
    val x = try{
      varName(lhs)
    }catch{
      case _: ScolFail =>
        try{
          constName(lhs)
        }catch{
          case _: ScolFail => throw ScolFail("LHS is not a var")
        }
    }
    try{
      primNewConstDefinition(x, rhs)
    }catch {
      case _: ScolFail =>
        try{
          val th0 = getConstDefinition(x)
          val rhs0 = eqthmRhs(th0)
          assert0(alphaEq(rhs, rhs0), LocalFail)
          th0
        }catch{
          case _: ScolFail => throw ScolFail("newConstDefinition failed")
          case _: LocalFail => throw ScolFail("newConstDefinition failed")
        }
    }
  }

  def newConstSpecification(xs: List[String], th: Thm): Thm = {
    try{
      primNewConstSpecification(xs, th)
    }catch{
      case _: ScolFail =>
        try{
          val ((xs0, th0), th1) = getConstSpecificationInfo(xs.head)
          assert0(xs.equals(xs0), LocalFail)
          assert0(alphaEq(concl(th), concl(th0)), LocalFail)
          th0
        }catch{
          case _: ScolFail => throw ScolFail("fail in newConstSpecification")
          case _: LocalFail => throw ScolFail("Fail in newConstSpecification")
        }
    }
  }

  /*def newTyconstDefinition(x: String, th: Thm): Thm = {
    val (v,p) = try1(destExists, concl(th), "Not of the form '?v. p'")

    val th1 = if(isComb(p)){
      val (cf, v0) = destComb(p)
      if(v == v0 && varFreeIn(v, cf)){
        th
      }
    }else{
      val p0 = mkComb(mkAbs(v, p), v)
      val e = mkIconst("=", List((aTy, boolTy)))
      val ex = mkIconst("?", List((aTy, typeOf(v))))
      val th1 = mkCombRule(eqReflConv(ex), mkAbsRule(v, betaConv(p0)))
      val th2 = eqReflConv(mkExists(v, p0))

      eqMpRule(eqMpRule(mkCombRule(mkCombRule(eqReflConv(e), th1), th2), th2))
      th
    }
  }*/
}
