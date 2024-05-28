package main.scala

import Type.*
import Term.*
import Utils1.*
import Lib.*
import utils.ScolException.ScolFail

object Thm {
  sealed trait Thm
  case class Theorem(terms: List[Term], conclusion: Term) extends Thm

  def destThm(theorem: Theorem): (List[Term], Term) =
    (theorem.terms, theorem.conclusion)

  def asms(theorem: Theorem): List[Term] = fst(destThm(theorem))

  def concl(theorem: Theorem): Term = snd(destThm(theorem))

  def thmEq(t1: Theorem, t2: Theorem): Boolean =
    t1.terms == t2.terms && t1.conclusion == t2.conclusion

  // Primitive inference

  // reflexivity of equality
  def primEqReflConv(tm: Term): Theorem = {
    val c_ = mkEq(tm, tm)
    Theorem(List.empty, c_)
  }

  // Beta reduction
  def primBetaConv(tm: Term): Theorem = {
    val func = "prim_beta_conv"
    val (f, tm2) = try1(destComb, tm, func)
    val (v, tm1) = try1(destAbs, f, func)
    val c_ = mkEq(tm, varInst(List((v, tm2)), tm1))
    Theorem(List.empty, c_)
  }

  // equality congruence
  def primMkCombRule(thm1: Theorem, thm2: Theorem): Theorem = {
    val func = "primMkCombRule"

    val (lhs1, rhs1) = try1(destEq, concl(thm1), func)
    val (lhs2, rhs2) = try1(destEq, concl(thm2), func)
    val hs_ = union_(alphaEq.curried, asms(thm1), asms(thm2))
    val c_ = try{
      mkEq(mkComb(lhs1, lhs2), mkComb(rhs1, rhs2))
    }catch{
      case e: ScolFail =>
        if(isFunType(typeOf(lhs1))) throw ScolFail("Function domain type not equal to argument type")
        else throw ScolFail(func + " Arg 1 not an equality between functions")

    }
    Theorem(hs_, c_)
  }

  // Equality congruence
  def primMkAbsRule(v: Term, tm: Theorem): Theorem = {
    val func = "primMkAbsRule"
    assert1(isVar(v), "Arg 1 not a variable")
    val (lhs, rhs) = try1(destEq, concl(tm), "Arg 2 not an equality theorem")
    val partVarFree = varFreeIn.curried(v)
    assert1(!(exists(partVarFree, asms(tm))), "Variable occurs free in asms")
    val c_ = mkEq(mkAbs(v, lhs), mkAbs(v, rhs))
    Theorem(asms(tm), c_)
  }

  // Assumption rule
  def primAssumeRule(tm: Term): Theorem = {
    assert1(isBoolTerm(tm), "Not a boolean term")
    Theorem(List(tm), tm)
  }

  // Implication introduction
  def primDishRule(tm: Term, thm: Theorem): Theorem = {
    assert1(isBoolTerm(tm), "primDishRule, arg 1 not a boolean term")
    val hs_ = subtract_(alphaEq.curried, asms(thm), List(tm))
    val c_ = mkImp(tm, concl(thm))
    Theorem(hs_, c_)
  }

  // Modus ponens
  def primMpRule(tm1: Theorem, tm2: Theorem): Theorem = {
    val func = "primMpRule"
    val (lhs, rhs) = try1(destImp, concl(tm1), "Arg 1 not a implication theorem")
    assert1(alphaEq(lhs,concl(tm2)), "Implication thm LHS not alpha-equivalent to 2nd thm")
    val hs_ = union_(alphaEq.curried, asms(tm1), asms(tm2))
    Theorem(hs_, rhs)
  }

  // Equality modus ponens
  def primEqMpRule(tm1: Theorem, tm2: Theorem): Theorem = {
    val (lhs, rhs) = try1(destEq, concl(tm1), "Arg 1 not an equality theorem")
    assert1(alphaEq(lhs, concl(tm2)), "Equality thm LHS not alpha-equivalent to 2nd thm")
    val hs_ = union_(alphaEq.curried, asms(tm1), asms(tm2))
    Theorem(hs_, rhs)
  }

  // Variable instantiation rule
  def primInstRule(theta: List[(Term, Term)], tm: Theorem): Theorem = {
    val partVarInst = varInst.curried
    val c_ = try2(partVarInst(theta), concl(tm))
    val hs_ = setify_(alphaEq.curried, map(partVarInst(theta), asms(tm)))
    Theorem(hs_, c_)
  }

  // Type variable instantiation
  def primInstTypeRule(tytheta: List[(HolType, HolType)], tm: Theorem): Theorem = {
    val partTyVar = tyvarInst.curried
    val c_ = try2(partTyVar(tytheta), concl(tm))
    val hs_ = setify_(alphaEq.curried, map(partTyVar(tytheta), asms(tm)))
    Theorem(hs_, c_)
  }


  // Primitive assertions

}
