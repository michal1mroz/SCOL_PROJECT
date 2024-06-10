package main.scala

import Type.*
import Term.*
import Utils1.*
import Lib.*
import utils.ScolException.ScolFail

import java.math.BigInteger
import scala.collection.mutable

object Thm {
  sealed trait Thm
  case class Theorem(terms: List[Term], conclusion: Term) extends Thm

  def destThm(theorem: Thm): (List[Term], Term) = theorem match {
    case Theorem(terms, conclusion) => (terms, conclusion)
    case _ => throw ScolFail("Supplied object not a Theorem")
  }

  def asms(theorem: Thm): List[Term] = fst(destThm(theorem))

  def concl(theorem: Thm): Term = snd(destThm(theorem))

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
  private val theAxioms: mutable.HashMap[String, Thm] = mutable.HashMap.empty

  def getAxiom(x: String): Thm = {
    theAxioms.getOrElse(x, throw ScolFail(s"No axiom called $x"))
  }

  def getAllAxioms: List[(String, Thm)] = {
    theAxioms.toList
  }

  def primNewAxiom(x: String, tm: Term): Thm ={
    require(isBoolTerm(tm), "Term must be a boolean term")
    require(freeVars(tm).isEmpty, "Free vars not allowed in term arg")
    require(cannot(getAxiom, x), "Axiom name already used")
    val th = Theorem(List.empty, tm)
    theAxioms.put(x, th)
    th
  }

  private val theConstDefs: mutable.HashMap[String, Thm] = mutable.HashMap.empty

  def getConstDefinition(x: String): Thm = {
    theConstDefs.getOrElse(x, throw ScolFail(s"No definition for constant $x"))
  }

  def getAllConstDefinitions: List[(String, Thm)] = {
    theConstDefs.toList
  }

  def primNewConstDefinition(x: String, tm: Term): Thm = {
    val ty = typeOf(tm)
    require(freeVars(tm).isEmpty, "Free vars not allowed in definition term")
    require(subset_(typeEq.curried, termTyvars(tm), typeTyVars(ty)), "Definition term contains tyvars not at top level")
    primNewConst(x, tm.asInstanceOf[HolType]) // Polymorphism has some problems here :<
    val c = mkGconst(x)
    val th = Theorem(List.empty, mkEq(c, tm))
    theConstDefs.put(x, th)
    th
  }

  private val theConstSpecs: mutable.HashMap[List[String], (Thm, Thm)] = mutable.HashMap.empty
  private val theConstSpecNames: mutable.HashMap[String, List[String]] = mutable.HashMap.empty

  def getConstSpecificationInfo(x: String): ((List[String], Thm), Thm) = {
    try{
      val xs = theConstSpecNames.getOrElse(x, throw ScolFail("Const spec name not found"))
      val th = theConstSpecs.getOrElse(xs, throw ScolFail("Const Specs not found"))// Don't know, it doesn't want to work otherwise
      ((xs, th._1), th._2)
    }catch{
      case _: ScolFail =>
        if(isConstName(x)){
          throw ScolFail(s"No specification for constant $x")
        }else{
          throw ScolFail(s"No constant called $x")
        }
    }
  }

  def getAllConstSpecificationInfo: List[((List[String], Thm), Thm)] = {
    val xtts = theConstSpecs.toList

    def remapTuple: ((List[String], (Thm, Thm))) => ((List[String], Thm), Thm) = {
      case (x, (y, z)) => ((x, y), z)
    }
    map[(List[String], (Thm, Thm)), ((List[String], Thm), Thm)](remapTuple, xtts)
  }

  def getConstSpecification(x: String): Thm = {
    try{
      snd(getConstSpecificationInfo(x))
    }catch{
      case _: ScolFail => throw ScolFail("Failed retrieving const specification")
    }
  }

  def getAllConstSpecifications: List[(List[String], Thm)] = {
    try{
      fstMap(fst[List[String], Thm], getAllConstSpecificationInfo)
    }catch{
      case _: ScolFail => throw ScolFail("Failed retrieving all const specifications")
    }
  }

  def primNewConstSpecification(xs: List[String], th: Thm): Thm= {
    val (hs, c) = destThm(th.asInstanceOf[Theorem])
    val (tm0, vs0) = stripExists(c)
    require(hs.isEmpty , "Assumptions not allowed")
    require(freeVars(c).isEmpty, "Free vars in conclusion")
    require(xs.nonEmpty, "Name list must be non-empty")
    val length_big_int = BigInteger.valueOf(xs.length)
    val (vs, vs1): (List[Term], List[Term]) = try1(cutBigInt.curried(length_big_int), vs0, "Name list longer than existential var list") // Not safe :<
    require(noDups(xs), "Name list not distinct")
    val tm1 = listMkExists(vs1, tm0)
    val tyvs1 = termTyvars(tm1)
    val (tyvs, tyvss) = hdTl(map(termTyvars, vs))
    val setEqual = setEq_[HolType].curried
    require(forall(setEqual(typeEq.curried)(tyvs), tyvss), "Each outer-existential var must have same tyvars")
    require(subset_(typeEq.curried, tyvs1, tyvs), "Existential body contains tyvars not in var list")
    def not(x: Boolean): Boolean = !x
    try{
      assert(forall(isConstName.andThen(not), xs))
    }catch{
      case _: AssertionError =>
        val x = find(isConstName, xs)
        throw ScolFail(s"Constant name $x already used")
    }
    val tys = map(typeOf, vs)
    doMap[(String, HolType)](primNewConst, zip(xs, tys))
    val cs = map(mkGconst, xs)
    val theta = zip(vs, cs)
    val th1 = Theorem(List.empty, varInst(theta, tm1))
    println("Adding specification for constant")
    theConstSpecs.put(xs, (th, th1))
    def insertMap(x: String): Unit = theConstSpecNames.put(x, xs)
    doMap(insertMap, xs)
    th1
  }

  private val theTyconsDefs: mutable.HashMap[String, (Thm, Thm)] = mutable.HashMap.empty

  private def getTyconstDefinitionInfo0(x: String): (Thm, Thm) = {
    try{
      theTyconsDefs.getOrElse(x, throw ScolFail("Failed retrieving const"))
    }catch{
      case _: ScolFail =>
        assert1(isTyconstName(x), s"No type constant called $x")
        throw ScolFail(s"No type definition for type constant $x")
    }
  }

  def getTyconstDefinitionInfo(x: String): (Thm, Thm) = {
    getTyconstDefinitionInfo0(x)
  }

  def getAllTyconstDefinitionInfo: List[(String, (Thm, Thm))] = {
    theTyconsDefs.toList
  }

  def getTyconstDefinition(x: String): Thm = {
    snd(getTyconstDefinitionInfo0(x))
  }

  def getAllTyconstDefinitions: List[(String, Thm)] = {
    val xthths = theTyconsDefs.toList

    def fun: ((String, (Thm, Thm))) => (String, Thm) = {
      case (x, (y, z)) => (x, y)
    }
    map[(String, (Thm, Thm)), (String, Thm)](fun, xthths)
  }

  def primNewTyconstDefinition(x: String, t0: Thm): Thm = {
    val hs0 = asms(t0.asInstanceOf[Theorem])
    val c0 = concl(t0.asInstanceOf[Theorem])

    val (v, pv) = try1(destExists, c0, "Thm arg must match '?x. P x'")
    val (p, v1) = try1(destComb, pv, "Thm arg must match '?x. P x'")
    require(termEq(v1, v), "Thm arg must match '?x. P x'")
    require(hs0.isEmpty, "Asms not allowed in thm arg")
    require(freeVars(p).isEmpty, "Free vars not allowed in thm arg characteristic function")

    val ty0 = typeOf(v)
    val tyvs = mergesort(typeLt.curried, termTyvars(p))
    val lengthBigInt = tyvs.length
    try2(primNewTyconst.curried(x), lengthBigInt)

    val ty = mkCompType(x, tyvs)
    val f = mkVar("f", mkFunType(ty, ty0))
    val tdef = mkIconst("TYPE_DEFINITION", List((aTy, ty0), (bTy, ty)))
    val th = Theorem(List.empty, mkExists(f, listMkComb(tdef, List(p, f))))
    println("Adding definition for type constant")
    theTyconsDefs.put(x, (t0, th))
    th
  }
}
