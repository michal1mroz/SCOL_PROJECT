package main.scala

import Type.*
import Term.*
import utils.ScolException.*
import Lib.*

import scala.annotation.tailrec

object Utils1 {
  def zip[A, B](l1: List[A], l2: List[B]): List[(A, B)] = (l1, l2) match {
    case (Nil, _) | (_, Nil) => Nil
    case (x :: xs, y :: ys) => (x, y) :: zip(xs, ys)
  }

  sealed trait DestructedType

  case class TypeVarDestructed(name: String) extends DestructedType

  case class TypeCompDestructed(name: String, types: List[HolType]) extends DestructedType

  def destType(ty: HolType): DestructedType =
    if (isVarType(ty)) TypeVarDestructed(destVarType(ty))
    else TypeCompDestructed(destCompType(ty)._1, destCompType(ty)._2)

  def isBoolType(ty: HolType): Boolean = {
    try {
      val (x, _) = destCompType(ty)
      x == "bool"
    } catch {
      case _: RuntimeException => false
    }
  }

  val aTy: HolType = mkVarType("a")
  val bTy: HolType = mkVarType("b")
  val cTy: HolType = mkVarType("c")

  def typeTyVars(ty: HolType): List[HolType] = destType(ty) match {
    case TypeVarDestructed(_) => List(ty)
    case TypeCompDestructed(_, tys) => unions_(typeEq.curried, map(typeTyVars, tys))//tys.flatMap(typeTyVars)
  }

  def typeMatch0(theta: List[(HolType, HolType)], patt: HolType, ty: HolType): List[(HolType, HolType)] = {
    (destType(patt), destType(ty)) match {
      case (TypeVarDestructed(xpatt), _) =>
        try {
          val tyPrime = Lib.try0(assoc[HolType, HolType].curried(patt), theta, Exception("assoc failed"))
          assert1(typeEq(ty, tyPrime), "Match failure")
          theta
        }
        catch {
          case _: Exception =>
            (patt, ty) :: theta
        }
      case (TypeCompDestructed(xpatt, patts), TypeCompDestructed(x, tys)) =>
        assert1(x == xpatt, "Match failure")
        val zipped = zip(patts, tys)
        zipped.foldLeft(theta) { case (accTheta, (patt, ty)) => typeMatch0(accTheta, patt, ty) }


      //val zipped = zip(patts, tys)
        //foldl(uncurry compose typeMatch0, theta, zipped)
      //foldl{ case (accTheta, (patt, ty)) => typeMatch0(accTheta, patt, ty) }(theta)(zipped)

      //val zipped = zip(patts, tys)
        //foldl({ case (accTheta: List[(HolType, HolType)], (patt:HolType, ty: HolType)) => typeMatch0(accTheta, patt, ty)})(theta)(zipped)
        //foldl(uncurry andThen typeMatch0, theta, zip)
        //zip(patts, tys).foldLeft(theta)((acc, pair) => typeMatch0(acc, pair._1, pair._2))
      case _ => throw ScolFail("typeMatch0: Match failure")
    }
  }

  def typeMatch(patt: HolType, ty: HolType): List[(HolType, HolType)] = {
    typeMatch0(List(), patt, ty)
  }

  sealed trait DestructedTerm

  case class TmvarDestructed(name: String, holType: HolType) extends DestructedTerm

  case class TmconstDestructed(name: String, holType: HolType) extends DestructedTerm

  case class TmcombDestructed(term1: Term, term2: Term) extends DestructedTerm

  case class TmabsDestructed(term1: Term, term2: Term) extends DestructedTerm

  def destTerm(tm: Term): DestructedTerm = {
    if (isVar(tm)) {
      val (name, holType) = destVar(tm)
      TmvarDestructed(name, holType)
    } else if (isConst(tm)) {
      val (name, holType) = destConst(tm)
      TmconstDestructed(name, holType)
    } else if (isComb(tm)) {
      val (term1, term2) = destComb(tm)
      TmcombDestructed(term1, term2)
    } else {
      val (term1, term2) = destAbs(tm)
      TmabsDestructed(term1, term2)
    }
  }

  def mkConst(x: String, ty: HolType): Term = {
    val func = "mk_const"
    val ty0 = try2(getConstGtype, x)
    try
      val theta = typeMatch(ty0, ty)
      mkIconst(x, theta)
    catch
      case _: ScolFail => throw ScolFail("Type doesn't match generic type")
  }

  def constName(tm: Term): String =
    try2[Term, String]((fst[String, HolType]).compose(destConst), tm)

  def constType(tm: Term): HolType =
    try2((snd[String, HolType]).compose(destConst), tm)

  def varName(tm: Term): String =
    try2((fst[String, HolType]).compose(destVar), tm)

  def varType(tm: Term): HolType =
    try2((snd[String, HolType]).compose(destVar), tm)

  def listMkComb(tm: Term, tms: List[Term]): Term = {
    try {
      foldl_[Term, Term](mkComb)(tm, tms)
    }
    catch {
      case e: ScolFail => throw ScolFail(e.getMessage)
    }
  }

  def mkBin(f: Term, tm1: Term, tm2: Term): Term = {
    try {
      listMkComb(f, List(tm1, tm2))
    }
    catch {
      case e: ScolFail => throw ScolFail(e.getMessage)
    }
  }

  def destBin(tm: Term): (Term, Term, Term) = {
    try {
      val (ftm1, tm2) = destComb(tm)
      val (f, tm1) = destComb(ftm1)
      (f, tm1, tm2)
    }
    catch {
      case _: ScolFail => throw ScolFail("Not a binary opertor")
    }
  }

  def isBin(tm: Term): Boolean = {
    try {
      destBin(tm)
      true
    } catch {
      case _: ScolFail => false
    }
  }

  def destCbin(x: String)(tm: Term): (Term, Term) = {
    try {
      val (f, tm1, tm2) = destBin(tm)
      assert(constName(f) == x)
      (tm1, tm2)
    } catch {
      case _: ScolFail =>
        throw ScolFail("Not a specified binary expression")
    }
  }

  def mkBinder(f: Term, v: Term, tm0: Term): Term = {
    try {
      mkComb(f, mkAbs(v, tm0))
    }
    catch {
      case _: ScolFail => throw ScolFail("Failed to create binder")
    }
  }

  def destBinder(tm: Term): (Term, Term, Term) = {
    try {
      val (f, tm1) = destComb(tm)
      val (v, tm0) = destAbs(tm1)
      (f, v, tm0)
    } catch {
      case _: ScolFail => throw ScolFail("Not a binder expression")
    }
  }

  def destCbinder(x: String)(tm: Term): (Term, Term) = {
    try {
      val (f, v, tm0) = try2(destBinder, tm)
      assert(constName(f) == x)
      (v, tm0)
    } catch {
      case _: ScolFail => throw ScolFail("Not the specified binder expression")
    }
  }

  def isBinder(tm: Term): Boolean = {
    try {
      destBinder(tm)
      true
    } catch {
      case _: ScolFail => false
    }
  }

  def isBoolTerm(tm: Term): Boolean = {
    isBoolType(typeOf(tm))
  }

  // Equality
  def mkEq(tm1: Term, tm2: Term): Term = {
    val (ty1, ty2) = (typeOf(tm1), typeOf(tm2))
    assert1(typeEq(ty1, ty2), "Arg 1 type not equal to Arg 2")
    val f = mkIconst("=", List((aTy, ty1)))
    mkBin(f, tm1, tm2)
  }

  def destEq(tm: Term): (Term, Term) = {
    try {
      destCbin("=")(tm)
    } catch {
      case _: ScolFail => throw ScolFail("Not an equality")
    }
  }

  def isEq(tm: Term): Boolean = {
    can(destEq, tm)
  }

  // Implication
  def mkImp(tm1: Term, tm2: Term): Term = {
    val ty1 = typeOf(tm1)
    val ty2 = typeOf(tm2)
    assert1(isBoolType(ty1), "Arg 1 not boolean")
    assert1(isBoolType(ty2), "Arg 2 not boolean")
    val f = mkGconst("==>")
    mkBin(f, tm1, tm2)
  }

  def destImp(tm: Term): (Term, Term) = {
    try1((destCbin("==>")), tm, "Not an implication")
  }

  def isImp(tm: Term): Boolean = {
    can(destImp, tm)
  }

  // Existential

  def mkExists(v: Term, tm0: Term): Term = {
    val ty = try1(varType, v, "Arg 1 not a variable")
    val ty0 = typeOf(tm0)
    assert1(isBoolType(ty0), "Arg 2 not boolean")
    val f = mkIconst("?", List((aTy, ty)))
    mkBinder(f, v, tm0)
  }

  def listMkExists(vs: List[Term], tm0: Term): Term = {
    try {
      foldr_[Term, Term](mkExists)(tm0, vs)
    } catch {
      case _: ScolFail => throw ScolFail("listMkExists failed")
    }
  }

  def destExists(tm: Term): (Term, Term) = {
    try {
      destCbinder("?")(tm)
    } catch {
      case _: ScolFail => throw ScolFail("Not an existential")
    }
  }

  def stripExists(tm: Term): (Term, List[Term]) = {
    unfoldl(destExists, tm).swap
  }

  def isExists(tm: Term): Boolean = {
    can(destExists, tm)
  }

  // Term utilities

  // fixme typeEq must work correctly, last 2 cases give type error


  def termTyvars(tm: Term): List[HolType] = {
    destTerm(tm) match {
      case TmvarDestructed(_, ty) =>
        typeTyVars(ty)
      case TmconstDestructed(_, ty) =>
        typeTyVars(ty)
      case TmcombDestructed(tm1, tm2) =>
        // typeEq needs currying to match function signatures
        union_(typeEq.curried, termTyvars(tm1), termTyvars(tm2))
      case TmabsDestructed(v, tm0) =>
        union_(typeEq.curried, termTyvars(v), termTyvars(tm0))
    }

  }


  def alphaEq0(theta0: List[(Term, Term)], tm1: Term, tm2: Term): Boolean = {
    (destTerm(tm1), destTerm(tm2)) match {
      case (TmvarDestructed(_, _), TmvarDestructed(_,_)) =>
        val tm1p = try assoc(tm1, theta0) catch {case _: ScolFail => tm1}
        val tm2p = try assoc(tm2, theta0) catch {case _: ScolFail => tm2}

        termEq(tm1p, tm2) && termEq(tm2p, tm1)
      case (TmconstDestructed(_, _), TmconstDestructed(_,_)) =>
        termEq(tm1, tm2)
      case (TmcombDestructed(tm1a, tm1b), TmcombDestructed(tm2a, tm2b)) =>
        alphaEq0(theta0, tm1a, tm2a) && alphaEq0(theta0, tm1b, tm2b)
      case (TmabsDestructed(v1, tm01), TmabsDestructed(v2, tm02)) =>
        val thetaOp = (v1, v2) :: theta0
        val ty1 = varType(v1)
        val ty2 = varType(v2)
        typeEq(ty1, ty2) && alphaEq0(thetaOp, tm01, tm02)
     case _ => false
    }
  }

  def alphaEq(tm1: Term, tm2: Term): Boolean = {
    termEq(tm1, tm2) || alphaEq0(List.empty, tm1, tm2)
  }


  def freeVars(tm: Term): List[Term] = {
    destTerm(tm) match {
      case TmvarDestructed(_,_) => List(tm)
      case TmconstDestructed(_,_) => List.empty
      case TmcombDestructed(tm1, tm2) => union_(termEq.curried, freeVars(tm1), freeVars(tm2))
      case TmabsDestructed(v, tm0) => subtract_(termEq.curried, freeVars(tm0), List(v.asInstanceOf[Term]))
    }
  }

  def varFreeIn0(v: Term, tm: Term): Boolean = {
    destTerm(tm) match {
      case TmvarDestructed(_,_) => termEq(v, tm)
      case TmconstDestructed(_,_) => false
      case TmcombDestructed(tm1, tm2) => varFreeIn0(v, tm1) || varFreeIn0(v, tm2)
      case TmabsDestructed(v0, tm0) => !termEq(v, v0) && varFreeIn0(v, tm0)
    }
  }

  def varFreeIn(v: Term, tm: Term): Boolean = {
    assert1(isVar(v), "Arg 1 not a variable")
    varFreeIn0(v, tm)
  }



  def variant(vs0: List[Term], v: Term): Term = {
    val (x, ty) = try1(destVar, v, "Not a variable")
    // fixme can rework this to use original map. Don't know how to do it
    val xs0 = try map(varName, vs0) catch {
      case _: ScolFail => throw ScolFail("Non-var in avoidance list")
    }
    val x1 = stringVariant(xs0, x)
    mkVar(x1, ty)
  }

  @tailrec
  def cvariantName(xs0: List[String], x: String): String = {
    val x1 = stringVariant(xs0, x)
    if (isConstName(x1)) cvariantName(xs0, x1 + "'")
    else x1
  }

  def cvariant(vs0: List[Term], v: Term): Term = {
    val (x, ty) = try1(destVar, v, "Not a variable")
    // fixme can rework this to use original map. Don't know how to do it
    val xs0 = try map(varName, vs0) catch {
      case _: ScolFail => throw ScolFail("Non-var in avoidanve list")
    }
    val x1 = cvariantName(xs0, x)
    mkVar(x1, ty)
  }


  case class Clash(v: Term) extends Exception
  def varInst0(vs0: List[Term], theta: List[(Term, Term)], tm: Term): Term = {
    destTerm(tm) match{
      case TmvarDestructed(_,_) =>
        try{
          val tm_ = assoc(tm, theta)
          val vsf_ = freeVars(tm_)
          if (disjoint_(termEq.curried, vsf_, vs0)) tm_
          else{
            val v_ = find[Term](v0 => mem_(termEq.curried, v0, vsf_), vs0.reverse)
            throw Clash(v_)
        }
      } catch {
        case _: ScolFail => tm
      }
      case TmconstDestructed(_,_) => tm
      case TmcombDestructed(tm1, tm2) =>
        val tm1_ = varInst0(vs0, theta, tm1)
        val tm2_ = varInst0(vs0, theta, tm2)
        if (tm1_ == tm1 && tm2_ == tm2) tm
        else mkComb(tm1_, tm2_)
      case TmabsDestructed(v, tm0) =>
        val theta_ :List[(Term, Term)] = fstFilter(v1 => !termEq(v1, v), theta)
        try {
          val tm0_ = varInst0(v :: vs0, theta_, tm0)
          if (tm0_ == tm0) tm else mkAbs(v, tm0_)
        } catch {
          case Clash(v_) if !termEq(v, v_) =>
            //assert0(termEq(v, v_), Clash(v_)) // I don't think it's needed here, but maybe I'm missing something
            val avs = flatten(freeVars(tm0).map {v => try freeVars(assoc(v, theta)) catch {case _: ScolFail => List(v)}})
            val v_ = cvariant(avs, v)
            val tm0_ = varInst0(vs0, (v, v_):: theta_, tm0)
            mkAbs(v_, tm0_)
        }
    }
  }

  def varInst(theta: List[(Term, Term)], tm: Term): Term = {
    try {
      theta match{
        case Nil => tm
        case _ =>
          assert1(theta.forall((v,_) => isVar(v)),"Non-variable in instantiation domain")
          assert1(theta.forall((v, tm_) => typeEq(typeOf(tm_), typeOf(v))), "Non-equal types in instantiation list")
          varInst0(Nil, theta, tm)
      }
    }catch {
      case Clash(v_) => throw internalError("varInst")
    }
  }


  def tyvarInst0(theta0: List[(Term, Term)], tytheta: List[(HolType,HolType)], tm: Term): Term = {
    destTerm(tm) match {
      case TmvarDestructed(x, ty) =>
        val ty_ = typeInst(tytheta, ty)
        val tm_ = if (ty_ == ty) tm else mkVar(x, ty_)
        try {
          val v0 = invAssoc(tm_, theta0)
          if (termEq(v0, tm)) tm_
          else throw Clash(v0)
        } catch{
          case _: ScolFail => tm_
        }
      case TmconstDestructed(x, ty) =>
        val ty_ = typeInst(tytheta, ty)
        if (typeEq(ty_, ty)) tm else mkConst(x, ty_)
      case TmcombDestructed(tm1, tm2) =>
        val tm1_ = tyvarInst0(theta0, tytheta, tm1)
        val tm2_ = tyvarInst0(theta0, tytheta, tm2)
        if (tm1_ == tm1 && tm2_ == tm2) tm
        else mkComb(tm1_, tm2_)
      case TmabsDestructed(v, tm0) =>
        val v_ = tyvarInst0(Nil, tytheta, v)
        try {
          val tm0_ = tyvarInst0((v, v_) :: theta0, tytheta, tm0)
          if (v_ == v && tm0_ == tm0) tm else mkAbs(v_, tm0_)
        }catch {
          case Clash(v_) if !termEq(v, v_) =>
            //assert0(termEq(v, v_), Clash(v_))
            val vs = freeVars(tm0)
            val v_ = cvariant(vs, v)
            val tm0_ = varInst0(Nil, List((v, v_)), tm0)
            val v__ = tyvarInst0(Nil, tytheta, v_)
            val tm0__ = tyvarInst0(theta0, tytheta, tm0_)
            mkAbs(v__, tm0__)
        }
    }
  }

  def tyvarInst(tytheta: List[(HolType, HolType)], tm: Term): Term = {
    try {
      tytheta match {
        case Nil => tm
        case _ =>
          assert1(tytheta.forall((ty,_) => isVarType(ty)), "Non-type-variable in instantiation domain")
          tyvarInst0(Nil, tytheta, tm)
      }
    } catch {
      case Clash(_) => throw internalError("tyvarInst")
    }
  }
} 