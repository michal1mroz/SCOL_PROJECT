package main.scala

import Type.*
import Term.*
import Utils1.*
import Names.*
import Lib.*
import Thm.*
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
    } catch {
      case _: ScolFail => throw ScolFail("Faile in listMkImp")
    }
  }

  def stripImp(tm: Term): (Term, List[Term]) = unfoldr(destImp, tm)

  def mkSelect(v: Term, tm0: Term): Term = {
    assert1(isBoolTerm(tm0), "mkSelect, Arg2 not boolean")
    val f = mkIconst("@", List((aTy, typeOf(v))))
    try {
      mkBinder(f, v, tm0)
    } catch {
      case _: ScolFail => throw ScolFail("mkBinder failed in mkSelect")
    }
  }

  def destSelect(tm: Term): (Term, Term) = try1(destCbinder("@"), tm, "destSelect, Not a selection")

  def isSelect(tm: Term): Boolean = can(destSelect, tm)

  def mkForall(v: Term, tm0: Term): Term = {
    assert1(isBoolTerm(tm0), "mkForall, Arg 2 not boolean")
    val f = mkIconst("!", List((aTy, typeOf(v))))
    try {
      mkBinder(f, v, tm0)
    } catch {
      case _: ScolFail => throw ScolFail("mkBinder failed in mkForall")
    }
  }

  def listMkForall(vs: List[Term], tm0: Term): Term = {
    try {
      foldr_(mkForall)(tm0, vs)
    } catch {
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

  def isConj(tm: Term): Boolean = can(destConj, tm)

  def stripConj(tm: Term): List[Term] = unfoldr1(destConj, tm)

  def flatstripConj(tm: Term): List[Term] = unfold(destConj, tm)

  def termUnion(tms1: List[Term], tms2: List[Term]): List[Term] = union_(alphaEq.curried, tms1, tms2)

  def sameTypes(tm1: Term, tm2: Term): Boolean = {
    typeEq(typeOf(tm1), typeOf(tm2))
  }

  def listFreeVars(tms: List[Term]): List[Term] =
    def fun(vs: List[Term], tm: Term): List[Term] = {
      union_(termEq.curried, vs, freeVars(tm))
    }
    foldl(fun.curried)(List.empty)(tms)

  def termFreeIn(tm00: Term, tm: Term): Boolean =
    alphaEq(tm00, tm) || (destTerm(tm) match {
      case TmcombDestructed(tm1, tm2) => termFreeIn(tm00, tm1.asInstanceOf[Term]) || termFreeIn(tm00, tm2.asInstanceOf[Term])
      case TmabsDestructed(v, tm0) => !varFreeIn(v.asInstanceOf[Term], tm00) && termFreeIn(tm00, tm0.asInstanceOf[Term])
      case _ => false
    })

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

  def listCvariant(vs0: List[Term], vs: List[Term]): List[Term] = vs match {
    case v1 :: vs1 =>
      val v1_ = cvariant(vs0, v1)
      val vs1_ = listCvariant((v1_ :: vs0), vs1)
      v1_ :: vs1_
    case Nil => List.empty
  }

  def allVars(tm: Term): List[Term] = 
    destTerm(tm) match{
      case TmvarDestructed(_, _) => List(tm)
      case TmconstDestructed(_, _) => List.empty
      case TmcombDestructed(tm1, tm2) => union_(termEq.curried, allVars(tm1.asInstanceOf[Term]), allVars(tm2.asInstanceOf[Term]))
      case TmabsDestructed(v, tm0) => insert_(termEq.curried, v.asInstanceOf[Term], allVars(tm0.asInstanceOf[Term]))
  }

  def listAllVars(tms: List[Term]): List[Term] = {
    def fun(vs: List[Term], tm: Term): List[Term] = {
      union_(termEq.curried, vs, allVars(tm))
    }

    foldl(fun.curried)(List.empty)(tms)
  }

  case class Clash(term: Term) extends Exception

  def subst0(vs0: List[Term], theta: List[(Term, Term)], tm:Term): Term = {
    try{
      def cmp(thm: (Term, Term)): Boolean = {
        alphaEq(tm, fst(thm))
      }
      val (_, tm_) = find(cmp, theta)
      val vsf_ = freeVars(tm_)
      if(disjoint_(termEq.curried, vsf_, vs0)){
        tm_
      }
      else{
        def memPriv(v0: Term): Boolean = {
          mem_(termEq.curried, v0, vsf_)
        }
        val v_ = find(memPriv, vs0.reverse)
        throw Clash(v_)
      }
    }catch{
      case _: ScolFail =>
        destTerm(tm) match{
          case TmvarDestructed(_,_) => tm
          case TmconstDestructed(_,_) => tm
          case TmcombDestructed(tm1, tm2) => {
            val tm1_ = subst0(vs0, theta, tm1.asInstanceOf[Term])
            val tm2_ = subst0(vs0, theta, tm2.asInstanceOf[Term])
            if(tm1_ == tm1 && tm2_ == tm2) tm
            else mkComb(tm1_, tm2_)
          }
          case TmabsDestructed(v, tm0) =>
            def inside(tm: Term): Boolean = {
              val flag = varFreeIn(v.asInstanceOf[Term], tm)
              !flag
            }
            val theta_ = fstFilter(inside, theta)
            try{
              val tm0_ = subst0(v.asInstanceOf[Term] :: vs0, theta_, tm0.asInstanceOf[Term])
              if(tm0_ == tm0) tm
              else mkAbs(v.asInstanceOf[Term], tm0_)
            }catch{
              case Clash(v_) =>
                assert0(termEq(v.asInstanceOf[Term], v_), Clash(v_))
                val vsf = freeVars(tm0.asInstanceOf[Term])
                def extractFree(x: (Term, Term)): List[Term] = {
                  freeVars(snd(x))
                }
                val vsf_ = flatten(map(extractFree, theta))
                val u = cvariant(vs0 ::: vsf_ ::: vsf, v.asInstanceOf[Term])
                val tm0_ = subst0(vs0, ((v.asInstanceOf[Term], u):: theta_), tm0.asInstanceOf[Term])
                mkAbs(u, tm0_)
            }
        }
    }
  }

  def subst(theta: List[(Term, Term)], tm: Term): Term = {
    assert1(forall[(Term, Term)](sameTypes, theta), "Non-equal types in substitution list")
    subst0(List.empty, theta, tm)
  }

  def varMatch0(btheta: List[(Term, Term)], theta: List[(Term, Term)], patt: Term, tm: Term): List[(Term, Term)] = {
    (destTerm(patt), destTerm(tm)) match {
      case (TmvarDestructed(_, _), _) =>
        if(can(assoc.curried(patt), btheta)){
          val tm_ = assoc(patt, btheta)
          assert1(termEq(tm_, tm), "Match failure")
          assert1(can(invAssoc.curried(tm),btheta),"Match failure")
          val patt_ = invAssoc(tm, btheta)
          assert1(termEq(patt_, patt), "Match failure")
          theta
        }
        else{
          def fun1(v: Term): Boolean = cannot(invAssoc.curried(v), btheta)
          assert1(forall(fun1, freeVars(tm)), "Match failure")
          if(can(assoc.curried(patt), theta)){
            val tm_ = assoc(patt, theta)
            assert1(alphaEq(tm, tm_), "Match failure")
            theta
          }
          else{
            val theta1 = (patt, tm) :: theta
            theta1
          }
        }
      case (TmconstDestructed(_,_), TmconstDestructed(_,_)) => {
        assert1(termEq(patt, tm), "Match failure")
        theta
      }
      case (TmcombDestructed(patt1, patt2), TmcombDestructed(tm1, tm2)) => {
        val theta1 = varMatch0(btheta, theta, patt1.asInstanceOf[Term], tm1.asInstanceOf[Term])
        varMatch0(btheta, theta1, patt2.asInstanceOf[Term], tm2.asInstanceOf[Term])
      }
      case (TmabsDestructed(pattv, patt0), TmabsDestructed(v, tm0)) =>{
        varMatch0((pattv.asInstanceOf[Term], v.asInstanceOf[Term])::btheta, theta, patt0.asInstanceOf[Term], tm0.asInstanceOf[Term])
      }
      case _ => throw ScolFail("Match failure")
    }
  }

  def varMatch(patt: Term, tm: Term): List[(Term, Term)] = varMatch0(List.empty, List.empty, patt, tm)

  def termMatch0(btheta: List[(Term, Term)], theta: List[(Term, Term)], tytheta: List[(HolType, HolType)], patt: Term, tm: Term): (List[(Term, Term)], List[(HolType, HolType)]) = {
    (destTerm(patt), destTerm(tm)) match {
      case (TmvarDestructed(_,_),_) =>
        val tytheta1 = typeMatch0(tytheta, typeOf(patt), typeOf(tm))
        val patt_ = tyvarInst(tytheta1, patt)
        if(can(assoc.curried(patt_), btheta)){
          val tm_ = assoc(patt_, btheta)
          assert1(termEq(tm_, tm), "Match failure")
          assert1(can(invAssoc.curried(tm), btheta), "Match failure")
          val patt__ = invAssoc(tm, btheta)
          assert1(termEq(patt__, patt_), "Match failure")
          (theta, tytheta1)
        }
        else{
          def fun1(v: Term) = cannot(invAssoc.curried(v), btheta)
          assert1(forall(fun1, freeVars(tm)), "Match failure")
          if(can(assoc.curried(patt_), theta)){
            val tm_ = assoc(patt_, theta)
            assert1(alphaEq(tm, tm_), "Match failure")
            (theta, tytheta1)
          }
          else{
            val theta1 = (patt_, tm) :: theta
            (theta1, tytheta1)
          }
        }
      case (TmconstDestructed(_, _), TmconstDestructed(_,_)) => {
        val tytheta1 = typeMatch0(tytheta, typeOf(patt), typeOf(tm))
        val patt_ = tyvarInst(tytheta1, patt)
        // @FixMe I don't have a clue what the code here means
        assert1(termEq(patt_, tm), "Match failure")
        (theta, tytheta1)
      }
      case (TmcombDestructed(patt1, patt2), TmcombDestructed(tm1, tm2)) =>{
        val (theta1, tytheta1) = termMatch0(btheta, theta, tytheta, patt1.asInstanceOf[Term], tm1.asInstanceOf[Term])
        termMatch0(btheta, theta1, tytheta1, patt2.asInstanceOf[Term], tm2.asInstanceOf[Term])
      }
      case (TmabsDestructed(pattv, patt0), TmabsDestructed(v, tm0)) =>{
        val tytheta1 = typeMatch0(tytheta, typeOf(pattv.asInstanceOf[Term]), typeOf(v.asInstanceOf[Term]))
        val pattv_ = tyvarInst(tytheta1, pattv.asInstanceOf[Term])
        termMatch0((pattv_, v.asInstanceOf[Term])::btheta, theta, tytheta1, patt0.asInstanceOf[Term], tm0.asInstanceOf[Term])
      }
      case _ => throw ScolFail("Match failure")
    }
  }

  def termMatch(patt: Term, tm: Term): (List[(Term, Term)], List[(HolType, HolType)]) = termMatch0(List.empty, List.empty, List.empty, patt, tm)

  def renameBvar(x_ : String, tm: Term ): Term = {
    assert1(can(destAbs, tm), "Not a lambda abstraction")
    val (v, tm0) = destAbs(tm)
    val v_ = mkVar(x_, typeOf(v))
    def not(x: Boolean): Boolean = !x
    assert1(not(varFreeIn(v_, tm)), "New variable occurs free in term")
    val tm0_ = varInst(List((v, v_)), tm0)
    mkAbs(v_, tm0_)
  }

  def findSubterm(testFn: Term => Boolean, tm: Term): Term = {
    if(testFn(tm)) tm
    else{
      destTerm(tm) match{
        case TmcombDestructed(tm1, tm2) => {
          try{
            findSubterm(testFn, tm1.asInstanceOf[Term])
          }catch{
            case _: ScolFail => findSubterm(testFn, tm2.asInstanceOf[Term])
          }
        }
        case TmabsDestructed(v, tm0) => findSubterm(testFn, tm0.asInstanceOf[Term])
        case _ => throw ScolFail("No subterm fits")
      }
    }
  }

  def findSubterms0(tms: List[Term], testFn: Term => Boolean, tm: Term): List[Term] = {
    if(testFn(tm)) tm :: tms
    else{
      destTerm(tm) match{
        case TmcombDestructed(tm1, tm2) =>{
          val tms_ = findSubterms0(tms, testFn, tm2.asInstanceOf[Term])
          findSubterms0(tms_, testFn, tm1.asInstanceOf[Term])
        }
        case TmabsDestructed(v, tm0) => findSubterms0(tms, testFn, tm0.asInstanceOf[Term])
        case _ => tms
      }
    }
  }

  def findSubterms(testFn: Term => Boolean, tm: Term): List[Term] =
    findSubterms0(List.empty, testFn, tm)

  def destEqthm(th: Thm): (Term, Term) = destEq(concl(th.asInstanceOf[Theorem]))

  def eqthmLhs(th: Thm): Term = eqLhs(concl(th.asInstanceOf[Theorem]))

  def eqthmRhs(th: Thm): Term = eqRhs(concl(th.asInstanceOf[Theorem]))

  def isEqthm(th: Thm): Boolean = isEq(concl(th.asInstanceOf[Theorem]))

  def thmFreeVars(th: Thm): List[Term] = {
    val (hs, c) = destThm(th.asInstanceOf[Theorem])
    val hvss = map(freeVars, hs)
    val cvs = freeVars(c)

    union_(termEq.curried, unions_(termEq.curried, hvss), cvs)
  }

  def thmAlphaEq(th1: Thm, th2: Thm): Boolean = {
    val (hs1, c1) = destThm(th1.asInstanceOf[Theorem])
    val (hs2, c2) = destThm(th2.asInstanceOf[Theorem])

    (alphaEq(c1, c2)) && (setEq_(alphaEq.curried, hs1, hs2))
  }

}
