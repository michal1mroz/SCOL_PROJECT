package main.scala

import main.scala.Lib.{disjoint, setify, try0}
import main.scala.Preterm.*
import main.scala.Term.{Term, getConstGtype, termEq}
import main.scala.Type.{HolType, destVarType, primGetTyconstArity}
import main.scala.Utils1.typeTyVars
import main.scala.utils.ScolException.{ScolError, ScolFail, TypeFail}

import scala.annotation.tailrec

object TypeAnal {

  private def FunError1(): TypeFail = TypeFail("Function subterm does not have function type")

  private def FunError2(): TypeFail = TypeFail("Function subterm domain type incompatible with argument subterm type")

  private def OverloadError(msg: String): TypeFail = TypeFail("Overloaded var " + msg + " type not resolved at name closure")

  private def AnnotError(): TypeFail = TypeFail("Subterm type incompatible with type annotation")

  private def TypesError(): TypeFail = TypeFail("Supplied types do no unify")

  private def ArityError(name: String, n1: Int, n2: Int): TypeFail = TypeFail("Type constant " + name + " has arity " + n1 +
    " but is used with type param list length " + n2)

  private def pretypeOk(pty: Pretype): Boolean = {
    pty match {
      case Ptyvar(_) | Ptygvar(_) => true
      case Ptycomp(x, ptys) =>
        val n = primGetTyconstArity(x)
        assert(ptys.length == n, ArityError(x, n, ptys.length))
        ptys.forall(pretypeOk)
    }
  }

  def check_pretype(pty: Pretype): Pretype = {
    try {
      pretypeOk(pty)
      pty
    } catch {
      case e: TypeFail => throw TypeFail(e.getMessage)
    }
  }

  var pretypeGvarCounter: Int = 0

  def resetPretypeGvarCounter(): Unit = {
    pretypeGvarCounter = 0
  }

  def newPretypeGvar(): Pretype = {
    val n = pretypeGvarCounter
    if (n >= Int.MaxValue)
      throw ScolFail("Exceeded generated type variable maximum")
    pretypeGvarCounter += 1
    Ptygvar(n)
  }

  def generateVarPreterm(x: String): Preterm = {
    Ptmvar(x, newPretypeGvar())
  }

  def generateConstPreterm(x: String): Preterm = {
    val ty = try0(getConstGtype, x, ScolFail("generateConstPreterm: ?"))
    val tyvs = typeTyVars(ty)
    val pty = typeToPretype(ty)
    val foo: HolType => (Pretype, Pretype) = tyv => {
      val x = destVarType(tyv)
      val ptyVar = newPretypeGvar()
      (Ptyvar(x), ptyVar)
    }
    val theta = tyvs.map(foo)
    val ptyInst = pretypeInst(theta, pty)
    Ptmconst(x, ptyInst)
  }

  private def detypePreterm0(ptm: Preterm): Preterm = {
    ptm match {
      case Ptmvar(x, _) => generateVarPreterm(x)
      case Ptmconst(x, _) => generateConstPreterm(x)
      case Ptmcomb(ptm1, ptm2) =>
        val ptm1_ = detypePreterm0(ptm1)
        val ptm2_ = detypePreterm0(ptm2)
        Ptmcomb(ptm1_, ptm2_)
      case Ptmabs(v, ptm0) =>
        val v_ = detypePreterm0(v)
        val ptm0_ = detypePreterm0(ptm0)
        Ptmabs(v_, ptm0_)
      case Ptmtyped(ptm0, pty) =>
        val ptm0_ = detypePreterm0(ptm0)
        Ptmtyped(ptm0_, pty)
    }
  }

  def detypePreterm(ptm: Preterm): Preterm = {
    resetPretypeGvarCounter()
    detypePreterm0(ptm)
  }


  def basicUnifyPretypes(pty1: Pretype, pty2: Pretype): List[(Pretype, Pretype)] = {
    (pty1, pty2) match {

      case (a, b) if a == b => List()
      case (Ptygvar(n1), Ptygvar(n2)) =>
        if (n1 < n2) List((pty2, pty1)) else List((pty1, pty2))
      case (Ptygvar(_), _) => List((pty1, pty2))
      case (_, Ptygvar(_)) => List((pty2, pty1))
      case (Ptycomp(x1, ptys1), Ptycomp(x2, ptys2)) =>
        assert(x1 == x2, "Types do not match")
        ptys1.zip(ptys2).flatMap { case (p1, p2) => basicUnifyPretypes(p1, p2) }
      case _ => throw TypesError()
    }
  }

  // Instantiation closure

  def thetaInst(theta0: List[(Pretype, Pretype)], theta: List[(Pretype, Pretype)]): List[(Pretype, Pretype)] = {
    theta.map { case (gty, pty) => (gty, pretypeInst(theta0, pty)) }
  }

  @tailrec
  def thetaClosure(theta0: List[(Pretype, Pretype)], theta: List[(Pretype, Pretype)]): List[(Pretype, Pretype)] = {
    theta match {
      case (gty, pty) :: theta1 =>
        val gtys = pretypeGtyvars(pty)
        val gtys0 = theta0.map(_._1)
        if (pty == gty) {
          // Identity map: remove
          thetaClosure(theta0, theta1)
        } else if (gtys.contains(gty)) {
          // Cyclical map: fail
          throw TypesError()
        } else if (gtys0.contains(gty)) {
          // Already in 'theta0': unify with existing pretype
          val pty0 = theta0.find(_._1 == gty).get._2
          val theta2 = basicUnifyPretypes(pty, pty0)
          thetaClosure(theta0, theta2 ++ theta1)
        } else if (!disjoint(gtys, gtys0)) {
          // Result includes 'theta0' entry: use 'theta0' on result
          val ptyPrime = pretypeInst(theta0, pty)
          thetaClosure(theta0, (gty, ptyPrime) :: theta1)
        } else {
          // Otherwise: incorporate into 'theta0'
          val theta0_ = thetaInst(List((gty, pty)), theta0)
          thetaClosure((gty, pty) :: theta0_, theta1)
        }
      case Nil => theta0
    }
  }

  private def unifyPretypes0(theta0: List[(Pretype, Pretype)], pty1: Pretype, pty2: Pretype): List[(Pretype, Pretype)] = {
    val theta12 = basicUnifyPretypes(pty1, pty2)
    thetaClosure(theta0, theta12)
  }

  def unifyPretypes(pty1: Pretype, pty2: Pretype): List[(Pretype, Pretype)] = {
    unifyPretypes0(Nil, pty1, pty2)
  }

  // Pretype list unification

  def unifyPretypeList(theta0: List[(Pretype, Pretype)], ptys: List[Pretype]): List[(Pretype, Pretype)] = {
    val (pty1, ptys2) = (ptys.head, ptys.tail)
    ptys2.foldLeft(theta0) { (theta, pty) => unifyPretypes0(theta, pty1, pty) }
  }

  // Pretypes pairs unification

  def unifyPretypePairs(theta0: List[(Pretype, Pretype)], ptyptys: List[(Pretype, Pretype)]): List[(Pretype, Pretype)] = {
    ptyptys.foldLeft(theta0) { case (theta, (pty1, pty2)) => unifyPretypes0(theta, pty1, pty2) }
  }

  // Variable environment

  type VarEnv = List[(String, List[Pretype])]

  def varenvInst(theta: List[(Pretype, Pretype)], venv : VarEnv): VarEnv = {
    val foo = (ptys : List[Pretype]) => setify(ptys.map(pretypeInst(theta, _)))
    venv.map((s, lp) => (s, foo(lp)))
  }

  def varenvSubtract(venv : VarEnv, x: String, pty: Pretype): VarEnv = {
    venv match {
      case (x0, ptys) :: rest =>
        if (x == x0) {
          val ptysPrime = ptys.filterNot(_ == pty)
          if (ptysPrime.isEmpty) rest else (x0, ptysPrime) :: rest
        } else {
          (x0, ptys) :: varenvSubtract(rest, x, pty)
        }
      case Nil => Nil
    }
  }

  def varenvUnion(venv1 : VarEnv, venv2: VarEnv): VarEnv = {
    (venv1, venv2) match {
      case ((x1, ptys1) :: rest1, (x2, ptys2) :: rest2) =>
        if (x1 < x2) (x1, ptys1) :: varenvUnion(rest1, venv2)
        else if (x2 < x1) (x2, ptys2) :: varenvUnion(venv1, rest2)
        else (x1, (ptys1 ++ ptys2).distinct) :: varenvUnion(rest1, rest2)
      case (_, Nil) => venv1
      case (Nil, _) => venv2
    }
  }


  def closeName0(venv: VarEnv, x: String, theta: List[(Pretype, Pretype)]): List[(Pretype, Pretype)] = {
    val ptys = venv.find(_._1 == x).get._2
    val (ptys1, ptys2) = ptys.partition(pt => pretypeGtyvars(pt).isEmpty)
    (ptys1, ptys2) match {
      case (_, Nil) =>
        // All 'x's already resolved
        theta
      case (List(_), _) | (Nil, _ :: _) =>
        // Some 'x's unresolved, and 0/1 different resolved 'x's
        try {
          unifyPretypeList(theta, ptys)
        } catch {
          case _: Exception => throw OverloadError(x)
        }
      case _ =>
        // Some 'x's unresolved, and 2 or more different resolved 'x's
        throw OverloadError(x)
    }
  }

  def closeName(x: String, pty: Pretype, theta: List[(Pretype, Pretype)], venv : VarEnv): (List[(Pretype, Pretype)], VarEnv) = {
    val thetaPrime = closeName0(venv, x, theta)
    val ptyPrime = pretypeInst(thetaPrime, pty)
    val venvPrime = varenvSubtract(venv, x, ptyPrime)
    (thetaPrime, venvPrime)
  }

  def closeAllNames(theta: List[(Pretype, Pretype)], venv : VarEnv): List[(Pretype, Pretype)] = {

    val xs = venv.map(_._1).distinct
    xs.foldRight(theta)((x, accTheta) => closeName0(venv, x, accTheta))

  }

// Type inference algorithm

  private def inferPretypes0(ptm: Preterm): (Pretype, List[(Pretype, Pretype)], VarEnv) = {
    ptm match {
      case Ptmvar(x, pty) =>
        (pty, Nil, List((x, List(pty))))
      case Ptmconst(x, pty) =>
        (pty, Nil, Nil)
      case Ptmcomb(ptm1, ptm2) =>
        val (pty1, theta1, venv1) = inferPretypes0(ptm1)
        val (pty2, theta2, venv2) = inferPretypes0(ptm2)
        val theta12 = theta1 ++ theta2
        val venv12 = varenvUnion(venv1, venv2)
        val (ptya, ptyb) = try {
          destFunPretype(pty1)
        } catch {
          case _: RuntimeException if isGtyvarPretype(pty1) =>
            (pty2, newPretypeGvar())
          case _: RuntimeException => throw FunError1()
        }
        val ptyab = mkFunPretype(ptya, ptyb)
        val theta = try {
          unifyPretypePairs(theta12, List((ptyab, pty1), (ptya, pty2)))
        } catch {
          case _: Exception => throw FunError2()
        }
        val venv = varenvInst(theta, venv12)
        val ptyPrime = pretypeInst(theta, ptyb)
        (ptyPrime, theta, venv)
      case Ptmabs(ptm1, ptm2) =>
        val (pty1, theta1, venv1) = inferPretypes0(ptm1)
        val (pty2, theta2, venv2) = inferPretypes0(ptm2)
        val x = atomPretermName(ptm1)
        val pty12 = mkFunPretype(pty1, pty2)
        val theta12 = theta1 ++ theta2
        val venv12 = varenvUnion(venv1, venv2)
        val (theta, venv) = closeName(x, pty1, theta12, venv12)
        val ptyPrime = pretypeInst(theta, pty12)
        (ptyPrime, theta, venv)
      case Ptmtyped(ptm0, pty) =>
        pretypeOk(pty)
        val (pty0, theta0, venv0) = inferPretypes0(ptm0)
        val theta = try {
          unifyPretypes0(theta0, pty0, pty)
        } catch {
          case _: Exception => throw AnnotError()
        }
        val venv = varenvInst(theta, venv0)
        val ptyPrime = pretypeInst(theta, pty0)
        (ptyPrime, theta, venv)
    }
  }

  def inferPretypes(ptm: Preterm): List[(Pretype, Pretype)] = {
    try {
      val (_, theta0, venv) = inferPretypes0(ptm)
      closeAllNames(theta0, venv)
    } catch {
      case TypeFail(x) => throw ScolError("TYPE ERROR: ", x)
    }
  }

  def resolvePreterm(ptm: Preterm): Preterm = {
    val theta = inferPretypes(ptm)
    pretermInst(theta, ptm)
  }

// Consistency checks

  def checkPretermAnnotations(tm: Term, ptm: Preterm): Preterm = {
    try {
      val ptm0 = detypePreterm(ptm)
      val ptm0Prime = resolvePreterm(ptm0)
      val tm0Prime = pretermToTerm(ptm0Prime)
      assert(termEq(tm0Prime, tm))
      ptm0Prime
    } catch {
      case _: Exception => throw new RuntimeException("Internal error: checkPretermAnnotations")
    }
  }

}