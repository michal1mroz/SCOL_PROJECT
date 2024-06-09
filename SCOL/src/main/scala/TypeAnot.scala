
package main.scala

import main.scala.Lib.{curry, invAssoc, setify, setify_, union}
import main.scala.Preterm.*
import main.scala.Term.getConstGtype
import main.scala.Type.Tyvar
import main.scala.TypeAnal.{detypePreterm, newPretypeGvar, thetaClosure, unifyPretypeList, unifyPretypePairs, unifyPretypes0}
import main.scala.Utils1.typeTyVars
import main.scala.utils.ScolException.ScolFail

import scala.annotation.tailrec


object TypeAnot {

    def domainRestrict[T, U](xs: List[T], xys: List[(T, U)]): List[(T, U)] = {
      xys.filter { case (x, _) => xs.contains(x) }
    }

    @tailrec
    def pretermVar(ptm: Preterm): Preterm = ptm match {
      case v: Ptmvar => v
      case Ptmtyped(ptm0, _) => pretermVar(ptm0)
      case _ => throw ScolFail(": preterm_var, ?")
    }

    def varEquiv1(v1: Preterm, v2: Preterm): Boolean = atomPretermName(v1) == atomPretermName(v2)

    def varEquiv2(theta: List[(Pretype, Pretype)], v1: Preterm, v2: Preterm): Boolean =
      pretermInst(theta, v1) == pretermInst(theta, v2)

    def atomTypeComplexity(ptm: Preterm): Int = ptm match {
      case Ptmvar(_, pty) => pretypeComplexity(pty)
      case Ptmconst(_, pty) => pretypeComplexity(pty)
      case _ => throw ScolFail(" atom_type_complexity, ?")
    }

    def sortByTypeComplexity(ptms: List[Preterm]): List[Preterm] = {
      val nptms = ptms.map(ptm => (atomTypeComplexity(ptm), ptm))
      val nptmsSorted = nptms.sortBy(_._1)
      nptmsSorted.map(_._2)
    }

    def unresolvedAtoms(atms: List[Preterm]): List[Preterm] =
      atms.filter(pretermHasGtyvars)

    def orderedUnresolvedAtoms(atms: List[Preterm]): List[Preterm] =
      sortByTypeComplexity(unresolvedAtoms(atms))

    def fullAnnotatePreterm(fl: Boolean, ptm: Preterm): Preterm = ptm match {
      case Ptmvar(_, pty) =>
        Ptmtyped(ptm, pty)
      case Ptmconst(x, pty) =>
        if (typeTyVars(getConstGtype(x)).nonEmpty)
          Ptmtyped(ptm, pty)
        else
          ptm
      case Ptmcomb(ptm1, ptm2) =>
        if (fl && isCondPreterm(ptm)) {
          val (ptm1, ptm2, ptm3) = destCondPreterm(ptm)
          val ptm1Annotated = fullAnnotatePreterm(fl, ptm1)
          val ptm2Annotated = fullAnnotatePreterm(fl, ptm2)
          val ptm3Annotated = fullAnnotatePreterm(fl, ptm3)
          mkCondPreterm(ptm1Annotated, ptm2Annotated, ptm3Annotated)
        } else if (fl && isPairPreterm(ptm)) {
          val ptms = stripPairPreterm(ptm)
          val ptmsAnnotated = ptms.map(fullAnnotatePreterm(fl, _))
          listMkPairPreterm(ptmsAnnotated)
        } else if (fl && isLetPreterm(ptm)) {
          val (vptms, ptm0) = destLetPreterm(ptm)
          val vptmsAnnotated = vptms.map { case (v, ptm) =>
            (fullAnnotatePreterm(fl, v), fullAnnotatePreterm(fl, ptm))
          }
          val ptm0Annotated = fullAnnotatePreterm(fl, ptm0)
          mkLetPreterm(vptmsAnnotated, ptm0Annotated)
        } else {
          val ptm1Annotated = fullAnnotatePreterm(fl, ptm1)
          val ptm2Annotated = fullAnnotatePreterm(fl, ptm2)
          Ptmcomb(ptm1Annotated, ptm2Annotated)
        }
      case Ptmabs(ptm1, ptm2) =>
        val ptm1Annotated = fullAnnotatePreterm(fl, ptm1)
        val ptm2Annotated = fullAnnotatePreterm(fl, ptm2)
        Ptmabs(ptm1Annotated, ptm2Annotated)
      case Ptmtyped(ptm0, pty) =>
        ptm0 match {
          case _: Ptmvar | _: Ptmconst => ptm
          case _ =>
            val ptm0Annotated = fullAnnotatePreterm(fl, ptm0)
            Ptmtyped(ptm0Annotated, pty)
        }
    }

    @tailrec
    private def siftAtoms0(atms0: List[Preterm], gtys0 : List[Pretype], atms: List[Preterm]): List[Preterm] = {
      atms match {
        case atm1 :: atms2 =>
          val gtys1 = pretermGtyvars(atm1)
          val gtys2 = gtys1 filterNot gtys0.contains
          if (gtys2.isEmpty)
            siftAtoms0(atms0, gtys0, atms2)
          else {
            val atms0Updated = atm1 :: atms0
            val gtys0Updated = gtys2 ++ gtys0
            siftAtoms0(atms0Updated, gtys0Updated, atms2)
          }
        case Nil => atms0
      }
    }

    def siftAtoms(gtys0: List[Pretype], atms: List[Preterm]): List[Preterm] = {
      val atms1 = siftAtoms0(Nil, gtys0, atms) // Traversal 1
      val atms2 = siftAtoms0(Nil, gtys0, atms1) // Traversal 2
      atms2
    }


  // Closure information

    def closureInfo(thetaC: List[(Pretype, Pretype)], theta0: List[(Pretype, Pretype)], fvs: List[Preterm], v: Preterm)
    : (List[Preterm], List[Preterm], List[(Pretype, Pretype)]) = {
      val vs1 = fvs.filter(varEquiv1(v, _))
      val vs2 = vs1.filter(varEquiv2(thetaC, v, _))

      if (vs2.length < vs1.length) {
        val vtheta = vs1.map(v => (v, pretermInst(theta0, v)))
        val vsPrime = orderedUnresolvedAtoms(vtheta.map(_._2))
        val vsDoublePrime = siftAtoms(Nil, vsPrime)
        val ovs = vsDoublePrime.map(vPrime => invAssoc(vPrime, vtheta))
        val gtys = ovs.map( destVarPreterm andThen (x => x._2))
        val theta1 = domainRestrict(gtys, thetaC)
        val theta0Prime = thetaClosure(theta0, theta1)
        (ovs, vs2, theta0Prime)
      } else {
        val ptys = vs1.map(destVarPreterm andThen (x => x._2))
        val theta0Prime = unifyPretypeList(theta0, ptys)
        (Nil, vs2, theta0Prime)
      }
    }

    // Atom information
    private def atomInfo0(thetaC: List[(Pretype, Pretype)], ptm: Preterm)
    : (List[Preterm], List[Preterm], List[Preterm], List[Preterm], Pretype, List[(Pretype, Pretype)]) = 
      ptm match {
      case Ptmvar(x, pty) => (Nil, List(ptm), Nil, Nil, pty, Nil)
      case Ptmconst(x, pty) =>
        if (pretypeHasGtyvars(pty)) (Nil, Nil, Nil, List(ptm), pty, Nil)
        else (Nil, Nil, Nil, Nil, pty, Nil)
      case Ptmcomb(ptm1, ptm2) =>
        val (ovs1, fvs1, bvs1, pcs1, pty1, theta1) = atomInfo0(thetaC, ptm1)
        val (ovs2, fvs2, bvs2, pcs2, pty2, theta2) = atomInfo0(thetaC, ptm2)
        val ovs = ovs1 ++ ovs2
        val fvs = fvs1 ++ fvs2
        val bvs = bvs1 ++ bvs2
        val pcs = union(pcs1, pcs2)
        val theta12 = theta1 ++ theta2
        val (ptya, ptyb) = try destFunPretype(pty1) catch {
          case _: ScolFail => (pty2, newPretypeGvar())
        }
        val ptyab = mkFunPretype(ptya, ptyb)
        val theta = unifyPretypePairs(theta12, List((ptyab, pty1), (ptya, pty2)))
        val ptybPrime = pretypeInst(theta, ptyb)
        (ovs, fvs, bvs, pcs, ptybPrime, theta)
      case Ptmabs(ptmv, ptm0) =>
        val v = pretermVar(ptmv)
        val ptyv = (destVarPreterm andThen (x => x._2))(v)
        val (ovs0, fvs0, bvs0, pcs0, pty0, theta0) = atomInfo0(thetaC, ptm0)
        val fvs00 = v :: fvs0
        val (ovs1, bvs1, theta) = closureInfo(thetaC, theta0, fvs00, v)
        val ovs = union(ovs0, ovs1)
        val fvs = fvs00 filterNot bvs1.contains
        val bvs = bvs1 ++ bvs0
        val pty12 = mkFunPretype(ptyv, pty0)
        val ptyPrime = pretypeInst(theta, pty12)
        (ovs, fvs, bvs, pcs0, ptyPrime, theta)
      case Ptmtyped(ptm0, pty) =>
        val (ovs0, fvs0, bvs0, pcs0, pty0, theta0) = atomInfo0(thetaC, ptm0)
        val theta = unifyPretypes0(theta0, pty0, pty)
        val ptyPrime = pretypeInst(theta, pty0)
        (ovs0, fvs0, bvs0, pcs0, ptyPrime, theta)
    }

    def atomInfo(thetaC: List[(Pretype, Pretype)], ptm: Preterm)
    : (List[Preterm], List[Preterm], List[Preterm], List[Preterm], List[(Pretype, Pretype)]) = {
      val (ovs0, fvs0, bvs0, pcs0, _, theta0) = atomInfo0(thetaC, ptm)
      val fvs00 = setify_(curry(varEquiv2(thetaC, _, _)), fvs0)
      val (ovs1, theta) = fvs00.foldLeft((ovs0, theta0)) { 
        case ((ovsAcc, thetaAcc), fv0) =>
        val (ovs0Prime, _, theta0Prime) = closureInfo(thetaC, thetaAcc, fvs0, fv0)
        val ovs0DoublePrime = union(ovsAcc, ovs0Prime)
        (ovs0DoublePrime, theta0Prime)
      }
      val bvs1 = bvs0 filterNot ovs1.contains
      val fvs1 = fvs0 filterNot ovs1.contains
      (ovs1, fvs1, bvs1, pcs0, theta)
    }

    // Picking atoms for annotation

    def pickAtomCoverage(thetaC: List[(Pretype, Pretype)], ptyOpt: Option[Pretype], ptm: Preterm): List[Preterm] = {
      val ptm1 = ptyOpt match {
        case Some(pty) => Ptmtyped(ptm, pty)
        case None => ptm
      }
      val (ovs, fvs, bvs, pcs, theta) = atomInfo(thetaC, ptm1)
      val atomTheta = (atms: List[Preterm]) => atms.map(atm => (atm, pretermInst(theta, atm)))
      val ovTheta = atomTheta(ovs)
      val fvTheta = atomTheta(fvs)
      val bvTheta = atomTheta(bvs)
      val pcTheta = atomTheta(pcs)
      val fvsPrime = orderedUnresolvedAtoms(fvTheta.map(_._2))
      val bvsPrime = unresolvedAtoms(bvTheta.map(_._2))
      val pcsPrime = orderedUnresolvedAtoms(pcTheta.map(_._2))
      val gtys0 = ovTheta.flatMap { case (_, preterm) => pretermGtyvars(preterm) }.toSet.toList
      val atmsPrime = siftAtoms(gtys0, bvsPrime ++ fvsPrime ++ pcsPrime)
      val atmTheta = bvTheta ++ fvTheta ++ pcTheta
      val atms = atmsPrime.map(atm => invAssoc(atm, atmTheta))
      ovs ++ atms
    }

    // Annotating preterm atoms

    def annotatePretermAtoms(thetaC: List[(Pretype, Pretype)], atms: List[Preterm], ptm: Preterm): Preterm
    = ptm match {
      
      case Ptmvar(x, pty) =>
        if (atms.contains(ptm)) {
          val ptyPrime = pretypeInst(thetaC, pty)
          Ptmtyped(ptm, ptyPrime)
        } else ptm
        
      case   Ptmconst(x, pty) =>
          if (atms.contains(ptm)) {
          val ptyPrime = pretypeInst(thetaC, pty)
            Ptmtyped(ptm, ptyPrime)
          } else ptm
          
      case Ptmcomb(ptm1, ptm2) =>
        val ptm1Prime = annotatePretermAtoms(thetaC, atms, ptm1)
        val ptm2Prime = annotatePretermAtoms(thetaC, atms, ptm2)
        if (ptm1Prime == ptm1 && ptm2Prime == ptm2) ptm else Ptmcomb(ptm1Prime, ptm2Prime)
        
      case Ptmabs(ptm1, ptm2) =>
        val ptm1Prime = annotatePretermAtoms(thetaC, atms, ptm1)
        val ptm2Prime = annotatePretermAtoms(thetaC, atms, ptm2)
        if (ptm1Prime == ptm1 && ptm2Prime == ptm2) ptm else Ptmabs(ptm1Prime, ptm2Prime)
        
      case Ptmtyped(ptm0, pty) =>
        val ptm0Prime = annotatePretermAtoms(thetaC, atms, ptm0)
        if (ptm0Prime == ptm0) ptm else Ptmtyped(ptm0Prime, pty)
    }

    // Type annotation

    def minAnnotatePreterm(ptyOpt: Option[Pretype], ptm: Preterm): Preterm = {
      val ptm1 = detypePreterm(ptm)
      val thetaC = pretermPretypeMatch((ptm1, ptm))
      val atms = pickAtomCoverage(thetaC, ptyOpt, ptm1)
      annotatePretermAtoms(thetaC, atms, ptm1)
    }

}
