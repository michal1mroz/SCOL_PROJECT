package main.scala

import main.scala.Lib.{assert0, assert1, cannot, quote}
import main.scala.Thm.*
import main.scala.Utils1.*
import main.scala.Utils2.*
import main.scala.utils.ScolException.{LocalFail, ScolFail}

import scala.collection.mutable
import scala.collection.mutable.HashMap


object Store {
  private val theTheorems: mutable.HashMap[String, Thm] = mutable.HashMap.empty

  def getThm(x: String): Thm = {
    theTheorems.getOrElse(x, throw ScolFail(s"No theorem called $x"))
  }

  def getAllThms: List[(String, Thm)] = {
    theTheorems.toList
  }

  def saveThm(x: String, th: Thm): Thm = {
    try{
      assert1(asms(th).isEmpty, "Assumptions not allowed")
      assert1(thmFreeVars(th).isEmpty, "Free vars not allowed")
      assert0(cannot(getThm, x), LocalFail)
      theTheorems.put(x, th)
      th
    }catch {
      case _: LocalFail =>
        val th0 = getThm(x)
        assert1(thmAlphaEq(th, th0), s"Theorem name $x already used")
        th
    }
  }

  private val theLemmas: mutable.HashMap[String, Thm] = mutable.HashMap.empty

  def getLemma(x: String): Thm = {
    theLemmas.getOrElse(x, throw ScolFail(s"No lemma called $x"))
  }

  def getAllLemmas: List[(String, Thm)] = {
    theLemmas.toList
  }

  def saveLemma(x: String, th: Thm): Thm = {
    try{
      assert0(cannot(getLemma, x), LocalFail)
      theLemmas.put(x, th)
      th
    } catch{
      case _: LocalFail =>
        val th0 = getLemma(x)
        assert1(thmAlphaEq(th, th0), s"Lemma name $quote(x) already used")
        th
    }
  }

}
