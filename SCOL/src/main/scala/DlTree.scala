package main.scala

import scala.math.{Ordering, log, min}
import scala.Function1.*

import Lib.{cut, hdTl, mergesort}

import scala.annotation.tailrec

class DlTree[A, B]


object DlTree {
  type DlTree[A, B] = Node[A, B]
  sealed trait Node[A, B]
  case class Branch[A, B](key: Int, value: (A, B), left: DlTree[A, B], right: DlTree[A, B]) extends Node[A, B]
  case class Leaf[A, B]() extends Node[A, B]

  /**
   * @tparam A
   * @tparam B
   * @return Empty DlTree
   */
  def dltreeEmpty[A, B]: DlTree[Nothing, Nothing] = Leaf()

  /**
   *
   * @param tr dltree to be printed out
   * @tparam A
   * @tparam B
   * Primitive print out of a given tree, created for console debugging
   */

  def dltreePrint[A, B](tr: DlTree[A, B]): Unit = {
    @tailrec
    def printLevel(level: List[DlTree[A, B]]): Unit = {
      if (level.nonEmpty){
        val (nextLevel, values) = level.foldLeft((List.empty[DlTree[A, B]], List.empty[(A,B)])){
          case ((accLevel, accValues), Branch(_, (key, value), left, right)) =>
            (accLevel ::: List(left, right), accValues::: List((key, value)))
          case ((accLevel, accValues), _) => (accLevel, accValues)
        }
        val levelValues = values.reverse.map {case (key, value) => s"($key, $value)"}.mkString(", ")
        println(levelValues)
        printLevel(nextLevel.reverse)
      }
    }
    printLevel(List(tr))
  }

  /**
   * @param n - type Double, number we want to calculate log of
   * @return value of logarithm base 2 of number n
   */
  def log2(n: Double): Double = {
    log(n) / log(2)
  }

  /**
   *
   * @param n number of elements in List
   * @param xys list of elements
   * @tparam A
   * @tparam B
   * @return Node[A,B] - root of a tree created from the given list
   */
  def dltreeUncheckedLoad0[A, B](n: Int, xys: List[(A,B)]): Node[A,B] = {
    if (n > 0) {
      val i = n / 2
      val (xys1, xys02) = cut(i, xys)
      val (xy, xys2) = hdTl(xys02)
      val h = log2(n + 2).toInt
      val tr1 = dltreeUncheckedLoad0(i - 1, xys1)
      val tr2 = dltreeUncheckedLoad0(n - i - 1, xys2)
      Branch(h, xy, tr1, tr2)
    }
    else{
      Leaf()
    }
  }

  // Entry function for a function above
  def dltreeUncheckedLoad[A, B](xys: List[(A, B)]): Node[A, B] = {
    val n = xys.length + 1 // If you find out why I need this +1 please tell me :<
    dltreeUncheckedLoad0(n, xys)
  }

  /**
   * Default method to create a tree. Returns the root Node
   * @param xys must support Ordering
   * @param ord
   * @tparam A
   * @tparam B
   * @return
   */
  def dltreeMake[A, B](xys: List[(A, B)])(implicit ord: Ordering[A]): Node[A, B] = {
    def lt(x1: (A, B))(x2: (A, B)): Boolean = ord.lt(x1._1, x2._1)
    val xys_sorted = mergesort(lt, xys)
    dltreeUncheckedLoad(xys_sorted)
  }

  /**
   * Method to transform dltree into a list
   * @param tr
   * @param xys0
   * @tparam A
   * @tparam B
   * @return List[(A, B)]
   */
  def dltreeElems0[A, B](tr: DlTree[A, B], xys0: List[(A,B)]): List[(A, B)] = tr match {
    case Branch(_,xy, tr1, tr2) =>
      val elemsLeft = dltreeElems0(tr1, xys0)
      val elemsRight = dltreeElems0(tr2, elemsLeft)
      xy :: elemsRight
    case Leaf() => xys0
  }

  def dltreeElems[A, B](tr: DlTree[A, B]): List[(A, B)] = dltreeElems0(tr, List.empty)

  def level[A, B](tr: DlTree[A, B]): Int = tr match {
    case Branch(h,_,_,_) => h
    case Leaf() => 0
  }

  @tailrec
  def rightmostElem[A, B](xy0: (A, B), tr: DlTree[A, B]): (A, B) = tr match {
    case Branch(_, xy, _, tr2) => rightmostElem(xy, tr2)
    case Leaf() => xy0
  }

  def rightApp[A, B](f: DlTree[A, B] => DlTree[A, B], tr: DlTree[A, B]): DlTree[A, B] = tr match{
    case Branch(h, xy, tr1, tr2) => Branch(h, xy, tr1, f(tr2))
    case _ => tr
  }

  def rightApp_[A, B](f: (Int, DlTree[A, B]) => DlTree[A, B], tr: DlTree[A, B]) : DlTree[A, B] = tr match{
    case Branch(h, xy, tr1, tr2) => Branch(h, xy, tr1, f(h, tr2))
    case _ => tr
  }

  def decreaseLevel0[A, B](h0: Int)(tr: DlTree[A, B]): DlTree[A, B] = tr match {
    case Branch(h, xy, tr1, tr2) if h > h0 => Branch(h0, xy, tr1, tr2)
    case _ => tr
  }

  // Have to add tests for this one
  def decreaseLevel[A, B](tr: DlTree[A, B]): DlTree[A, B] = tr match{
    case Branch(h, _, tr1, tr2) =>
      val h0 = min(level(tr1), level(tr2)) + 1
      if (h > h0) rightApp_((h0, tr2) => decreaseLevel0(h0)(tr2), tr)
      else tr
    case _ => tr
  }

  def skew[A, B](tr: DlTree[A, B]): DlTree[A, B] = tr match{
    case Branch(h, xy, Branch(h1, xy1, tr11, tr12), tr2) if h1 == h =>
      Branch(h1, xy1, tr11, Branch(h, xy, tr12, tr2))
    case _ => tr
  }

  def split[A, B](tr: DlTree[A, B]): DlTree[A, B] = tr match{
    case Branch(h, xy, tr1, Branch(h2, xy2, tr21, tr22)) if level(tr22) == h =>
      Branch(h2+1, xy2, Branch(h, xy, tr1, tr21), tr22)
    case _ => tr
  }

  def dltreeInsert[A, B](xy0: (A, B), tr: DlTree[A, B])(implicit ord: Ordering[A]): DlTree[A, B]= {
    val rebalance:DlTree[A, B] => DlTree[A, B] = (split[A, B]) compose (skew[A, B])
    tr match {
      case Branch(h, xy, tr1, tr2) =>
        val cmp = ord.compare(xy0._1, xy._1)
        if(cmp < 0)
          rebalance(Branch(h, xy, dltreeInsert(xy0, tr1), tr2))
        else if (cmp > 0)
          rebalance(Branch(h, xy, tr1, dltreeInsert(xy0, tr2)))
        else
          throw new IllegalArgumentException("Already in tree")

      case Leaf() => Branch(1, xy0, Leaf(), Leaf())
    }
  }

 

}