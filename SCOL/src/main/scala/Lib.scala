package main.scala
import utils.ScolException.ScolFail

import java.math.BigInteger
import scala.::
import scala.annotation.tailrec

object Lib {

  def check[A](func: A => Boolean, arg: A): A = {
    if (func(arg)) arg
    else throw ScolFail("Your arg does not satisfy boolean function!")
  }

  def assert0(b: Boolean, exn: Exception): Unit = {
    if (!b) throw exn
  }

  def assert1(b: Boolean, msg: String): Unit = {
    if (!b) throw ScolFail(msg)
  }

  def try0[A, B](func: A => B, arg: A, exn: Exception): B = {
    try
      func(arg)
    catch
      case _: ScolFail => throw exn
  }

  def try1[A, B](func: A => B, arg: A, msg: String): B = {
    try
      func(arg)
    catch
      case _: ScolFail => throw ScolFail(msg)
  }

  def try2[A, B](func: A => B, arg: A): B = {
    try
      func(arg)
    catch
      case e: ScolFail => throw ScolFail(e.getMessage)
  }

  def tryFind[A, B](f: A => B, xs: List[A]): B = xs match {
    case x :: xs0 =>
      try {
        f(x)
      } catch {
        case _: ScolFail => tryFind(f, xs0)
      }
    case Nil => throw ScolFail("No successful application")
  }

  def tryFilter[A, B](f: A => B, xs: List[A]): List[B] = xs match {
    case x :: xs0 =>
      try {
        val result = f(x)
        result :: tryFilter(f, xs0)
      } catch {
        case _: ScolFail => tryFilter(f, xs0)
      }
    case Nil => List.empty
  }

  def can[A, B](f: A => B, arg: A): Boolean = {
    try {
      val result = f(arg)
      true
    } catch {
      case _: Exception => false
    }
  }

  def cannot[A, B](f: A => B, arg: A): Boolean = {
    !can(f, arg)
  }

  def repeat[A](f: A => A, arg: A): Unit = {
    var i = 0
    var y = arg
    try {
      while (true) {
        y = f(y)
        i += 1
      }
    } catch {
      case e: Exception => throw ScolFail("Repeat function has led to Exception on iteration " + i + "\t" + e.getMessage)
    }
  }

  // fst : ('a, 'b) => 'a
  def fst[A, B](tuple: (A, B)): A = tuple._1

  // snd : ('a, 'b) => 'b
  def snd[A, B](tuple: (A, B)): B = tuple._2

  // pair : 'a => 'b => ('a, 'b)
  def pair[A, B](x: A)(y: B): (A, B) = (x, y)

  // switch : ('a, 'b) => ('b, 'a)
  def switch[A, B](tuple: (A, B)): (B, A) = tuple match {
    case (x, y) => (y, x)
  }

  // Most List function are built in scala Lists methods, so we provide no explicit implementation

  def hdTl[A](l: List[A]): (A, List[A]) = l match {
    case x :: xs => (x, xs)
    case _ => throw IllegalArgumentException("Empty list")
  }

  def frontLast[A](l: List[A]): (List[A], A) = (l.init, l.last)

  @tailrec
  def listEq[A, B](eq: (A, B) => Boolean, xs: List[A], ys: List[B]): Boolean = (xs, ys) match {
    case (x :: xs0, y :: ys0) => eq(x, y) && listEq(eq, xs0, ys0)
    case (Nil, Nil) => true
    case _ => false
  }

  def copy[A](el: A, count: Int): List[A] = List.fill(count)(el)

  def append[A](l1: List[A], l2: List[A]): List[A] = l1.concat(l2)

  def flatten[A](l: List[List[A]]): List[A] = l.flatten

  // Warning!!! In cut implementation from holzero indexes are 1 based (that's why we have n-1 here)
  def cut[A](n: Int, l: List[A]): (List[A], List[A]) = l.splitAt(n - 1)

  def cutBigInt[A](n: BigInteger, xs: List[A]): (List[A], List[A]) = {
    val zero = BigInteger.ZERO
    val one = BigInteger.ONE

    def cutHelper(n: BigInteger, xs: List[A]): (List[A], List[A]) = {
      if (n.compareTo(zero) > 0) xs match {
        case x :: xs0 =>
          val (ys, zs) = cutHelper(n.subtract(one), xs0)
          (x :: ys, zs)
        case _ => throw IllegalArgumentException("Index larger than list length")
      } else if (n.equals(zero)) {
        (Nil, xs)
      } else {
        throw IllegalArgumentException("Negative index")
      }
    }

    cutHelper(n, xs)
  }

  @tailrec
  def cutWhile0[A](p: A => Boolean, ys: List[A], xs: List[A]): (List[A], List[A]) = xs match {
    case x :: xs0 =>
      if (p(x)) cutWhile0(p, x :: ys, xs0)
      else (ys.reverse, xs)
    case Nil => (ys.reverse, Nil)
  }

  def cutWhile[A](p: A => Boolean, xs: List[A]): (List[A], List[A]) = cutWhile0(p, Nil, xs)

  def decrement(n: Int): Int = if (n > 0) n - 1 else 0

  def curry[A, B, C](f: (A, B) => C)(arg1: A)(arg2: B): C = f(arg1, arg2)

  def uncurry[A, B, C](f: A => B => C)(arg1: A)(arg2: B): C = f(arg1)(arg2)

  def curry_[A, B, C](f: (A, B) => C): A => B => C = (a: A) => (b: B) => f(a, b)

  def uncurry_[A, B, C](f: A => B => C): (A, B) => C = (a: A, b: B) => f(a)(b)

  def apply[A, B](f: A => B, arg: A): B = f(arg)

  def idFn[A](x: A): A = x

  def conFn[A, B](x: A, y: B): A = x

  // Use `compose` keyword instead of `<*`

  def funpow[A](f: A => A, arg: A, n: Int): A = {
    require(n >= 0)

    @tailrec
    def rec(n: Int, f: A => A, arg: A): A = {
      if (n != 0) rec(n, f, f(arg))
      else arg
    }

    rec(n, f, arg)
  }

  def swapArg[A, B, C](f: A => B => C)(y: B)(x: A): C = f(x)(y)

  def dblArg[A, B](f: A => A => B, arg: A): B = f(arg)(arg)

  // Define a function to apply a pair of functions to corresponding components of a given pair
  def pair_apply[A, B, C, D](pair: (A => B, C => D))(tuple: (A, C)): (B, D) = {
    val (f, g) = pair
    val (x, y) = tuple
    (f(x), g(y))
  }

  def map[A, B](f: A => B, args: List[A]): List[B] = args.map(f)

  def bimap[A, B, C](f: A => B => C, l1: List[A], l2: List[B]): List[C] = (l1, l2) match {
    case (x :: xs, y :: ys) => f(x)(y) :: bimap(f, xs, ys)
    case _ => throw IllegalArgumentException("Bimap received lists of different lengths")
  }

  // foldl: Fold left operation on a list
//  def foldl[A, B](f: B => A => B)(a: B)(xs: List[A]): B = xs.foldLeft(a)(uncurry_(f))
  def foldl[A, B](f: B => A => B)(a: B)(xs: List[A]): B = xs match {
    case Nil => a
    case l :: ls => foldl(f)(f(a)(l))(ls)
  }

  // foldl1: Fold left operation on a non-empty list
  def foldl1[A](f: A => A => A)(xs: List[A]): A = xs match {
    case x :: xs1 => foldl(f)(x)(xs1)
    case _ => throw IllegalArgumentException("foldl1 received empty list")
  }

  // foldr: Fold right operation on a list
  def foldr[A, B](f: A => B => B)(xs: List[A], a: B): B = xs.foldRight(a)(uncurry_(f))

  // foldr1: Fold right operation on a non-empty list
  def foldr1[A](f: A => A => A)(xs: List[A]): A = xs match {
    case Nil => throw new IllegalArgumentException("Empty list")
    case x :: Nil => x
    case x1 :: xs2 => f(x1)(foldr1(f)(xs2))
  }

  // foldl': Variant of foldl suited for uncurried binary functions
  def foldl_[A, B](f: (B, A) => B)(x: B, xs: List[A]): B = xs.foldLeft(x)(f)

  // foldr': Variant of foldr suited for uncurried binary functions
  def foldr_[A, B](f: (A, B) => B)(x: B, xs: List[A]): B = xs.foldRight(x)(f)

  // foldl1': Variant of foldl1 suited for uncurried binary functions
  def foldl1_[A](f: (A, A) => A)(xs: List[A]): A = foldl1(curry_(f))(xs)

  // foldr1': Variant of foldr1 suited for uncurried binary functions
  def foldr1_[A](f: (A, A) => A)(xs: List[A]): A = foldr1(curry(f))(xs)

  private def unfoldl0[A, B](dest_fn: A => (A, B), x: A, xs: List[B]): (A, List[B]) = {
    try {
      val (x1, x2) = dest_fn(x)
      unfoldl0(dest_fn, x1, x2 :: xs)
    } catch {
      case _: ScolFail => (x, xs)
    }
  }

  def unfold1[A](dest_fn: A => (A, A), x: A, xs: List[A]): (A, List[A]) = {
    @annotation.tailrec
    def helper(seed: A, acc: List[A]): (A, List[A]) = {
      val (nextSeed, result) = dest_fn(seed)
      if (nextSeed == seed) (nextSeed, acc.reverse ++ xs)
      else helper(nextSeed, result :: acc)
    }

    helper(x, Nil)
  }

  // Define the unfoldl function
  def unfoldl[A, B](dest_fn: A => (A, B), x: A): (List[B], A) = unfoldl0(dest_fn, x, Nil).swap

  def unfoldl1[A](dest_fn: A => (A, A), x: A): List[A] = {
    val (xs, x1) = unfoldl(dest_fn, x)
    x1 :: xs
  }

  def  unfoldr0[A, B](dest_fn: B => (A, B), x: B, xs:List[A]): (List[A], B) = {
    try{
      val (x1, x2) = dest_fn(x)
      unfoldr0(dest_fn, x2, x1::xs)
    } catch{
      case _: ScolFail => (x, xs.reverse).swap
    }
  }

  def unfoldr[A, B](dest_fn: B => (A ,B), x: B): (List[A], B) = {
    val (xs, x1) = unfoldr0(dest_fn, x, List.empty)
    (x1, xs.reverse).swap
  }

  def unfoldlAlter[A, B](dest_fn: A => (A, B), x: A): (List[B], A) = {
    @annotation.tailrec
    def helper(acc: List[B], seed: A): (List[B], A) = {
      val (newSeed, b) = dest_fn(seed)
      if (b == null) (acc.reverse, newSeed)
      else helper(b :: acc, newSeed)
    }

    helper(Nil, x)
  }

  def unfoldrAlter[A, B](dest_fn: B => (A, B), x: B): (List[A], B) = {
    @annotation.tailrec
    def helper(acc: List[A], seed: B): (List[A], B) = {
      val (a, newSeed) = dest_fn(seed)
      if (a == null) (acc.reverse, newSeed) // Stop condition if `a` is null
      else helper(a :: acc, newSeed)
    }

    helper(Nil, x)
  }

  def unfoldr1[A](dest_fn: A => (A, A), x: A): List[A] = {
    val (xs, x1) = unfoldr0(dest_fn, x, List.empty)
    (x1::xs).reverse
  }

  def unfold0[A](dest_fn: A => (A, A), x:A, xs:List[A]): List[A] = {
    try{
      val (x1, x2) = dest_fn(x)
      unfold0(dest_fn, x1, unfold0(dest_fn, x2, xs))
    }catch {
      case _: ScolFail => x :: xs
    }
  }

  def unfold[A](dest_fn: A => (A, A), x: A): List[A] = unfold0(dest_fn, x, List.empty)

  def find[A](p: A => Boolean, l: List[A]): A = l.find(p) match
    case Some(x) => x
    case _ => throw ScolFail("Find failed to find element satisfying boolean function in a supplied list")

  def filter[A](p: A => Boolean, l: List[A]): List[A] = l.filter(p)

  def partition[A](p: A => Boolean, l: List[A]): (List[A], List[A]) = l.partition(p)

  def exists[A](p: A => Boolean, l: List[A]): Boolean = l.exists(p)

  def forall[A](p: A => Boolean, l: List[A]): Boolean = l.forall(p)

  // Define the assoc function
  def assoc[A, B](x: A, xys: List[(A, B)]): B = xys match {
    case (x0, y0) :: xys0 =>
      if (x == x0) y0
      else assoc(x, xys0)
    case Nil => throw ScolFail("assoc: No match")
  }

  // Define the inv_assoc function
  def invAssoc[A, B](y: B, xys: List[(A, B)]): A = xys match {
    case (x0, y0) :: xys0 =>
      if (y == y0) x0
      else invAssoc(y, xys0)
    case Nil => throw new NoSuchElementException("inv_assoc: No match")
  }

  def fstMap[A, B, C](f: A => C, xys: List[(A, B)]): List[(C, B)] = xys.map((x, y) => (f(x), y))

  def sndMap[A, B, C](f: B => C, xys: List[(A, B)]): List[(A, C)] = xys.map((x, y) => (x, f(y)))

  def fstFilter[A, B](f: A => Boolean, xys: List[(A, B)]): List[(A, B)] = xys.filter((x, _) => f(x))

  def sndFilter[A, B](f: B => Boolean, xys: List[(A, B)]): List[(A, B)] = xys.filter((_, y) => f(y))

  def enumerate[A](l: List[A]): List[(Int, A)] = l.zipWithIndex.map { case (element, index) => (index + 1, element) }

  def doMap[A](f: A => Unit, xs: List[A]): Unit = xs.foreach(f)

  def mem[A](a: A, as: List[A]): Boolean = as.contains(a)

  def mem_[A, B](eq: A => B => Boolean, a: A, bs: List[B]): Boolean = bs.filter(b => eq(a)(b)).contains(a)

  def insert[A](x: A, xs: List[A]): List[A] = {
    if (mem(x, xs)) xs
    else x :: xs
  }

  def insert_[A](eq: A => A => Boolean, x: A, xs: List[A]): List[A] = {
    if mem_(eq, x, xs) then xs
    else x :: xs
  }
  
  def subtract_[A](eq: A => A => Boolean, xs1: List[A], xs2: List[A]): List[A] = {
    xs1.filter(x1 => !mem_(eq, x1, xs2))
  }

  def insert_Curried[A](eq: A => A => Boolean)(x: A, xs: List[A]): List[A] = insert_(eq, x, xs)

  def insert_Curried_[A](eq: A => A => Boolean)(xs: List[A], x: A): List[A] = insert_(eq, x, xs)

  def setify[A](l: List[A]): List[A] = l.toSet.toList

  def setify_[A](eq: A => A => Boolean, l: List[A]): List[A] = l.foldLeft(List.empty[A])((acc, x) => insert_Curried_(eq)(acc, x)).reverse

  def union[A](l1: List[A], l2: List[A]): List[A] = (l1 ++ l2).distinct
  // This works a little bit different than original since it kills all the duplicates in a list
  // You can think of it as a legitimate union of 2 sets
  // not sure if is ok for our purposes
  def unionAlt[A](l1: List[A], l2: List[A]): List[A] = setify(l1.concat(l2))

  // fixme not sure if it works correctly or not
  def union_[A](eq: A => A => Boolean, xs1: List[A], xs2: List[A]): List[A] = {
    xs2.foldRight(xs1)((elem, acc) => insert_(eq, elem, acc))
  }


  def union_Curried[A](eq: A => A => Boolean)(l1: List[A], l2: List[A]): List[A] = union_(eq, l2, l2)

  def unions[A](ls: List[List[A]]): List[A] = ls.flatten.distinct

  // fixme not sure if it works correctly or not
  def unions_[A](eq: A => A => Boolean, ls: List[List[A]]): List[A] = ls match
    case Nil => Nil
    case head :: tail => tail.foldLeft(head)((acc, xs) => union_(eq,acc, xs))

  def intersect[A](l1: List[A], l2: List[A]): List[A] = l1.intersect(l2)

  def intersect_[A, B](eq: A => B => Boolean, l1: List[A], l2: List[B]): List[A] = l1.filter(x => !mem_(eq, x, l2))

  def subset[A](l1: List[A], l2: List[A]): Boolean = l1.forall(l2.contains)

  def subset_[A, B](eq: A => B => Boolean, l1: List[A], l2: List[B]): Boolean = l1.forall(x => mem_(eq, x, l2))

  def disjoint[A](l1: List[A], l2: List[A]): Boolean = !l1.exists(l2.contains)

  def disjoint_[A, B](eq: A => B => Boolean, l1: List[A], l2: List[B]): Boolean = !l1.exists(x => mem_(eq, x, l2))

  def setEq[A](l1: List[A], l2: List[A]): Boolean = subset(l1, l2) && subset(l2, l1)

  def setEq_[A](eq: A => A => Boolean, l1: List[A], l2: List[A]): Boolean = subset_(eq, l1, l2) && subset_(eq, l2, l1)

  def noDups[A](l: List[A]): Boolean = l.size == l.toSet.size

  def noDups_[A](eq: A => A => Boolean, l: List[A]): Boolean = !l.indices.exists { i =>
    (i + 1 until l.length).exists { j =>
      eq(l(i))(l(j))
    }
  }

  def stringOfInt(n: Int): String = n.toString

  def intOfString(s: String): Int = s.toInt

  def charImplode(cs: List[Char]): String = cs.mkString

  def charExplode(s: String): List[Char] = s.toList

  def implode(ss: List[String]): String = ss.mkString

  def explode(s: String): List[String] = s.split("").toList.filter(_.nonEmpty)

  @tailrec
  def stringVariant(xs: List[String], s: String): String = {
    if (xs.contains(s)) {
      stringVariant(xs, s + "'")
    } else {
      s
    }
  }

  def quote0(s : String) : String = "'" + s + "'"

  def charEscape(c: Char): String = {
    val n = c.toInt
    if (n == 34 || n == 92) {
      "\\" + c
    } else if (n >= 32 && n <= 126 && n != 96) {
      c.toString
    } else {
      val x = "%03d".format(n)
      if (x.length == 1) "\\00" + x
      else if (x.length == 2) "\\0" + x
      else "\\" + x
    }
  }

  def quote(x: String): String = {
    val x1 = x.flatMap(charEscape) // char_escape is applied to each character of the string
    "\"" + x1 + "\""
  }

  // Not implementing report (just do println if needed)

  def warn(msg : String) : Unit = println("SCOL WARNING: " + msg)

  def mergesort[A](rel : A => A => Boolean, l : List[A]) : List[A] = l.sortWith(uncurry_(rel))


  def reverseTail[A](list : List[A]) : List[A] =  list match{
    case Nil => Nil
    case head :: tail => head :: tail.reverse
  }
}