import utils.ScolException.ScolFail

import java.math.BigInteger
import scala.annotation.tailrec

object Lib {

  def check[A](func : A => Boolean, arg : A) : A = {
    if (func(arg)) arg
    else throw ScolFail("Your arg does not satisfy boolean function!")
  }

  def assert0(b : Boolean, exn : Exception): Unit = {
    if (!b) throw exn
  }

  def assert1(b : Boolean, msg : String) : Unit = {
    if (!b) throw ScolFail(msg)
  }

  def try0[A, B](func : A => B, arg : A, exn : Exception) : B = {
    try
      func(arg)
    catch
      case _ : ScolFail => throw exn
  }

  def try1[A, B](func : A => B, arg : A, msg : String) : B = {
    try
      func(arg)
    catch
      case _ : ScolFail => throw ScolFail(msg)
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

  def can[A, B](f : A => B, arg : A) : Boolean = {
    try {
      val result = f(arg)
      true
    }catch {
      case _ : Exception => false
    }
  }

  def cannot[A, B](f : A => B, arg : A) : Boolean = {
    !can(f, arg)
  }

  def repeat[A](f : A => A, arg: A): Unit = {
    var i = 0
    var y = arg
    try {
      while(true) {
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

  def hdTl[A](l : List[A]) : (A, List[A]) = l match{
    case x :: xs => (x, xs)
    case _ => throw IllegalArgumentException("Empty list")
  }

  def frontLast[A](l : List[A]) : (A , A) = (l.head, l.last)

  @tailrec
  def listEq[A, B](eq: (A, B) => Boolean, xs: List[A], ys: List[B]): Boolean = (xs, ys) match {
    case (x :: xs0, y :: ys0) => eq(x, y) && listEq(eq, xs0, ys0)
    case (Nil, Nil) => true
    case _ => false
  }

  def copy[A](el : A, count : Int) : List[A] = List.fill(count)(el)

  def append[A](l1 : List[A], l2 : List[A]) : List[A] = l1.concat(l2)

  def flatten[A](l : List[List[A]]) : List[A] = l.flatten

  // Warning!!! In cut implementation from holzero indexes are 1 based (that's why we have n-1 here)
  def cut[A](n : Int, l : List[A]) : (List[A], List[A]) = l.splitAt(n-1)

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

  def decrement(n : Int) : Int = if (n > 0) n-1 else 0

  def curry[A, B, C](f : (A, B) => C, arg1 : A, arg2: B) : C = f(arg1, arg2)
  def uncurry[A, B, C](f : A =>  B => C, arg1 : A, arg2: B) : C = f(arg1)(arg2)

  def apply[A, B](f : A => B, arg : A) : B = f(arg)
  def idFn[A](x : A) : A = x
  def conFn[A, B](x : A, y : B) : A = x

  // Use `compose` keyword instead of `<*`

  def funpow[A](f : A => A, arg : A, n : Int) : A = {
    require(n >= 0)

    @tailrec
    def rec(n : Int, f : A => A, arg : A) : A = {
      if (n != 0) rec(n, f, f(arg))
      else arg
    }

    rec(n, f, arg)
  }

  def swapArg[A, B, C](f: A => B => C)(y: B)(x: A): C = f(x)(y)
  def dblArg[A, B](f : A => A => B, arg : A) : B = f(arg)(arg)

  // Define a function to apply a pair of functions to corresponding components of a given pair
  def pair_apply[A, B, C, D](pair: (A => B, C => D))(tuple: (A, C)): (B, D) = {
    val (f, g) = pair
    val (x, y) = tuple
    (f(x), g(y))
  }

  def map[A, B](f : A => B, args : List[A]) : List[B] = args.map(f)

  def bimap[A, B, C](f : A => B => C, l1 : List[A], l2 : List[B]) : List[C] =  (l1, l2) match {
      case (x :: xs, y :: ys) => f(x)(y) :: bimap(f, xs, ys)
      case _ => throw IllegalArgumentException("Bimap received lists of different lengths")
  }
  // foldl: Fold left operation on a list
  def foldl[A, B](f: B => A => B)(a: B)(xs: List[A]): B = xs.foldLeft(a)(uncurry(f, _, _))

  // foldl1: Fold left operation on a non-empty list
  def foldl1[A](f: A => A => A)(xs: List[A]): A = xs match {
    case x :: xs1 => foldl(f)(x)(xs1)
    case _ => throw IllegalArgumentException("foldl1 received empty list")
  }

  // foldr: Fold right operation on a list
  def foldr[A, B](f: A => B => B)(xs: List[A], a: B): B = xs.foldRight(a)(uncurry(f, _, _))

  // foldr1: Fold right operation on a non-empty list
  def foldr1[A](f: A =>  A => A)(xs: List[A]): A = xs match {
    case x :: Nil => x
    case x1 :: xs2 => xs.foldRight(x1)(uncurry(f,_, _))
    case Nil => throw new IllegalArgumentException("Empty list")
  }

  // foldl': Variant of foldl suited for uncurried binary functions
  def foldl_[A, B] (f: (B , A) => B)(x: B, xs: List[A]): B = xs.foldLeft(x)(f)

  // foldr': Variant of foldr suited for uncurried binary functions
  def foldr_[A, B] (f: (A, B) => B)(x: B, xs: List[A]): B = xs.foldRight(x)(f)

  //todo doesnt wor

  // foldl1': Variant of foldl1 suited for uncurried binary functions
  // def foldl1_[A] (f: (A, A) => A)(xs: List[A]): A = foldl1(curry(f, _, _))(xs)

  // foldr1': Variant of foldr1 suited for uncurried binary functions
  // def foldr1_[A] (f: (A, A) => A)(xs: List[A]): A = foldr1(curry(f, _, _))(xs)

  def unfoldl0[A, B](dest_fn: A => (A, B), x: A, xs: List[B]): (A, List[B]) = {
    try {
      val (x1, x2) = dest_fn(x)
      unfoldl0(dest_fn, x1, x2 :: xs)
    } catch {
      case _: Throwable => (x, xs.reverse)
    }
  }

  // Define the unfoldl function
  def unfoldl[A, B](dest_fn: A => (A, B), x: A): (A, List[B]) = unfoldl0(dest_fn, x, Nil)


}
