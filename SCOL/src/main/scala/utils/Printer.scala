package main.scala.utils
import main.scala.Lib.*
import main.scala.Names.*
import main.scala.Preterm.*
import main.scala.Term.*
import main.scala.Type.isTyconstName
import main.scala.utils.ScolException.ScolFail

import scala.annotation.tailrec

object Printer {
    private def printSep(x: String): Unit = print(x)

    private def printOpenBrkt(): Unit = print("(")

    private def printCloseBrkt(): Unit = print(")")

    private def printSpace(): Unit = print(" ")

    // Conditional printer utils
    private def printOpenBrktIf(condition: Boolean): Unit = if (condition) printOpenBrkt()

    private def printCloseBrktIf(condition: Boolean): Unit = if (condition) printCloseBrkt()

    private def printSpaceIf(condition: Boolean): Unit = if (condition) printSpace()

    // List printer utils
    @tailrec
    private def printSeplist[A](printFn: A => Unit, printSepFn: () => Unit, xs: List[A]): Unit = xs match {
      case Nil => ()
      case List(x1) => printFn(x1)
      case x1 :: xs2 =>
        printFn(x1)
        printSepFn()
        printSeplist(printFn, printSepFn, xs2)
    }

    def printSpSeplist[A](sp: Boolean, printFn: A => Unit, printSepFn: () => Unit, xs: List[A]): Unit = {
      val printSepFn1 = () => {
        printSepFn()
        printSpaceIf(sp)
      }
      printSeplist(printFn, printSepFn1, xs)
    }

    def printSplist[A](printFn: A => Unit, xs: List[A]): Unit = {
      printSeplist(printFn, () => printSpace(), xs)
    }

    // Precedence comparison
    private def needPrecBrkts(fl0: Boolean, l0n0: (Int, Int), l1n1: (Int, Int)): Boolean = {
      val (l0, n0) = l0n0
      val (l1, n1) = l1n1
      (l1 < l0) || (l1 == l0 && n1 < n0) || (l1 == l0 && n1 == n0 && fl0)
    }

    // Name class comparison
    private def needSeparation(ss0: List[Int], s1: Int): Boolean = (s1 > 0) && ss0.contains(s1)

    def termNameForm(x: String): Int = {
      if (isKeyword(x) || isEnumBracket(x)) {
        0
      } else if (isAlphanumeric(x)) {
        1
      } else if (isSymbolic(x)) {
        2
      } else {
        0
      }
    }
    // Token boundary class
    private def typeNameForm(x: String): Int = {
      if (isKeyword(x) || isEnumBracket(x)) 0
      else if (isAlphanumeric(x) || isNumeric(x)) 1
      else if (isSymbolic(x)) 2
      else 0
    }

    // Identifier disambiguation markers
    private def typePrintableName(x: String): String = {
      if (isKeyword(x) || isEnumBracket(x)) quote(x)
      else if (isAlphanumeric(x) || isNumeric(x) || isSymbolic(x)) x
      else quote(x)
    }

    private def tyvarPrintableName(x: String): String = {
      val x_ = typePrintableName(x)
      val x__ = if (isTyconstName(x)) s"'$x_" else x_
      x__
    }

    private def isCompoundPreterm(ptm : Preterm) : Boolean = ptm match
    case Ptmvar(_, _) | Ptmconst(_, _)  => true
    case _ => false

    private def termPrintableName(name : String) : String = {
      if (isKeyword(name) || isEnumBracket(name)) {
        quote(name)
      }else if (isAlphanumeric(name) || isSymbolic(name)) {
        return name
      }
      quote(name)
    }

    private def varPrintableName(name : String) : String = {
      if (isConstName(name)) "%" + termPrintableName(name)
      else termPrintableName(name)
    }

    private def printPretype0(ss0: List[Int], fl0: Boolean, pr0: (Int, Int))(pty: Pretype): Unit = {
      pty match {
        case Ptyvar(x) =>
          // Type variable
          val x_ = tyvarPrintableName(x)
          val s1 = typeNameForm(x)
          if (needSeparation(ss0, s1)) printOpenBrktIf(true)
          print(x_)
          if (needSeparation(ss0, s1)) printCloseBrktIf(true)

        case Ptygvar(n) =>
          // Generated type variable
          if (needSeparation(ss0, 1)) printOpenBrktIf(true)
          print("%")
          print(n.toString)
          if (needSeparation(ss0, 1)) printCloseBrktIf(true)

        case Ptycomp(x, ptys) =>
          if (hasInfixTypeFixity(x)) {
            // Infix compound type
            val (x, ptys_) = stripInfixPretype(pty)
            val (n, h) = getInfixTypeInfo(x)
            val x_ = typePrintableName(x)
            val printOp = () => printSep(x_)
            val ss1 = insert(typeNameForm(x), ss0)
            val pr1 = (10, n)
            if (needPrecBrkts(fl0, pr0, pr1)) printOpenBrktIf(true)
            h match {
              case LeftAssoc =>
                // Left-associative infix type
                printPretype0(ss1, false, pr1)(ptys_.head)
                printOp()
                printSeplist(printPretype0(ss1, true, pr1), printOp, ptys_.tail)

              case RightAssoc =>
                // Right-associative infix type
                printSeplist(printPretype0(ss1, true, pr1), printOp, ptys_.init)
                printOp()
                printPretype0(ss1, false, pr1)(ptys_.last)

              case NonAssoc =>
                // Non-associative infix type
                // Note that length 'ptys_' = 2
                printSeplist(printPretype0(ss1, true, pr1), printOp, ptys_)
            }
            if (needPrecBrkts(fl0, pr0, pr1)) printCloseBrktIf(true)
          } else {
            // Nonfix compound type
            val x_ = typePrintableName(x)
            val s1 = typeNameForm(x)
            val pr1 = (20, 0)

            printOpenBrktIf(needSeparation(ss0, s1))
            printOpenBrktIf(ptys.nonEmpty)
            printSeplist(printPretype0(Nil, false, pr1), () => printSep(","), ptys)
            printCloseBrktIf(ptys.nonEmpty)
            print(x_)
            printCloseBrktIf(needSeparation(ss0, s1))
          }
      }
    }

    def printPretype(ty: Pretype): Unit = printPretype0(Nil, false, (10, 0))(ty)
    
    
    private def printAtom(ptm : Preterm) : Unit = ptm match {
      case Ptmvar(x, _) => print(varPrintableName(x))
      case Ptmconst(x, _) => print(termPrintableName(x))
      case Ptmtyped(ptm0, pty) =>
        print("(")
        printAtom(ptm0)
        print(":")
        printPretype(pty)
        print(")")

      case _ => ScolFail("printAtom : no pattern found")

    }

    private def printFullPreterm0(fl0: Boolean, pr0: (Int, Int), ptm: Preterm): Unit = {
      if (isNatPreterm(ptm)) {
        // Numeral
        println("Preterm is nat: " + ptm)
        val n = destNatPreterm(ptm)
        print(n.toString)
      } else if (isEnumPreterm(ptm)) {
        // Enumeration
        val (br1, ptms, br2) = destEnumPreterm(ptm)
        val pr1 = (5, 0)
        val sp = ptms.exists(isCompoundPreterm)
        print(br1)
        print(" ")
        printSpSeplist(sp, printFullPreterm0(false, pr1, _), () => printSep(","), ptms)
        print(" ")
        print(br2)
      } else ptm match {
        case Ptmvar(x, _) =>
          if (hasNonfixFixity(x)) {
            // Nonfix atom
            printAtom(ptm)
          } else {
            // Defixed prefix/infix/postfix/binder atom
            print("$")
            printAtom(ptm)
          }
        case  Ptmconst(x, _) => if (hasNonfixFixity(x)) {
          // Nonfix atom
          printAtom(ptm)
        } else {
          // Defixed prefix/infix/postfix/binder atom
          print("$")
          printAtom(ptm)
        }
        case Ptmcomb(_, _) =>
          if (isCondPreterm(ptm)) {
            // Conditional expression
            val (ptm0, ptm1, ptm2) = destCondPreterm(ptm)
            val pr1 = (10, 0)
            printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
            print("if ")
            printFullPreterm0(true, pr1, ptm0)
            print(" then ")
            printFullPreterm0(true, pr1, ptm1)
            print(" else ")
            printFullPreterm0(true, pr1, ptm2)
            printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
          } else if (isLetPreterm(ptm)) {
            // Let-expression
            val (vtms, tm0) = destLetPreterm(ptm)
            val pr1 = (10, 0)

            def printVtm(vtm: (Preterm, Preterm)): Unit = {
              val (v, tm) = vtm
              printFullPreterm0(true, pr1, v)
              print(" = ")
              printFullPreterm0(true, pr1, tm)
            }

            printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
            print("let ")
            printSeplist(printVtm, () => printSep(" and "), vtms)
            print(" in ")
            printFullPreterm0(true, pr1, tm0)
            printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
          } else if (isPairPreterm(ptm)) {
            // Pair expression
            val ptms = stripPairPreterm(ptm)
            val pr1 = (5, 0)
            val sp = ptms.exists(isCompoundPreterm)
            printOpenBrkt()
            printSpSeplist(sp, printFullPreterm0(false, pr1, _), () => printSep(","), ptms)
            printCloseBrkt()
          } else if (isPrefixPreterm(ptm)) {
            // Prefix expression
            val (f, ptm0) = destCombPreterm(ptm)
            val pr1 = (30, 0)
            printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
            printAtom(f)
            print(" ")
            printFullPreterm0(false, pr1, ptm0)
            printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
          } else if (isInfixPreterm(ptm)) {
            // Infix expression
            val (f, ptms) = stripInfixPreterm(ptm)
            val (n, h) = getInfixInfo(atomPretermName(f))

            def printOp(): Unit = {
              print(" ")
              printAtom(f)
              print(" ")
            }

            val pr1 = (20, n)
            printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
            h match {
              case LeftAssoc =>
                // Left-associative infix application
                printFullPreterm0(false, pr1, ptms.head)
                printOp()
                printSeplist(printFullPreterm0(true, pr1, _), printOp, ptms.tail)
              case RightAssoc =>
                // Right-associative infix application
                printSeplist(printFullPreterm0(true, pr1, _), printOp, ptms.init)
                printOp()
                printFullPreterm0(false, pr1, ptms.last)
              case NonAssoc =>
                // Non-associative infix application
                printSeplist(printFullPreterm0(true, pr1, _), printOp, ptms)
                printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
            }
            printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
          } else if (isPostfixPreterm(ptm)) {
            // Postfix expression
            val (f, ptm0) = destCombPreterm(ptm)
            val pr1 = (40, 0)
            printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
            printFullPreterm0(true, pr1, ptm0)
            print(" ")
            printAtom(f)
            printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
          } else if (isBinderPreterm(ptm)) {
            // Binder expression
            val (f, vs, ptm0) = stripBinderPreterm(ptm)
            val pr1 = (10, 0)
            val sf = termNameForm(atomPretermName(f))
            val s1 = termNameForm(atomPretermName(vs.head))
            val s2 = termNameForm(atomPretermName(vs.last))
            printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
            printAtom(f)
            printSpaceIf(needSeparation(List(sf), s1))
            printSplist(printFullPreterm0(false, pr1, _), vs)
            printSpaceIf(needSeparation(List(2), s2))
            print(". ")
            printFullPreterm0(false, pr1, ptm0)
            printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
          } else {
            // Curried function application
            val (f, ptm0) = destCombPreterm(ptm)
            val pr1 = (50, 0)
            printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
            printFullPreterm0(false, pr1, f)
            print(" ")
            printFullPreterm0(true, pr1, ptm0)
            printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
          }
        case Ptmabs(_, _) =>
          // Lambda abstraction
          val (vs, ptm0) = stripAbsPreterm(ptm)
          val pr1 = (10, 0)
          val s1 = termNameForm(atomPretermName(vs.head))
          val s2 = termNameForm(atomPretermName(vs.last))
          printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
          print("\\")
          printSpaceIf(needSeparation(List(2), s1))
          printSplist(printFullPreterm0(false, pr1, _), vs)
          printSpaceIf(needSeparation(List(2), s2))
          print(". ")
          printFullPreterm0(false, pr1, ptm0)
          printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
        case Ptmtyped(ptm0, pty) =>
          // Type-annotated expression
          val pr1 = (5, 0)
          printOpenBrktIf(needPrecBrkts(fl0, pr0, pr1))
          printFullPreterm0(true, pr1, ptm0)
          print(":")
          printPretype(pty)
          printCloseBrktIf(needPrecBrkts(fl0, pr0, pr1))
      }
}

    def printFullPreterm(ptm: Preterm): Unit = {
      printFullPreterm0(false, (5, 0), ptm)
    }
}
