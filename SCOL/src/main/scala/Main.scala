import main.scala.Names.isNumeric
import main.scala.TypeAnal.*

@main
def mAin(): Unit = {
    println("Hello world!")
    // Use the custom infix function
    println(isNumeric("!#!#!#".toList.mkString))
    println("!#!#!#".toList.mkString)
    println('!'.isLower)
}