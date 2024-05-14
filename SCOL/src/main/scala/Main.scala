import main.scala.Names.isNumeric


@main
def mAin(): Unit = {
    println("Hello world!")
    // Use the custom infix function
    println(isNumeric("!#!#!#".toList.mkString))
    println("!#!#!#".toList.mkString)
    println('!'.isLower)
}