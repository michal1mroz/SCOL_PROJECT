package main.scala
import Lib.*

@main
def main(): Unit = {
    println("Hello world!")
    //  val l = List(1)
    //  println(l.head)
    //  val list1 = List(1, 2, 3)
    //  val list2 = List("1", "2", "3")
    val list: List[Int] = List(4, 2, 1, 2, 3, 4, 5, 6)

    // Define a predicate function
    def isEven(x: Int): Boolean = x % 2 == 0

    def add(x: Int, y: Int) = x + y
    //  val myList = List("a", "b", "c", "d")
    println(foldl1_(add)(list))

    def isEqual(a: Int)(b: Int): Boolean = a == b

    val myList = List(1, 2, 3, 4, 2, 3, 5)
    val myList2 = List(1, 2, 2, 6, 8)
    println("Union_: " + union(myList, myList2)) // Output: List(1, 2, 3, 4, 5)
    // Example usage:
    val list1 = List(1, 2)
    val list2 = List(1, 2, 3, 4, 2, 3, 5)


    val result1 = noDups_(isEqual, list1)
    val result2 = noDups_(isEqual, list2)

    println(result1) // Output: false
    println(result2) // Output: true

    val str = "Hello you"

    val charList: List[String] = str.split("").toList.filter(_.nonEmpty)

    println(charList) // Output: List(H, e, l, l, o)
    val avoidanceList = List("example", "example'")
    val inputString = "example"

    val result = stringVariant(avoidanceList, inputString)
    println(result) // Output: example

    val lists = List(List(1, 2, 3), List(2, 3, 4), List(3, 4, 5))
    val result3 = unions(lists)
    val result4 = unions_(isEqual, lists)
    println(result3)
    println(result4)
}