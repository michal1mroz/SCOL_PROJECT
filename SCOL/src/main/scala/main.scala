import Lib.cutWhile

@main
def main(): Unit = {
  println("Hello world!")
  val l = List(1)
  println(l.head)
  val list1 = List(1, 2, 3)
  val list2 = List("1", "2", "3")
  val list = List(4, 2, 1, 2, 3, 4, 5, 6)

  // Define a predicate function
  def isEven(x: Int): Boolean = x % 2 == 0

  // Cut the list into two segments based on the predicate
  val (segment1, segment2) = cutWhile(isEven, list)
  println(s"Segment 1: $segment1") // Output: Segment 1: List(1)
  println(s"Segment 2: $segment2") // Output: Segment 2: List(2, 3, 4, 5, 6)

}