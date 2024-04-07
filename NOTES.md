This file could be used to write certain ideas and problems in the process of porting hol-zero. Notes should probably be deleted. I just use them to communicate some quick ideas, but "Implementation" section sould probably stay as a reference and be extended from now on.

## Notes
- Ported full Lib (hasn't been tested, but it shouldn't be too bad)
- Created custom exception ScolFail. It should be used in places where exception could be 'legal', for example IllegalArgumentException sould be used everywhere where there is a risk of accepting a illegal argument and ScolFail is not a replacement for it, but when you call a function to find some element that satisfies provided boolean function (see tryFind in Lib) it should throw ScolFail because for exmple for user it might indicate that a proof went wrong somewhere, but it doesn't pose danger to the system, it should be mostly used to communicate problems to user (maybe I am not entirely sure, but that's my intuition)
- ported first half of Names (the second half requires implementation of DLTree), I will finish it when DLTree is ready.
- Keeping naming convention in Scala camel case (e.g. OCaml : do_map, Scala : doMap). Also the `'` character is not allowed in names in Scala so using '\_' instead (e.g. OCaml : mem' Scala : mem\_).

## Implementation
1. Should use Lists instead of Arrays or anything of that sort. Lists are immutable and we need that to ensure correctness of the system.
2. In original Lib most functions are in curried form (e.g f : A => B => C => D), it suits pure functional languages like Haskell or ML. When writing Lib I wrote most of them in not fully curried or uncurried form (e.g f : (A, B, C) => D or f : (A, B) => C => D). Also few functions like `foldr`, `foldl` have different implementations.
3. There might be problems later on because when using some polymorphic functions in Scala you have to explicitly define its type variable when calling it (e.g. let's say you have a list of Int, then foldl1_(_ + _)(list) doesn't work "value + is not a member of Any", but  foldl1_[Int](_ + _)(list) does.). Perhaps you would have to define your own addition, explicitly of type Int to get rid of [Int] in function call, but this might be quite problematic if you for example don't know beforehand which type will your function call accept, then idea of funciton polymorphism kind of goes out of the window.
4. dltreeMake and dltreeInsert uses sorting on the List[(A, B)], this requires implicit definition for ordering on A.
