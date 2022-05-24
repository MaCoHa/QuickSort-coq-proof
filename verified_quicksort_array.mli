
type ('a, 'b) prod =
| Pair of 'a * 'b

val snd : ('a1, 'a2) prod -> 'a2

val length : 'a1 Array.array -> int

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val divmod : int -> int -> int -> int -> (int, int) prod

  val modulo : int -> int -> int
 end

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 Array.array -> 'a1 -> 'a1

val lookup : int Array.array -> int -> int

val insert : int Array.array -> int -> int -> int Array.array

val randnat : int -> int -> int

val fst3 : (('a1, 'a2) prod, 'a3) prod -> 'a1

val swap : int Array.array -> int -> int -> int Array.array

val shuffle : int Array.array -> int Array.array

val partition_left_func :
  (int Array.array, (int, (int, int) sigT) sigT) sigT -> int

val partition_left : int Array.array -> int -> int -> int -> int

val partition_right_func :
  (int Array.array, (int, (int, int) sigT) sigT) sigT -> int

val partition_right : int Array.array -> int -> int -> int -> int

val partition_func :
  (int Array.array, (int, (int, (int, int) sigT) sigT) sigT) sigT -> (int,
  int Array.array) prod

val partition :
  int Array.array -> int -> int -> int -> int -> (int, int Array.array) prod

val sort_func : (int Array.array, (int, int) sigT) sigT -> int Array.array

val sort : int Array.array -> int -> int -> int Array.array

val quicksort : int Array.array -> int Array.array
