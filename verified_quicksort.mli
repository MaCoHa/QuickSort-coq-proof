
type ('a, 'b) prod =
| Pair of 'a * 'b

val snd : ('a1, 'a2) prod -> 'a2

val length : 'a1 list -> int

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

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val lookup : int list -> int -> int

val insert : int -> int -> int list -> int list

val randnat : int -> int -> int

val fst3 : ((int list, int) prod, int) prod -> int list

val swap : int list -> int -> int -> int list

val shuffle : int list -> int list

val partition_left_func : (int list, (int, (int, int) sigT) sigT) sigT -> int

val partition_left : int list -> int -> int -> int -> int

val partition_right_func : (int list, (int, (int, int) sigT) sigT) sigT -> int

val partition_right : int list -> int -> int -> int -> int

val partition_func :
  (int list, (int, (int, (int, int) sigT) sigT) sigT) sigT -> (int, int list) prod

val partition : int list -> int -> int -> int -> int -> (int, int list) prod

val sort_func : (int list, (int, int) sigT) sigT -> int list

val sort : int list -> int -> int -> int list

val quicksort : int list -> int list
