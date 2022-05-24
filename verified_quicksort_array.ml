
type ('a, 'b) prod =
| Pair of 'a * 'b

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

(** val length : 'a1 Array.array -> int **)

let rec length = Array.length

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h

(** val add : int -> int -> int **)

let rec add = ( + )

(** val mul : int -> int -> int **)

let rec mul = ( - )

(** val sub : int -> int -> int **)

let rec sub = ( - )

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
      (fun _ -> n)
      (fun k ->
      (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val divmod : int -> int -> int -> int -> (int, int) prod **)

  let rec divmod x y q u =
    (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
      (fun _ -> Pair (q, u))
      (fun x' ->
      (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
        (fun _ -> divmod x' y ((fun x -> x + 1) q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun zero succ n ->

 if n=0 then zero ()

 else succ (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 Array.array -> 'a1 -> 'a1 **)

let rec fold_left = (fun folder l acc -> Array.fold_left folder acc l)

(** val lookup : int Array.array -> int -> int **)

let rec lookup = Array.get

(** val insert : int Array.array -> int -> int -> int Array.array **)

let rec insert = (fun xs i x -> Array.set xs i x; xs)

(** val randnat : int -> int -> int **)

let randnat seed bound =
  Nat.modulo
    (add
      (mul seed ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))))))))))))))))))) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) 0)))))))) bound

(** val fst3 : (('a1, 'a2) prod, 'a3) prod -> 'a1 **)

let fst3 = function
| Pair (p, _) -> let Pair (a, _) = p in a

(** val swap : int Array.array -> int -> int -> int Array.array **)

let swap l i1 i2 =
  insert (insert l i2 (lookup l i1)) i1 (lookup l i2)

(** val shuffle : int Array.array -> int Array.array **)

let shuffle l =
  fst3
    (fold_left (fun acc _ ->
      let Pair (p, point) = acc in
      let Pair (li, seed) = p in
      Pair ((Pair ((swap li point (randnat seed (length li))),
      (add seed ((fun x -> x + 1) 0)))), (add point ((fun x -> x + 1) 0)))) l
      (Pair ((Pair (l, ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0)))))))))))))))))))))))))))))))))))))))))))), 0)))

(** val partition_left_func :
    (int Array.array, (int, (int, int) sigT) sigT) sigT -> int **)

let rec partition_left_func x =
  let l = projT1 x in
  let pivot = projT1 (projT2 x) in
  let lo = projT1 (projT2 (projT2 x)) in
  let hi = projT2 (projT2 (projT2 x)) in
  let partition_left0 = fun l0 pivot0 lo0 hi0 ->
    partition_left_func (ExistT (l0, (ExistT (pivot0, (ExistT (lo0, hi0))))))
  in
  let filtered_var = (<=) hi lo in
  if filtered_var
  then lo
  else let filtered_var0 = (<=) (lookup l lo) pivot in
       if filtered_var0
       then partition_left0 l pivot (add lo ((fun x -> x + 1) 0)) hi
       else lo

(** val partition_left : int Array.array -> int -> int -> int -> int **)

let partition_left l pivot lo hi =
  partition_left_func (ExistT (l, (ExistT (pivot, (ExistT (lo, hi))))))

(** val partition_right_func :
    (int Array.array, (int, (int, int) sigT) sigT) sigT -> int **)

let rec partition_right_func x =
  let l = projT1 x in
  let pivot = projT1 (projT2 x) in
  let lo = projT1 (projT2 (projT2 x)) in
  let hi = projT2 (projT2 (projT2 x)) in
  let partition_right0 = fun l0 pivot0 lo0 hi0 ->
    partition_right_func (ExistT (l0, (ExistT (pivot0, (ExistT (lo0, hi0))))))
  in
  let filtered_var = (<=) hi lo in
  if filtered_var
  then hi
  else let filtered_var0 = (<=) pivot (lookup l hi) in
       if filtered_var0
       then partition_right0 l pivot lo (sub hi ((fun x -> x + 1) 0))
       else hi

(** val partition_right : int Array.array -> int -> int -> int -> int **)

let partition_right l pivot lo hi =
  partition_right_func (ExistT (l, (ExistT (pivot, (ExistT (lo, hi))))))

(** val partition_func :
    (int Array.array, (int, (int, (int, int) sigT) sigT) sigT) sigT -> (int,
    int Array.array) prod **)

let rec partition_func x =
  let l = projT1 x in
  let pivot = projT1 (projT2 x) in
  let lo = projT1 (projT2 (projT2 x)) in
  let initial_lo = projT1 (projT2 (projT2 (projT2 x))) in
  let hi = projT2 (projT2 (projT2 (projT2 x))) in
  let partition0 = fun l0 pivot0 lo0 initial_lo0 hi0 ->
    partition_func (ExistT (l0, (ExistT (pivot0, (ExistT (lo0, (ExistT
      (initial_lo0, hi0))))))))
  in
  let filtered_var = Pair ((partition_left l pivot lo hi),
    (partition_right l pivot lo hi))
  in
  let Pair (i, j) = filtered_var in
  let filtered_var0 = (<=) j i in
  if filtered_var0
  then Pair (j, (swap l initial_lo j))
  else let filtered_var1 = (<=) j hi in
       if filtered_var1
       then let filtered_var2 = (<=) lo i in
            if filtered_var2
            then partition0 (swap l i j) pivot i initial_lo j
            else Pair (j, l)
       else Pair (j, l)

(** val partition :
    int Array.array -> int -> int -> int -> int -> (int, int Array.array) prod **)

let partition l pivot lo initial_lo hi =
  partition_func (ExistT (l, (ExistT (pivot, (ExistT (lo, (ExistT
    (initial_lo, hi))))))))

(** val sort_func :
    (int Array.array, (int, int) sigT) sigT -> int Array.array **)

let rec sort_func x =
  let l = projT1 x in
  let lo = projT1 (projT2 x) in
  let hi = projT2 (projT2 x) in
  let sort0 = fun l0 lo0 hi0 -> sort_func (ExistT (l0, (ExistT (lo0, hi0))))
  in
  let filtered_var = (<=) hi lo in
  if filtered_var
  then l
  else let filtered_var0 = partition l (lookup l lo) lo lo hi in
       let Pair (j, partitioned) = filtered_var0 in
       let filtered_var1 = if (<=) j hi then (<=) lo j else false in
       if filtered_var1
       then sort0 (sort0 partitioned lo (sub j ((fun x -> x + 1) 0)))
              (add j ((fun x -> x + 1) 0)) hi
       else [||]

(** val sort : int Array.array -> int -> int -> int Array.array **)

let sort l lo hi =
  sort_func (ExistT (l, (ExistT (lo, hi))))

(** val quicksort : int Array.array -> int Array.array **)

let quicksort l =
  let shuffled = shuffle l in
  sort shuffled 0 (sub (length shuffled) ((fun x -> x + 1) 0))
