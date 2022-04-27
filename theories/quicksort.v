
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.
From Coq Require Export Numbers.NatInt.NZDiv.

(*Arraylist code*)
Fixpoint lookup (i : nat) (l : list nat) := 
    match l with
    | [] => 0
    | h :: t => if i <=? 0 then h else lookup (i-1) t
    end.
   

Example lookup_example1 :
    lookup 3 [2;3;4;5;1;2] = 5.
Proof. simpl. reflexivity. Qed.

Example lookup_example_empty_list :
    lookup 3 [] = 0.
Proof. simpl. reflexivity. Qed.

Example lookup_example_higher_than_list :
    lookup 10 [2;3;4;5;1;2] = 0.
Proof. simpl. reflexivity. Qed.


Fixpoint insert (elem : nat) (index : nat) (l : list nat) :=
match (index, l) with
| (0, x::xs) => elem :: xs
| (0, []) => [elem] (* should never happen *)
| (n, x::xs) => x :: (insert elem (index-1) xs)
| (n, []) => [elem] (* should never happen *)
end.

Example insert_example1:
    insert 3 1 [2;2;2] = [2;3;2].
Proof.
    trivial.
Qed.

Example insert_example2:
    insert 3 0 [2] = [3].
Proof.
    trivial.
Qed.

(*Shuffle code*)

Definition randnat (seed : nat) (bound : nat) : nat :=
    (seed*31+7) mod bound.

Definition fst3 (tuple : (list nat*nat*nat)) : list nat :=
    match tuple with
    | (a,b,c) => a
    end.

Definition swap (l : list nat) (i1 : nat) (i2 : nat) : list nat :=
    insert (lookup i2 l) i1 (insert (lookup i1 l) i2 l).

Example swap_example1:
    swap [1;2;3;4] 0 3 = [4;2;3;1].
Proof.
    trivial.
Qed.

Example swap_example2:
    swap [1;2;3;4;5] 0 3 = [4;2;3;1;5].
Proof.
    trivial.
Qed.

Definition shuffle (l : list nat) : list nat :=
    fst3 (List.fold_left (fun (acc : ((list nat)*nat*nat)) (a : nat) =>
            match acc with
            | (li,seed,point) => (swap li point (randnat seed (List.length li)) ,seed+1,point+1)
            end) l (l,42,0)).

Example shuffle_example1:
    shuffle [1;2;3;4;5] = [2;3;4;1;5]. (*pseudorandom order*)
Proof.
    reflexivity.
Qed.


(*Quicksort code*)
Fixpoint partition_left (l : list nat) (pivot : nat) (lo : nat) (hi : nat) : nat :=
    if ((lookup l lo < pivot) && (lo < hi)) then partition_left l pivot (lo+1) else lo
.    


Fixpoint partition_right (l : list nat) (pivot : nat) (lo : nat) (hi : nat) : nat :=
    if ((lookup l hi > pivot) && (lo < hi)) then partition_right l pivot (hi-1) else hi
    




Fixpoint partition2 (l : list nat) (pivot : nat) (lo : nat) (hi : nat) : list nat :=
    (*
    match (lo,hi) with
    | ((lookup hi l > pivot) && (lookup lo l < pivot)) => partition2 l pivot (lo+1) (hi-1)
    | ((lookup hi l > pivot) && (lookup lo l > pivot)) => partition2 l pivot (lo) (hi-1)
    | ((lookup hi l < pivot) && (lookup lo l < pivot)) => partition2 l pivot (lo+1) (hi)
    | ((lookup hi l < pivot) && (lookup lo l > pivot)) => partition2 (swap l lo hi) pivot (lo+1) (hi-1)
    *)


    match ((partition_left l pivot lo hi), (partition_right l pivot lo hi)) with
    | (lo, hi) => if lo < hi then partition2 (swap l lo hi) pivot (lo+1) (hi-1) else l

    end







(* Fixpoint partition (l : list nat) (lo : nat) (hi : nat) : list nat :=
    match l with
    | [] => l
    | [x] => l 
    | [h :: t] => 





Definition quicksort (l : list nat) : list nat :=
    shuffle l *)



