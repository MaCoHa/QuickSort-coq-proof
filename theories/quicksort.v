
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.
From Coq Require Export Numbers.NatInt.NZDiv.
Require Coq.Program.Wf.


(*Arraylist code*)
Fixpoint lookup (l : list nat) (i : nat) := 
    match l with
    | [] => 0
    | h :: t => if i <=? 0 then h else lookup t (i-1)
    end.
   

Example lookup_example1 :
    lookup [2;3;4;5;1;2] 3= 5.
Proof. simpl. reflexivity. Qed.

Example lookup_example_empty_list :
    lookup [] 3= 0.
Proof. simpl. reflexivity. Qed.

Example lookup_example_higher_than_list :
    lookup [2;3;4;5;1;2] 10 = 0.
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

Definition fst3 (tuple : ((list nat)*nat*nat)) : list nat :=
    match tuple with
    | (a,b,c) => a
    end.

Definition swap (l : list nat) (i1 : nat) (i2 : nat) : list nat :=
    insert (lookup l i2) i1 (insert (lookup l i1) i2 l).

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

Program Fixpoint partition_left (l : list nat) (pivot : nat) (lo : nat) (hi : nat) {measure (hi-lo)} : nat :=
    match hi <=? lo with
        | true => lo
        | false => match (lookup l lo <=? pivot) with
            | true => partition_left l pivot (lo+1) hi
            | false => lo
    end end.
Next Obligation.
    symmetry in Heq_anonymous0. apply leb_complete_conv in Heq_anonymous0.
    lia.
Qed.

Example partition_left_example1:
    partition_left [1;2;3;4;5] 1 0 4 = 1.
Proof.
    reflexivity.
Qed.

Program Fixpoint partition_right (l : list nat) (pivot : nat) (lo : nat) (hi : nat) {measure (hi-lo)} : nat :=
    match hi <=? lo with
        | true => hi
        | false => match (pivot <=? lookup l hi) with
            | true => partition_right l pivot lo (hi-1)
            | false => hi
    end end.
Next Obligation.
    symmetry in Heq_anonymous0. apply leb_complete_conv in Heq_anonymous0.
    lia.
Qed.

Example partition_right_example1:
    partition_right [1;2;3;4;5] 1 0 4 = 0.
Proof.
    reflexivity.
Qed.

Lemma partition_right_le : forall (l : list nat) (pivot lo hi : nat), partition_right l pivot lo hi <= hi.
Proof. intros. unfold partition_right. unfold partition_right_func.
Admitted.

Lemma partition_left_ge : forall (l : list nat) (pivot lo hi : nat), partition_left l pivot lo hi >= lo.
Proof.
Admitted.

Lemma helper : forall pr pl hi lo, pr <= hi -> pl >= lo -> pl < pr -> pr - 1 - (pl + 1) < hi - lo.
Proof. intros. lia.
Qed. 

(* swaps 2 elements that should be swapped *)
Program Fixpoint partition2 (l : list nat) (pivot : nat) (lo : nat) (hi : nat) {measure (hi-lo)} : list nat :=
    (*
    match (lo,hi) with
    | ((lookup hi l > pivot) && (lookup lo l < pivot)) => partition2 l pivot (lo+1) (hi-1)
    | ((lookup hi l > pivot) && (lookup lo l > pivot)) => partition2 l pivot (lo) (hi-1)
    | ((lookup hi l < pivot) && (lookup lo l < pivot)) => partition2 l pivot (lo+1) (hi)
    | ((lookup hi l < pivot) && (lookup lo l > pivot)) => partition2 (swap l lo hi) pivot (lo+1) (hi-1)
    *)
    match ((partition_left l pivot lo hi), (partition_right l pivot lo hi)) with
    | (lo1, hi1) => match hi1 <=? lo1 with
        | false => match (hi1 <=? hi) with
            | true => match (lo <=? lo1) with 
                | true => partition2 (swap l lo1 hi1) pivot (lo1+1) (hi1-1)
                | false => l (* will never happen *)
                end
            | false => l (* will never happen *)
            end
        | true => l
    end end.
    Next Obligation.
    (* symmetry in Heq_anonymous. apply leb_complete_conv in Heq_anonymous. assert (partition_right l pivot lo hi <= hi). apply partition_right_le. assert (partition_left l pivot lo hi >= lo). apply partition_left_ge.
    apply helper. trivial. trivial. trivial. *)
    symmetry in Heq_anonymous1. apply leb_complete_conv in Heq_anonymous1. symmetry in Heq_anonymous.
    apply Nat.leb_le in Heq_anonymous. symmetry in Heq_anonymous2. apply Nat.leb_le in Heq_anonymous2. apply helper. trivial. trivial. trivial.
    Qed.

Definition quicksort (l : list nat) : list nat :=
    match (shuffle l) with
    (* | shuffeled => shuffeled  *)
    | shuffled => partition2 shuffled (lookup shuffled 0) 0 (List.length shuffled - 1)
    end.

Compute (quicksort [5;2;6;3;1;4;9;8;7]).

Example quicksort_example1:
    quicksort [2;3;1;4] = [2;1;3].
Proof.
    reflexivity.
Qed.







(* Fixpoint partition (l : list nat) (lo : nat) (hi : nat) : list nat :=
    match l with
    | [] => l
    | [x] => l 
    | [h :: t] => 





Definition quicksort (l : list nat) : list nat :=
    shuffle l *)



