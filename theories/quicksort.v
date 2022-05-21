
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
From Coq Require Export Permutation.




(***************************************
            Arraylist code
****************************************)

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


Definition sublist (lo : nat) (hi : nat) (l : list nat) :=
    fst (List.fold_right (fun (ele : nat) (acc : ((list nat)*nat)) =>
            match acc with
            | (l,index) => if (lo <=? index) && (index <? hi) then
                    (ele :: l, index-1)
                else (l, index-1)
                end) ([],List.length l - 1) l).
    
Compute (sublist 2 5 [0;2;5;3;7;9;5;4;4]).
Example sublist_example1:
    sublist 2 5 [0;2;5;3;7;9;5;4;4] = [5;3;7].
Proof.
    trivial.
Qed.




(***************************************
            Shuffle code
****************************************)



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










(***************************************
            Quicksort code
****************************************)





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

Lemma partition_left_sort :
forall l pivot lo hi,
lo < hi -> hi < List.length l -> lo <= pivot -> pivot <= hi -> ((partition_left l pivot lo hi) = lo) \/ (pivot < (partition_left l pivot lo hi)). 
Proof.
    intros l pivot lo hi H H1 H2 H3. left. unfold partition_left. unfold partition_left_func. admit.
Admitted.

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

Lemma helper : forall pr pl hi lo, pr <= hi -> pl >= lo -> pl < pr -> pr - 1 - (pl + 1) < hi - lo.
Proof. intros. lia.
Qed. 

Program Fixpoint partition (l : list nat) (pivot : nat) (lo : nat) (initial_lo : nat) (hi : nat) {measure (hi-lo)} : (nat*list nat) :=
    match ((partition_left l pivot lo hi), (partition_right l pivot lo hi)) with
    | (i, j) => match j <=? i with
        | false => match (j <=? hi) with
            | true => match (lo <=? i) with 
                | true => partition (swap l i j) pivot i initial_lo j
                | false => (j,[0]) (* will never happen *)
                end
            | false => (j,[1]) (* will never happen *)
            end
        | true => (j, (swap l initial_lo j))
    end end.
Next Obligation.
symmetry in Heq_anonymous1. apply leb_complete_conv in Heq_anonymous1. symmetry in Heq_anonymous.
apply Nat.leb_le in Heq_anonymous. symmetry in Heq_anonymous2. apply Nat.leb_le in Heq_anonymous2. apply helper. trivial. trivial. trivial.
Qed.

Compute (partition (shuffle [15;14;13;12;11;10;5;2;6;3;1;4;9;8;7]) 12 0 0 14).

Program Fixpoint sort (l : list nat) (lo : nat) (hi : nat) {measure (hi-lo)} : list nat :=
    match (hi <=? lo) with
    | true => l
    | false => match (partition l (lookup l lo) lo lo hi) with
        | (j, partitioned) => match ((j <=? hi) && (lo <=? j)) with 
            | false => [2] (* will never happen *)
            | true => sort (sort partitioned lo (j-1)) (j+1) hi
            end
    end end.
Next Obligation.
symmetry in Heq_anonymous0. apply leb_complete_conv in Heq_anonymous0.
symmetry in Heq_anonymous. apply andb_true_iff in Heq_anonymous. destruct  Heq_anonymous.
apply Nat.leb_le in H.
lia.
Qed.
Next Obligation.
symmetry in Heq_anonymous0. apply leb_complete_conv in Heq_anonymous0.
symmetry in Heq_anonymous. apply andb_true_iff in Heq_anonymous. destruct  Heq_anonymous.
apply Nat.leb_le in H0.
lia.
Qed.

Compute (partition_left [3;4;7;1;2;5;6;8;9] 3 0 8).
Compute (partition_right [3;4;7;1;2;5;6;8;9] 3 0 8).
Compute (partition [3;4;7;1;2;5;6;8;9] 3 0 0 8).

Compute (sort [3;4;7;1;2;5;6;8;9] 0 8).

Definition quicksort (l : list nat) : list nat :=
    match (shuffle l) with
    (* | shuffeled => shuffeled  *)
    | shuffled => sort shuffled 0 (List.length shuffled - 1)
    end.

Compute (quicksort [15;14;13;12;11;10;5;2;6;3;1;4;9;8;7]).
Compute (quicksort [66; 91; 69; 62; 52; 10; 49; 38; 53; 54; 98; 95; 92; 6; 20; 32; 41; 71; 59; 25; 80; 75; 73; 79; 63; 48; 12; 46; 28; 68; 65; 24; 81; 85; 47; 35; 33; 30; 17; 72; 7; 89; 40; 39; 94; 51; 13; 11; 67; 16; 76; 31; 77; 60; 82; 61; 42; 18; 36; 87; 93; 88; 26; 22; 8; 4; 84; 29; 21; 97; 56; 2; 37; 90; 9; 15; 50; 58; 70; 78; 19; 99; 86; 44; 96; 1; 100; 14; 43; 64; 55; 3; 27; 45; 74; 0; 23; 57; 34; 5; 83]).
Example quicksort_example1:
    quicksort [2;3;1;4] = [1;2;3;4].
Proof.
    reflexivity.
Qed.




(***************************************
            Definitions for a sortede list taken/reused from Vfa sort.v file
****************************************)




 Inductive sorted : list nat -> Prop :=
 | sorted_nil :
     sorted []
 | sorted_1 : forall x,
     sorted [x]
 | sorted_cons : forall x y l,
     x <= y -> sorted (y :: l) -> sorted (x :: y :: l).
 
 Hint Constructors sorted.


Check nth : forall A : Type, nat -> list A -> A -> A.
Check nth_error : forall A : Type, list A -> nat -> option A.


Definition sorted'' (al : list nat) := forall i j,
    i < j < length al ->
    nth i al 0 <= nth j al 0.



    Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

    Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(* ################################################################# *)
(** * Proof of Correctness *)


Definition sublist_sorted (lo : nat) (hi : nat) (l : list nat) : Prop :=
lo < hi -> 
hi < (List.length l) ->
sorted (sublist lo hi l).

Inductive indexSorted : list nat -> nat -> nat -> Prop :=
| indSorted_sorted : forall l lo hi,
    sorted l -> indexSorted l lo hi
| indSorted_trivial : forall l lo hi,
    hi < lo -> indexSorted l lo hi
| indSorted_sort : forall l lo hi,
    sublist_sorted lo hi l -> indexSorted l lo hi.

Hint Constructors indexSorted.

(*First proof that if l is shuffle it still contains all
 the same elemetns just in a different order*)
Search (Permutation _ _).
Lemma perm_shuffle_list:
    forall l, Permutation l (shuffle l).
Proof.
    intros *. induction l.
    - apply perm_nil.
    - unfold shuffle.
    admit.
Admitted.

Lemma Sort_btw_index :
    forall l lo hi, 
   indexSorted (sort l lo hi) lo hi.
Proof.
    intros l lo hi. destruct (lo <? hi).
    - unfold sort. unfold sort_func. apply indSorted_sort. unfold sublist_sorted. intros. destruct l.
    
    
Search(length _).
Lemma quicksort_sortes:
    forall l , sorted (quicksort l).
Proof.
    intros l. induction l. simpl.
- trivial.
- unfold quicksort. induction (shuffle (a :: l)).
    * trivial.
    * simpl. unfold sort. unfold sort_func. 

    