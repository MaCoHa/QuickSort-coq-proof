
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
Require Coq.extraction.Extraction.
Extraction Language OCaml.



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

Lemma lookup_elem: forall (l : list nat) (index elem : nat),
index < List.length l -> In (lookup l index) l.
Proof.
    intros.
Admitted.




Fixpoint insert (l : list nat) (index : nat) (elem : nat) :=
match (index, l) with
| (0, x::xs) => elem :: xs
| (0, []) => [elem] (* should never happen *)
| (n, x::xs) => x :: (insert xs (index-1) elem)
| (n, []) => [elem] (* should never happen *)
end.

Example insert_example1:
    insert [2;2;2] 1 3 = [2;3;2].
Proof.
    trivial.
Qed.

Example insert_example2:
    insert [2] 0 3 = [3].
Proof.
    trivial.
Qed.

Lemma insert_ele: forall (l : list nat)(index elem : nat),
    index < List.length l -> lookup (insert l index elem) index = elem.
Proof.
    intros.
Admitted.

Fixpoint sublist (lo : nat) (hi : nat) (l : list nat) :=
    match (lo,hi,l) with
    | (_,_,[]) => []
    | (_,0,_) => []
    | (0,_,x::xs) => x :: (sublist 0 (hi-1) xs)
    | (_,_,x::xs) => sublist (lo-1) (hi-1) xs
    end.
    
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

Lemma randnat_less: forall (seed bound : nat),
    bound > 0 -> randnat seed bound < bound.
Proof.
    intros. unfold randnat. apply Nat.mod_bound_pos.
    - lia.
    - lia.
Qed.

Definition fst3 (A : Type) (B : Type) (C : Type) (tuple : (A*B*C)) : A :=
    match tuple with
    | (a,b,c) => a
    end.

Lemma fst3_first: forall (A B C : Type) (a:A) (b:B) (c:C),
    fst3 A B C (a,b,c) = a.
Proof.
    trivial.
Qed.

Definition swap (l : list nat) (i1 : nat) (i2 : nat) : list nat :=
    insert (insert l i2 (lookup l i1)) i1 (lookup l i2).

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

Lemma swap_perm:
    forall (l : list nat) (i0 i1 : nat),
    i0 < List.length l -> i1 < List.length l -> Permutation l (swap l i0 i1).
Proof.
    intros. generalize dependent i0. generalize dependent i1. induction l.
    - intros. simpl in H. lia.
    - intros. simpl in *. unfold swap.
Admitted. 


Definition shuffle (l : list nat) : list nat :=
    fst3 (list nat) nat nat (List.fold_left (fun (acc : ((list nat)*nat*nat)) (a : nat) =>
            match acc with
            | (li,seed,point) => (swap li point (randnat seed (List.length li)) ,seed+1,point+1)
            end) l (l,42,0)).

Example shuffle_example1:
    shuffle [1;2;3;4;5] = [2;3;4;1;5]. (*pseudorandom order*)
Proof.
    reflexivity.
Qed.




Lemma perm_shuffle_list:
    forall l, Permutation l (shuffle l).
Proof.
    intros. unfold shuffle.
    - assert (forall (l : list nat) (i0 i1 : nat),
    Permutation l (swap l i0 i1)).
        + intros. apply swap_perm.
            * admit.
            * admit.
        + 
Admitted.

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


Lemma partition_left_partitions : forall (l : list nat) (pivot lo hi j : nat),
    lo <= hi -> hi < List.length l -> j < (partition_left l pivot lo hi) -> lookup l j < pivot.
Proof.
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

Lemma partition_right_partitions : forall (l : list nat) (pivot lo hi j : nat),
    lo <= hi -> hi < List.length l -> j < List.length l -> (partition_right l pivot lo hi) < j -> pivot < lookup l j.
Proof.
    Admitted.

Program Fixpoint partition (l : list nat) (pivot : nat) (lo : nat) (initial_lo : nat) (hi : nat) {measure (hi-lo)} : (nat*list nat) :=
    match ((partition_left l pivot lo hi), (partition_right l pivot lo hi)) with
    | (i, j) => match j <=? i with
        | false => match (j <=? hi) with
            | true => match (lo <=? i) with 
                | true => partition (swap l i j) pivot i initial_lo j
                | false => (j,l) (* will never happen *)
                end
            | false => (j,l) (* will never happen *)
            end
        | true => (j, (swap l initial_lo j))
    end end.
Next Obligation.
symmetry in Heq_anonymous1. apply leb_complete_conv in Heq_anonymous1. symmetry in Heq_anonymous.
apply Nat.leb_le in Heq_anonymous. symmetry in Heq_anonymous2. apply Nat.leb_le in Heq_anonymous2.
Admitted.

Lemma partition_low : forall (l : list nat) (pivot lo initial_lo hi j : nat),
initial_lo <= lo -> lo <= hi -> hi < List.length l -> lo <= j -> j < (fst(partition l pivot lo initial_lo hi)) -> (lookup (snd(partition l pivot lo initial_lo hi)) j < pivot).
Proof.
    intros.
    Admitted.

Lemma partition_high : forall (l : list nat) (pivot lo initial_lo hi i : nat),
initial_lo <= lo -> lo <= hi -> hi < List.length l -> i <= hi -> fst(partition l pivot lo initial_lo hi) < i -> (pivot < lookup (snd(partition l pivot lo initial_lo hi)) i).
Proof.
    intros.
    Admitted.

Inductive sorted_segment : nat -> nat -> list nat -> Prop :=
| sorted_segment_nil : forall x lst, x <= List.length lst -> sorted_segment x x lst
| sorted_segment_1 : forall x lst, x < List.length lst -> lst <> [] -> sorted_segment x (x + 1) lst
| sorted_segment_cons : forall x y lst, x < y -> y <= List.length lst ->
    lookup lst x <= lookup lst (x + 1) -> sorted_segment (x + 1) y lst -> sorted_segment x y lst.

Hint Constructors sorted_segment.

Program Fixpoint sort (l : list nat) (lo : nat) (hi : nat) {measure (hi-lo)} : list nat :=
    match (hi <=? lo) with
    | true => l
    | false => match (partition l (lookup l lo) lo lo hi) with
        | (j, partitioned) => match ((j <=? hi) && (lo <=? j)) with 
            | false => [] (* will never happen *)
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

Lemma sort_sorted_seqment : forall (l : list nat) (lo hi : nat),
 lo <= hi -> hi <= List.length l -> sorted_segment lo hi (sort l lo (hi-1)).
Proof.
    intros l. induction l.
    - intros. simpl in *.
    inversion H0. subst. inversion H. subst. apply sorted_segment_nil. simpl. lia.
    - intros. destruct H.
    + apply sorted_segment_nil.
Admitted.

Definition quicksort (l : list nat) : list nat :=
    let shuffled := (shuffle l) in sort shuffled 0 (List.length shuffled - 1).

Example quicksort_example1:
    quicksort [2;3;1;4] = [1;2;3;4].
Proof.
    reflexivity.
Qed.

Example quickort_example2:
    quicksort [15;14;13;12;11;10;5;2;6;3;1;4;9;8;7] = [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15].
Proof.
    trivial.
Qed.

Example quicksort_example3:
    quicksort [66;91;69;62;52;10;49;38;53;54;98;95;92;6;20;32;41;71;59;25;80;75;73;79;63;48;12;46;28;68;65;24;81;85;47;35;33;30;17;72;7;89;40;39;94;51;13;11;67;16;76;31;77;60;82;61;42;18;36;87;93;88;26;22;8;4;84;29;21;97;56;2;37;90;9;15;50;58;70;78;19;99;86;44;96;1;100;14;43;64;55;3;27;45;74;0;23;57;34;5;83]
    = [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32;33;34;35;36;37;38;39;40;41;42;43;44;45;46;47;48;49;50;51;52;53;54;55;56;57;58;59;60;61;62;63;64;65;66;67;68;69;70;71;72;73;74;75;76;77;78;79;80;81;82;83;84;85;86;87;88;89;90;91;92;93;94;95;96;97;98;99;100].
Proof.
    trivial.
Qed.




(***************************************
            Definitions for a sorted list taken/reused from Vfa sort.v file
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

Lemma sorted_segment_smaller :
    forall l lo hi a,
    lo < hi -> sorted_segment (lo+1) (hi+1) (a::l) -> sorted_segment (lo) (hi) l.
Proof.
    intros l.
    induction l.
    - intros. inversion H0.
    + lia.
    + inversion H1.
    * subst. simpl in *. lia.
    + subst. simpl in *. destruct H2.
    * inversion H4.
    -- subst. simpl in *. lia. 
    -- subst. simpl in *. lia.
    -- subst. simpl in *. assert (hi = 1). lia. subst. lia.
    * inversion H4.
    -- subst. simpl in *. lia. 
    -- subst. simpl in *. lia.
    -- subst. simpl in *. assert (hi = 1). lia. subst. lia.
    - intros. inversion H0.
    + lia.
    + simpl in *. subst. destruct lo.
    * simpl in *. assert (hi = 1). lia. subst. apply sorted_segment_1.
    -- simpl. lia.
    -- apply not_eq_sym. apply nil_cons.
    * simpl in *. assert (hi = S (S lo)). lia. subst. assert (S (S lo) = (S lo) + 1). lia. rewrite H3. apply sorted_segment_1.
    -- simpl in *. lia.
    -- apply not_eq_sym. apply nil_cons.
    + subst. apply sorted_segment_cons.
    * trivial.
    * simpl in H2. rewrite Nat.add_1_r in H2. apply le_S_n in H2. simpl. apply H2.
    * admit.
    * admit.
Admitted.

Lemma start_end_sort :
    forall l,
    sorted_segment 0 (List.length l) l -> sorted l .
Proof.
    intros l H. induction l.
    - apply sorted_nil.
    - induction l.
    + apply sorted_1.
    + apply sorted_cons.
    * inversion H. subst. simpl in *. lia.
    * inversion H. subst. simpl in *. apply IHl. apply sorted_segment_smaller with (a:=a).
    -- lia.
    -- simpl in *. rewrite Nat.add_1_r. apply H3.
Qed.

Lemma sort_perm : forall l,
    Permutation (sort l 0 (length l - 1)) l.
Proof.
    intros.
    induction l.
    - trivial.
    -  
Admitted.

Lemma sort_same_length : forall l,
    length (sort l 0 (length l - 1)) = length l.
Proof.
    intros. apply Permutation_length. apply sort_perm.
Qed.

Theorem quicksort_sorts:
    forall l , sorted (quicksort l).
Proof.
    intros l. induction l.
    - trivial.
    - unfold quicksort. apply start_end_sort. rewrite sort_same_length. apply sort_sorted_seqment.
    + lia.
    + rewrite <- perm_shuffle_list. lia. 
Qed.



Extract Inductive nat => "int"
 [ "0" "(fun x -> x + 1)" ]
 "(fun zero succ n ->
 if n=0 then zero ()
 else succ (n-1))".

Extract Inductive list => "Array.array" [ "[||]" "(::)" ].
Extract Constant plus => "( + )".
Extract Constant minus => "( - )".
Extract Constant mult => "( - )".
Extract Constant lookup => "Array.get".
Extract Constant insert => "(fun xs i x -> Array.set xs i x; xs)".
Extract Constant length => "Array.length".
Extract Constant fold_left => "(fun folder l acc -> Array.fold_left folder acc l)".
Extract Inlined Constant leb => "(<=)".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant eqb => "( = )".

Extraction "verified_quicksort_array.ml" quicksort.

    