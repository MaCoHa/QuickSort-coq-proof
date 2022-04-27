Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.
From Coq Require Export Numbers.NatInt.NZDiv.


Fixpoint lookup (l : list nat) (i : nat) := 
    match l with
    | [] => 0
    | h :: t => if i <=? 0 then h else lookup t (i-1)
    end.
   

Example lookup_example1 :
    lookup [2;3;4;5;1;2] 3 = 5.
Proof. simpl. reflexivity. Qed.

Example lookup_example_empty_list :
    lookup [] 3 = 0.
Proof. simpl. reflexivity. Qed.

Example lookup_example_higher_than_list :
    lookup [2;3;4;5;1;2] 10 = 0.
Proof. simpl. reflexivity. Qed.


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

Definition randnat (seed : nat) (bound : nat) : nat :=
    (seed*31+7) mod bound.

Definition fst3 (tuple : (list nat*nat*nat)) : list nat :=
    match tuple with
    | (a,b,c) => a
    end.

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
