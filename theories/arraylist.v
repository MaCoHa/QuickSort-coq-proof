Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.






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