Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.

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