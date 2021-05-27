Require Import Arith ZArith.

Theorem conv_example (n : nat) : 7*5 < n -> 6*6 <= n.
Proof. intro H. assumption. Qed.

Print conv_example.
(* conv_example = fun (n : nat) (H : 7 * 5 < n) => H
   : forall n : nat, 7 * 5 < n -> 6 * 6 <= n *)

Theorem conv_example' (n : nat) : 7*5 < n -> 6*6 <= n.
Proof. exact id. Qed.

Theorem conv_example'' (n : nat) : 7*5 < n -> 6*6 <= n.
Proof. simpl. intro H. assumption. Qed.

Print conv_example''.
(* conv_example'' = fun (n : nat) (H : 35 < n) => H
(*      : forall n : nat, 7 * 5 < n -> 6 * 6 <= n *)
