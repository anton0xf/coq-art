Require Import Bool Arith ZArith List.

Import ListNotations.

(* EXAMPLES *) 
(* The following function takes two arguments a and b
which are numbers of type nat and returns b + 2 * (a + b) *)
Definition f_ex (a b : nat) := b + 2 * (a + b).

(* When p is a pair, you can access its components by the "pattern-matching"
  construct illustrated in the following function. *)
Definition add_pair_components (p : nat * nat) :=
  match p with (a, b) => a + b end.

(* f_ex is a function with two arguments.  add_pair_components is a
  function with one argument, which is a pair. *)

(* END OF EXAMPLES *)

(* 1/ Define a function that takes two numbers as arguments and returns
  the sum of the squares of these numbers. *)
Definition sumsq (a b : nat) := a * a + b * b.

(* 2/ Define a function that takes 5 arguments a b c d e, which are all
   numbers and returns the sum of all these numbers. *)
Definition sum5 (a b c d e : nat) := a + b + c + d + e.

(* 3/ Define a function named add5 that takes a number as argument and returns
   this number plus 5. *)
Definition add5 := Nat.add 5.

(* The following should return 8 *)
Compute add5 3.

(* The following commands make it possible to find pre-defined functions
Search nat.
Search bool.
 *)

(* 4/ Write a function swap of type list nat -> list nat such that
  swap (a::b::l) = (b::a::l)  and
  swap l' = l' if l' has less than 2 elements. *)
Definition swap (ns : list nat) : list nat
  := match ns with
     | [] | [_] => ns
     | n1 :: n2 :: ns' => n2 :: n1 :: ns'
     end.

Theorem swap_long (a b : nat) (l : list nat) : swap (a::b::l) = (b::a::l).
Proof. reflexivity. Qed.

Theorem swap_short (ns : list nat) : length ns < 2 -> swap ns = ns.
Proof.
  intro H.
  destruct ns; try reflexivity.
  destruct ns; try reflexivity.
  repeat apply lt_S_n in H.
  now apply Nat.nlt_0_r in H.
Qed.

(* 5/ Write a function proc2 of type list nat -> nat, such that
   proc2 (a::b::l) = (b + 3) and
   proc2 l' = 0 if l' has less than 2 elements.

   In other words, proc2 only processes the 2nd argument of the list and
   returns that number plus 3.  If there is no second argument to the list,
   proc2 returns 0.  *)
Definition proc2 (ns : list nat) : nat
  := match ns with
     | [] | [_] => 0
     | n1 :: n2 :: _  => n2 + 3
     end.

(* 6/ Write a function ms of type list nat -> list nat such that
      ms (a::b::...::nil) = a+2::b+2::...::nil
      For instance
      ms (2::3::5::nil) = (4::5::7::nil) *)
Fixpoint ms (ns : list nat) : list nat
  := match ns with
     | [] => []
     | n :: ns' => (n + 2) :: (ms ns')
     end.

Example ms_ex : ms (2::3::5::nil) = (4::5::7::nil).
Proof. reflexivity. Qed.

(* 7/ Write a function sorted of type list nat -> bool, such that
    sorted l = true exactly when the natural numbers in
   l are in increasing order. *)
Definition sorted (ns : list nat) : bool
  := let fix iter (n : nat) (ns : list nat)
         := match ns with
            | [] => true
            | n' :: ns' => (n <=? n') && iter n' ns'
            end
     in match ns with
        | [] => true
        | n :: ns' => iter n ns'
        end.

Example sorted_ex : sorted [1; 3; 3; 5] = true.
Proof. reflexivity. Qed.

Example sorted_ex2 : sorted [1; 3; 2; 3; 5] = false.
Proof. reflexivity. Qed.

Inductive sorted_p  : list nat -> Prop
  := sorted0 : sorted_p []
   | sorted1 (n : nat) : sorted_p [n]
   | sorted_n (n0 n1 : nat) (ns : list nat) :
       n0 <= n1
       -> sorted_p (n1 :: ns)
       -> sorted_p (n0 :: n1 :: ns).

Example sorted_p_ex : sorted_p [1; 3; 3; 5].
Proof. auto using sorted_p with arith. Qed.

Example sorted_p_ex2 : ~ sorted_p [1; 3; 2; 3; 5].
Proof.
  intro H. inversion H. inversion H4.
  now apply Nat.nle_succ_diag_l in H7.
Qed.

Theorem iff_true_r (A : Prop) : A -> (A <-> True).
Proof. firstorder. Qed.

Theorem iff_true_l (A : Prop) : A -> (True <-> A).
Proof. firstorder. Qed.

Theorem proven_iff (A B : Prop) : A -> B -> (A <-> B).
Proof. firstorder. Qed.

Theorem sorted_correct (ns : list nat) : sorted ns = true <-> sorted_p ns.
Proof.
  induction ns as [| n0 ns0 IH]; try destruct ns0 as [| n1 ns1];
    try ( apply proven_iff; try reflexivity; constructor ).
  split; intro H; inversion H.
  - apply andb_prop in H1 as [H1 H2].
    apply Nat.leb_le in H1 as H1'.
    apply sorted_n; try assumption.
    apply IH. assumption.
  - subst n2 n3 ns. apply Nat.leb_le in H2 as H2'.
    assert (sorted (n1 :: ns1) = true) as Hs.
    { apply IH. assumption. }
    simpl. apply andb_true_intro; split; assumption.
Qed.

(* 8/ Write a function p2 of type nat -> nat such that
    p2 n = 2 ^ n *)
Fixpoint p2 (n : nat) : nat
  := match n with
     | O => 1
     | S n' => 2 * (p2 n')
     end.

Example p2_ex : p2 3 = 8.
Proof. reflexivity. Qed.

Theorem p2_correct (n : nat) : Nat.pow 2 n = p2 n.
Proof.
  induction n as [| n' IH]; try reflexivity.
  simpl. rewrite <- IH. ring.
Qed.

(* 9/ Write a function salt of type nat -> nat -> nat such that
   salt x n = x^n - x^(n-1) + x^(n-2) .... + 1 or -1, if x <> 0,
   depending on the parity of n, thus
   salt x 3 = x^3 - x^2 + x - 1
   salt x 4 = x^4 - x^3 + x^2 - x + 1
   salt 2 3 = 5

   You may have to define auxiliary functions. *)

(* 10/  Consider the following definition *)

Inductive btree : Type :=
|  leaf
|  bnode (n:nat)(t1 t2: btree).

(* write a function that list the labels of a tree by infix order *)
(** you may use the concatenation function app on lists
  (also written l1 ++ l2 ) *)


(* write a boolean function that checks whether a tree is a binary
search tree *)
