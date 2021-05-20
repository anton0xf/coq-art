Require Import Arith ZArith.

Parameters (prime_divisor : nat -> nat)
           (prime : nat -> Prop)
           (divides: nat -> nat -> Prop).

Open Scope nat_scope.
Check (prime (prime_divisor 220)).
(* prime (prime_divisor 220) : Prop *)

Check (divides (prime_divisor 220) 220).
(* divides (prime_divisor 220) 220 : Prop *)

Check (divides 3).
(* divides 3 : nat -> Prop *)

Parameter binary_word : nat -> Set.
Check binary_word. (* binary_word : nat -> Set *)

Definition short : Set := binary_word 32.
Definition long  : Set := binary_word 64.

Check short. (* short : Set *)

Check (not (divides 3 81)).
(* ~ divides 3 81 : Prop *)

Check (let d := prime_divisor 220 in prime d /\ divides d 220).
(* let d := prime_divisor 220 in prime d /\ divides d 220 : Prop *)

Require Import List.
Parameters (decomp : nat -> list nat)
           (decomp2 : nat -> nat * nat).
Check (decomp 220).  (* decomp 220 : list nat *)
Check (decomp2 284). (* decomp2 284 : nat * nat *)

Check (forall n : nat, if n <=? 1 then bool else nat).
(* forall n : nat, if n <=? 1 then bool else nat : Set *)

Parameter prime_divisor_correct : forall n : nat,
    2 <= n -> let d := prime_divisor n
              in prime d /\ divides d n.

Check prime_divisor_correct.
(* prime_divisor_correct : forall n : nat,
   2 <= n -> let d := prime_divisor n in prime d /\ divides d n *)

Check cons.
(* cons : ?A -> list ?A -> list ?A
   where ?A : [ |- Type] *)

Check pair.
(* pair : ?A -> ?B -> ?A * ?B
   where ?A : [ |- Type]
         ?B : [ |- Type] *)

Check (forall A B : Set, A -> B -> A * B).
(* forall A B : Set, A -> B -> A * B : Type *)

Check fst.
(* fst : ?A * ?B -> ?A
   where ?A : [ |- Type]
         ?B : [ |- Type] *)

Check le_n. (* le_n : forall n : nat, n <= n *)
Check le_S. (* le_S : forall n m : nat, n <= m -> n <= S m *)
Check (le_n 36). (* le_n 36 : 36 <= 36 *)

Definition le_36_37 := le_S 36 36 (le_n 36).
Check le_36_37. (* le_36_37 : 36 <= 37 *)

Definition le_36_38 := le_S 36 37 le_36_37.
Check le_36_38. (* le_36_38 : 36 <= 38 *)

Check (le_S _ _ (le_S _ _ (le_n 36))).
(* le_S 36 37 (le_S 36 36 (le_n 36)) : 36 <= 38 *)

Check (prime_divisor_correct 220).
(* prime_divisor_correct 220
   : 2 <= 220 -> let d := prime_divisor 220 in prime d /\ divides d 220 *)

Parameter iterate : forall A : Set, (A -> A) -> nat -> A -> A.
Check (iterate nat).
(* iterate nat : (nat -> nat) -> nat -> nat -> nat *)
Check (iterate _ (mult 2)).
(* iterate nat (Init.Nat.mul 2) : nat -> nat -> nat *)
Check (iterate _ (mult 2) 10).
(* iterate nat (Init.Nat.mul 2) 10 : nat -> nat *)
Check (iterate _ (mult 2) 10 1).
(* iterate nat (Init.Nat.mul 2) 10 1 : nat *)

Parameter binary_word_concat
  : forall n m : nat, binary_word n -> binary_word m -> binary_word (n + m).

Check binary_word_concat.
(* binary_word_concat : forall n m : nat,
     binary_word n -> binary_word m -> binary_word (n + m) *)
Check (binary_word_concat 32).
(* binary_word_concat 32 : forall m : nat,
     binary_word 32 -> binary_word m -> binary_word (32 + m) *)
Check (binary_word_concat 32 32).
(* binary_word_concat 32 32
   : binary_word 32 -> binary_word 32 -> binary_word (32 + 32) *)

Check (forall (A B : Set) (a : A) (b : B), A * B).
(* forall A B : Set, A -> B -> A * B : Type *)

Definition twice (A : Set) (f : A -> A) (a : A) : A := f (f a).
Check twice. (* twice : forall A : Set, (A -> A) -> A -> A *)
Check (twice Z). (* twice Z : (Z -> Z) -> Z -> Z *)
Check (twice Z (fun z => (z * z)%Z)).
(* twice Z (fun z : Z => (z * z)%Z) : Z -> Z *)
Check (twice _ S 56). (* twice nat S 56 : nat *)
Check (twice (nat -> nat) (fun f x => f (f x)) (mult 3)).
(* twice (nat -> nat)
         (fun (f : nat -> nat) (x : nat) => f (f x))
         (Init.Nat.mul 3)
   : nat -> nat *)
Check (twice (nat -> nat) (twice _) (mult 3)).
(* twice (nat -> nat) (twice nat) (Init.Nat.mul 3)
   : nat -> nat *)
Eval compute in (twice (nat -> nat) (fun f x => f (f x)) (mult 3) 1).
(* = 81 : nat *)
Eval compute in (twice (nat -> nat) (twice _) (mult 3) 1).
(* = 81 : nat *)

Definition binary_word_duplicate (n : nat) (w : binary_word n)
  : binary_word (n + n)
  := binary_word_concat _ _ w w.
Check binary_word_duplicate.
(* binary_word_duplicate
   : forall n : nat, binary_word n -> binary_word (n + n) *)

Theorem le_n_SSn (n : nat) : n <= S (S n).
Proof. exact (le_S _ _ (le_S _ _ (le_n n))). Qed.

Theorem le_n_SSn' (n : nat) : n <= S (S n).
Proof. apply le_S, le_S, le_n. Qed.
Print le_n_SSn'.
(* le_n_SSn' = 
   fun n : nat => le_S n (S n) (le_S n n (le_n n))
   : forall n : nat, n <= S (S n) *)

Definition compose (A B C : Set) : (A -> B) -> (B -> C) -> A -> C
  := fun f g x => g (f x).
Print compose.
(* compose = 
   fun (A B C : Set) (f : A -> B) (g : B -> C) (x : A) => g (f x)
   : forall A B C : Set, (A -> B) -> (B -> C) -> A -> C *)

Check compose.
(* compose : forall A B C : Set, (A -> B) -> (B -> C) -> A -> C *)

Check (fun (A : Set) (f : Z -> A) => compose _ _ _ Z_of_nat f).
(* fun (A : Set) (f : Z -> A) => compose nat Z A Z.of_nat f
   : forall A : Set, (Z -> A) -> nat -> A *)

Check (compose _ _ _ Z.abs_nat (plus 78) 45%Z).
(* compose Z nat nat Z.abs_nat (Init.Nat.add 78) 45%Z : nat *)

Check (le_n_SSn 1515). (* le_n_SSn 1515 : 1515 <= 1517 *)
Check (le_S _ _ (le_n_SSn 1515)).
(* le_S 1515 1517 (le_n_SSn 1515) : 1515 <= 1518 *)

Arguments compose [A B C].
Check compose.
(* compose : forall A B C : Set, (A -> B) -> (B -> C) -> A -> C *)
Print Implicit compose.
(* compose : forall [A B C : Set], (A -> B) -> (B -> C) -> A -> C
   Arguments A, B, C are implicit *)


Arguments compose {A B C}.
Arguments le_S {n m}.

Check compose.
(* compose : (?A -> ?B) -> (?B -> ?C) -> ?A -> ?C
   where ?A : [ |- Set]
         ?B : [ |- Set]
         ?C : [ |- Set] *)

Print Implicit compose.
(* compose : forall {A B C : Set}, (A -> B) -> (B -> C) -> A -> C
   Arguments A, B, C are implicit and maximally inserted *)

Check (compose Z.abs_nat (plus 78)).
(* compose Z.abs_nat (Init.Nat.add 78) : Z -> nat *)
Check (le_S (le_n_SSn 1515)).
(* le_S (le_n_SSn 1515) : 1515 <= 1518 *)

Check (compose S).
(* compose S : (nat -> ?C) -> nat -> ?C
   where ?C : [ |- Set] *)

Check (compose (C := Z) S).
(* compose S : (nat -> Z) -> nat -> Z *)

Check (le_S (n := 45)).
(* le_S (n := 45) : forall m : nat, 45 <= m -> 45 <= S m *)

Reset compose.
Set Implicit Arguments.
Definition compose (A B C : Set) (f : A -> B) (g : B -> C) (a : A) := g (f a).
Definition thrice (A : Set) (f : A -> A) := compose f (compose f f).
(* Unset Implicit Arguments. *)
Print Implicit compose.
(* compose : forall [A B C : Set], (A -> B) -> (B -> C) -> A -> C
   Arguments A, B, C are implicit *)

Print Implicit thrice.
(* thrice : forall [A : Set], (A -> A) -> A -> A
   Argument A is implicit *)

Eval cbv beta delta in (thrice (thrice (A := nat)) S 0).
(* = 27 : nat *)

Check (thrice (thrice (A := nat)) S 0).
(* thrice (thrice (A:=nat)) S 0 : nat *)

(* Check (thrice thrice S 0). *)
(* Toplevel input, characters 14-20:
   > Check (thrice thrice S 0).
   >               ^^^^^^
   Error:
   The term "thrice" has type "forall A : Set, (A -> A) -> A -> A"
   while it is expected to have type "?A -> ?A"
   (unable to find a well-typed instantiation for
   "?A": cannot ensure that "Type" is a subtype of
   "Set"). *)

Arguments thrice {A}.
Check (thrice thrice S 0).
(* thrice thrice S 0 : nat *)
