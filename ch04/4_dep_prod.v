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

Check (thrice (A := nat -> nat) (thrice (A := nat)) S 0).
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

Definition short_concat : short -> short -> long
  := binary_word_concat 32 32.

Check (binary_word_concat 32 32).
(* binary_word_concat 32 32
   : binary_word 32 -> binary_word 32 -> binary_word (32 + 32) *)

Print short. (* short = binary_word 32 : Set *)
Print long. (* long = binary_word 64 : Set *)
Eval cbv delta beta iota in (binary_word (32 + 32)).
(* = binary_word 64 : Set *)

(* Exercise 4.3
   In the context of the following section, verify that the three
   theorems have well-formed statements and then construct terms
   that inhabit these types. *)
Section A_declared.
  Variables (A : Set) (P Q : A -> Prop) (R : A -> A -> Prop).

  Theorem all_perm : (forall a b : A, R a b) -> forall a b : A, R b a.
  Proof using. intros H a b. apply H. Qed.

  Theorem all_imp_dist
    : (forall a : A, P a -> Q a) -> (forall a : A, P a)
      -> forall a : A, Q a.
  Proof using. intros H1 H2 a. apply H1, H2. Qed.

  Theorem all_delta : (forall a b : A, R a b) -> forall a : A, R a a.
  Proof using. intros H a. apply H. Qed.
End A_declared.

Reset iterate.
Fixpoint iterate {A : Set} (f : A -> A) (n : nat) (a : A) : A
  := match n with
     | O => a
     | S n' => iterate f n' (f a)
     end.
Arguments iterate {A}.

Definition my_plus : nat -> nat -> nat := iterate S.

Theorem iterate_assoc {A : Set} (f : A -> A) (n : nat) (a : A)
  : iterate f n (f a) = f (iterate f n a).
Proof.
  generalize dependent a.
  induction n as [| n' IH]; intro a; try reflexivity.
  simpl. apply IH.
Qed.

Theorem iterate_one {A : Set} (f : A -> A) (n : nat) (a : A)
  : iterate f (S n) a = f (iterate f n a).
Proof.
  generalize dependent a.
  induction n as [| n' IH]; intro a; try reflexivity.
  simpl. apply IH.
Qed.

Theorem my_plus_correct (n m : nat) : my_plus n m = n + m.
Proof.
  induction n as [| n' IH]; try reflexivity.
  simpl. rewrite <- IH.
  unfold my_plus. simpl.
  apply iterate_assoc.
Qed.

Definition my_mult (n m : nat) : nat := iterate (my_plus n) m 0.

Theorem my_mult_zero_l (n : nat) : my_mult 0 n = 0.
Proof.
  induction n as [| n' IH]; try reflexivity.
  unfold my_mult. simpl. rewrite my_plus_correct. simpl.
  unfold my_mult in IH. exact IH.
Qed.

Theorem my_mult_zero_r (n : nat) : my_mult n 0 = 0.
Proof. unfold my_mult. reflexivity. Qed.

Theorem my_mult_Sn_r (n m : nat) : my_mult n (S m) = n + my_mult n m.
Proof.
  unfold my_mult. simpl.
  rewrite iterate_assoc, my_plus_correct. reflexivity.
Qed.

Theorem my_mult_Sn_l (n m : nat) : my_mult (S n) m = m + my_mult n m.
Proof.
  generalize dependent n.
  induction m as [| m' IH]; intro n.
  - repeat rewrite my_mult_zero_r. reflexivity.
  - repeat rewrite my_mult_Sn_r. rewrite IH. ring.
Qed.

Theorem my_mult_correct (n m : nat) : my_mult n m = n * m.
Proof.
  induction n as [| n' IH].
  - now rewrite my_mult_zero_l.
  - rewrite my_mult_Sn_l, IH. reflexivity.
Qed.

Definition my_expt (n m : nat) : nat := iterate (my_mult n) m 1.

Theorem my_expt_zero_l (m : nat) : my_expt 0 (S m) = 0.
Proof.
  induction m as [| m' IH]; try reflexivity.
  unfold my_expt in *. simpl in *.
  repeat rewrite my_mult_correct in *. simpl in *.
  exact IH.
Qed.

Theorem my_expt_zero_r (n : nat) : my_expt n 0 = 1.
Proof. unfold my_expt. reflexivity. Qed.

Theorem my_expt_Sn_r (n m : nat) : my_expt n (S m) = n * my_expt n m.
Proof.
  unfold my_expt. simpl.
  rewrite iterate_assoc, my_mult_correct. reflexivity.
Qed.

Theorem my_expt_correct (n m : nat) : my_expt n m = n ^ m.
Proof.
  induction m as [| m' IH].
  - rewrite my_expt_zero_r. reflexivity.
  - rewrite my_expt_Sn_r, IH. reflexivity.
Qed.

Definition ackermann (m : nat) : nat -> nat
  := let g := fun (f : nat -> nat) (p : nat) => iterate f (S p) 1
     in iterate g m S.

Compute (ackermann 0 3). (* = 4 : nat *)

Theorem ack1 (n : nat) : ackermann 0 n = n + 1.
Proof. unfold ackermann. simpl. ring. Qed.

Theorem ack2 (m : nat) : ackermann (S m) 0 = ackermann m 1.
Proof. unfold ackermann. rewrite iterate_one. reflexivity. Qed.

Theorem ack3 (m n : nat)
  : ackermann (S m) (S n) = ackermann m (ackermann (S m) n).
Proof.
  unfold ackermann. rewrite iterate_one.
  simpl. rewrite iterate_assoc. reflexivity.
Qed.

(* Excercise 4.4
   For each of the following spécifications,
   check that its type has sort Type, then give some function
   which realizes this specification *)
Definition id : forall A : Set, A -> A := fun (A : Set) (a : A) => a.

Definition id' : forall A : Set, A -> A.
  intros A a. exact a.
Defined.

Print id'.
(* id' = fun (A : Set) (a : A) => a
       : forall A : Set, A -> A *)

Definition diag : forall A B : Set, (A -> A -> B) -> A -> B
  := fun (A B : Set) (f : A -> A -> B) (a : A)
     => f a a.

Definition diag' : forall A B : Set, (A -> A -> B) -> A -> B.
  intros A B f a. apply f; assumption.
Defined.

Print diag'.
(* diag' = [fun A B f a => f a a]
   fun (A B : Set) (f : A -> A -> B) (a : A) => f a a
   : forall A B : Set, (A -> A -> B) -> A -> B *)

Definition permute : forall A B C : Set, (A -> B -> C) -> B -> A -> C
  := fun (A B C : Set) (f : A -> B -> C) (b : B) (a : A)
     => f a b.

Definition permute' : forall A B C : Set, (A -> B -> C) -> B -> A -> C.
  intros A B C f b a. auto.
Defined.

Print permute'.
(* permute' = [fun (A B C) f b a => f a b]
   fun (A B C : Set) (f : A -> B -> C) (b : B) (a : A) => f a b
   : forall A B C : Set, (A -> B -> C) -> B -> A -> C *)

Definition f_nat_Z : forall A : Set, (nat -> A) -> Z -> A
  := fun (A : Set) (f : nat -> A) (z : Z) => f (Z.to_nat z).

Definition f_nat_Z' : forall A : Set, (nat -> A) -> Z -> A.
  intros A f z. auto using Z.to_nat.
Defined.

Print f_nat_Z'.
(* f_nat_Z' = [fun Z f z => f (Z.to_nat z)]
   fun (A : Set) (f : nat -> A) (z : Z) => f (Z.to_nat z)
   : forall A : Set, (nat -> A) -> Z -> A *)

(* Excercise 4.5
   Replace auto with basic tactics : intros, apply and assumption*)
Lemma all_perm : forall (A : Type) (P : A -> A -> Prop),
    (forall x y : A, P x y) -> forall x y : A, P y x.
Proof.
  intros A P H x y. apply H.
Qed.

Lemma resolution : forall (A : Type) (P Q R S : A -> Prop),
    (forall a : A, Q a -> R a -> S a)
    -> (forall b : A, P b -> Q b)
    -> forall c : A, P c -> R c -> S c.
Proof.
  intros A P Q R S H1 H2 c HPc HRc.
  (* apply H1; [apply H2 | idtac]; assumption. *)
  (* apply H1; try apply H2; assumption. *)
  apply H1; try assumption.
  apply H2. assumption.
Qed.

Theorem ThirtySix : 9 * 4 = 6 * 6.
Proof. exact (refl_equal 36). Qed.

Check eq_ind.
(* eq_ind : forall (A : Type) (x : A) (P : A -> Prop),
              P x -> forall y : A, x = y -> P y *)

Definition eq_sym (A : Type) (x y : A) (h : x = y) : y = x
  := eq_ind x (fun z => z = x) (refl_equal x) y h.

Check eq_sym.
(* eq_sym : forall (A : Type) (x y : A), x = y -> y = x *)

Check (eq_sym _ _ _ ThirtySix).
(* eq_sym nat (9 * 4) (6 * 6) ThirtySix
   : 6 * 6 = 9 * 4 *)

Check list : Type -> Type.
Check prod : Type -> Type -> Type.

Check (forall P : Prop, P -> P) : Prop.
Check (fun P : Prop => P -> P) : Prop -> Prop.

Check and : Prop -> Prop -> Prop.
Check (forall P Q : Prop, P /\ Q) : Prop.

Print not.
(* not = fun A : Prop => A -> False
   : Prop -> Prop *)

(* introduce 'and' and 'or' *)
Check conj.
(* conj : forall A B : Prop, A -> B -> A /\ B *)
Check (forall A B : Prop, A -> B -> A /\ B) : Prop.
Check or_introl.
(* or_introl : forall A B : Prop, A -> A \/ B *)
Check or_intror.
(* or_intror : forall A B : Prop, B -> A \/ B *)

(* eliminate 'and' and 'or' *)
Check and_ind.
(* and_ind : forall A B P : Prop, (A -> B -> P) -> A /\ B -> P *)

Theorem conj3 (P Q R : Prop) : P -> Q -> R -> P /\ Q /\ R.
Proof.
  exact (fun p q r => conj p (conj q r)).
Qed.

Theorem conj3' (P Q R : Prop) : P -> Q -> R -> P /\ Q /\ R.
Proof.
  intros p q r. repeat split; assumption.
Qed.
Print conj3'.
(* conj3' = [fun (P Q R) p q r => conj p (conj q r)]
   fun (P Q R : Prop) (p : P) (q : Q) (r : R) => conj p (conj q r)
   : forall P Q R : Prop, P -> Q -> R -> P /\ Q /\ R *)

Theorem disj4_3 (P Q R S : Prop) : R -> P \/ Q \/ R \/ S.
Proof.
  exact (fun r => or_intror _ (or_intror _ (or_introl _ r))).
Qed.

Unset Printing Notations.
Check (forall P Q R S : Prop, R -> P \/ Q \/ R \/ S).
(* forall (P Q R S : Prop) (_ : R), or P (or Q (or R S)) : Prop *)
Set Printing Notations.

Print Implicit or_introl.
(* or_introl : forall [A B : Prop], A -> A \/ B
   When applied to no more than 1 argument: Arguments A, B are implicit
   When applied to 2 arguments: Argument A is implicit *)

Print Implicit or_intror.
(* or_intror : forall [A B : Prop], B -> A \/ B
   When applied to no more than 1 argument: Arguments A, B are implicit
   When applied to 2 arguments: Argument B is implicit *)

Theorem disj4_3' (P Q R S : Prop) : R -> P \/ Q \/ R \/ S.
Proof.
  intro r. right. right. left. assumption.
Qed.
Print disj4_3'.
(* disj4_3' =
   fun (P Q R S : Prop) (r : R) => or_intror (or_intror (or_introl r))
   : forall P Q R S : Prop, R -> P \/ Q \/ R \/ S *)

Theorem disj3_3 (P Q R : Prop) : R -> P \/ Q \/ R.
Proof.
  exact (fun r => or_intror _ (or_intror (A := Q) (B := R) r)).
Qed.

Theorem disj3_3' (P Q R : Prop) : R -> P \/ Q \/ R.
Proof.
  intro r. right. right. assumption.
Qed.
Print disj3_3'.
(* disj3_3' =
   fun (P Q R : Prop) (r : R) => or_intror (or_intror r)
   : forall P Q R : Prop, R -> P \/ Q \/ R *)

Theorem disj3_3'' (P Q R : Prop) : R -> P \/ Q \/ R.
Proof.
  exact (fun r => or_intror P (B := Q \/ R)
                            (or_intror Q (B := R) r)).
Qed.

Theorem disj3_3''' (P Q R : Prop) : R -> P \/ Q \/ R.
Proof.
  exact (fun r => or_intror P (or_intror Q r)).
Qed.

Theorem disj4_3'' (P Q R S : Prop) : R -> P \/ Q \/ R \/ S.
Proof.
  exact (fun r => or_intror P (or_intror Q (or_introl S r))).
Qed.

Print Implicit and_ind.
(* and_ind : forall [A B P : Prop], (A -> B -> P) -> A /\ B -> P
   Arguments A, B, P are implicit *)

Theorem proj1' (A B : Prop) : A /\ B -> A.
Proof.
  exact (fun H => and_ind (fun a b => a) H).
Qed.

Theorem proj1'' (A B : Prop) : A /\ B -> A.
Proof. intros [a b]. exact a. Qed.
Print proj1''.
(* proj1'' =
   fun (A B : Prop) (H : A /\ B) => match H with
   | conj a _ => a
   end
   : forall A B : Prop, A /\ B -> A *)

Check ex.
(* ex : forall A : Type, (A -> Prop) -> Prop *)
Check ex_intro.
(* ex_intro : forall (A : Type) (P : A -> Prop) (x : A),
                P x -> exists y, P y *)

Locate "exists".
(* Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
   : type_scope (default interpretation) *)

(* So [exists y, P y] is [ex (fun y => P y)] *)
(* ex_intro : forall (A : Type) (P : A -> Prop) (x : A),
                P x -> ex (fun y => P y) *)

Check (exists z : Z, z*z <= 37 < (z + 1)*(z + 1))%Z : Prop.

Check ex_ind.
(* ex_ind
   : forall (A : Type) (P : A -> Prop) (P0 : Prop),
   (forall x : A, P x -> P0) -> (exists y, P y) -> P0 *)

Require Import List.

Check (list Z -> nat).
(* list Z -> nat : Set *)

Unset Printing Notations.
Check (list Z -> nat).
(* forall _ : list Z, nat : Set *)
Set Printing Notations.

Check (cons Z.abs_nat nil) : list (Z -> nat).
