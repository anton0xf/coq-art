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
   : forall n : nat, 7 * 5 < n -> 6 * 6 <= n *)

Definition neutral_left (A : Set) (op : A -> A -> A) (e : A) : Prop
  := forall x : A, op e x = x.

Theorem one_neutral_left : neutral_left Z Zmult 1%Z.
Proof. intro z. apply Z.mul_1_l. Qed.

Lemma le_i_SSi : forall i : nat, i <= S (S i).
Proof. intro i. apply le_S, le_S, le_n. Qed.

Lemma all_imp_dist : forall (A : Type) (P Q : A -> Prop),
    (forall x : A, P x -> Q x)
    -> (forall y : A, P y) -> forall z : A, Q z.
Proof. intros A P Q H Hp z. apply H, Hp. Qed.

Check le_trans.
(* Nat.le_trans : forall n m p : nat, n <= m -> m <= p -> n <= p *)

Check mult_le_compat_l.
(* mult_le_compat_l : forall n m p : nat,
                        n <= m -> p * n <= p * m *)

Theorem mult_le_compat_r (m n p : nat) : n <= p -> n * m <= p * m.
Proof.
  intro H. rewrite (mult_comm n m). rewrite (mult_comm p m).
  apply mult_le_compat_l. assumption.
Qed.


Theorem le_mult_mult (n m p q : nat)
  : n <= m -> p <= q -> n * p <= m * q.
Proof.
  intros H1 H2.
  (* apply le_trans with (m := (m * p)). *)
  apply (le_trans _ (m * p)).
  - apply mult_le_compat_r, H1.
  - apply mult_le_compat_l, H2.
Qed.

Theorem le_mult_mult' (n m p q : nat)
  : n <= m -> p <= q -> n * p <= m * q.
Proof.
  intros H1 H2. eapply le_trans.
  - apply mult_le_compat_r. exact H1.
  - apply mult_le_compat_l, H2.
Qed.

Lemma le_O_mult (n p : nat) : 0 * n <= 0 * p.
Proof. apply le_n. Qed.

Lemma le_O_mult_R (n p : nat) : n * 0 <= p * 0.
Proof.
  (* apply le_n. (* => Unable to unify "p * 0" with "n * 0". *) *)
  repeat rewrite (mult_comm _ 0). apply le_n.
Qed.

Lemma lt_8_9 : 8 < 9.
Proof.
  (* unfold lt; apply le_n. *)
  apply le_n.
Qed.

SearchPattern (_ + _ <= _)%Z.
SearchPattern (?X1 * _ <= ?X1 * _)%Z.

Lemma lt_S (n p : nat) : n < p -> n < S p.
Proof. unfold lt. intro H. apply le_S, H. Qed.

Definition opaque_f : nat -> nat -> nat.
  intros. assumption.
Qed.

Lemma bad_proof_example_for_opaque (x y : nat) : opaque_f x y = y.
Proof.
  intros.
  (* unfold opaque_f. (* Error: opaque_f is opaque. *) *)
Abort.

Open Scope Z_scope.

Definition Zsquare_diff (x y : Z):= x * x - y * y.

Theorem unfold_example (x y : Z)
   : x*x = y*y
     -> Zsquare_diff x y * Zsquare_diff (x+y) (x*y) = 0.
Proof.
 intros H. unfold Zsquare_diff at 1.
 rewrite H. ring.
Qed.

(* 5.2 Logical Connectives *)
Check conj.
(* conj : forall A B : Prop, A -> B -> A /\ B *)

Print and.
(* Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B *)

Check and_ind.
(* and_ind : forall A B P : Prop, (A -> B -> P) -> A /\ B -> P *)

Print or.
(* Inductive or (A B : Prop) : Prop
   := or_introl : A -> A \/ B | or_intror : B -> A \/ B *)

Check or_ind.
(* or_ind : forall A B P : Prop,
   (A -> P) -> (B -> P) -> A \/ B -> P *)

Open Scope nat_scope.
Print nat.
(* Inductive nat : Set :=  O : nat | S : nat -> nat *)

Check nat_ind.
(* nat_ind : forall P : nat -> Prop,
   P 0 -> (forall n : nat, P n -> P (S n))
   -> forall n : nat, P n *)

Check False_ind.
(* False_ind : forall P : Prop, False -> P *)

Section ex_falso_quodlibet.
  Hypothesis ff : False.

  Lemma ex1 : 220 = 284.
  Proof using ff. apply False_ind. exact ff. Qed.

  Lemma ex2 : 220 = 284.
  Proof using ff. destruct ff. Qed.
End ex_falso_quodlibet.
Print ex2.
(* ex2 =
   fun ff : False
     => let f : False := ff
        in match f return (220 = 284) with
        end
   : False -> 220 = 284 *)

Theorem absurd : forall P Q : Prop, P -> ~P -> Q.
Proof.
  intros P Q p np. elim np. assumption.
Qed.

Theorem double_neg_i : forall P : Prop, P -> ~~P.
Proof.
  intros P p np. apply np, p.
Qed.

Theorem modus_ponens (P Q : Prop) : P -> (P -> Q) -> Q.
Proof.
  intros p pq. apply pq, p.
Qed.

Theorem double_neg_i' : forall P : Prop, P -> ~~P.
Proof.
  intros P p np.
  (* apply (modus_ponens P False p np). *)
  apply (modus_ponens P False); assumption.
Qed.

(* Exercise 5.3
   Prove the following statements: *)

(** Instance of identity on propositions *)
Theorem not_False : ~ False.
Proof. intro f. exact f. Qed.

Definition not_False' : ~ False
  := fun H => H.

Theorem triple_neg (P : Prop): ~~~P -> ~P.
Proof. intros tnp p. apply tnp, double_neg_i, p. Qed.

Theorem P3PQ (P Q : Prop): ~~~P -> P -> Q.
Proof.
  intros tnp p. apply triple_neg in tnp.
  apply (absurd P Q); assumption.
Qed.

(** instance of the transivity of -> *)
Theorem contrap (P Q : Prop) : (P -> Q) -> ~Q -> ~P.
Proof. intros pq nq p. apply nq, pq, p. Qed.

Theorem imp_absurd (P Q R : Prop) : (P -> Q) -> (P -> ~Q) -> P -> R.
Proof.
  intros pq pnq p.
  apply (absurd Q R); [apply pq | apply pnq]; exact p.
Qed.

(* Exercise 5.4
   Usual reasoning errors rely on pseudo inference rules that can
   lead to contradictions. These rules are often the result of some sort of dyslexia.
   Here are two examples: implication dyslexia (confusion between P -> Q and
   Q -> P) and dyslexic contraposition: *)

Definition dyslexic_imp := forall P Q : Prop, (P -> Q) -> Q -> P.

Definition dyslexic_contrap := forall P Q:Prop, (P -> Q) -> ~P -> ~Q.

Theorem dyslexic_imp_false : dyslexic_imp -> False.
Proof.
  unfold dyslexic_imp. intros H. apply (H False True).
  - apply False_ind.
  - apply I.
Qed.

Theorem dyslexic_contrap_false : dyslexic_contrap -> False.
Proof.
  unfold dyslexic_contrap. intros H. apply (H False True).
  - apply False_ind.
  - intro f. exact f.
  - exact I.
Qed.

(* *** *)

Lemma and_commutes (A B : Prop) : A /\ B -> B /\ A.
Proof.
  intro H. elim H. split; assumption.
Qed.

Lemma and_commutes' (A B : Prop) : A /\ B -> B /\ A.
Proof.
  intros [a b]. apply (conj b a).
Qed.

Lemma or_commutes (A B : Prop) : A \/ B -> B \/ A.
Proof.
  intro H. elim H; auto.
Qed.

Lemma or_commutes' (A B : Prop) : A \/ B -> B \/ A.
Proof.
  intros [a | b]; [ right | left ]; assumption.
Qed.


