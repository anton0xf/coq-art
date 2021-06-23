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


(* Exercise 5.5
   Prove the following theorem : *)
Theorem abcd_c (A : Set) (a b c d : A) : a=c \/ b=c \/ c=c \/ d=c.
Proof.
  right. right. left. apply (eq_refl c).
Qed.

(* Exercise 5.6
   Prove the following theorems: *)

Lemma and_assoc (A B C : Prop) : A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
 intros [a [b c]]; repeat split; assumption.
Qed.

Lemma and_imp_dist (A B C D : Prop)
  : (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
  intros [ab cd] [a c].
  split; [ exact (ab a) | exact (cd c) ].
Qed.

Lemma not_contrad (A : Prop) : ~(A /\ ~A).
Proof.
  intros [a na]. apply na, a.
Qed.

Lemma or_and_not (A B : Prop) : (A \/ B) /\ ~A -> B.
Proof.
  intros [[a | b] na];
    [ apply (absurd A B) | idtac ]; assumption.
Qed.

Lemma or_and_not' (A B : Prop) : (A \/ B) /\ ~A -> B.
Proof.
  intros [[a | b] na]; [ contradiction | assumption ].
Qed.

(* Exercise 5.7 *
   Here are five statements that are often considered
   as characterizations of classical logic.
   Prove that these five propositions are equivalent. *)
Definition peirce := forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition classic := forall P : Prop, ~~P -> P.
Definition excluded_middle := forall P : Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q : Prop, (P -> Q) -> (~P \/ Q).

Definition impl_excluded_middle := forall P : Prop, (~P -> P) -> P.

Theorem ExM_impl_Cl : excluded_middle -> classic.
Proof.
  unfold excluded_middle, classic. intros E P nnp.
  destruct (E P) as [p | np]; [assumption | contradiction].
Qed.

Theorem ExM_impl_ImplToOr : excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle, implies_to_or.
  intros E P Q H. destruct (E P) as [p | np].
  - right. apply H, p.
  - left. exact np.
Qed.

Lemma Cl_iff : classic -> forall P : Prop, P <-> ~~P.
Proof.
  intros Cl P. split; [apply double_neg_i | apply Cl].
Qed.

Lemma ImplToOr_iff : implies_to_or -> forall P Q : Prop,
      (P -> Q) <-> (~P \/ Q).
Proof.
  intros I P Q. split.
  - apply I.
  - intros [np | q] p; [contradiction | assumption].
Qed.

Lemma OrToImpl (P Q : Prop) : ~P \/ Q -> P -> Q.
Proof. intros [np | q] p; [contradiction | assumption]. Qed.

Lemma de_morgan_or (A B : Prop) : ~(A \/ B) <-> ~A /\ ~B.
Proof.
  split.
  - intro H.
    split; intro H1; apply H;
      [ left | right ]; assumption.
  - intros [na nb] [a | b]; contradiction.
Qed.

Lemma triple_neg_iff (P : Prop): ~P <-> ~~~P.
Proof. split; [apply double_neg_i | apply triple_neg]. Qed.

Theorem ExM_impl_DMnan : excluded_middle -> de_morgan_not_and_not.
Proof.
  intros E P Q H. destruct (E P) as [p | np].
  - left. assumption.
  - destruct (E Q) as [q | nq].
    + right. assumption.
    + contradiction H. split; assumption.
Qed.

Theorem DMnan_impl_ExM : de_morgan_not_and_not -> excluded_middle.
Proof.
  intros DM P. apply (DM P (~P)).
  intros [np nnp]. contradiction.
Qed.

Lemma double_and (P : Prop) : P <-> P /\ P.
Proof.
  split; intro H.
  - split; assumption.
  - destruct H as [H _]. assumption.
Qed.

Lemma double_or (P : Prop) : P <-> P \/ P.
Proof.
  split; intro H.
  - left. assumption.
  - destruct H as [H | H]; assumption.
Qed.

Theorem DMnan_impl_Cl : de_morgan_not_and_not -> classic.
Proof.
  intros DM P. pose (DM P P) as H.
  rewrite <- double_and, <- double_or in H.
  assumption.
Qed.

Theorem ExM_impl_Peirce : excluded_middle -> peirce.
Proof.
  intros EM P Q H. pose (ExM_impl_ImplToOr EM) as I.
  rewrite (ImplToOr_iff I) in H.
  destruct H as [H | H]; try assumption.
  rewrite (ImplToOr_iff I) in H. rewrite de_morgan_or in H.
  destruct H as [nnp nq].
  apply (ExM_impl_Cl EM). assumption.
Qed.

Lemma contrap_inv : classic -> forall P Q : Prop, (~P -> ~Q) -> Q -> P.
Proof.
  intros Cl P Q H. rewrite (Cl_iff Cl Q), (Cl_iff Cl P).
  apply contrap, H.
Qed.

Theorem Cl_impl_ImplToOr : classic -> implies_to_or.
Proof.
  intros Cl P Q. apply (contrap_inv Cl).
  intros H H1. apply de_morgan_or in H.
  destruct H as [p nq].
  apply  nq, H1, Cl, p.
Qed.

Theorem ImplToOr_impl_ExM : implies_to_or -> excluded_middle.
Proof.
  intros I P. apply or_commutes. apply (I P P).
  intro p. assumption.
Qed.

Theorem ImplExM_impl_ExM : impl_excluded_middle -> excluded_middle.
Proof.
  intros IE P. apply (IE (P \/ ~P)).
  intros H. apply de_morgan_or in H.
  destruct H as [np p]. contradiction.
Qed.

Theorem Peirce_impl_ImplExM : peirce -> impl_excluded_middle.
Proof. intros Pr P. apply (Pr P False). Qed.

(* 5.2.6 Existential Quantification *)

Lemma ex_imp_ex (A : Type) (P Q : A -> Prop)
  : (ex P) -> (forall x : A, P x -> Q x) -> (ex Q).
Proof.
  intros H H0. destruct H as [a Ha].
  exists a. apply H0. assumption.
Qed.

(* Exercise 5.9
   In a context where [A : Set] and [P, Q : A -> Prop] are declared,
   prove the following statements: *)

Section on_ex.
  Variables (A : Type)
            (P Q : A -> Prop).

  Lemma ex_or : (exists x : A, P x \/ Q x) -> ex P \/ ex Q.
  Proof using.
    intros [x [px | qx]]; [left | right]; exists x; assumption.
  Qed.

 Lemma ex_or_R : ex P \/ ex Q -> (exists x : A, P x \/ Q x).
 Proof using.
   intros [[x px] | [x qx]]; exists x; [left | right]; assumption.
 Qed.

 Lemma two_is_three : (exists x : A, forall R : A -> Prop, R x) -> 2 = 3.
 Proof using.
   intros [x H]. apply (H (fun _ => 2 = 3)).
 Qed.

 Lemma forall_no_ex : (forall x : A, P x) -> ~(exists y : A, ~ P y).
 Proof using. intros H [y npy]. apply npy, (H y). Qed.

End on_ex.

(* 5.3 Equality and Rewriting *)

Lemma L36 : 6 * 6 = 9 * 4.
Proof. reflexivity. Qed.

Print L36. (* L36 = eq_refl : 6 * 6 = 9 * 4 *)

Lemma diff_of_squares (a b : Z) : ((a + b) * (a - b) = a * a - b * b)%Z.
Proof.
  (* reflexivity. *)
  (* Error: In environment a, b : Z
     Unable to unify "(a * a - b * b)%Z" with "((a + b) * (a - b))%Z". *)
  ring. (* auto with zarith. *)
Qed.

Theorem eq_sym' (A : Type) (a b : A) : a = b -> b = a.
Proof.
  intros e. rewrite e. reflexivity.
Qed.

Theorem eq_sym'' (A : Type) (a b : A) : a = b -> b = a.
Proof.
  intros e. destruct e. apply eq_refl.
Qed.

Open Scope Z_scope.

Lemma Zmult_distr1 (n x : Z) : n*x + x = (n + 1) * x.
Proof.
 rewrite Zmult_plus_distr_l.
 now rewrite Zmult_1_l.
Qed.

Lemma regroup (x : Z) : x + x + x + x + x = 5 * x.
Proof.
  pattern x at 1.
  rewrite <- Zmult_1_l.
  repeat rewrite Zmult_distr1.
  reflexivity.
Qed.

(* Exercise 5.10 Prove the following statement: *)
Open Scope nat_scope.
Theorem plus_permute2 (n m p : nat) : n + m + p = n + p + m.
Proof.
  rewrite <- plus_assoc.
  pattern (m + p). rewrite plus_comm.
  now rewrite plus_assoc.
Qed.

(* 5.3.4 * Conditional Rewriting *)
Theorem le_lt_S_eq (n p : nat) : n <= p -> p < S n -> n = p.
Proof. omega. Qed.

Theorem le_lt_S_eq' (n p : nat) : n <= p -> p < S n -> n = p.
Proof.
  generalize dependent p.
  induction n as [| n' IH]; intros p H1 H2.
  - unfold lt in H2. apply le_S_n in H2.
    apply Nat.le_antisymm; assumption.
  - destruct p as [| p'].
    + contradict H1. apply Nat.nle_succ_0.
    + apply eq_S. apply le_S_n in H1. apply lt_S_n in H2.
      apply IH; assumption.
Qed.

Lemma conditional_rewrite_example (n : nat)
  : 8 <= n + 6 -> 3 + n < 6 -> n * n = n + n.
Proof.
  intros H H0.
  rewrite <- (le_lt_S_eq 2 n).
  - reflexivity.
  - apply Nat.add_le_mono_r with (p := 6). assumption.
  - apply plus_lt_reg_l with (p:= 3). assumption.
Qed.

(** A shorter proof ... *)
Require Import Lia.
Lemma conditional_rewrite_example' (n : nat)
  : 8 <= n + 6 -> 3 + n < 6 -> n * n = n + n.
Proof.
  intros H H0. assert (n = 2) by lia. now subst n.
Qed.

(* Exercise 5.11
   Prove the following theorem, first by a direct use of eq_ind,
   then with the rewri t e tactic: *)
Theorem eq_trans (A : Type) (a b c : A) : a = b -> b = c -> a = c.
Proof.
  intros H1 H2.
  apply eq_ind with (P := fun t => a = t) (x := b); assumption.
Qed.

Theorem eq_trans' (A : Type) (a b c : A) : a = b -> b = c -> a = c.
Proof. intros H1 H2. rewrite H1, H2. reflexivity. Qed.

(* 5.5 *** Impredicative Definitions *)

Definition my_True : Prop
  := forall P : Prop, P -> P.

Definition my_False : Prop
  := forall P : Prop, P.

Theorem my_I : my_True.
Proof. intros P p. assumption. Qed.

Theorem my_False_ind (P : Prop) : my_False -> P.
Proof. intro F. apply F. Qed.

(* Exercise 5.12
   Construct manually the proof terms that are used as values
   of the constants my_I and my_False_ind. *)
Theorem my_I' : my_True.
Proof. exact (fun P p => p). Qed.

Theorem my_False_ind' (P : Prop) : my_False -> P.
Proof. exact (fun F => (F P)). Qed.

(* Exercise 5.13 *
   It is possible to define negation on top of our notion of falsehood: *)
Definition my_not (P : Prop) : Prop := P -> my_False.

(* Redo Exercise 5.3 using my_False and my_not instead of False and not. *)

(** Instance of identity on propositions *)
Theorem not_my_False : my_not my_False.
Proof. intro f. exact f. Qed.

Definition not_my_False' : my_not my_False
  := fun H => H.

Theorem double_my_neg_i (P : Prop) : P -> my_not (my_not P).
Proof. intros p np. apply np, p. Qed.

Theorem triple_my_neg (P : Prop): my_not (my_not (my_not P)) -> my_not P.
Proof. intros tnp p. apply tnp, double_my_neg_i, p. Qed.

Theorem my_absurd (P Q : Prop) : P -> my_not P -> Q.
Proof. intros p np. apply my_False_ind, np, p. Qed.

Theorem my_P3PQ (P Q : Prop): my_not (my_not (my_not P)) -> P -> Q.
Proof.
  intros tnp p. apply triple_my_neg in tnp.
  apply (my_absurd P Q); assumption.
Qed.

(** instance of the transivity of -> *)
Theorem my_contrap (P Q : Prop) : (P -> Q) -> my_not Q -> my_not P.
Proof. intros pq nq p. apply nq, pq, p. Qed.

Theorem imp_my_absurd (P Q R : Prop) : (P -> Q) -> (P -> my_not Q) -> P -> R.
Proof.
  intros pq pnq p.
  apply (my_absurd Q R); [apply pq | apply pnq]; exact p.
Qed.
