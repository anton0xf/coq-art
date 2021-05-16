Theorem t1 (P Q R : Prop) : (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros H1 H2 H. apply H2, H1, H.
Qed.

Print t1.
(* t1 = fun (P Q R : Prop)
   (H1 : P -> Q) (H2 : Q -> R) (H : P) => H2 (H1 H)
   : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R *)

Theorem t2 (P Q R : Prop) : (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  exact (fun f g p => g (f p)).
Qed.

Print t2.
(* t2 = fun (P Q R : Prop)
   (f : P -> Q) (g : Q -> R) (p : P) => g (f p)
   : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R *)

Definition ex_middle := forall P : Prop, P \/ ~P.
Definition pierce_law := forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition pierce_law' := forall P : Prop, ((P -> False) -> P) -> P.

Theorem ex_middle_impl_pierce_law : ex_middle -> pierce_law'.
Proof.
  unfold ex_middle, pierce_law'. intros E P H.
  pose (E P) as Hp. destruct Hp as [Hp | Hnp]; try assumption.
  apply H. intro Hp. contradiction.
Qed.

Theorem pierce : pierce_law <-> pierce_law'.
Proof.
  unfold pierce_law, pierce_law'.
  split; intro L.
  - intro P. apply (L P False).
  - intros P Q H. apply L. intro Hnp.
    apply H. intro Hp.
    contradiction. (* apply Hnp in Hp. destruct Hp. *)
Qed.

Print pierce.
(* pierce = conj
   (fun (L : forall P Q : Prop, ((P -> Q) -> P) -> P) (P : Prop) => L P False)
   (fun (L : forall P : Prop, ((P -> False) -> P) -> P)
     (P Q : Prop) (H : (P -> Q) -> P) =>
       L P (fun Hnp : P -> False => H (fun Hp : P => False_ind Q (Hnp Hp))))
     : pierce_law <-> pierce_law' *)

Theorem pierce' : pierce_law' -> pierce_law.
Proof.
  unfold pierce_law, pierce_law'. intro L.
  intros P Q H. apply L. intro Hnp.
  apply H. intro Hp.
  apply Hnp in Hp. destruct Hp.
Qed.

Print pierce'.
(* pierce' =
   fun (L : forall P : Prop, ((P -> False) -> P) -> P)
     (P Q : Prop) (H : (P -> Q) -> P) =>
       L P (fun Hnp : P -> False =>
         H (fun Hp : P => let Hp0 : False := Hnp Hp
           in match Hp0 return Q with end))
   : pierce_law' -> pierce_law *)

Section Minimal_propositional_logic.
  Variables P Q R T : Prop.

  Theorem imp_trans : (P -> Q) -> (Q -> R) -> (P -> R).
  Proof using. intros H H' p. apply H', H, p. Qed.

  Print imp_trans.
  (* imp_trans = [fun (f g p) => g (f p)]
     fun (H : P -> Q) (H' : Q -> R) (p : P) => H' (H p)
     : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R *)

  Theorem imp_trans' : (P -> Q) -> (Q -> R) -> (P -> R).
  Proof using. auto. Qed.

  Check Q. (* Q : Prop *)
  Check (P -> Q) -> (Q -> R) -> (P -> R).
  (*    (P -> Q) -> (Q -> R) -> P -> R : Prop *)


  Section example_of_assumption.
    Hypothesis H : P -> Q -> R.
    Lemma L1 : P -> Q -> R.
    Proof using H. assumption. Qed.
  End example_of_assumption.

  Theorem delta : (P -> P -> Q) -> P -> Q.
  Proof using. exact (fun f p => f p p). Qed.

  Theorem apply_example: (Q -> R -> T) -> (P -> Q) -> P -> R -> T.
  Proof using.
    intros H H0 p. apply H, H0, p.
  Qed.

  Theorem imp_dist : (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof using.
    intros H H' p. apply H.
    - exact p.
    - exact (H' p).
  Qed.

  Print imp_dist.
  (* imp_dist = [fun f g x => f x (g x)]
     fun (H : P -> Q -> R) (H' : P -> Q) (p : P) => H p (H' p)
     : (P -> Q -> R) -> (P -> Q) -> P -> R *)

  Theorem K : P -> Q -> P.
  Proof using. intros p q. assumption. Qed.

  Print K. (* K = [fun p q => p]
                  fun (p : P) (_ : Q) => p
                : P -> Q -> P *)

  Definition f : (nat -> bool) -> (nat -> bool) -> nat -> bool.
    intros f1 f2. assumption.
  Defined.

  Print f.
  (* f = [fun f1 f2 => f2]
       fun _ f2 : nat -> bool => f2
     : (nat -> bool) -> (nat -> bool) -> nat -> bool *)

  Eval compute in (f (fun n => true) (fun n => false) 45).
  (* = false : bool *)

  Opaque f.

  Eval compute in (f (fun n => true) (fun n => false) 45).
  (* = f (fun _ : nat => true) (fun _ : nat => false) 45 : bool *)

  Section proof_of_triple_impl.
    Hypothesis H : ((P -> Q) -> Q) -> Q.
    Hypothesis p : P.

    Lemma Rem: (P -> Q) -> Q.
    Proof using p.
      exact (fun H0 : P -> Q => H0 p).
    Qed.

    Theorem triple_impl : Q.
    Proof using H p. exact (H Rem). Qed.
  End proof_of_triple_impl.

  Print triple_impl.
  (* triple_impl = [fun H p => H (Rem p)]
     fun (H : ((P -> Q) -> Q) -> Q) (p : P) => H (Rem p)
     : (((P -> Q) -> Q) -> Q) -> P -> Q *)

  Print Rem.
  (* Rem = fun (p : P) (H0 : P -> Q) => H0 p
         : P -> (P -> Q) -> Q *)

  Theorem then_example : P -> Q -> (P -> Q -> R) -> R.
  Proof using.
    intros p q H.
    apply H; assumption.
  Qed.

  Theorem triple_impl_one_shot : (((P -> Q) -> Q) -> Q) -> P -> Q.
  Proof using.
    intros H p; apply H; intro H0; apply H0; assumption.
  Qed.

  Theorem compose_example : (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof using.
    intros H H' p.
    apply H; [exact p | exact (H' p)].
  Qed.

  Theorem compose_example' : (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof using.
    intros H H' p.
    apply H; try apply H'; assumption.
  Qed.

  Theorem orelse_example
    : (P -> Q) -> R -> ((P -> Q) -> R -> (T -> Q) -> T) -> T.
  Proof.
    intros H r H0. apply H0; (assumption || intro H1).
  Abort.

  Lemma L3 : (P -> Q) -> (P -> R) -> (P -> Q -> R -> T) -> P -> T.
  Proof using.
    intros H H0 H1 p.
    apply H1; [idtac | apply H | apply H0]; assumption.
  Qed.

  Theorem then_fail_example : (P -> Q) -> (P -> Q).
  Proof using.
    intro X; apply X; fail.
  Qed.

  Theorem then_fail_example2 : ((P -> P) -> (Q -> Q) -> R) -> R.
  Proof using.
    (* intro X; apply X; fail. *)
  Abort.

  Theorem try_example : (P -> Q -> R -> T) -> (P -> Q) -> (P -> R -> T).
  Proof using.
    intros H H' p r.
    apply H; try assumption. apply H', p.
  Qed.

End Minimal_propositional_logic.

