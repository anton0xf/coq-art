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

  Theorem imp_dist' : (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof using.
    intros. apply H.
    - exact H1.
    - exact (H0 H1).
  Qed.

  Section section_for_cut_example.
    Hypotheses (H : P -> Q)
               (H0 : Q -> R)
               (H1 : (P -> R) -> T -> Q)
               (H2 : (P -> R) -> T).

    Theorem cut_example : Q.
    Proof using H H0 H1 H2.
      cut (P -> R).
      - intro H3. apply H1; [idtac | apply H2]; assumption.
      - intro Hp. apply H0, H, Hp.
    Qed.

    Print cut_example.
    (* cut_example =
       let H3 : P -> R := fun Hp : P => H0 (H Hp)
       in (fun H4 : P -> R => H1 H4 (H2 H4)) H3
       : Q *)

    Theorem cut_example' : Q.
    Proof using H H0 H1 H2.
      assert (P -> R) as H3.
      { intro Hp. apply H0, H, Hp. }
      apply H1; [idtac | apply H2]; assumption.
    Qed.

    Print cut_example'.
    (* cut_example' =
       let H3 : P -> R := fun Hp : P => H0 (H Hp)
       in H1 H3 (H2 H3)
       : Q *)

    Theorem cut_example0 : Q.
    Proof using H H0 H1 H2.
      apply H1.
      - intro Hp. apply H0, H, Hp.
      - apply H2.
        intro Hp. apply H0, H, Hp.
    Qed.

    Print cut_example0.
    (* cut_example0 =
       H1 (fun Hp : P => H0 (H Hp)) (H2 (fun Hp : P => H0 (H Hp)))
       : Q *)
  End section_for_cut_example.

  Theorem triple_impl' : (((P -> Q) -> Q) -> Q) -> P -> Q.
  Proof using. auto. Qed.

  Theorem auto1 : (P -> Q) -> P -> Q.
  Proof using. auto 0. auto 1. Qed.

  Print auto1.
  (* auto1 = fun H : P -> Q => H
           : (P -> Q) -> P -> Q *)

  Theorem auto2 : ((Q -> P) -> Q) -> P -> Q.
  Proof using. auto 1. auto 2. Qed.

  Print auto2.
  (* auto2 = fun (H : (Q -> P) -> Q) (H0 : P) => H (fun _ : Q => H0)
           : ((Q -> P) -> Q) -> P -> Q *)

  Theorem auto_t2 : P -> (P -> Q) -> Q.
  Proof using. auto 1. auto 2. Qed.

  Theorem auto3 : (((P -> Q) -> Q) -> Q) -> P -> Q.
  Proof using. auto 2. auto 3. Qed.

  Print auto3.
  (* auto3 = [fun H H0 => H (fun H1 => H1 H0)]
     fun (H : ((P -> Q) -> Q) -> Q) (H0 : P) => H (fun H1 : P -> Q => H1 H0)
     : (((P -> Q) -> Q) -> Q) -> P -> Q *)

  Theorem auto3' : ((((Q -> P) -> Q) -> Q) -> Q) -> P -> Q.
  Proof using. auto 2. auto 3. Qed.

  Print auto3'.
  (* auto3' = [fun H H0 => H (fun H1 => H1 (fun _ => H0))]
     fun (H : (((Q -> P) -> Q) -> Q) -> Q) (H0 : P)
         => H (fun H1 : (Q -> P) -> Q => H1 (fun _ : Q => H0))
     : ((((Q -> P) -> Q) -> Q) -> Q) -> P -> Q *)

  Theorem auto_t3 : P -> (P -> Q) -> (Q -> R) -> R.
  Proof using. auto 2. auto 3. Qed.

  Theorem auto4 : (((((P -> Q) -> Q) -> Q) -> Q) -> Q) -> P -> Q.
  Proof using. auto 3. auto 4. Qed.

  Theorem auto4' : ((((((Q -> P) -> Q) -> Q) -> Q) -> Q) -> Q) -> P -> Q.
  Proof using. auto 3. auto 4. Qed.

  Theorem auto_t4 : P -> (P -> Q) -> (Q -> R) -> (R -> T) -> T.
  Proof using. auto 3. auto 4. Qed.

  Theorem auto5 : (((((((P -> Q) -> Q) -> Q) -> Q) -> Q) -> Q) -> Q)
                  -> P -> Q.
  Proof using. auto 4. auto 5. Qed.

  Variables S U : Prop.

  Theorem auto_t5 : P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> S) -> S.
  Proof using. auto 4. auto 5. Qed.

  Theorem auto6 : (((((((((P -> Q) -> Q) -> Q) -> Q) -> Q)
                      -> Q) -> Q) -> Q) -> Q)
                  -> P -> Q.
  Proof using. auto 5. auto 6. Qed.

  Theorem auto_t6 : P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> S)
                    -> (S -> U) -> U.
  Proof using. auto 5. auto 6. Qed.
End Minimal_propositional_logic.

Print imp_dist.
(* imp_dist =
   fun (P Q R : Prop) (H : P -> Q -> R) (H' : P -> Q) (p : P) => H p (H' p)
   : forall P Q R : Prop, (P -> Q -> R) -> (P -> Q) -> P -> R *)

Section using_imp_dist.
  Variables (P1 P2 P3 : Prop).
  Check (imp_dist P1 P2 P3).
  (* imp_dist P1 P2 P3
     : (P1 -> P2 -> P3) -> (P1 -> P2) -> P1 -> P3 *)

  Check (imp_dist (P1 -> P2) (P2 -> P3) (P3 -> P1)).
  (* imp_dist (P1 -> P2) (P2 -> P3) (P3 -> P1)
     : ((P1 -> P2) -> (P2 -> P3) -> P3 -> P1) ->
       ((P1 -> P2) -> P2 -> P3) -> (P1 -> P2) -> P3 -> P1 *)
End using_imp_dist.
