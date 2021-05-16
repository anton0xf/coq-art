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

End Minimal_propositional_logic.

