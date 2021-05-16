Section simple_proofs.
  Variables P Q R S : Prop.

  Lemma id_P : P -> P.
  Proof using. intro H. exact H. Qed.

  Lemma id_PP : (P -> P) -> P -> P.
  Proof using. intros H Hp. exact Hp. Qed.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof using. intros H1 H2 Hp. apply H2, H1, Hp. Qed.

  Lemma imp_perm : (P -> Q -> R) -> Q -> P -> R.
  Proof using. intros H Hq Hp. apply H; assumption. Qed.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Proof using. intros H Hp Hq. apply H, Hp. Qed.

  Lemma delta_imp : (P -> P -> Q) -> P -> Q.
  Proof using. intros H Hp. apply H; assumption. Qed.

  Lemma delta_impR : (P -> Q) -> P -> P -> Q.
  Proof using. intros H Hp _. apply H, Hp. Qed.

  Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
  Proof using.
    intros H1 H2 H3 Hp. apply H3.
    - apply H1, Hp.
    - apply H2, Hp.
  Qed.

  Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof using.
    intro H1. apply H1.
    intro H2. apply H2.
    intro Hp. apply H1.
    intros _. exact Hp.
  Qed.

End simple_proofs.
