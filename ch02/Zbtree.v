Require Import Bool ZArith.

Inductive Zbtree : Type
  := leaf
   | bnode (r : Z) (t1 t2 : Zbtree).

Definition is_leaf (t : Zbtree) : bool
  := match t with
     | leaf => true
     | _ => false
     end.

Fixpoint size (t : Zbtree) : nat
  := match t with
     | leaf => 1
     | bnode _ t1 t2 => 1 + size t1 + size t2
     end.

Require Export Max.

Fixpoint height (t : Zbtree) : nat
  := match t with
     | leaf => 0
     | bnode _ t1 t2 => 1 + max (height t1) (height t2)
     end.

Fixpoint mirror (t : Zbtree) : Zbtree
  := match t with
     | leaf => leaf
     | bnode r t1 t2 => bnode r (mirror t2) (mirror t1)
     end.

Definition height' (t : Zbtree) : nat
  := Zbtree_rec _  0 (fun _ t1 ht1 t2 ht2 => 1 + max ht1 ht2) t.

Theorem height'_correct (t : Zbtree) : height t = height' t.
Proof. reflexivity. Qed.

Fixpoint memb (n : Z) (t : Zbtree) : bool
  := match t with
     | leaf => false
     | bnode r t1 t2 => Z.eqb r n || memb n t1 || memb n t2
     end.

Require Export List.

Fixpoint infix_list (t : Zbtree) : list Z
  := match t with
     | leaf => nil
     | bnode r t1 t2 => infix_list t1 ++ (r :: infix_list t2)
     end.

(**
m is strictly greater than every node of t
*)

Fixpoint strict_majorant (m : Z) (t : Zbtree) : bool
  := match t with
     | leaf => true
     | bnode r t1 t2 => Z.ltb r m
                        && strict_majorant m t1
                        && strict_majorant m t2
     end.

(**
m is strictly less than every node of t
*)
Fixpoint strict_minorant (m : Z) (t : Zbtree) : bool
  := match t with
     | leaf => true
     | bnode r t1 t2 => Z.ltb m r
                        && strict_minorant m t1
                        && strict_minorant m t2
     end.

Fixpoint is_searchtree (t : Zbtree) : bool
  := match t with
     | leaf => true
     | bnode n t1 t2 => strict_minorant n t2
                        && strict_majorant n t1
                        && is_searchtree t1
                        && is_searchtree t2
end.

Theorem right_is_search_tree (r : Z) (t1 t2 : Zbtree)
  : is_searchtree (bnode r t1 t2) = true -> is_searchtree t2 = true.
Proof.
  intro H. simpl in H.
  apply andb_prop in H as [H H2].
  assumption.
Qed.

Theorem left_is_search_tree (r : Z) (t1 t2 : Zbtree)
  : is_searchtree (bnode r t1 t2) = true -> is_searchtree t1 = true.
Proof.
  intro H. simpl in H.
  apply andb_prop in H as [H H2].
  apply andb_prop in H as [H H1].
  assumption.
Qed.

Fixpoint memb_in_searchtree (n : Z) (t : Zbtree) : bool
  := match t with
     | leaf => false
     | bnode r t1 t2 => match Z.compare n r with
                        | Lt => memb_in_searchtree n t1
                        | Eq => true
                        | Gt => memb_in_searchtree n t2
                        end
     end.

Open Scope Z_scope.

Theorem right_greater_than_center (r : Z) (t1 t2 : Zbtree)
      : is_searchtree (bnode r t1 t2) = true
        -> forall n : Z, memb n t2 = true -> r < n.
Proof.
  intro Hs.
  induction t2 as [| r2 t21 IH1 t22 IH2]; intros n Hm.
  - inversion Hm.
  - simpl in Hm. remember (bnode r2 t21 t22) as t2.
    simpl in Hs.
    apply andb_prop in Hs as [Hs Hs2].
    apply andb_prop in Hs as [Hs Hs1].
    apply andb_prop in Hs as [Hsm2 Hsm1].
    rewrite Heqt2 in Hs2. simpl in Hs2.
    apply andb_prop in Hs2 as [Hs2 Hs22].
    apply andb_prop in Hs2 as [Hs2 Hs21].
    apply andb_prop in Hs2 as [Hsm22 Hsm21].
    rewrite Heqt2 in Hsm2. simpl in Hsm2.
    apply andb_prop in Hsm2 as [Hsm2 Hsm22'].
    apply andb_prop in Hsm2 as [neq Hsm21'].
    assert (is_searchtree (bnode r t1 t21) = true) as Hs1_21.
    { simpl. repeat (apply andb_true_intro; split); assumption. }
    pose (IH1 Hs1_21 n) as H1.
    assert (is_searchtree (bnode r t1 t22) = true) as Hs1_22.
    { simpl. repeat (apply andb_true_intro; split); assumption. }
    pose (IH2 Hs1_22 n) as H2.
    apply orb_prop in Hm as [Hm | Hm22].
    apply orb_prop in Hm as [eq | Hm21].
    + apply Z.eqb_eq in eq. subst n.
      apply Z.ltb_lt. assumption.
    + apply H1, Hm21.
    + apply H2, Hm22.
Qed.

Theorem left_lower_than_center (r : Z) (t1 t2 : Zbtree)
      : is_searchtree (bnode r t1 t2) = true
        -> forall n : Z, memb n t1 = true -> n < r.
Proof.
  intro Hs.
  induction t1 as [| r1 t11 IH1 t12 IH2]; intros n Hm.
  - inversion Hm.
  - simpl in Hm. remember (bnode r1 t11 t12) as t1.
    simpl in Hs.
    apply andb_prop in Hs as [Hs Hs2].
    apply andb_prop in Hs as [Hs Hs1].
    apply andb_prop in Hs as [Hsm2 Hsm1].
    rewrite Heqt1 in Hs1. simpl in Hs1.
    apply andb_prop in Hs1 as [Hs1 Hs12].
    apply andb_prop in Hs1 as [Hs1 Hs11].
    apply andb_prop in Hs1 as [Hsm12 Hsm11].
    rewrite Heqt1 in Hsm1. simpl in Hsm1.
    apply andb_prop in Hsm1 as [Hsm1 Hsm12'].
    apply andb_prop in Hsm1 as [neq Hsm11'].
    assert (is_searchtree (bnode r t11 t2) = true) as Hs11_2.
    { simpl. repeat (apply andb_true_intro; split); assumption. }
    pose (IH1 Hs11_2 n) as H1.
    assert (is_searchtree (bnode r t12 t2) = true) as Hs12_2.
    { simpl. repeat (apply andb_true_intro; split); assumption. }
    pose (IH2 Hs12_2 n) as H2.
    apply orb_prop in Hm as [Hm | Hm22].
    apply orb_prop in Hm as [eq | Hm21].
    + apply Z.eqb_eq in eq. subst n.
      apply Z.ltb_lt. assumption.
    + apply H1, Hm21.
    + apply H2, Hm22.
Qed.

Theorem memb_in_st_correct (n : Z) (t : Zbtree)
  : is_searchtree t = true -> memb n t = memb_in_searchtree n t.
Proof.
  induction t as [| r t1 IH1 t2 IH2]; intro H; try reflexivity.
  assert (H0 := H). simpl in H.
  apply andb_prop in H as [H Hs2].
  apply andb_prop in H as [H Hs1].
  apply andb_prop in H as [Hm2 Hm1].
  apply IH1 in Hs1. clear IH1.
  apply IH2 in Hs2. clear IH2.
  simpl. pose (Dcompare (n ?= r)) as H. destruct H as [eq | [neq | neq]].
  - rewrite eq. apply Z.compare_eq in eq. subst r.
    rewrite Z.eqb_refl. reflexivity.
  - rewrite neq. rewrite Z.compare_lt_iff in neq.
    replace (r =? n) with false.
    2:{ symmetry. apply Z.eqb_neq. apply Z.neq_sym, Z.lt_neq. assumption. }
    simpl. destruct (memb n t2) eqn:Hmem2.
    + pose (right_greater_than_center r t1 t2 H0 n Hmem2) as neq2.
      apply Z.lt_asymm in neq2. contradiction.
    + rewrite <- Hs1. apply orb_false_r.
  - rewrite neq. rewrite Z.compare_gt_iff in neq.
    replace (r =? n) with false.
    2:{ symmetry. apply Z.eqb_neq. apply Z.lt_neq. assumption. }
    simpl. destruct (memb n t1) eqn:Hmem1.
    + pose (left_lower_than_center r t1 t2 H0 n Hmem1) as neq2.
      apply Z.lt_asymm in neq2. contradiction.
    + rewrite <- Hs2. apply orb_false_l.
Qed.

Fixpoint insert_in_searchtree (n : Z) (t : Zbtree) : Zbtree
  := match t with
     | leaf => bnode n leaf leaf
     | bnode r t1 t2 => match Z.compare n r with
                        | Lt => bnode r (insert_in_searchtree n t1) t2
                        | Eq => t
                        | Gt => bnode r t1 (insert_in_searchtree n t2)
                        end
     end.

Theorem insert_in_st_save_majority (r n : Z) (t : Zbtree)
  : n < r -> strict_majorant r t = true
    -> strict_majorant r (insert_in_searchtree n t) = true.
Proof.
  intros neq_nr H. induction t as [| m t1 IH1 t2 IH2].
  - simpl. repeat rewrite andb_true_r. apply Z.ltb_lt. assumption.
  - simpl in H.
    apply andb_prop in H as [H H2].
    apply andb_prop in H as [neq_mr H1].
    apply Z.ltb_lt in neq_mr. simpl.
    destruct (n ?= m) eqn:neq_nm; simpl;
      repeat (apply andb_true_intro; split);
      try apply Z.ltb_lt; try assumption.
    + apply IH1, H1.
    + apply IH2, H2.
Qed.

Theorem insert_in_st_save_minority (r n : Z) (t : Zbtree)
  : r < n -> strict_minorant r t = true
    -> strict_minorant r (insert_in_searchtree n t) = true.
Proof.
  intros neq_nr H. induction t as [| m t1 IH1 t2 IH2].
  - simpl. repeat rewrite andb_true_r. apply Z.ltb_lt. assumption.
  - simpl in H.
    apply andb_prop in H as [H H2].
    apply andb_prop in H as [neq_mr H1].
    apply Z.ltb_lt in neq_mr. simpl.
    destruct (n ?= m) eqn:neq_nm; simpl;
      repeat (apply andb_true_intro; split);
      try apply Z.ltb_lt; try assumption.
    + apply IH1, H1.
    + apply IH2, H2.
Qed.

Theorem insert_in_st_is_st (n : Z) (t : Zbtree)
  : is_searchtree t = true
    -> is_searchtree (insert_in_searchtree n t) = true.
Proof.
  induction t as [| r t1 IH1 t2 IH2]; intro H; try reflexivity.
  simpl. assert (H0 := H). simpl in H.
  apply andb_prop in H as [H Hs2].
  apply andb_prop in H as [H Hs1].
  apply andb_prop in H as [Hsm2 Hsm1].
  destruct (n ?= r) eqn:cmp.
  - assumption.
  - rewrite Z.compare_lt_iff in cmp.
    apply IH1 in Hs1. simpl.
    repeat (apply andb_true_intro; split); try assumption.
    apply insert_in_st_save_majority; assumption.
  - rewrite Z.compare_gt_iff in cmp.
    apply IH2 in Hs2. simpl.
    repeat (apply andb_true_intro; split); try assumption.
    apply insert_in_st_save_minority; assumption.
Qed.

Theorem insert_in_st_memb (n : Z) (t : Zbtree)
  : memb n (insert_in_searchtree n t) = true.
Proof.
  induction t as [| r t1 IH1 t2 IH2]; simpl.
  - now rewrite Z.eqb_refl.
  - destruct (n ?= r) eqn:neq; simpl.
    + rewrite Z.compare_eq_iff in neq.
      subst n. now rewrite Z.eqb_refl.
    + rewrite IH1. rewrite orb_true_r, orb_true_l. reflexivity.
    + rewrite IH2. repeat rewrite orb_true_r. reflexivity.
Qed.

(* Zbtree contains same elements *)
Definition eqt (s t : Zbtree) : Prop
  := forall n : Z, memb n s = true <-> memb n t = true.

Require Import Lia.
Theorem insert_in_st_memb1 (n m : Z) (t : Zbtree)
  : is_searchtree t = true -> memb m t = true
    -> memb m (insert_in_searchtree n t) = true.
Proof.
  induction t as [| r t1 IH1 t2 IH2]; intros Hs Hm.
  - inversion Hm.
  - pose (left_is_search_tree r t1 t2 Hs) as Hs1.
    pose (right_is_search_tree r t1 t2 Hs) as Hs2.
    simpl in Hm. simpl.
    repeat apply orb_prop in Hm as [Hm | Hm];
      destruct (n ?= r) eqn:neq_nr; simpl;
      try apply Z.eqb_eq in H;
      try apply Z.compare_eq_iff in neq_nr;
      try rewrite Z.compare_lt_iff in neq_nr;
      try rewrite Z.compare_gt_iff in neq_nr;
      try rewrite Hm; try lia.
    + rewrite (IH1 Hs1 Hm). lia.
    + rewrite (IH2 Hs2 Hm). lia.
Qed.

Theorem insert_in_st_memb2 (n m : Z) (t : Zbtree)
  : memb m (insert_in_searchtree n t) = true -> n = m \/ memb m t = true.
Proof.
  induction t as [|r t1 IH1 t2 IH2]; intro H;
    case (Z.eq_dec n m); intro Hnm; try firstorder.
  - simpl in H. lia.
  - right. simpl in H. simpl.
    destruct (n ?= r) eqn:Hnr;
      try apply Z.compare_eq_iff in Hnr;
      try rewrite Z.compare_lt_iff in Hnr;
      try rewrite Z.compare_gt_iff in Hnr;
      try assumption; simpl in H;
        repeat apply orb_prop in H as [H | H];
        try rewrite H; try lia.
    + apply IH1 in H as [H | H]; try rewrite H; try lia.
    + apply IH2 in H as [H | H]; try rewrite H; try lia.
Qed.

Theorem insert_in_st_correct (n : Z) (t : Zbtree)
  : is_searchtree t = true
    -> let t' := insert_in_searchtree n t in
       is_searchtree t' = true /\ memb n t' = true.
Proof.
  intros H t'. split.
  - apply insert_in_st_is_st. assumption.
  - apply insert_in_st_memb.
Qed.

Definition list_to_searchtree l := List.fold_right insert_in_searchtree leaf l.

Theorem list_to_st_is_st (ns : list Z)
  : is_searchtree (list_to_searchtree ns) = true.
Proof.
  induction ns as [| n ns' IH]; try reflexivity.
  simpl. apply insert_in_st_is_st, IH.
Qed.

Fixpoint meml (m : Z) (ns : list Z) : bool
  := match ns with
     | nil => false
     | cons n ns' => (n =? m) || meml m ns'
     end.

Theorem list_to_st_save_elements (ns : list Z) (m : Z)
  : meml m ns = true <-> memb m (list_to_searchtree ns) = true.
Proof.
  split; intro H.
  - (* -> *) induction ns as [| n ns' IH].
    + inversion H.
    + simpl. remember (list_to_searchtree ns') as t eqn:eqt.
      simpl in H. apply orb_prop in H as [H | H].
      * apply Z.eqb_eq in H. subst m. apply insert_in_st_memb.
      * { apply insert_in_st_memb1.
          - rewrite eqt. apply list_to_st_is_st.
          - apply IH, H.
        }
  - (* <- *) induction ns as [| n ns' IH].
    + simpl in H. discriminate H.
    + simpl. apply orb_true_intro. simpl in H.
      apply insert_in_st_memb2 in H as [H | H]; try lia.
      right. apply (IH H).
Qed.

Definition weak_sort l := infix_list (list_to_searchtree l).

Compute weak_sort (4::6::9::3::8::nil)%Z.

Definition list_to_searchtree_test l : bool := is_searchtree (list_to_searchtree l).

Compute is_searchtree
        (bnode 8
               (bnode 5 (bnode 3 leaf leaf)
                      (bnode 7 leaf leaf))
               (bnode 15 (bnode 10 leaf leaf)
                      (bnode 18 leaf leaf)))%Z.

Compute is_searchtree
        (bnode  8
                (bnode 5 (bnode 3 leaf leaf)
                       (bnode 7 leaf leaf))
                (bnode 15 (bnode 16 leaf leaf)
                       (bnode 18 leaf leaf)))%Z.

(* Proove that weak_sort works *)

Import ListNotations.

Inductive sorted : list Z -> Prop
  :=
  | sorted0 : sorted []
  | sorted1 (n : Z) : sorted [n]
  | sorted_n (n0 n1 : Z) (ns : list Z) :
      n0 < n1
      -> sorted (n1 :: ns)
      -> sorted (n0 :: n1 :: ns).

#[export] Hint Constructors sorted : sort.

Fixpoint list_majorant (k : Z) (ns : list Z) : bool
  := match ns with
     | [] => true
     | n :: ns' => (n <? k) && list_majorant k ns'
     end.

Fixpoint list_minorant (k : Z) (ns : list Z) : bool
  := match ns with
     | [] => true
     | n :: ns' => (k <? n) && list_minorant k ns'
     end.

Theorem list_majorant_cons_inv (k n : Z) (ns : list Z)
  : list_majorant k (n :: ns) = true -> list_majorant k ns = true.
Proof.
  intro H. simpl in H. apply andb_prop in H as [neq H].
  assumption.
Qed.

Theorem list_majorant_gt_head (k n : Z) (ns : list Z)
  : list_majorant k (n :: ns) = true -> n < k.
Proof.
  simpl. intro H. apply andb_prop in H as [H _].
  apply Z.ltb_lt. assumption.
Qed.

Theorem list_minorant_lt_head (k n : Z) (ns : list Z)
  : list_minorant k (n :: ns) = true -> k < n.
Proof.
  simpl. intro H. apply andb_prop in H as [H _].
  apply Z.ltb_lt. assumption.
Qed.

Theorem list_minorant_cons_inv (k n : Z) (ns : list Z)
  : list_minorant k (n :: ns) = true -> list_minorant k ns = true.
Proof.
  intro H. simpl in H. apply andb_prop in H as [neq H].
  assumption.
Qed.

Theorem list_majorant_cons (k n : Z) (ns : list Z)
  : n < k -> list_majorant k ns = true -> list_majorant k (n :: ns) = true.
Proof.
  intros neq H. simpl. apply andb_true_intro.
  rewrite Z.ltb_lt. easy.
Qed.

Theorem list_majorant_app (k : Z) (ns ms : list Z)
  : list_majorant k ns = true
    -> list_majorant k ms = true
    -> list_majorant k (ns ++ ms) = true.
Proof.
  induction ns as [| n ns' IH]; intros Hn Hm; try auto.
  rewrite <- app_comm_cons.
  pose (list_majorant_gt_head _ _ _ Hn) as neq.
  pose (list_majorant_cons_inv _ _ _ Hn) as Hn'.
  apply list_majorant_cons; try assumption.
  apply IH; assumption.
Qed.

Theorem list_minorant_cons (k n : Z) (ns : list Z)
  : k < n -> list_minorant k ns = true -> list_minorant k (n :: ns) = true.
Proof.
  intros neq H. simpl. apply andb_true_intro.
  rewrite Z.ltb_lt. easy.
Qed.

Theorem list_minorant_app (k : Z) (ns ms : list Z)
  : list_minorant k ns = true
    -> list_minorant k ms = true
    -> list_minorant k (ns ++ ms) = true.
Proof.
  induction ns as [| n ns' IH]; intros Hn Hm; try auto.
  rewrite <- app_comm_cons.
  pose (list_minorant_lt_head _ _ _ Hn) as neq.
  pose (list_minorant_cons_inv _ _ _ Hn) as Hn'.
  apply list_minorant_cons; try assumption.
  apply IH; assumption.
Qed.

Theorem list_minorant_lt_majorant (m0 m1 : Z) (ns : list Z)
  : ns <> []
    -> list_minorant m0 ns = true
    -> list_majorant m1 ns = true
    -> m0 < m1.
Proof.
  destruct ns as [| n ns]; intros H H0 H1; try easy.
  apply list_minorant_lt_head in H0.
  apply list_majorant_gt_head in H1.
  apply (Z.lt_trans m0 n m1); assumption.
Qed.

Theorem list_minorant_closure (m k : Z) (ns : list Z)
  : m < k -> list_minorant k ns = true -> list_minorant m ns = true.
Proof.
  induction ns as [| n ns' IH]; intros neq_mk H; try reflexivity.
  simpl. apply andb_true_intro.
  simpl in H. apply andb_prop in H as [neq_mn H].
  apply Z.ltb_lt in neq_mn. split.
  - apply Z.ltb_lt. apply (Z.lt_trans m k n); assumption.
  - apply IH; assumption.
Qed.

Theorem infix_list_majorant (k : Z) (t : Zbtree)
  : strict_majorant k t = true -> list_majorant k (infix_list t) = true.
Proof.
  induction t as [| r t1 IH1 t2 IH2]; intro H; try reflexivity.
  simpl. simpl in H.
  apply andb_prop in H as [H H2].
  apply andb_prop in H as [neq_rk H1].
  apply Z.ltb_lt in neq_rk.
  apply list_majorant_app.
  - apply IH1, H1.
  - apply list_majorant_cons; try assumption.
    apply IH2, H2.
Qed.

Theorem infix_list_minorant (k : Z) (t : Zbtree)
  : strict_minorant k t = true -> list_minorant k (infix_list t) = true.
Proof.
  induction t as [| r t1 IH1 t2 IH2]; intro H; try reflexivity.
  simpl. simpl in H.
  apply andb_prop in H as [H H2].
  apply andb_prop in H as [neq_rk H1].
  apply Z.ltb_lt in neq_rk.
  apply list_minorant_app.
  - apply IH1, H1.
  - apply list_minorant_cons; try assumption.
    apply IH2, H2.
Qed.

Theorem cons_sorted (k : Z) (ns : list Z)
  : sorted ns -> (list_minorant k ns) = true -> sorted (k :: ns).
Proof.
  destruct ns as [| n ns']; intros Hs Hm; try auto with sort.
  constructor; try assumption.
  apply list_minorant_lt_head in Hm. assumption.
Qed.

Theorem cons_sorted_inv (n : Z) (ns : list Z)
  : sorted (n :: ns) -> sorted ns.
Proof.
  intro H. destruct ns as [| n1 ns1 IH]; try constructor.
  inversion H. assumption.
Qed.

Theorem sorted_rm_snd (n0 n1 : Z) (ns : list Z)
  : sorted (n0 :: n1 :: ns) -> sorted (n0 :: ns).
Proof.
  intro H.
  destruct ns as [| n2 ns2];
    constructor; inversion H; inversion H4;
      auto with zarith.
Qed.

Theorem sorted_head_is_minorant (n : Z) (ns : list Z)
  : sorted (n :: ns) -> list_minorant n ns = true.
Proof.
  induction ns as [| n0 ns0 IH]; intro Hs; try reflexivity.
  simpl. apply andb_true_intro. split.
  - inversion Hs. apply Z.ltb_lt. assumption.
  - apply IH. apply (sorted_rm_snd n n0 ns0 Hs).
Qed.

Theorem join_sorted (k : Z) (ns ms : list Z)
  : sorted ns -> sorted ms
    -> (list_majorant k ns) = true
    -> (list_minorant k ms) = true
    -> sorted (ns ++ k :: ms).
Proof.
  induction ns as [| n0 ns0 IH]; intros Hsn Hsm Hmn Hmm; simpl.
  - apply cons_sorted; assumption.
  - case (list_eq_dec Z.eq_dec ns0 []); intro H0.
    + subst ns0. simpl. apply cons_sorted.
      * simpl in IH. apply IH; try auto with sort.
      * apply list_majorant_gt_head in Hmn.
        apply (list_minorant_cons n0 k ms Hmn).
        apply (list_minorant_closure n0 k ms Hmn Hmm).
    + apply cons_sorted.
      * apply cons_sorted_inv in Hsn.
        apply list_majorant_cons_inv in Hmn.
        apply IH; assumption.
      * apply sorted_head_is_minorant in Hsn.
        apply list_minorant_app; try assumption.
        apply list_majorant_cons_inv in Hmn.
        pose (list_minorant_lt_majorant n0 k ns0 H0 Hsn Hmn) as Hnk.
        apply list_minorant_cons; try assumption.
        apply (list_minorant_closure n0 k ms) in Hmm; assumption.
Qed.

Theorem infix_list_sorted (t : Zbtree) : is_searchtree t = true -> sorted (infix_list t).
Proof.
  induction t as [| r t1 IH1 t2 IH2]; intro H; try auto with sort.
  simpl. simpl in H.
  apply andb_prop in H as [H Hs2].
  apply andb_prop in H as [H Hs1].
  apply andb_prop in H as [Hsm2 Hsm1].
  apply IH1 in Hs1. apply IH2 in Hs2.
  apply infix_list_majorant in Hsm1.
  apply infix_list_minorant in Hsm2.
  apply join_sorted; assumption.
Qed.

(* weak list equality : ns and ms contains same elements in any order and counts *)
Definition weql (ns ms : list Z) : Prop
  := forall z : Z, meml z ns = true <-> meml z ms = true.

(* weak list to Zbtree equality : ns and t contains same elements
   in any order and counts *)
Definition weqlt (ns : list Z) (t : Zbtree) : Prop
  := forall z : Z, meml z ns = true <-> memb z t = true.

Theorem memb_is_meml (t : Zbtree) (z : Z)
  : memb z t = true <-> meml z (infix_list t) = true.
Proof.
Admitted.

Theorem weql_is_weqlt (ns : list Z) (t : Zbtree)
  : weqlt ns t <-> weql ns (infix_list t).
Proof.
  split; intros H z.
  - (* -> *) unfold weqlt in H. pose (H z) as H'.
    destruct H' as [H1 H2]. clear H.
    split; intro Hm.
    + (* -> *) apply memb_is_meml, H1, Hm.
    + (* <- *) apply H2, memb_is_meml, Hm.
  - unfold weql in H. pose (H z) as H'.
    destruct H' as [H1 H2]. clear H.
    split; intro Hm.
    + (* -> *) apply memb_is_meml, H1, Hm.
    + (* <- *) apply H2, memb_is_meml, Hm.
Qed.

Theorem weqlt_insert (k : Z) (ns : list Z) (t : Zbtree)
  : weqlt ns t -> weqlt (k :: ns) (insert_in_searchtree k t).
Proof.
Admitted.

Theorem weak_sort_save_elements (ns : list Z) : weql ns (weak_sort ns).
Proof.
  induction ns as [| n ns' IH].
  - (*[ ns = [] ]*) simpl. firstorder.
  - (*[ ns = n :: ns' ]*)
    unfold weak_sort, list_to_searchtree. simpl.
    remember (list_to_searchtree ns') as t eqn:eqt.
    unfold list_to_searchtree in eqt. rewrite <- eqt.
    apply weql_is_weqlt, weqlt_insert. subst t. apply weql_is_weqlt.
    unfold weak_sort, list_to_searchtree in IH. apply IH.
Qed.

Definition zsort : (list Z -> list Z) -> Prop
  := fun fn => forall ns : list Z,
         sorted (fn ns) /\ weql ns (fn ns).

Theorem weak_sort_is_zsort : zsort weak_sort.
Proof.
  intros ns. split.
  - unfold weak_sort. apply infix_list_sorted. apply list_to_st_is_st.
  - apply weak_sort_save_elements.
Qed.
