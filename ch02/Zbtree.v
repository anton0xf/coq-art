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

Definition list_to_searchtree l := List.fold_right insert_in_searchtree leaf l.

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
