Require Import ZArith List Arith Bool Lia.
Import ListNotations.

(* 6.5 * Dependent Inductive Types *)

(* 6.5.1 First-Order Data as Parameters *)
Inductive ltree (n : nat) : Set
  := lleaf : ltree n
   | lnode : forall p : nat, p <= n -> ltree n -> ltree n -> ltree n.

Check ltree_ind.
(* ltree_ind : forall (n : nat) (P : ltree n -> Prop),
     P (lleaf n)
     -> (forall (p : nat) (l : p <= n) (l0 : ltree n),
         P l0 -> forall l1 : ltree n, P l1 -> P (lnode n p l l0 l1))
     -> forall l : ltree n, P l *)

Inductive sqrt_data (n : nat) : Set
  := sqrt_intro : forall x : nat, x * x <= n -> n <  S x * S x -> sqrt_data n.

Check sqrt_data_ind.
(* sqrt_data_ind : forall (n : nat) (P : sqrt_data n -> Prop),
     (forall (x : nat) (l : x * x <= n) (l0 : n < S x * S x),
             P (sqrt_intro n x l l0))
     -> forall s : sqrt_data n, P s *)

(* 6.5.2 Variably Dependent Inductive Types *)
Inductive htree (X : Type) : nat -> Type
  := hleaf : X -> htree X 0
   | hnode : forall h : nat, X -> htree X h -> htree X h -> htree X (S h).

Arguments hleaf {X} x.
Arguments hnode {X} h x t1 t2.

Check htree_ind.
(* htree_ind : forall (A : Type) (P : forall n : nat, htree A n -> Prop),
     (forall a : A, P 0 (hleaf A a))
     -> (forall (n : nat) (a : A) (h : htree A n),
          P n h -> forall h0 : htree A n,
                     P n h0 -> P (S n) (hnode A n a h h0))
     -> forall (n : nat) (h : htree A n), P n h *)

(* repeat Z_btree definition *)
Open Scope Z_scope.
Inductive Z_btree : Set
  := Z_leaf : Z_btree
   | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Fixpoint htree_to_btree (n : nat) (t : htree Z n) {struct t} : Z_btree
  := match t with
     | hleaf x => Z_bnode x Z_leaf Z_leaf
     | hnode p v t1 t2
       => Z_bnode v (htree_to_btree p t1) (htree_to_btree p t2)
     end.

Fixpoint invert {A : Type} (n : nat) (t : htree A n) {struct t} : htree A n
  := match t in htree _ x return htree A x with
     | hleaf v => hleaf v
     | hnode p v t1 t2 => hnode p v (invert p t2) (invert p t1)
     end.

(* Exercise 6.46 **
   Prove one of the injection lemmas for the hnode construct: *)
Open Scope nat_scope.
Definition htree_left (X : Type) (n : nat) (t : htree X (S n)) : htree X n
  := match t with
     | hnode n v t1 t2 => t1
     end.

Theorem injection_left_htree (n : nat) (t1 t2 t3 t4 : htree nat n)
   : hnode n O t1 t2 = hnode n O t3 t4 ->  t1 = t3.
Proof.
  intro H. apply (f_equal (htree_left nat n)) in H. apply H.
Qed.

(* authors' solution *)
Definition first_of_htree {A : Type} (n : nat)
  : htree A n -> htree A (S n) -> htree A n.
  intros v t. generalize v.
  change (htree A (pred (S n)) -> htree A (pred (S n))).
  case t.
  - intros x v'. exact v'.
  - intros p x t1 t2 v'. exact t1.
Defined.

Print first_of_htree.
(* first_of_htree : forall (A : Type) (n : nat),
                           htree A n -> htree A (S n) -> htree A n
   = fun (A : Type) (n : nat) (v : htree A n) (t : htree A (S n))
     => (match t in (htree _ n0)
             return (htree A (pred n0) -> htree A (pred n0))
         with
         | hleaf _ _ => fun (v' : htree A (pred 0)) => v'
         | hnode _ p _ t1 _ => fun _ : htree A (pred (S p)) => t1
         end) v *)

Check (first_of_htree 0 (hleaf 1)
                      (hnode 0 2 (hleaf 3) (hleaf 4))).
(* first_of_htree 0 (hleaf 1) (hnode 0 2 (hleaf 3) (hleaf 4))
   : htree nat 0 *)

Compute (first_of_htree 0 (hleaf 1)
                        (hnode 0 2 (hleaf 3) (hleaf 4))).
(* = hleaf 3 : htree nat 0 *)

Theorem injection_first_htree (n : nat) (t1 t2 t3 t4 : htree nat n)
  : hnode n O t1 t2 = hnode n O t3 t4 -> t1 = t3.
Proof.
  intro H.
  change
    (first_of_htree n t1 (hnode n O t1 t2)
     = first_of_htree n t1 (hnode n O t3 t4)).
  now rewrite H.
Qed.

(** Exercise 6.47
   Define a function that takes a number n and builds
   a fixedheight tree of height n containing
   pairwise different -integer- natural values
   (proofs with [nat] is slightly simpler). *)

(* [pn_tree] is for "perfect numbered tree" *)

(* Helper function for [pn_tree]
   * h - height of tree
   * n - value of root of tree
   Nodes numbered like its arryay indexes in ahnentafel tree representaton.
   See [Binary heap implementation](https://en.wikipedia.org/wiki/Binary_heap#Heap_implementation)
 *)
Fixpoint pn_tree_aux (h n : nat) {struct h} : htree nat h
  := match h with
     | O => hleaf n
     | S h' => hnode h' n
                    (pn_tree_aux h' (2*n + 1))
                    (pn_tree_aux h' (2*n + 2))
     end.

Definition pn_tree (h : nat) : htree nat h := pn_tree_aux h 0.

Example pn_tree_ex2
  : pn_tree 2 = hnode 1 0
                      (hnode 0 1 (hleaf 3) (hleaf 4))
                      (hnode 0 2 (hleaf 5) (hleaf 6)).
Proof. reflexivity. Qed.

Example pn_tree_ex3
  : pn_tree 3
    = hnode 2 0
            (hnode 1 1
                   (hnode 0 3 (hleaf 7) (hleaf 8))
                   (hnode 0 4 (hleaf 9) (hleaf 10)))
            (hnode 1 2
                   (hnode 0 5 (hleaf 11) (hleaf 12))
                   (hnode 0 6 (hleaf 13) (hleaf 14))).
Proof. reflexivity. Qed.

(** authors' solution (with Z replaced by [nat])*)
Fixpoint make_htree_aux (h start : nat) : nat * htree nat h
  := match h with
     | 0 => (start + 1, hleaf start)
     | S h' => let (start2, t1) := make_htree_aux h' (start + 1) in
              let (next, t2) := make_htree_aux h' start2 in
              (next, hnode h' start t1 t2)
     end.

Definition make_htree (n : nat) : htree nat n := snd (make_htree_aux n 0).

Example make_htree_ex3
  : make_htree 3
    = hnode 2 0
            (hnode 1 1
                   (hnode 0 2 (hleaf 3) (hleaf 4))
                   (hnode 0 5 (hleaf 6) (hleaf 7)))
            (hnode 1 8
                   (hnode 0 9 (hleaf 10) (hleaf 11))
                   (hnode 0 12 (hleaf 13) (hleaf 14))).
Proof. reflexivity. Qed.

(** my proof of some properties *)

(* get range of natural numbers
   from n0 (inclusive) to n (exclusive) *)
Fixpoint range (n0 n : nat) : list nat
  := match n with
     | O => []
     | S n' => n0 :: range (S n0) n'
     end.

Example range_ex1 : range 0 4 = [0; 1; 2; 3].
Proof. reflexivity. Qed.

(* list htree elements DFS *)
Fixpoint flat_htree_dfs {X : Type} {h : nat} (t : htree X h)
         {struct t} : list X
  := match t with
     | hleaf x => [x]
     | hnode h' x t1 t2 => x :: (flat_htree_dfs t1) ++ (flat_htree_dfs t2)
     end.

Compute flat_htree_dfs (pn_tree 3).
(* = [0; 1; 3; 7; 8; 4; 9; 10; 2; 5; 11; 12; 6; 13; 14] : list nat *)
Compute flat_htree_dfs (make_htree 3).
(* = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14] : list nat *)
Compute range 0 15.
(* = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14] : list nat *)

Example flat_htree_dfs_ex3 : flat_htree_dfs (make_htree 3) = range 0 15.
Proof. simpl. reflexivity. Qed.

Definition htree_x {X : Type} {h : nat} (t : htree X h) : X
  := match t with
     | hleaf x => x
     | hnode _ x _ _ => x
     end.

Definition htree_t1 {X : Type} {h : nat} (t : htree X (S h)) : htree X h
  := match t with hnode _ _ t1 _ => t1 end.

Definition htree_t2 {X : Type} {h : nat} (t : htree X (S h)) : htree X h
  := match t with hnode _ _ _ t2 => t2 end.

(** see "convoy pattern" in http://adam.chlipala.net/cpdt/html/MoreDep.html *)
(** illustration on simple example: *)
(*
Definition convoy_test_err (n : nat) (t : htree Z n) : htree Z (pred n)
  := match n with
     | O => t
     | S n' => htree_t1 n' t
     end t.
*)

(* Toplevel input, characters 131-132: *)
(* > Definition convoy_test_err (n : nat) (t : htree Z n) : htree Z (pred n)   := match n with      | O => t      | S n' => htree_t1 n' t      end t. *)
(* >                                                                                                                                    ^ *)
(* Error: *)
(* In environment *)
(* n : nat *)
(* t : htree Z n *)
(* n' : nat *)
(* The term "t" has type "htree Z n" while it is expected to have type *)
(*  "htree Z (S n')" (cannot unify "n" and "S n'"). *)

Definition convoy_test_ok (n : nat) (t : htree Z n) : htree Z (pred n)
  := match n return htree Z n -> htree Z (pred n) with
     | O => fun t => t
     | S n' => fun t => htree_t1 t
     end t.

(* It is bad example because "convoy" and even match "in" clause
   is not nececarry *)
Definition convoy_test_no_convoy (n : nat) (t : htree Z n) : htree Z (pred n)
  := match t with
     | hleaf x => hleaf x
     | hnode h x t1 t2 => t1
     end.

(** list htree elements BFS *)
Definition flat_htree_bfs_aux1 {X : Type}
           (h : nat) (t : htree X (S h)) (acc : list (htree X h))
  := (htree_t1 t) :: (htree_t2 t) :: acc.

Fixpoint flat_htree_bfs_aux {X : Type} {h : nat}
         (q : list (htree X h)) {struct h}
  : list X
  := match h return list (htree X h) -> list X with
     | O => fun Q => map htree_x Q
     | S h' => fun Q => let q' := fold_right (flat_htree_bfs_aux1 h') [] Q in
                    let cur_layer := map htree_x Q in
                    let next_layers := (flat_htree_bfs_aux q') in
                    cur_layer ++ next_layers
     end q.

Print flat_htree_bfs_aux.

Definition flat_htree_bfs {X : Type} {h : nat} (t : htree X h) : list X
  := @flat_htree_bfs_aux X h [t].

Compute flat_htree_bfs (pn_tree 1).
(* = [0; 1; 2] : list nat *)

Compute pn_tree 2.
(* = hnode 1 0 (hnode 0 1 (hleaf 3) (hleaf 4))
               (hnode 0 2 (hleaf 5) (hleaf 6))
   : htree nat 2 *)

Compute flat_htree_bfs (pn_tree 2).
(* = [0; 1; 2; 3; 4; 5; 6] : list nat *)

Compute flat_htree_bfs (pn_tree 3).
(* = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14] : list nat *)

Example flat_htree_bfs_ex3 : flat_htree_bfs (pn_tree 3) = range 0 15.
Proof. reflexivity. Qed.

Fixpoint In_htree {X : Type} {h : nat} (y : X) (t : htree X h) {struct t} : Prop
  := match t with
     | hleaf x => x = y
     | hnode h x t1 t2 => x = y \/ In_htree y t1 \/ In_htree y t2
     end.

(* htree is pairwise different *)
Fixpoint htree_is_pwdiff {X : Type} {h : nat} (t : htree X h) {struct t} : Prop
  := match t with
     | hleaf x => True
     | hnode h' x t1 t2
       => htree_is_pwdiff t1 /\ htree_is_pwdiff t2
         /\ (forall y : X, In_htree y t1 -> y <> x)
         /\ (forall y : X, In_htree y t2 -> y <> x)
         /\ (forall y1 y2 : X, In_htree y1 t1 -> In_htree y2 t2 -> y1 <> y2)
     end.

Theorem not_in_tree_iff {X : Type} (x : X) (h : nat) (t : htree X h)
  : (forall y : X, In_htree y t -> y <> x) <-> ~ In_htree x t.
Proof.
  split; intro H.
  - intro H1. apply H in H1. apply H1. reflexivity.
  - intros y H1 eq. subst y. apply H, H1.
Qed.

Theorem not_in_pn_tree_aux (h n k : nat)
  : n < k -> ~ In_htree n (pn_tree_aux h k).
Proof.
  generalize dependent k.
  induction h as [| h1 IH]; simpl; try lia.
  intros k k_gt [H | [H | H]]; try lia.
  - apply (IH (k + (k + 0) + 1)); [lia | apply H].
  - apply (IH (k + (k + 0) + 2)); [lia | apply H].
Qed.

Theorem pn_tree_contains_left_branch (h n y : nat)
  : In_htree y (pn_tree_aux h (2 * n + 1))
    -> In_htree y (pn_tree_aux (S h) n).
Proof.
  intro H. simpl. right. left. exact H.
Qed.

Theorem pn_tree_contains_right_branch (h n y : nat)
  : In_htree y (pn_tree_aux h (2 * n + 2))
    -> In_htree y (pn_tree_aux (S h) n).
Proof.
  intro H. simpl. right. right. exact H.
Qed.

Theorem pn_tree_max (h n y : nat)
  : In_htree y (pn_tree_aux h n) -> y <= 2^h * (n + 2) - 2.
Proof.
  generalize dependent n.
  induction h as [| h1 IH]; intros n H.
  - simpl in *. lia.
  - destruct h1 as [| h2];
      [|remember (S h2) as h1 eqn:eq_h1];
      simpl in H;
      replace (n + (n + 0)) with (2*n) in H by lia;
      destruct H as [H | [H | H]];
      try (subst y; simpl; lia).
    + subst n. rewrite Nat.pow_succ_r'.
      rewrite <- Nat.mul_assoc.
      rewrite <- Nat.mul_pred_r.
      rewrite <- Nat.double_twice. unfold Nat.double.
      apply le_plus_trans, Nat.lt_le_pred.
      rewrite <- (Nat.mul_1_l y) at 1.
      apply Nat.mul_lt_mono; [|lia].
      apply Nat.pow_gt_1; lia.
    + apply IH in H. simpl in *. lia.
    + apply IH in H. simpl in *. lia.
Qed.

Theorem pn_tree_in_Sh' (h n y : nat)
  : In_htree y (pn_tree_aux (S h) n)
    -> In_htree y (pn_tree_aux h n)
      \/ (2^(S h) * (n + 1) - 1) <= y.
Proof.
  generalize dependent n.
  induction h as [| h' IH]; intros n H.
  - simpl in *. lia.
  - remember (S h') as h eqn:eq_h. simpl in H.
    replace (n + (n + 0)) with (2*n) in H by lia.
    destruct H as [H | [H | H]].
    + left. subst h n. simpl. left. reflexivity.
    + apply IH in H. destruct H as [H | H].
      * left. subst h. apply pn_tree_contains_left_branch, H.
      * subst h. right. simpl in *. lia.
    + apply IH in H. destruct H as [H | H].
      * left. subst h. apply pn_tree_contains_right_branch, H.
      * subst h. right. simpl in *. lia.
Qed.

Theorem pn_tree_in_Sh (h n y : nat)
  : In_htree y (pn_tree_aux (S h) n)
    -> In_htree y (pn_tree_aux h n)
      \/ (2^(S h) * (n + 1) - 1) <= y <= 2^(S h) * (n + 2) - 2.
Proof.
  intro H. apply pn_tree_in_Sh' in H as H'.
  destruct H' as [H' | H'].
  - left. assumption.
  - right. split.
    + assumption.
    + apply pn_tree_max in H. lia.
Qed.

Theorem pow_ge_1 (n m : nat) : 1 <= n -> 1 <= n ^ m.
Proof. intro H. induction m as [| m' IH]; simpl; lia. Qed.

Lemma le_sub (a b c : nat) : b <= a -> c <= a -> a - b <= a - c -> c <= b.
Proof.
  intros H1 H2 H.
  apply (Nat.le_sub_le_add_r _ _ b) in H.
  rewrite <- Nat.add_sub_swap in H; [|exact H2].
  apply (plus_le_compat_r _ _ c) in H.
  rewrite <- Nat.add_sub_swap in H; [|lia].
  rewrite Nat.add_sub in H.
  apply (Nat.add_le_mono_l c b a), H.
Qed.

Lemma le_sub2 (a b c d : nat)
  : b <= a -> d <= c -> a - b <= c - d -> a + d <= c + b.
Proof.
  intros H1 H2 H.
  apply (Nat.le_sub_le_add_r _ _ b) in H.
  rewrite <- Nat.add_sub_swap in H; [|exact H2].
  apply (plus_le_compat_r _ _ d) in H.
  rewrite <- Nat.add_sub_swap in H; [|lia].
  rewrite Nat.add_sub in H. exact H.
Qed.

Theorem pow_ge (a b c : nat) : 0 < a <= c -> a <= a ^ b * c.
Proof.
  intros [a_gt a_lt]. rewrite <- (Nat.mul_1_l a) at 1.
  apply Nat.mul_le_mono; [|lia].
  apply pow_ge_1. lia.
Qed.

Theorem pn_tree_last_layer (h n y : nat)
  : (2^h * (n + 1) - 1) <= y <= 2^h * (n + 2) - 2
    -> In_htree y (pn_tree_aux h n).
Proof.
  generalize dependent n.
  induction h as [| h1 IH]; intros n [y_gt y_lt].
  - simpl in *. lia.
  - pose (IH (2*n + 1)) as H1.
    pose (IH (2*n + 2)) as H2.
    destruct (y <=? 2 ^ h1 * (2 * n + 1 + 2) - 2) eqn:neq.
    + apply Nat.leb_le in neq.
      apply pn_tree_contains_left_branch, H1.
      simpl in y_gt. split; lia.
    + apply Nat.leb_gt in neq. unfold lt in neq.
      rewrite <- Nat.add_1_r in neq.
      rewrite <- Nat.add_sub_swap in neq.
      2:{ apply pow_ge. lia. }
      apply pn_tree_contains_right_branch, H2.
      simpl in y_lt. split; lia.
Qed.

Theorem pn_tree_branches_is_diff (h n y : nat)
  : In_htree y (pn_tree_aux h (2*n + 1))
    -> ~ In_htree y (pn_tree_aux h (2*n + 2)).
Proof.
  generalize dependent n.
  induction h as [| h1 IH]; [simpl; lia|].
  intros n H1 H2.
  apply pn_tree_in_Sh in H1.
  apply pn_tree_in_Sh in H2.
  destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
  - apply (IH n H1 H2).
  - apply pn_tree_max in H1. destruct H2 as [y_gt y_lt].
    pose (Nat.le_trans _ y _ y_gt H1) as H.
    replace (2 * n + 2 + 1) with (2 * n + 1 + 2) in H by lia.
    rewrite Nat.pow_succ_r' in H.
    assert (2 <= 2 ^ h1 * (2 * n + 1 + 2)) as Hgt.
    { apply pow_ge. lia. }
    apply le_sub2 in H; lia.
  - apply pn_tree_max in H2. destruct H1 as [y_gt y_lt].
    pose (Nat.le_trans _ y _ y_gt H2) as H.
    replace (2 * n + 1 + 1) with (2 * n + 2) in H by lia.
    rewrite Nat.pow_succ_r' in H.
    assert (2 <= 2 ^ h1 * (2 * n + 1 + 2)) as Hgt.
    { apply pow_ge. lia. }
    apply le_sub2 in H; lia.
  - destruct H1 as [_ y_lt]. destruct H2 as [y_gt _].
    pose (Nat.le_trans _ y _ y_gt y_lt) as H.
    replace (2 * n + 2 + 1) with (2 * n + 1 + 2) in H by lia.
    rewrite Nat.pow_succ_r' in H.
    assert (2 <= 2 ^ h1 * (2 * n + 1 + 2)) as Hgt.
    { apply pow_ge. lia. }
    apply le_sub2 in H; lia.
Qed.

Theorem pn_tree_aux_is_pwdiff (h n : nat) : htree_is_pwdiff (pn_tree_aux h n).
Proof.
  generalize dependent n.
  induction h as [| h' IH]; [reflexivity|].
  intro n. simpl. repeat split; try apply IH.
  - apply not_in_tree_iff, not_in_pn_tree_aux. lia.
  - apply not_in_tree_iff, not_in_pn_tree_aux. lia.
  - intros y1 y2 H1 H2. apply not_eq_sym.
    generalize dependent H2.
    generalize dependent y2.
    rewrite (not_in_tree_iff y1).
    apply pn_tree_branches_is_diff, H1.
Qed.

Theorem pn_tree_is_pwdiff (h : nat) : htree_is_pwdiff (pn_tree h).
Proof. apply pn_tree_aux_is_pwdiff. Qed.

Theorem make_htree_aux_fst_eq (h n : nat)
  : fst (make_htree_aux h n) = (n + 2^(S h) - 1).
Proof.
  generalize dependent n.
  induction h as [| h1 IH]; [simpl; lia|].
  intro n. simpl make_htree_aux.
  destruct (make_htree_aux h1 (n + 1)) as (start2, t1) eqn:eq1.
  destruct (make_htree_aux h1 start2) as (next, t2) eqn:eq2.
  simpl fst.
  apply (f_equal fst) in eq1 as eq_start2. simpl in eq_start2.
  apply (f_equal fst) in eq2 as eq_next. simpl in eq_next.
  rewrite IH in eq_next, eq_start2.
  rewrite <- eq_next, <- eq_start2.
  remember (S h1) as h eqn:eq_h. rewrite Nat.pow_succ_r'.
  replace (n + 1 + 2^h - 1 + 2^h - 1) with (n + (2 * 2^h + 1) - 2) by lia.
  rewrite <- Nat.add_sub_assoc.
  replace (2 * 2 ^ h + 1 - 2) with (2 * 2 ^ h - 1); try lia.
  - rewrite Nat.add_sub_assoc; [lia|].
    rewrite <- Nat.pow_succ_r'. apply pow_ge_1. lia.
  - apply le_plus_trans. rewrite Nat.mul_comm. apply pow_ge. lia.
Qed.

Theorem make_htree_start_lt_next (h n : nat)
  : n < fst (make_htree_aux h n).
Proof.
  rewrite make_htree_aux_fst_eq.
  rewrite <- Nat.add_sub_assoc.
  - rewrite plus_n_O at 1. apply plus_le_lt_compat; [lia|].
    pose (Nat.pow_gt_1 2 (S h)) as neq. lia.
  - apply pow_ge_1. lia.
Qed.

Theorem make_htree_bounds (h n y : nat)
  : In_htree y (snd (make_htree_aux h n))
    <-> n <= y < fst (make_htree_aux h n).
Proof.
  generalize dependent n.
  generalize dependent y.
  induction h as [| h1 IH]; [simpl; lia|]. simpl. intros y n.
  destruct (make_htree_aux h1 (n + 1)) as (start2, t1) eqn:eq1.
  destruct (make_htree_aux h1 start2) as (next, t2) eqn:eq2.
  apply (f_equal fst) in eq1 as eq_start2. simpl in eq_start2.
  apply (f_equal fst) in eq2 as eq_next. simpl in eq_next.
  apply (f_equal snd) in eq1 as eq_t1. simpl in eq_t1.
  apply (f_equal snd) in eq2 as eq_t2. simpl in eq_t2.
  simpl. split; intro H.
  - assert (n + 1 < start2) as neq1.
    { subst start2. apply make_htree_start_lt_next. }
    assert (start2 < next) as neq2.
    { subst next. apply make_htree_start_lt_next. }
    destruct H as [H | [H | H]].
    + subst n. split; lia.
    + rewrite <- eq_t1 in H. apply IH in H. rewrite eq_start2 in H. lia.
    + rewrite <- eq_t2 in H. apply IH in H. rewrite eq_next in H. lia.
  - destruct H as [y_ge_n y_lt_next].
    apply le_lt_or_eq in y_ge_n. destruct y_ge_n as [y_gt_n | y_eq_n].
    2:{ subst n. now left. }
    right.
    destruct (le_lt_dec start2 y) as [y_gt_s2 | y_lt_s2].
    + right. rewrite <- eq_t2. apply IH. lia.
    + left. rewrite <- eq_t1. apply IH. lia.
Qed.

Theorem make_htree_aux_is_pwdiff (h n : nat)
  : htree_is_pwdiff (snd (make_htree_aux h n)).
Proof.
  generalize dependent n.
  induction h as [| h1 IH]; intro n; [reflexivity|].
  simpl.
  destruct (make_htree_aux h1 (n + 1)) as (start2, t1) eqn:eq1.
  destruct (make_htree_aux h1 start2) as (next, t2) eqn:eq2.
  apply (f_equal fst) in eq1 as eq_start2. simpl in eq_start2.
  apply (f_equal fst) in eq2 as eq_next. simpl in eq_next.
  apply (f_equal snd) in eq1 as eq_t1. simpl in eq_t1.
  apply (f_equal snd) in eq2 as eq_t2. simpl in eq_t2.
  simpl. repeat split.
  - rewrite <- eq_t1. apply (IH (n + 1)).
  - rewrite <- eq_t2. apply (IH start2).
  - intros y H eq. subst y. rewrite <- eq_t1 in H.
    apply make_htree_bounds in H. lia.
  - intros y H eq. subst y. rewrite <- eq_t2 in H.
    apply make_htree_bounds in H.
    pose (make_htree_start_lt_next h1 (n + 1)) as neq. lia.
  - intros y1 y2 H1 H2 eq.
    rewrite <- eq_t1 in H1. rewrite <- eq_t2 in H2.
    apply make_htree_bounds in H1, H2.
    rewrite eq_start2 in H1. rewrite eq_next in H2. lia.
Qed.

Theorem make_htree_is_pwdiff (h : nat) : htree_is_pwdiff (make_htree h).
Proof. apply make_htree_aux_is_pwdiff. Qed.

Theorem range_cons (n m : nat) : n :: range (S n) m = range n (S m).
Proof. reflexivity. Qed.

Theorem range_app (n1 n2 m1 m2 : nat)
  : n2 = n1 + m1 -> range n1 m1 ++ range n2 m2 = range n1 (m1 + m2).
Proof.
  generalize dependent n2.
  generalize dependent n1.
  induction m1 as [| m1' IH]; intros n1 n2 eq.
  - simpl. subst n2. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite (IH (S n1) n2); [reflexivity | lia].
Qed.

Theorem fold_double (n : nat) : n + (n + 0) = 2 * n.
Proof. reflexivity. Qed.

Theorem flat_make_htree_aux_is_range (h n : nat)
  : flat_htree_dfs (snd (make_htree_aux h n)) = range n (2^(S h) - 1).
Proof.
  generalize dependent n.
  induction h as [| h1 IH]; intro n; [reflexivity|].
  simpl make_htree_aux. rewrite Nat.pow_succ_r'.
  destruct (make_htree_aux h1 (n + 1)) as (start2, t1) eqn:eq1.
  destruct (make_htree_aux h1 start2) as (next, t2) eqn:eq2.
  apply (f_equal fst) in eq1 as eq_start2. simpl in eq_start2.
  apply (f_equal fst) in eq2 as eq_next. simpl in eq_next.
  apply (f_equal snd) in eq1 as eq_t1. simpl in eq_t1.
  apply (f_equal snd) in eq2 as eq_t2. simpl in eq_t2.
  simpl. rewrite <- eq_t1, <- eq_t2. rewrite !IH.
  rewrite fold_double, Nat.add_1_r, range_app, range_cons.
  - apply (f_equal (range n)). rewrite <- Nat.add_1_r.
    rewrite fold_double.
    replace (2^(S h1)) with (2 * 2^h1) by auto with arith.
    replace (2 * 2^h1 + (2 * 2^h1 + 0)) with (4 * 2^h1) by lia.
    replace (2 * 2^h1 - 1 + (2 * 2^h1 - 1)) with (4 * 2^h1 - 2) by lia.
    rewrite <- Nat.add_sub_swap. lia.
    rewrite Nat.mul_comm. apply pow_ge. lia.
  - rewrite <- eq_start2, make_htree_aux_fst_eq.
    rewrite Nat.add_sub_assoc; [| apply pow_ge_1]; lia.
Qed.

Theorem flat_make_htree_is_range (h : nat)
  : flat_htree_dfs (make_htree h) = range 0 (2^(S h) - 1).
Proof. apply flat_make_htree_aux_is_range. Qed.

Theorem cons_eq {X : Type} (x1 x2 : X) (xs1 xs2 : list X)
  : x1 = x2 -> xs1 = xs2 -> x1 :: xs1 = x2 :: xs2.
Proof. intros eq_x eq_xs. subst x2 xs2. reflexivity. Qed.

Theorem flat_htree_bfs_aux_Sh {X : Type} (h : nat)
        (ts : list (htree X (S h)))
  : flat_htree_bfs_aux ts
    = (map htree_x ts)
        ++ flat_htree_bfs_aux (fold_right (flat_htree_bfs_aux1 h) [] ts).
Proof. reflexivity. Qed.

Theorem flat_htree_bfs_aux_Sh_cons {X : Type} (h : nat)
        (t : htree X (S h)) (ts : list (htree X (S h)))
  : flat_htree_bfs_aux (t :: ts)
    = (htree_x t)
        :: (map htree_x ts)
        ++ (flat_htree_bfs_aux
              ((htree_t1 t)
                 :: (htree_t2 t)
                 :: (fold_right (flat_htree_bfs_aux1 h) [] ts))).
Proof. reflexivity. Qed.

Theorem flat_htree_bfs_aux0 {X : Type} (ts : list (htree X 0))
  : flat_htree_bfs_aux ts = map htree_x ts.
Proof. reflexivity. Qed.

Theorem pn_trees_range_x (h n0 m : nat)
  : map htree_x (map (pn_tree_aux h) (range n0 m))
    = range n0 m.
Proof.
  generalize dependent n0.
  induction m as [| m' IH]; [reflexivity|].
  intro n0. simpl. rewrite IH.
  destruct h as [| h']; reflexivity.
Qed.

Theorem pn_trees_range_second_layer (n0 m : nat)
  : map htree_x
        (fold_right (flat_htree_bfs_aux1 0) []
                    (map (pn_tree_aux 1) (range n0 m)))
    = range (2 * n0 + 1) (2 * m).
Proof.
  generalize dependent n0.
  induction m as [| m1 IH]; intro n0; [reflexivity|].
  simpl. rewrite IH. simpl. apply cons_eq; [reflexivity|].
  replace (m1 + S (m1 + 0)) with (S (2 * m1)) by lia. simpl.
  apply cons_eq; [lia|]. f_equal. lia.
Qed.

Theorem flat_htree_bfs_aux_nil (X : Type) (h : nat)
  : @flat_htree_bfs_aux X h [] = [].
Proof.
  induction h as [| h' IH]; [reflexivity|].
  simpl. exact IH.
Qed.

Theorem pn_trees_range_next_layers (h n0 m : nat)
  : fold_right (flat_htree_bfs_aux1 h) []
               (map (pn_tree_aux (S h)) (range n0 m))
    = map (pn_tree_aux h) (range (2 * n0 + 1) (2 * m)).
Proof.
  generalize dependent n0.
  induction m as [| m' IH]; intro n0; [reflexivity|].
  simpl in *. rewrite IH. unfold flat_htree_bfs_aux1. simpl.
  apply cons_eq; [reflexivity|]. rewrite (Nat.add_succ_r m').
  simpl. apply cons_eq.
  - f_equal. lia.
  - f_equal. f_equal. lia.
Qed.

Theorem flat_htree_bfs_aux_pn_tree_Sh_head (h n0 m : nat)
  : flat_htree_bfs_aux (map (pn_tree_aux (S h)) (range n0 m))
    = (range n0 m)
        ++ (flat_htree_bfs_aux (map (pn_tree_aux h)
                                    (range (2 * n0 + 1) (2 * m)))).
Proof.
  rewrite flat_htree_bfs_aux_Sh, pn_trees_range_x. apply app_inv_head_iff.
  rewrite pn_trees_range_next_layers. reflexivity.
Qed.

Theorem flat_htree_bfs_aux_pn_tree_Sh_last (h n0 m : nat)
  : flat_htree_bfs_aux (map (pn_tree_aux (S h)) (range n0 m))
    = (flat_htree_bfs_aux
         (map (pn_tree_aux h) (range n0 m)))
        ++ range (2^(S h) * (n0 + 1) - 1) (m * 2^(S h)).
Proof.
  generalize dependent n0.
  generalize dependent m.
  induction h as [| h1 IH]; intros m n0.
  - rewrite flat_htree_bfs_aux_Sh, !flat_htree_bfs_aux0, !pn_trees_range_x.
    apply app_inv_head_iff. rewrite pn_trees_range_second_layer.
    f_equal; simpl; lia.
  - rewrite flat_htree_bfs_aux_pn_tree_Sh_head, IH.
    rewrite flat_htree_bfs_aux_pn_tree_Sh_head.
    rewrite <- app_assoc. repeat apply app_inv_head_iff.
    f_equal; simpl; try lia.
Qed.

Compute (flat_htree_bfs (pn_tree_aux 1 1)).
(* = [1; 3; 4] : list nat *)
Compute range (2^2 * (1 + 1) - 1) (2^2).
(* = [7; 8; 9; 10] : list nat *)
Compute (flat_htree_bfs (pn_tree_aux 2 1)).
(* = [1; 3; 4; 7; 8; 9; 10] : list nat *)

Theorem flat_pn_tree_Sh (h n : nat)
  : flat_htree_bfs (pn_tree_aux (S h) n)
    = (flat_htree_bfs (pn_tree_aux h n))
        ++ range (2^(S h) * (n + 1) - 1) (2^(S h)).
Proof.
  unfold flat_htree_bfs.
  pose (flat_htree_bfs_aux_pn_tree_Sh_last h n 1) as H.
  simpl in *. rewrite H. rewrite !fold_double.
  apply app_inv_head_iff. f_equal. lia.
Qed.

Theorem flat_pn_tree_is_range (h : nat)
  : flat_htree_bfs (pn_tree h) = range 0 (2^(S h) - 1).
Proof.
  unfold pn_tree. induction h as [| h' IH].
  { unfold flat_htree_bfs. reflexivity. }
  rewrite flat_pn_tree_Sh, IH. rewrite range_app; [|lia].
  remember (S h') as h eqn:eq_h. rewrite Nat.pow_succ_r'.
  f_equal. lia.
Qed.

(* Exercise 6.48 * Define inductively the type [binary_word]
   used in section 4.1.1.2 and define recursively
   the function [binary_word_concat]. *)
Inductive binary_word : nat -> Set
  := BW_empty : binary_word 0
   | BW_cons : forall n : nat, bool -> binary_word n -> binary_word (S n).

Arguments BW_cons {n} _ _.

Fixpoint binary_word_concat {n1 n2 : nat}
         (w1 : binary_word n1) (w2 : binary_word n2)
  : binary_word (n1 + n2)
  := match w1 in binary_word n return binary_word (n + n2) with
     | BW_empty => w2
     | BW_cons b w1' => BW_cons b (binary_word_concat w1' w2)
     end.

Fixpoint bin_list_to_word (bs : list bool) : binary_word (length bs)
  := match bs as x return binary_word (length x) with
     | nil => BW_empty
     | cons b bs' => BW_cons b (bin_list_to_word bs')
     end.

Example binary_word_concat_ex
  : (binary_word_concat (bin_list_to_word [true; false; true])
                        (bin_list_to_word [false; false]))
    = (bin_list_to_word [true; false; true; false; false]).
Proof. reflexivity. Qed.

(* Exercise 6.49 ** Define the function [binary_word_or]
   that computes the bit-wise "or" operation of two words
   of the same length (like the "|" operator in the C language). *)

Definition convert_bw_len (n1 n2 : nat) (H : S n2 = S n1)
           (xs : binary_word n1) : binary_word n2.
apply eq_add_S in H. rewrite H. exact xs.
Defined.

Print convert_bw_len.
(* convert_bw_len =
   fun (n1 n2 : nat) (H : S n2 = S n1) (xs : binary_word n1)
   => let H0 : n2 = n1 := eq_add_S n2 n1 H
      in eq_rec_r (fun n3 : nat => binary_word n3) xs H0
   : forall n1 n2 : nat, S n2 = S n1 -> binary_word n1 -> binary_word n2
 *)

Fixpoint binary_word_or {n : nat} (xs ys : binary_word n) : binary_word n
  := match xs in binary_word m1 return binary_word m1 -> binary_word m1 with
     | BW_empty => fun _ => BW_empty
     | @BW_cons n1 x xs'
       => fun ys : binary_word (S n1)
         => match ys in binary_word m2 return m2 = S n1 -> binary_word m2 with
           | BW_empty => fun _ => BW_empty
           | @BW_cons n2 y ys'
             => fun H => BW_cons (x || y)
                             (binary_word_or
                                (convert_bw_len n1 n2 H xs') ys')
           end (eq_refl (S n1))
     end ys.

Theorem binary_word_or_idempotent (n : nat) (xs : binary_word n)
  : binary_word_or xs xs = xs.
Proof.
  induction xs as [| n' b xs' IH]; [reflexivity|].
  simpl. unfold convert_bw_len. simpl.
  replace (b || b) with b.
  2:{ destruct b; reflexivity. }
  f_equal.
  replace (eq_rec_r (fun n2 : nat => binary_word n2) xs' eq_refl) with xs'.
  2:{ unfold eq_rec_r. reflexivity. }
  apply IH.
Qed.

(* Do the same exercises (last two), but considering vectors *)
Require Import Vector.
Definition bword := t bool.
Definition bw_concat := @append bool.

Fixpoint binary_word_to_bword {n : nat} (w : binary_word n)
         {struct w} : bword n
  := match w with
     | BW_empty => nil bool
     | @BW_cons n' b w' => cons bool b n' (binary_word_to_bword w')
     end.

Fixpoint bword_to_binary_word {n : nat} (w : bword n)
         {struct w} : binary_word n
  := match w with
     | nil _ => BW_empty
     | cons _ b n' w' => @BW_cons n' b (bword_to_binary_word w')
     end.

Theorem binary_word_to_bword_inv (n : nat) (w : binary_word n)
  : bword_to_binary_word (binary_word_to_bword w) = w.
Proof.
  induction w as [| n' b w' IH]; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Theorem bword_to_binary_word_inv (n : nat) (w : bword n)
  : binary_word_to_bword (bword_to_binary_word w) = w.
Proof.
  induction w as [| b n' w' IH]; [reflexivity|].
  simpl. rewrite IH. reflexivity.
Qed.

Theorem bw_concat_correct (n1 n2 : nat) (w1 : bword n1) (w2 : bword n2)
  : bw_concat n1 n2 w1 w2
    = binary_word_to_bword
        (binary_word_concat (bword_to_binary_word w1)
                            (bword_to_binary_word w2)).
Proof.
  induction w1 as [| b n1' w1' IH].
  - simpl. rewrite bword_to_binary_word_inv. now unfold bw_concat.
  - simpl. rewrite <- IH. unfold bw_concat. reflexivity.
Qed.

Definition bw_or {n : nat} (w1 w2 : bword n) : bword n
  := map2 orb w1 w2.

Theorem bw_or_correct {n : nat} (w1 w2 : bword n)
  : bw_or w1 w2
    = binary_word_to_bword
        (binary_word_or (bword_to_binary_word w1)
                        (bword_to_binary_word w2)).
Proof.
  unfold bword in *.
  generalize dependent w2.
  generalize dependent w1.
  generalize dependent n.
  apply rect2; [reflexivity|].
  intros n' w1' w2' IH x1 x2. simpl.
  unfold convert_bw_len. simpl.
  unfold eq_rec_r. simpl.
  rewrite <- IH. reflexivity.
Qed.

Theorem bw_or_idempotent (n : nat) (xs : bword n) : bw_or xs xs = xs.
Proof.
  rewrite bw_or_correct, binary_word_or_idempotent.
  now rewrite bword_to_binary_word_inv.
Qed.

(* See also Consider the following definition,
   very similar to Standard Library's definition: *)
Section Vector_definitions.

  Variable X : Type.

  Inductive vector : nat -> Type
    := vnil : vector 0
     | vcons (x : X) (n : nat) (v : vector n) : vector (S n).

  (* Define the functions that return respectively
     the head and the tail of a non-empty vector,
     as direct applications of the recursor vector_rect> *)

  Definition vhd {n : nat} (v : vector (S n)) : X
    := match v in vector m
             return (match m with O => unit | S _ => X end)
       with
       | vnil => tt
       | vcons x n' v' => x
       end.

  Definition vtl {n : nat} (v : vector (S n)) : vector n
    := match v in vector m
             return (match m with O => unit | S m' => vector m' end)
       with
       | vnil => tt
       | vcons x n' v' => v'
       end.

  Definition v_Id (n : nat) : vector n -> vector n
    := match n with
       | 0 => fun v => vnil
       | S p => fun v => vcons (vhd v) p (vtl v)
       end.

  Compute fun v : vector 0 => v_Id 0 v.
  (*   = fun _ : vector 0 => vnil : vector 0 -> vector 0 *)

  Lemma v_Id_eq (n : nat) (v : vector n) : v = v_Id n v.
  Proof using.
    pattern n, v. apply vector_rect.
    - reflexivity.
    - intros. reflexivity.
  Qed.

  Lemma vector0 (v : vector 0) : v = vnil.
  Proof using.
    change vnil with (v_Id 0 v).
    apply v_Id_eq.
  Qed.

  Lemma vector_S (n : nat) (v : vector (S n)) : v = vcons (vhd v) n (vtl v).
  Proof using.
    change (vcons (vhd v) n (vtl v)) with (v_Id (S n) v).
    apply v_Id_eq.
  Qed.
End Vector_definitions.

Arguments vnil {X}.
Arguments vcons {X}.
Arguments vhd {X} {n}.
Arguments vtl {X} {n}.

Example vhd_ex : vhd (vcons 42 0 vnil) = 42.
Proof. reflexivity. Qed.

Example vtl_ex : vtl (vcons 42 1 (vcons 22 0 vnil)) = vcons 22 0 vnil.
Proof. reflexivity. Qed.

(* Exercise 6.50 ** Define a function with a dependent type
   that returns [true] for natural numbers of the form [4*n + 1],
   [false] for numbers of the form [4*n + 3],
   and [n] for numbers of the form [2*n]. *)

Fixpoint dep_fn_type (n : nat) : Set
  := match n with
     | 0 => nat
     | 1 => bool
     | (S (S n')) => dep_fn_type n'
     end.

Fixpoint dep_fn (n : nat) : dep_fn_type n
  := match n with
     | 0 => 0
     | 1 => true
     | 2 => 1
     | 3 => false
     | S (S (S (S n'))) => dep_fn n'
     end.

Example dep_fn_ex6 : dep_fn 6 = 1.
Proof. reflexivity. Qed.

Example dep_fn_ex7 : dep_fn 7 = false.
Proof. reflexivity. Qed.

Example dep_fn_ex9 : dep_fn 9 = true.
Proof. reflexivity. Qed.
