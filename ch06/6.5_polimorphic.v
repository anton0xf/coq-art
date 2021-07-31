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
Inductive htree (A : Type) : nat -> Type
  := hleaf : A -> htree A 0
   | hnode : forall n : nat, A -> htree A n -> htree A n -> htree A (S n).

Arguments hleaf {A}.
Arguments hnode {A}.

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

(* Exercise 6.47
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

(* authors' solution (with Z replaced by [nat])*)
Fixpoint make_htree_aux (h start : nat) : nat * htree nat h
  := match h with
     | 0 => (start + 1, hleaf start)
     | S h' => let p := make_htree_aux h' (start + 1) in
              let q := make_htree_aux h' (fst p) in
              (fst q, hnode h' start (snd p) (snd q))
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
