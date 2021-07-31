Require Export ZArith List Arith Bool Lia.
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
     | hleaf _ x => Z_bnode x Z_leaf Z_leaf
     | hnode _ p v t1 t2
       => Z_bnode v (htree_to_btree p t1) (htree_to_btree p t2)
     end.

Fixpoint invert (A : Type) (n : nat) (t : htree A n) {struct t} : htree A n
  := match t in htree _ x return htree A x with
     | hleaf _ v => hleaf A v
     | hnode _ p v t1 t2 => hnode A p v (invert A p t2) (invert A p t1)
     end.

(* Exercise 6.46 **
   Prove one of the injection lemmas for the hnode construct: *)
Open Scope nat_scope.
Definition htree_left (X : Type) (n : nat) (t : htree X (S n)) : htree X n
  := match t with
     | hnode _ n v t1 t2 => t1
     end.

Theorem injection_left_htree (n : nat) (t1 t2 t3 t4 : htree nat n)
   : hnode nat n O t1 t2 = hnode nat n O t3 t4 ->  t1 = t3.
Proof.
  intro H. apply (f_equal (htree_left nat n)) in H. apply H.
Qed.

(* authors' solution *)
Definition first_of_htree (A : Type) (n : nat)
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

Check (first_of_htree nat 0 (hleaf nat 1)
                      (hnode nat 0 2 (hleaf nat 3) (hleaf nat 4))).
(* first_of_htree nat 0 (hleaf nat 1)
       (hnode nat 0 2 (hleaf nat 3) (hleaf nat 4))
   : htree nat 0 *)

Compute (first_of_htree nat 0 (hleaf nat 1)
                        (hnode nat 0 2 (hleaf nat 3) (hleaf nat 4))).
(* = hleaf nat 3 : htree nat 0 *)

Theorem injection_first_htree (n : nat) (t1 t2 t3 t4 : htree nat n)
  : hnode nat n O t1 t2 = hnode nat n O t3 t4 -> t1 = t3.
Proof.
  intro H.
  change
    (first_of_htree nat n t1 (hnode nat n O t1 t2)
     = first_of_htree nat n t1 (hnode nat n O t3 t4)).
  now rewrite H.
Qed.
