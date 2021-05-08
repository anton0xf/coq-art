(* 2.5 Types, Sorts, and Universes *)
Require Import Arith ZArith Bool.
Open Scope Z_scope.

Check Z. (* Z : Set *)
Check ((Z -> Z) -> nat -> nat).
(* (Z -> Z) -> nat -> nat : Set *)

Section domain.
  Variables (D : Set) (op : D -> D -> D) (sym : D -> D) (e : D).
  Let diff : D -> D -> D
    := fun (x y : D) => op x (sym y).
  Check diff. (* diff : D -> D -> D *)
  Definition Diff := diff.
End domain.

Check Diff.
(* Diff : forall D : Set, (D -> D -> D) -> (D -> D) -> D -> D -> D *)
