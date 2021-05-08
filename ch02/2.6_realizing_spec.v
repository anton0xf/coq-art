(* 2.6 Realizing Specifications *)
Require Import Arith.

Section realization.
  Variables (A B : Set).
  Let spec: Set := (((A -> B) -> B) -> B) -> A -> B.
  Let realization : spec := fun f a => f (fun g => g a).
End realization.

