(* 2.6 Realizing Specifications *)
Require Import Arith.

Section realization.
  Variables (A B : Set).
  Let spec: Set := (((A -> B) -> B) -> B) -> A -> B.
  Let realization : spec
    := fun (f : ((A -> B) -> B) -> B) (a : A)
       => f (fun (g : A -> B) => g a).
End realization.

