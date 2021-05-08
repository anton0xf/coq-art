(* 2.6 Realizing Specifications *)
Require Import Arith ZArith Bool.
Open Scope Z_scope.

Section realization.
  Variables (A B : Set).
  Let spec: Set := (((A -> B) -> B) -> B) -> A -> B.
  Let realization : spec := fun f a => f (fun g => g a).
  Print realization.
  (* realization : spec :=
     fun (f : ((A -> B) -> B) -> B) (a : A)
         => f (fun g : A -> B => g a) *)

  Example spec_proof : spec.
  Proof using A B.
    intros f a. apply f. intro g. apply g, a.
  Qed.

  Print spec_proof.
  (* spec_proof : spec =
     fun (f : ((A -> B) -> B) -> B) (a : A)
         => f (fun g : A -> B => g a) *)

End realization.

Definition nat_fun_to_Z_fun : Set := (nat -> nat) -> Z -> Z.

Definition absolute_fun : nat_fun_to_Z_fun
  := fun f z => Z_of_nat (f (Z.abs_nat z)).

Definition always_O : nat_fun_to_Z_fun
  := fun _ _ => 0%Z.

Definition to_marignan : nat_fun_to_Z_fun
  := fun _ _ => 1515%Z.

Definition ignore_f : nat_fun_to_Z_fun
  := fun _ z => z.

Definition from_marignan : nat_fun_to_Z_fun
  := fun f _ => Z_of_nat (f 1515%nat).
