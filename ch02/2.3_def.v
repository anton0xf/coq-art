(* 2.3 Declarations and Definitions *)
Require Import Arith ZArith Bool.
Open Scope Z_scope.

Parameter max_int : Z.
Definition min_int := 1 - max_int.
Print min_int.

(* Definition cube := fun z : Z => z*z*z. *)
(* Definition cube (z : Z) := z*z*z. *)
Definition cube z := z*z*z.
Print cube.

(* Definition Z_thrice : (Z -> Z) -> Z -> Z := fun f z => f (f (f z)). *)
Definition Z_thrice (f : Z -> Z) (z : Z) := f (f (f z)).
Print Z_thrice.

Definition plus9 := Z_thrice (Z_thrice (Z.add 1)).
Print plus9.
Compute plus9 2. (* => 11 *)

(* Exercise 2.5.
   Write a function that takes five integer arguments and returns their sum. *)
Definition sum5 x1 x2 x3 x4 x5 := x1 + x2 + x3 + x4 + x5.

Section binomial_def.
  Variables a b : Z.
  Definition monomial (z:Z) := a.
  Print monomial.
  (* monomial = fun _ : Z => a : Z -> Z *)
  Definition binomial (z:Z) := a*z + b.
  Print binomial.
  (* binomial = fun z : Z => a * z + b : Z -> Z *)
  Section trinomial_def.
    Variable c : Z.
    Definition trinomial z:Z := (binomial z)*z + c.
    Print trinomial.
    (* trinomial = fun z : Z => binomial z * z + c : Z -> Z *)
  End trinomial_def.
  Print trinomial.
  (* trinomial = fun c z : Z => binomial z * z + c : Z -> Z -> Z *)
End binomial_def.

Print monomial.
(* monomial = fun a _ : Z => a : Z -> Z -> Z *)
Print binomial.
(* binomial = fun a b z : Z => a * z + b : Z -> Z -> Z -> Z *)
Print trinomial.
(* trinomial = fun a b c z : Z => binomial a b z * z + c : Z -> Z -> Z -> Z -> Z *)

(* Exercise 2.6.
   Use the section mechanism to build a function that takes five
   arguments and returns their sum, without explicitly writing any abstractions. *)
Section s5.
  Variable x1 x2 x3 x4 x5 : Z.
  Definition sum5' := x1 + x2 + x3 + x4 + x5.
End s5.
Print sum5'.
(* sum5' = fun x1 x2 x3 x4 x5 : Z => x1 + x2 + x3 + x4 + x5
           : Z -> Z -> Z -> Z -> Z -> Z *)

Section h_def.
  Variables a b : Z.
  Let s:Z := a+b.
  Let d:Z := a-b.
  Definition h:Z := s*s + d*d.
End h_def.
Print h.
(* h = fun a b : Z => let s := a + b in
                      let d := a - b in
                      s * s + d * d
       : Z -> Z -> Z *)
