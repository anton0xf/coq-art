(* 2.4 Computing *)
Require Import Arith ZArith Bool.
Open Scope Z_scope.

Definition Zsqr (z:Z) : Z := z*z.
Definition my_fun (f : Z -> Z) (z : Z) : Z := f (f z).
Eval cbv delta [my_fun Zsqr] in (my_fun Zsqr).
(* = (fun (f : Z -> Z) (z : Z) => f (f z)) 
     (fun z : Z => z * z) 
   : Z -> Z *)

Eval cbv delta [my_fun] in (my_fun Zsqr).
(* = (fun (f : Z -> Z) (z : Z) => f (f z)) Zsqr
   : Z -> Z *)

Eval cbv beta delta [my_fun Zsqr] in (my_fun Zsqr).
(* = fun z : Z => z * z * (z * z)
   : Z -> Z *)

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

Eval cbv delta [h] zeta in h.
(* = fun a b : Z => (a + b) * (a + b) + (a - b) * (a - b)
   : Z -> Z -> Z *)

Eval cbv beta delta [h] in (h 56 78).
(* = let s := 56 + 78 in
     let d := 56 - 78 in s * s + d * d
   : Z *)

Eval cbv beta zeta delta [h] in (h 56 78).
(* = (56 + 78) * (56 + 78) + (56 - 78) * (56 - 78) : Z *)

Eval compute in (h 56 78). (* = 18440 : Z *)
Eval compute in (my_fun Zsqr 3). (* = 81 : Z *)

(* Exercise 2.7
Write the function that corresponds to the polynomial 2*x^2 + 3*x + 3
on relative integers, using λ-abstraction
and the functions Zplus and Zmult provided in the ZArith library of Coq.
Compute the value of this function on integers 2, 3, and 4. *)
Definition ex_poly (x : Z) := 2*x*x + 3*x + 3.
Compute ((ex_poly 2), (ex_poly 3), (ex_poly 4)).
(* = (17, 30, 47) : Z * Z * Z *)
