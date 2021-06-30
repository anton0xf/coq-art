Require Export ZArith List Arith Bool.

Inductive month : Set
  := January | February | March | April | May | June
     | July | August | September | October | November | December.

(* Exercise 6.1
   Define an inductive type for seasons and then use the function
   [month_rec] to define a function that maps every month to the season that
   contains most of its days. *)
Inductive season : Set := Winter | Spring | Summer | Fall.

Check season_rec.
(* season_rec : forall P : season -> Set,
   P Winter -> P Spring -> P Summer -> P Fall
   -> forall s : season, P s *)

Definition is_winter : season -> bool.
  intro s. apply season_rec.
  - (* Winter *) exact true.
  - (* Spring *) exact false.
  - (* Summer *) exact false.
  - (* Fall   *) exact false.
  - exact s.
Defined.

Print is_winter.
(* is_winter : season -> bool
   := fun s : season
      => season_rec (fun _ : season => bool) true false false false s *)

Compute (is_winter Winter). (* = true : bool *)
Compute (is_winter Fall). (* = false : bool *)

Definition season_of_month : month -> season
  := month_rec (fun _ : month => season)
               Winter Winter
               Spring Spring Spring
               Summer Summer Summer
               Fall Fall Fall
               Winter.

Compute (season_of_month December). (* = Winter : season *)
Compute (season_of_month July). (* = Summer : season *)

(* Exercise 6.2
   What are the types of [bool_ind] and [bool_rec] that are
   generated by the Coq system for the type bool? *)
Check bool_ind.
(* bool_ind : forall P : bool -> Prop,
     P true -> P false -> forall b : bool, P b *)

(* 6.1.2 Simple Reasoning and Computing *)
Theorem month_equal (m : month)
 : m=January \/ m=February \/ m=March \/ m=April \/ m=May \/ m=June
   \/ m=July \/ m=August \/  m=September \/ m=October \/ m=November
   \/ m=December.
Proof. destruct m; auto 12. Qed.

(** explicit use of month_ind: *)
Theorem month_equal' (m : month)
 : m=January \/ m=February \/ m=March \/ m=April
   \/ m=May \/ m=June \/ m=July \/ m=August
   \/ m=September \/ m=October \/ m=November \/ m=December.
Proof. pattern m. apply month_ind; auto 12. Qed.

(* Exercise 6.3 Prove in two different ways the following theorem:
   1. Give directly a proof term, with occurences of
      bool_ind, or_introl, or_intror and refl_equal.
   2. Use the following tactics :
      pattern, apply, left, right, and reflexivity. *)
Theorem bool_cases (b : bool) : b = true \/ b = false.
Proof.
  exact (bool_ind (fun c => c = true \/ c = false)
                  (or_introl eq_refl)
                  (or_intror eq_refl) b).
Qed.

Theorem bool_cases' (b : bool) : b = true \/ b = false.
Proof. pattern b. apply bool_ind; [left | right]; reflexivity. Qed.

Theorem bool_cases'' (b : bool) : b = true \/ b = false.
Proof. destruct b; [left | right]; reflexivity. Qed.

(* 6.1.4 Pattern Matching *)
Check (fun b : bool => match b with false => 45 | true => 33 end).
(* fun b : bool => if b then 33 else 45 : bool -> nat *)

Definition month_length (leap : bool) (m : month) : nat
  := match m with
     | January => 31 | February => if leap then 29 else 28
     | March => 31   | April => 30    | May => 31  | June => 30
     | July => 31    | August => 31   | September => 30
     | October => 31 | November => 30 | December => 31
     end.

Definition month_length' (leap : bool)
  := month_rec (fun _ : month => nat)
               31 (if leap then 29 else 28)
               31 30 31 30 31 31 30 31 30 31.

Definition month_length'' (leap : bool) (m : month)
  := match m with
     | February => if leap then 29 else 28
     | April  | June  | September | November => 30
     | _  => 31
     end.

Example month_length_eq1 : month_length = month_length'.
Proof. reflexivity. Qed.

Example month_length_eq2 : month_length = month_length''.
Proof. reflexivity. Qed.

Eval compute in (fun leap => month_length leap November).
(* = fun _ : bool => 30 : bool -> nat *)

Example length_february : month_length false February = 28.
Proof. reflexivity. Qed.

(* Exercise 6.4
   Using the type introduced for seasons in Exercise 6.1 page 139,
   write the function that maps any month to the season
   that contains most of its days, this time
   using the pattern matching construct. *)

Definition season_of_month' (m : month) : season
  := match m with
     | December | January | February => Winter
     | March | April | May => Spring
     | June | July | August => Summer
     | September | October | November => Fall
     end.

Example season_of_month_eq : season_of_month = season_of_month'.
Proof. reflexivity. Qed.

(* Exercise 6.5
   Write the function that maps every month that has an even
   number of days to the boolean value true and the others to false. *)
Definition is_even_days_in_month (leap : bool) (m : month)
  := Nat.even (month_length leap m).

(* Exercise 6.6
   Define the functions associated with the following boolean connectives:
   Notice that these functions are already defined in the standard library
   under the names negb, orb, andb, xorb and Bool.eqb. *)
Definition bool_not (b : bool) : bool := if b then false else true.
Definition bool_or (a b : bool) : bool
  := if a then true else
       if b then true else false.
Definition bool_and (a b : bool) : bool := if a then b else false.
Definition bool_xor (a b : bool) : bool
  := if a then bool_not b else b.
Definition bool_eq (a b : bool) : bool
  := if a then b else bool_not b.

(* Prove the following theorems: *)
Theorem bool_xor_not_eq (b1 b2 : bool)
  : bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof. destruct b1, b2; reflexivity. Qed.

Theorem bool_not_and (b1 b2 : bool)
  : bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).
Proof. destruct b1, b2; reflexivity. Qed.

Theorem bool_not_not (b : bool) : bool_not (bool_not b) = b.
Proof. destruct b; reflexivity. Qed.

Theorem bool_tex (b : bool) : bool_or b (bool_not b) = true.
Proof. destruct b; reflexivity. Qed.

Theorem bool_eq_reflect (b1 b2 : bool) : bool_eq b1 b2 = true -> b1 = b2.
Proof.
  destruct b1, b2; simpl; intro H;
    try rewrite H; reflexivity.
Qed.

Theorem bool_eq_reflect2 (b1 b2 : bool) : b1 = b2 -> bool_eq b1 b2 = true.
Proof. intro H. subst b2. destruct b1; reflexivity. Qed.

Theorem bool_not_or (b1 b2 : bool)
  : bool_not (bool_or b1 b2) = bool_and (bool_not b1) (bool_not b2).
Proof. destruct b1, b2; reflexivity. Qed.

Theorem bool_or_and_distr (b1 b2 b3 : bool)
  : bool_or (bool_and b1 b3) (bool_and b2 b3) = bool_and (bool_or b1 b2) b3.
Proof. destruct b1, b2, b3; reflexivity. Qed.

(* 6.1.5 Record Types *)
Open Scope Z_scope.

Inductive plane : Set := point : Z -> Z -> plane.
(*
plane is defined
plane_rect is defined
plane_ind is defined
plane_rec is defined
plane_sind is defined
*)

Check point. (* point : Z -> Z -> plane *)
Check plane_ind.
(* plane_ind : forall P : plane -> Prop,
   (forall z z0 : Z, P (point z z0)) -> forall p : plane, P p *)

Definition abscissa (p : plane) : Z
  := match p with point x y => x end.
Check abscissa. (* abscissa : plane -> Z *)

Reset plane. (* also reset [abscissa] *)

Record plane : Set := point {abscissa : Z; ordinate : Z}.
(*
plane is defined
abscissa is defined
ordinate is defined
*)
Print plane.
(* Record plane : Set := point { abscissa : Z;  ordinate : Z } *)
Check point. (* point : Z -> Z -> plane *)
Check abscissa. (* abscissa : plane -> Z *)
Print abscissa.
(* abscissa : plane -> Z
   := fun p : plane => let (abscissa, _) := p in abscissa *)

(* Exercise 6.7 What is the type of plane_rec? *)
(* Check plane_rec. *)
(* Error: The reference plane_rec was not found in the current environment. *)

(* Exercise 6.8
   Define a function that computes the "Manhattan" distance for
   points of the plane (the Manhattan distance
   is the sum of the absolute values of differences of coordinates). *)
Definition manhattan_distance (p1 p2 : plane) : Z
  := let (x1, y1) := p1 in
     let (x2, y2) := p2 in
     Z.abs (x1 - x2) + Z.abs (y1 - y2).

Check (point 1 2).
Check (point 1 (-2)).

Example manhattan_distance_ex
  : manhattan_distance (point (-1) (-2)) (point 4 2) = 9.
Proof. reflexivity. Qed.

(* 6.1.6 Records with Variants *)
Inductive vehicle : Set
  := bicycle (* [number of seats] *) : nat -> vehicle
   | motorized (* [number of seats, number of wheels] *)
     : nat -> nat -> vehicle.

Check vehicle_ind.
(* vehicle_ind : forall P : vehicle -> Prop,
   (forall n : nat, P (bicycle n)) ->
   (forall n n0 : nat, P (motorized n n0)) -> forall v : vehicle, P v *)

Definition nb_seats (v : vehicle) : nat
  := match v with
     | bicycle n => n
     | motorized n _ => n
     end.

Definition nb_wheels (v : vehicle) : nat
  := match v with
     | bicycle _ => 2
     | motorized _ m => m
     end.

(* Exercise 6.9
   What is the type of [vehicle_rec]? Use this function to define
   an equivalent to [nb_seats]. *)
Check vehicle_rec.
(* vehicle_rec : forall P : vehicle -> Set,
   (forall n : nat, P (bicycle n)) ->
   (forall n n0 : nat, P (motorized n n0)) -> forall v : vehicle, P v *)

Definition nb_seats' : vehicle -> nat
  := vehicle_rec (fun _ : vehicle => nat)
                 (fun n => n)
                 (fun n _ => n).

Example nb_seats_eq : nb_seats = nb_seats'.
Proof. reflexivity. Qed.

(* 6.2 Case-Based Reasoning *)
Open Scope nat_scope.
Theorem at_least_28 (leap : bool) (m : month)
  : 28 <= month_length leap m.
Proof. case m, leap; simpl; auto with arith. Qed.

Theorem at_least_28' (leap : bool) (m : month)
  : 28 <= month_length leap m.
Proof.
  case m, leap; simpl;
    repeat ( try apply le_n; apply le_S ).
Qed.

Print at_least_28.
(* at_least_28 : forall (leap : bool) (m : month), 28 <= month_length leap m
  := fun (leap : bool) (m : month) =>
       match m as m0 return (28 <= month_length leap m0) with
       | January =>
         if leap as b return (28 <= month_length b January)
         then le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
         else le_S 28 30 (le_S 28 29 (le_S 28 28 (le_n 28)))
       | February =>
         if leap as b return (28 <= month_length b February)
         then le_S 28 28 (le_n 28)
         else le_n 28
       ...
       end. *)

(* 6.2.2.1 The discriminate Tactic *)
Definition next_month (m : month)
  := match m with
     | January => February  | February => March | March => April
     | April => May         | May => June       | June => July
     | July => August       | August => September
     | September => October | October => November
     | November => December | December => January
     end.

Theorem next_august_then_july (m : month) : next_month m = August -> m = July.
Proof.
  case m; simpl; intros H;
    (reflexivity || discriminate H).
Qed.

(* 6.2.2.2 ** The Inner Workings of discriminate *)
Theorem not_January_eq_February : January <> February.
Proof. discriminate. Qed.

(* not using [discriminate] *)
Theorem not_January_eq_February' : January <> February.
Proof.
  unfold not. intros H.
  change ((fun m : month
           => match m with | January => True | _ => False end)
            February).
  now rewrite <- H.
Qed.

(* not using [change], [rewrite] and [reflexivity] *)
Theorem not_January_eq_February'' : January <> February.
Proof.
  unfold not. intros H.
  pose (f := (fun m : month
              => match m with
                 | January => True
                 | _ => False end)).
  apply (eq_ind (f February) (fun P => P)).
  - apply (eq_ind January f).
    + unfold f. apply I.
    + exact H.
  - unfold f. apply eq_refl.
Qed.

(* Exercise 6.10
   Define a function [is_January] that maps [January] to [True]
   and any other month to [False], using the function [month_rect]. *)
Definition is_January' (m : month) : Prop
  := match m with
     | January => True
     | _ => False
     end.

Definition is_January : month -> Prop
  := month_rect (fun _ => Prop)
                True
                False False False False False False False False
                False False False.

Example is_January_eq : is_January = is_January'.
Proof. reflexivity. Qed.

(* Try to automate applying [month_rect (fun _ => Prop) True]
   to [False] 11 times *)
Definition add_arg_type (A B : Type) : Type := A -> B.
Compute ((add_arg_type Prop) ((add_arg_type Prop) nat)).
(* = Prop -> Prop -> nat : Type *)

Fixpoint iterate (A : Type) (f : A -> A) (n : nat) (a : A) : A
  := match n with
     | O => a
     | S n' => iterate A f n' (f a)
     end.
Compute (iterate nat S 3 O). (* = 3 : nat *)
Compute (iterate Type (add_arg_type Prop) 3 nat).
(* = Prop -> Prop -> Prop -> nat : Type *)

Definition add_n_arg_types (A B : Type) (n : nat) : Type
  := (iterate Type (add_arg_type A) n B).
Compute (add_n_arg_types Prop nat 3).
(* = Prop -> Prop -> Prop -> nat : Type *)
Compute (add_n_arg_types Prop nat 0). (* = nat : Type *)

(* TODO Attempt failed *)
(* Fixpoint repeat_arg (A B : Type) (a : A)
         (n : nat) (f : add_n_arg_types A B n) : B
  := match n with
     | O => f (* The term "f" has type "add_n_arg_types A B n"
                 while it is expected to have type "B". *)
     | S n' => repeat_arg A B a n' (f a)
     end. *)

(* Fixpoint repeat_arg (A B : Type) (a : A)
         (n : nat) (f : add_n_arg_types A B n) : B
  := match n
           return (match n with
                   | O => add_n_arg_types A B n
                   | S n' => add_n_arg_types A B n'
                   end)
     with
     | O => f (* The term "f" has type "add_n_arg_types A B n"
                 while it is expected to have type "add_n_arg_types A B 0". *)
     | S n' => repeat_arg A B a n' (f a)
     end. *)

(* Exercise 6.11 *
   Use the same technique to build a proof of [true <> false]. *)
Theorem true_is_not_false : true <> false.
Proof. discriminate. Qed.

Theorem true_is_not_false' : true <> false.
Proof.
  intro H.
  change ((fun b : bool => if b then True else False) false).
  now rewrite <- H.
Qed.

(* Exercise 6.12
   For the [vehicle] type (see Sect. 6.1.6), use the same technique
   to build a proof that no [bicycle] is equal to a [motorized] vehicle. *)
Theorem bicycle_is_not_motorized (n m : nat) : bicycle n <> motorized n m.
Proof. discriminate. Qed.

Theorem bicycle_is_not_motorized' (n m : nat) : bicycle n <> motorized n m.
Proof.
  intro H.
  change ((fun v : vehicle
           => match v with
              | bicycle _ => False
              | motorized _ _ => True
              end) (bicycle n)).
  now rewrite H.
Qed.

(* 6.2.3 Injective Constructors *)
Theorem bicycle_eq_seats (x1 y1 : nat) : bicycle x1 = bicycle y1 -> x1 = y1.
Proof. intro H. now injection H. Qed.

(* Simulating injection (for the fun) *)
Theorem bicycle_eq_seats' (x1 y1 : nat) : bicycle x1 = bicycle y1 -> x1 = y1.
Proof.
 intro H.
 change (nb_seats (bicycle x1) = nb_seats (bicycle y1)).
 rewrite H. reflexivity.
Qed.

(* use more primitive tactics *)
Theorem bicycle_eq_seats'' (x1 y1 : nat) : bicycle x1 = bicycle y1 -> x1 = y1.
Proof.
 intro H.
 apply (eq_ind (bicycle x1)
               (fun v : vehicle => nb_seats (bicycle x1) = nb_seats v)
               (eq_refl (nb_seats (bicycle x1)))
               (bicycle y1) H).
Qed.

Section injection_example.
  Variables A B : Set.
  Inductive T : Set := c1 : A -> T | c2 : B -> T.

  Theorem inject_c2 (x y : B) : c2 x = c2 y -> x = y.
  Proof using. intro H. now injection H. Qed.

  Theorem inject_c2' (x y : B) : c2 x = c2 y -> x = y.
  Proof using.
    intro H.
    pose (fun t : T => match t with | c1 a => x | c2 b => b end) as f.
    change (f (c2 x) = f (c2 y)).
    rewrite H. reflexivity.
  Qed.
End injection_example.

(* 6.2.4 Inductive Types and Equality *)

(* Exercise 6.13 **
   This exercise shows a use of discriminate and underlines
   the danger of adding axioms to the system.
   The ''theory'' introduced here proposes a description of rational numbers
   as fractions with a non-zero denominator. An axiom is added to
   indicate that two rational numbers are equal as soon
   as they satisfy a classical arithmetic condition. *)

Require Import Arith.

Record RatPlus : Set
  := mkRat {top : nat; bottom : nat; bottom_condition : bottom <> 0}.

Axiom eq_RatPlus : forall r1 r2 : RatPlus,
    top r1 * bottom r2 = top r2 * bottom r1 -> r1 = r2.

Theorem eq_RatPlus_imp_False : False.
Proof.
  pose (mkRat 1 1 (Nat.neq_succ_0 _)) as r1.
  pose (mkRat 2 2 (Nat.neq_succ_0 _)) as r2.
  assert (r1 = r2) as eq.
  { apply eq_RatPlus. reflexivity. }
  discriminate eq.
Qed.
