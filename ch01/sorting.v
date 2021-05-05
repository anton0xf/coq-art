Require Import Arith List.
Import ListNotations.

Inductive sorted  : list nat -> Prop
  :=
  | sorted0 : sorted []
  | sorted1 (n : nat) : sorted [n]
  | sorted_n (n0 n1 : nat) (ns : list nat) :
      n0 <= n1
      -> sorted (n1 :: ns)
      -> sorted (n0 :: n1 :: ns).

#[export] Hint Constructors sorted :  sort.

Example sorted_ex : sorted [1; 3; 7].
Proof.
  auto with sort arith.
Qed.

Theorem sorted_inv (n : nat) (ns : list nat) : sorted (n :: ns) -> sorted ns.
Proof.
  intros H. inversion H; auto with sort.
Qed.

Theorem sorted_order (n0 n1 : nat) (ns : list nat)
  : sorted (n0 :: n1 :: ns) -> n0 <= n1.
Proof.
  intros H. inversion H. assumption.
Qed.

Fixpoint nb_occ (m : nat) (ns : list nat) : nat
  := match ns with
     | [] => 0
     | n :: ns' => Nat.b2n (m =? n) + nb_occ m ns'
     end.

Example nb_occ_ex : nb_occ 3 [1; 3; 2; 3] = 2.
Proof. reflexivity. Qed.

Theorem nb_occ_cons (n m : nat) (ns : list nat)
  : nb_occ n (m :: ns) = Nat.b2n (n =? m) + nb_occ n ns.
Proof.
  simpl. destruct (n =? m) eqn:eq; reflexivity.
Qed.

Theorem nb_occ_cons_same (n : nat) (ns : list nat)
  : nb_occ n (n :: ns) = S (nb_occ n ns).
Proof.
  simpl. rewrite Nat.eqb_refl. simpl. ring.
Qed.

Theorem nb_occ_cons_other (n m : nat) (ns : list nat)
  : n <> m -> nb_occ n (m :: ns) = nb_occ n ns.
Proof.
  simpl. intros neq. apply Nat.eqb_neq in neq.
  rewrite neq. reflexivity.
Qed.

Definition permutation (ns ms : list nat) : Prop
  := forall n : nat, nb_occ n ns = nb_occ n ms.

Theorem permutation_is_refl (ns ms : list nat)
  : permutation ns ms -> permutation ms ns.
Proof.
  unfold permutation. intros H n.
  symmetry. apply (H n).
Qed.

Theorem permutation_is_sym (ns : list nat) : permutation ns ns.
Proof. intros n. reflexivity. Qed.

Theorem permutation_is_trans (ns ms ks : list nat)
  : permutation ns ms -> permutation ms ks -> permutation ns ks.
Proof.
  unfold permutation. intros Hnm Hmk n.
  rewrite (Hnm n). apply (Hmk n).
Qed.

Theorem permutation_cons (k : nat) (ns ms : list nat)
  : permutation ns ms -> permutation (k :: ns) (k :: ms).
Proof.
  unfold permutation. intros H n.
  repeat rewrite nb_occ_cons.
  rewrite (H n). reflexivity.
Qed.

Theorem permutation_perm (k1 k2 : nat) (ns ms : list nat)
  : permutation ns ms -> permutation (k1 :: k2 :: ns) (k2 :: k1 :: ms).
Proof.
  unfold permutation. intros H n.
  repeat rewrite nb_occ_cons. rewrite (H n).
  ring.
Qed.

Fixpoint insert (m : nat) (ns : list nat)
  := match ns with
     | [] => [m]
     | n :: ns' => if m <=? n then m :: ns
                   else n :: (insert m ns')
     end.

Theorem insert_sorted (m : nat) (ns : list nat)
  : sorted ns -> sorted (insert m ns).
Proof.
  induction ns as [| n1 ns1 IH]; intros H.
  - (*[ ns = [] ]*) simpl. constructor.
  - (*[ ns = n1 :: ns1 ]*)
    simpl. destruct (m <=? n1) eqn:neq.
    + (*[ m <= n1 ]*) apply sorted_n.
      { apply Nat.leb_le, neq. }
      assumption.
    + (*[ m > n1 ]*)
      apply Nat.leb_gt in neq as neq'.
      apply sorted_inv in H as H1.
      apply IH in H1 as H2.
      remember (insert m ns1) as ms eqn:eq_ms.
      destruct ms as [| m1 ms1].
      * (*[ ms = [] ]*) constructor. 
      * (*[ ms = m1 :: ms1 ]*)
        apply sorted_n; try assumption.
        { (* proof that [n1 <= m1] *)
          destruct ns1 as [| n2 ns2].
          - (*[ ns1 = [] ]*) simpl in eq_ms.
            inversion eq_ms. apply Nat.lt_le_incl. assumption.
          - (*[ ns1 = n2 :: ns2 ]*)
            simpl in eq_ms.
            destruct (m <=? n2) eqn:neq1.
            + (*[ m <= n2 ]*) inversion eq_ms.
              apply Nat.lt_le_incl. assumption.
            + (*[ m > n2 ]*) inversion eq_ms.
              apply sorted_order in H. assumption.
        }
Qed.

Theorem insert_ob_occ (n m : nat) (ks : list nat)
  : nb_occ m (insert n ks) = Nat.b2n (m =? n) + nb_occ m ks.
Proof.
  induction ks as [| k ks' IH].
  - (* ks = [] *) reflexivity.
  - (* ks = k :: ks' *) simpl.
    destruct (n <=? k) eqn:neq.
    + (* n <= k *) repeat rewrite nb_occ_cons. reflexivity.
    + (* n > k *) rewrite nb_occ_cons, IH. ring.
Qed.

Theorem insert_is_permutaion (k : nat) (ns ms : list nat)
  : permutation ns ms -> permutation (k :: ns) (insert k ms).
Proof.
  unfold permutation. intros H n.
  rewrite nb_occ_cons, insert_ob_occ, (H n).
  reflexivity.
Qed.

Fixpoint insertion_sort (ns : list nat)
  := match ns with
     | [] => []
     | n :: ns' => insert n (insertion_sort ns')
     end.

Example insertion_sort_ex : insertion_sort [4; 2; 3; 1; 3] = [1; 2; 3; 3; 4].
Proof. reflexivity. Qed.

Theorem insertion_sort_sorts (ns : list nat) : sorted (insertion_sort ns).
Proof.
  induction ns as [| n ns' IH].
  - (*[ ns = [] ]*) simpl. constructor.
  - (*[ ns = n :: ns' ]*)
    simpl. apply insert_sorted, IH.
Qed.

Theorem insertion_sort_save_elements (ns : list nat)
  : permutation ns (insertion_sort ns).
Proof.
  induction ns as [| n ns' IH].
  - (*[ ns = [] ]*) simpl. apply permutation_is_sym.
  - (*[ ns = n :: ns' ]*)
    simpl. apply insert_is_permutaion, IH.
Qed.

Definition nat_sort : (list nat -> list nat) -> Prop
  := fun fn => forall ns : list nat,
         sorted (fn ns) /\ permutation ns (fn ns).

Theorem insertion_sort_is_nat_sort : nat_sort insertion_sort.
Proof.
  intros ns. split.
  - apply insertion_sort_sorts.
  - apply insertion_sort_save_elements.
Qed.
