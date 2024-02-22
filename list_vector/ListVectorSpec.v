Set Mangle Names.
Set Default Goal Selector "!".
Require Fin List.
Require Import ListVectorDef PeanoNat Eqdep_dec.
Import ListVectorNotations EqNotations.
Require Import Lia.
Require list_utils.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, t A n -> Prop),
  P 0 (nil _) -> (forall (h : A) (n : nat) (v : t A n), P n v -> P (S n) (cons _ h n v)) ->
  forall (n : nat) (v : t A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n as [|n IHn]; cbn.
  - intros [[|h elts] Helts]; cbn.
    + destruct Helts.
      apply H1.
    + cbn in Helts.
      lia.
  - intros [[|h elts] Helts]; cbn.
    + cbn in Helts.
      lia.
    + specialize (H2 h n (mk_vector elts (f_equal pred Helts)) (IHn _)).
      cbn in H2.
      replace Helts with (f_equal S (f_equal Nat.pred Helts)).
      * apply H2.
      * apply UIP_dec.
        decide equality.
Qed.

Definition cons_inj {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
conj 
  (f_equal hd eq)
  (proj1 (vec_spec_eq v1 v2) (f_equal elts (f_equal tl eq))).

Definition cons_spec {A} {a1 a2} {n} {v1 v2 : t A n} (eq: a1 = a2 /\ v1 = v2) :
  (a1 :: v1 = a2 :: v2) :=
eq_ind_r (fun a3 : A => a3 :: v1 = a2 :: v2)
(eq_ind_r (fun v3 : t A n => a2 :: v3 = a2 :: v2) eq_refl (proj2 eq))
(proj1 eq).

(*
as in std does not work because this implementation relies on equality by definition 
with List Vectors, equality needs to take the elts_spec proof into account 
this can be loosend by using vec_spec_eq wich is the Proof that two ListVectors are equal 
iff their elements are equal, even if the elts_spec proofs are different 
Definition cons_inj_std {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
   match eq in _ = x return caseS _ (fun a2' _ v2' => fun v1' => a1 = a2' /\ v1' = v2') x v1
   with | eq_refl => conj eq_refl eq_refl
   end.
*)

Lemma cons_exists_spec {A} {n} (v:t A (S n)): exists h:A, exists t:t A n, v = h::t.
Proof.
destruct v as [l l_sp].
destruct l as [|h t].
- cbn in l_sp.
  lia.
- exists h.
  cbn in l_sp.
  exists (mk_vector t (f_equal Nat.pred l_sp)).
  unfold cons.
  cbn.
  apply vec_spec_eq.
  reflexivity.
Qed.

(*as in std*)
Lemma nil_spec_std {A} (v : t A 0) : v = [].
Proof.
apply (fun P E => case0 P E v). reflexivity.
Defined.

Lemma eta' {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof.
apply (fun P IS => caseS P IS (n := n) v). 
intros. 
apply vec_spec_eq.
reflexivity.
Defined.

(*as in std
Lemma eta_std {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof.
apply (fun P IS => caseS P IS (n := n) v); intros; reflexivity.
Defined.
*)

Lemma eq_nth_iff A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1 ] = v2 [@ p2 ]) <-> v1 = v2.
Proof.
split.
- intros H.
  induction n as [|n IHn].
  + apply vec_spec_eq.
    destruct v1 as [l1 l_sp1], v2 as [l2 l_sp2].
    cbn.
    rewrite (list_utils.list_nil_spec l_sp1).
    rewrite (list_utils.list_nil_spec l_sp2).
    reflexivity.
  + destruct (cons_exists_spec v1) as [h1 [t1 H1]].
    destruct (cons_exists_spec v2) as [h2 [t2 H2]]. 
    rewrite H1, H2 in *.
    apply cons_spec.
    split.
    * apply (H Fin.F1 Fin.F1 eq_refl).
    * apply IHn.
      intros p1 p2 p_eq.
      specialize (H (Fin.FS p1) (Fin.FS p2) (f_equal (@Fin.FS n) p_eq)).
      destruct p_eq.
      cbn in H.
      rewrite <- (proj1 (vec_spec_eq  (mk_vector (elts t1) (f_equal Init.Nat.pred (f_equal S (elts_spec t1)))) t1) eq_refl).
      rewrite <- (proj1 (vec_spec_eq  (mk_vector (elts t2) (f_equal Init.Nat.pred (f_equal S (elts_spec t2)))) t2) eq_refl).
      assumption.
- intros v_eq p1 p2 p_eq.
  rewrite v_eq, p_eq; reflexivity.
Qed.

Lemma eq_nth_iff' A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1 ] = v2 [@ p2 ]) <-> v1 = v2.
Proof.
split.
- revert n v1 v2. refine (@rect2 _ _ _ _ _).
  + reflexivity.
  + intros n v1 v2 H ? ? H0. f_equal.
    * apply (H0 Fin.F1 Fin.F1 eq_refl).
    * destruct v1 as [l1 l_sp1], v2 as [l2 l_sp2]. 
      apply H. 
      intros p1 p2 H1.
      rewrite H1.
      specialize (H0 (Fin.FS p2) (Fin.FS p2) eq_refl).
      cbn in H0. 
      rewrite (lia_utils.nat_uip l_sp1 (f_equal Init.Nat.pred (f_equal S l_sp1))).
      rewrite (lia_utils.nat_uip l_sp2 (f_equal Init.Nat.pred (f_equal S l_sp2))).
      apply H0.
- intros H p1 p2 eq.
  rewrite H.
  rewrite eq.
  now reflexivity.
Qed.


(*as in std*)
Lemma nth_order_hd A: forall n (v : t A (S n)) (H : 0 < S n),
  nth_order v H = hd v.
Proof. intros n v H; now rewrite (eta v). Qed.

(*as in std*)
Lemma nth_order_tl A: forall n k (v : t A (S n)) (H : k < n) (HS : S k < S n),
  nth_order (tl v) H = nth_order v HS.
Proof.
intros n; induction n; intros k v H HS.
- inversion H.
- rewrite (eta v).
  unfold nth_order; simpl.
  now rewrite (Fin.of_nat_ext H (proj2 (Nat.succ_lt_mono _ _) HS)).
Qed.
