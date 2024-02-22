Set Mangle Names.
Set Default Goal Selector "!".
Require Fin List.
Require Import FunctionalVectorDef PeanoNat Eqdep_dec.
Import FunctionalVectorNotations EqNotations.

Require Import FunctionalExtensionality.

Lemma vector_ind :
  forall (A : Type) (P : forall n : nat, t A n -> Prop),
    P 0 [] -> 
    (forall (h : A) (n : nat) (v : t A n), P n v -> P (S n) (h :: v)) -> 
    forall (n : nat) (v : t A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n as [|n IHn]; cbn.
  - intros v.
    replace v with (nil A).
    + apply H1.
    + apply functional_extensionality.
      apply (Fin.case0 _).
  - intros v.
    replace v with (cons _ (hd v) _ (tl v)).
    + apply H2.
      apply IHn.
    + apply functional_extensionality.
      intros i.
      apply (fin_utils.fin_caseS i (fun i => cons _ (hd v) _ (tl v) i = v i)); reflexivity.
Qed.

Definition cons_inj {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 := conj (f_equal hd eq) (f_equal tl eq).

(*
as in std does not work because this implementation relies on equality by definition 
With functional vectors, equality comes with functional extensionality
 Definition cons_inj_std {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
   match eq in _ = x return caseS ((fun (n0 : nat) (_ : t A (S n0)) =>
   t A n0 -> Prop)) (fun a2' _ v2' => fun v1' => a1 = a2' /\ v1' = v2') x v1
   with | eq_refl => conj eq_refl eq_refl
   end.
*)

(*as in std*)
Lemma nil_spec_std {A} (v : t A 0) : v = [].
Proof.
apply (fun P E => case0 P E v). reflexivity.
Defined.


(*as in std*)
Lemma eta_std {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof.
apply (fun P IS => caseS P IS (n := n) v); intros; reflexivity.
Defined.

Lemma eq_nth_iff A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1] = v2 [@ p2] ) <-> v1 = v2.
Proof.
split; intros H.
- apply functional_extensionality.
  intros x.
  apply (H x x (eq_refl x)).
- intros p1 p2 p_eq.
  rewrite H.
  rewrite p_eq.
  reflexivity.
Qed.

(*as in std*)
Lemma eq_nth_iff_std A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1 ] = v2 [@ p2 ]) <-> v1 = v2.
Proof.
split.
- revert n v1 v2; refine (@rect2 _ _ _ _ _).
  + reflexivity.
  + intros n ? ? H ? ? H0. f_equal.
    * apply (H0 Fin.F1 Fin.F1 eq_refl).
    * apply H. intros p1 p2 H1;
        apply (H0 (Fin.FS p1) (Fin.FS p2) (f_equal (@Fin.FS n) H1)).
- intros; now f_equal.
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

(*just changed (now smipl) with (now cbn)*)
Lemma nth_order_last A: forall n (v: t A (S n)) (H: n < S n),
  nth_order v H = last v.
Proof.
unfold nth_order; refine (@rectS _ _ _ _); now cbn.
Qed.

(*as in std*)
Lemma nth_order_ext A: forall n k (v : t A n) (H1 H2 : k < n),
  nth_order v H1 = nth_order v H2.
Proof.
intros n k v H1 H2; unfold nth_order.
now rewrite (Fin.of_nat_ext H1 H2).
Qed.


Lemma nth_append_L A: forall n m (v : t A n) (w : t A m) p,
  (v ++ w) [@ Fin.L m p] = v [@ p].
Proof.
intros n m v. 
revert m. 
apply (vector_ind A (fun n v => forall (m : nat) (w : t A m) (p : Fin.t n), (v ++ w)[@Fin.L m p] = v[@p])). 
- now simpl.
- intros h n' v' IH m w p.
  cbn.
  change (tl (h :: v')) with v'.
  apply (Fin.caseS' p (fun p => (h :: v' ++ w) (Fin.L m p) = (h :: v')[@p])); auto.
  + intros p'.
    cbn.
    apply (IH m w p').
Qed.

Lemma nth_append_R A: forall n m (v : t A n) (w : t A m) p,
  (v ++ w) [@ Fin.R n p] = w [@ p].
Proof.
intros n m v.
revert m.
apply (vector_ind A (fun n v => forall (m : nat) (w : t A m) (p : Fin.t m), (v ++ w)[@Fin.R n p] = w[@p])); now cbn.
Qed.

(*vector_ind instead of tactic*)
Lemma In_nth A: forall n (v : t A n) p,
  In (nth v p) v.
Proof.
intros n v. 
apply (vector_ind A (fun n v => forall p : Fin.t n, In v[@p] v)).
- apply Fin.case0.
- intros h n' v' IH p. apply (Fin.caseS' p).
  + apply In_cons_hd.
  + intros q. apply In_cons_tl, IH.
Qed.

Lemma nth_replace_eq A: forall n p (v : t A n) a,
  nth (replace v p a) p = a.
Proof.
intros n p v.
revert p.
apply (vector_ind A (fun n v =>forall (p : Fin.t n) (a : A), (replace v p a)[@p] = a)).
- intros p a. now apply Fin.case0.
- intros h n' v' IH p a. 
  apply (Fin.caseS' p).
  + reflexivity.
  + intros p'.
    cbn.
    apply (IH p' a). 
Qed.


Lemma nth_replace_neq A: forall n p q, p <> q -> forall (v : t A n) a,
  nth (replace v q a) p = nth v p.
Proof.
intros n p q Hpq v a.
revert p q Hpq a.
apply (vector_ind A (fun n v => forall p q : Fin.t n, p <> q -> forall a : A, (replace v q a)[@p] = v[@p])).
- intros p q Hpq a. now apply Fin.case0.
- intros h n' v' IH p q Hpq a.
  revert Hpq.  
  apply (Fin.caseS' p); apply (Fin.caseS' q); [easy..|].
  intros f1 f2 Hpq. apply IH. contradict Hpq. now f_equal.
Qed.

Lemma nth_order_replace_eq A: forall n k (v : t A n) a (H1 : k < n) (H2 : k < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = a.
Proof.
intros n k v a H1 H2.
rewrite (Fin.of_nat_ext H2 H1).
apply nth_replace_eq.
Qed.
