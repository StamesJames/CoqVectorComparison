Require Fin List.
Require Import FunctionalVectorDef PeanoNat Eqdep_dec.
Import FunctionalVectorNotations EqNotations.
Require Import FunctionalExtensionality.


Lemma vector_ind :
  forall (A : Type) (P : forall n : nat, t A n -> Prop),
    P 0 (nil _) -> 
    (forall (h : A) (n : nat) (v : t A n), P n v -> P (S n) (cons _ h _ v)) -> 
    forall (n : nat) (v : t A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n; cbn.
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
      Check Fin.caseS.
      apply (fin_utils.fin_caseS i (fun i => cons _ (hd v) _ (tl v) i = v i)); reflexivity.
Qed.

Lemma eq_nth_iff A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1] = v2 [@ p2] ) <-> v1 = v2.
Proof.
constructor.
- intros.
  apply functional_extensionality.
  intros x.
  specialize (H x x (eq_refl x)).
  apply H.
- intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.