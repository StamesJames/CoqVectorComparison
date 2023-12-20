Require Fin List.
Require Import FunctionalVectorDef PeanoNat Eqdep_dec.
Import FunctionalVectorNotations EqNotations.
Require Import FunctionalExtensionality.


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