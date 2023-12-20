Require Fin List.
Require Import ListVectorDef PeanoNat Eqdep_dec.
Import ListVectorNotations EqNotations.

Lemma eq_nth_iff A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1 ] = v2 [@ p2 ]) <-> v1 = v2.
Proof.
split.
- intros.
  destruct v1 as [el_v1 sp_v1], v2 as [el_v2 sp_v2].
  enough (el_v1 = el_v2 /\ sp_v1 = sp_v2).
  


Lemma nth_ext : forall l l' d d', length l = length l' ->
  (forall n, n < length l -> nth n l d = nth n l' d') -> l = l'.