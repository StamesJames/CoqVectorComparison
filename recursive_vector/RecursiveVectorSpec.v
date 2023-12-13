Require Fin List.
Require Import RecursiveVectorDef PeanoNat Eqdep_dec.
Import RecursiveVectorNotations EqNotations.

Definition cons_inj {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
   match eq in _ = x return caseS _ (fun a2' _ v2' => fun v1' => a1 = a2' /\ v1' = v2') x v1
   with | eq_refl => conj eq_refl eq_refl
   end.

Lemma nil_spec {A} (v : t A 0) : v = [].
Proof.
apply (fun P E => case0 P E v). reflexivity.
Defined.

Lemma eq_nth_iff A n (v1 v2: t A n):
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

Lemma eta {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof.
apply (fun P IS => caseS P IS (n := n) v); intros; reflexivity.
Defined.

Lemma replace_id A: forall n p (v : t A n),
  replace v p (nth v p) = v.
Proof.
intros n p; induction p as [|? p IHp]; intros v; rewrite (eta v); simpl; [reflexivity|].
now rewrite IHp.
Qed.

Lemma replace_replace_eq A: forall n p (v : t A n) a b,
  replace (replace v p a) p b = replace v p b.
Proof.
intros n p v a b.
induction p as [|? p IHp]; rewrite (eta v); simpl; [reflexivity|].
now rewrite IHp.
Qed.

Lemma const_nth A (a: A) n (p: Fin.t n): (const a n)[@ p] = a.
Proof.
now induction p.
Qed.

Lemma append_const A (a : A) n m : (const a n) ++ (const a m) = const a (n + m).
Proof.
induction n as [|n IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

Lemma map_id A: forall n (v : t A n),
  map (fun x => x) v = v.
Proof.
intros n.
induction n as [|? IHn]; simpl.
- destruct v.
  auto.
- intros v.
  destruct v as [h t].
  rewrite (IHn t).
  reflexivity.
Qed.

Lemma map_map A B C: forall (f:A->B) (g:B->C) n (v : t A n),
  map g (map f v) = map (fun x => g (f x)) v.
Proof.
intros f g n. 
induction n as [|? IHn].
- auto.
- intros v. 
  destruct v.
  simpl.
  rewrite (IHn t).
  auto.
Qed.

Lemma map_append A B: forall (f:A->B) n m (v: t A n) (w: t A m),
  (map f (v ++ w)) = map f v ++ map f w.
Proof.
intros f n.
induction n as [|? IHn]; intros m v w.
- reflexivity.
- destruct v. cbn. apply f_equal, IHn.
Qed.

Lemma take_O : forall {A} {n} le (v:t A n), take 0 le v = [].
Proof.
  intros A n.
  now induction n.
Qed.

Lemma take_idem : forall {A} p n (v:t A n) le le',
  take p le' (take p le v) = take p le v.
Proof.
  intros A p; induction p as [|p IHp]; intros n v le le'.
  - now induction n. 
  - induction n; destruct v.
    + inversion le.
    + simpl. apply f_equal, IHp.
Qed.

Lemma append_comm_cons {A} : forall {n m : nat} (v : t A n) (w : t A m) (a : A),
  a :: (v ++ w) = (a :: v) ++ w.
Proof. reflexivity. Qed.

Lemma rev_cons A: forall a n (v : t A n), rev (a :: v) = shiftin a (rev v).
Proof.
intros a n v. unfold rev, rev_append, eq_rect_r.
rewrite !rew_compose.
enough (H : forall m (w : t A m) k (E1 : _ = k) E2,
  rew [t A] E2 in rev_append_tail v (shiftin a w) =
  shiftin a (rew [t A] E1 in rev_append_tail v w)) by apply (H 0 []).
induction n as [|n IHn]; intros m w k E1 E2.
- subst k. destruct v. now rewrite (UIP_refl_nat _ E2).
- destruct v as [h t].
  apply (IHn _ _ (h :: w)).
Qed.


Lemma splitat_append {A} : forall {n m : nat} (v : t A n) (w : t A m),
  splitat n (v ++ w) = (v, w).
Proof.
  intros n.
  induction n as [|n IHn]; intros m v w. 
  - destruct v. reflexivity.
  - destruct v as [h t]. cbn. now rewrite (IHn m t w).
Qed.


Lemma append_inj {A} : forall {n m : nat} (v v' : t A n) (w w' : t A m),
  v ++ w = v' ++ w' -> v = v' /\ w = w'.
Proof.
intros n m v v' w w' E%(f_equal (splitat _)).
apply pair_equal_spec.
now rewrite <- !splitat_append.
Qed.

Lemma rev_nil A: rev (@nil A) = [].
Proof.
unfold rev, rev_append.
now rewrite (UIP_refl_nat _ (plus_n_O 0)), (UIP_refl_nat _ (Nat.tail_add_spec 0 0)).
Qed.

Lemma rev_shiftin A: forall a n (v : t A n),
  rev (shiftin a v) = a :: rev v.
Proof.
intros a n.
induction n as [|n IHn]; intros v. 
- destruct v. cbn. now rewrite rev_cons, !rev_nil.
- destruct v as [b v]. cbn.
  specialize (IHn v).
  rewrite rev_cons.
  rewrite IHn.
  cbn.
  change (b,v) with (b :: v).
  rewrite (rev_cons A b n v).
  reflexivity.
Qed.




