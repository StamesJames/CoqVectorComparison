Require Fin List.
Require Import InductiveVectorDef PeanoNat Eqdep_dec.
Import InductiveVectorNotations EqNotations.

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
intros n v; induction v as [|? ? v IHv]; simpl; [ | rewrite IHv ]; auto.
Qed.

Lemma map_map A B C: forall (f:A->B) (g:B->C) n (v : t A n),
  map g (map f v) = map (fun x => g (f x)) v.
Proof.
intros f g n v; induction v as [|? ? v IHv]; simpl; [ | rewrite IHv ]; auto.
Qed.

Lemma map_append A B: forall (f:A->B) n m (v: t A n) (w: t A m),
  (map f (v ++ w)) = map f v ++ map f w.
Proof.
intros f n m v w. induction v as [|? ? v IHv].
- reflexivity.
- cbn. apply f_equal, IHv.
Qed.

Lemma take_O : forall {A} {n} le (v:t A n), take 0 le v = [].
Proof.
  reflexivity.
Qed.


Lemma take_idem : forall {A} p n (v:t A n) le le',
  take p le' (take p le v) = take p le v.
Proof.
  intros A p; induction p as [|p IHp]; intros n v le le'.
  - reflexivity.
  - destruct v.
    + inversion le.
    + simpl. apply f_equal, IHp.
Qed.

Lemma append_comm_cons {A} : forall {n m : nat} (v : t A n) (w : t A m) (a : A),
  a :: (v ++ w) = (a :: v) ++ w.
Proof. reflexivity. Qed.

Locate "rew".

Lemma rev_cons A: forall a n (v : t A n), rev (a :: v) = shiftin a (rev v).
Proof.
intros a n v. unfold rev, rev_append, eq_rect_r.
rewrite !rew_compose.
enough (H : forall m (w : t A m) k (E1 : _ = k) E2,
  rew [t A] E2 in rev_append_tail v (shiftin a w) =
  shiftin a (rew [t A] E1 in rev_append_tail v w)) by apply (H 0 []).
induction v as [|b n v IH]; intros m w k E1 E2; cbn.
- subst k. now rewrite (UIP_refl_nat _ E2).
- apply (IH _ (b :: w)).
Qed.

Lemma splitat_append {A} : forall {n m : nat} (v : t A n) (w : t A m),
  splitat n (v ++ w) = (v, w).
Proof.
  intros n m v w. induction v as [|a n v IH].
  - reflexivity.
  - cbn. now rewrite IH.
Qed.

Lemma append_inj {A} : forall {n m : nat} (v v' : t A n) (w w' : t A m),
  v ++ w = v' ++ w' -> v = v' /\ w = w'.
Proof.
intros n m v v' w w' E%(f_equal (splitat _)).
apply pair_equal_spec.
now rewrite <- !splitat_append.
Qed.

Lemma rev_nil A: rev (nil A) = [].
Proof.
unfold rev, rev_append.
now rewrite (UIP_refl_nat _ (plus_n_O 0)), (UIP_refl_nat _ (Nat.tail_add_spec 0 0)).
Qed.

Lemma rev_shiftin A: forall a n (v : t A n),
  rev (shiftin a v) = a :: rev v.
Proof.
intros a n v. induction v as [|b n v IH]; cbn.
- now rewrite rev_cons, !rev_nil.
- now rewrite !rev_cons, IH.
Qed.

Lemma rev_rev A: forall n (v : t A n), rev (rev v) = v.
Proof.
intros n v. induction v as [|a n v IH].
- now rewrite !rev_nil.
- now rewrite rev_cons, rev_shiftin, IH.
Qed.

Lemma map_shiftin A B: forall (f : A -> B) a n (v : t A n),
  map f (shiftin a v) = shiftin (f a) (map f v).
Proof.
intros f a n v. induction v as [|b n v IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

Lemma map_rev A B: forall (f : A -> B) n (v : t A n),
  map f (rev v) = rev (map f v).
Proof.
intros f n v. induction v as [|a n v IH]; cbn.
- now rewrite !rev_nil.
- now rewrite !rev_cons, map_shiftin, IH.
Qed.

Lemma to_list_of_list_opp {A} (l: list A): to_list (of_list l) = l.
Proof.
induction l.
- reflexivity.
- unfold to_list; simpl. now f_equal.
Qed.


Lemma length_to_list A n (v : t A n): length (to_list v) = n.
Proof. induction v; cbn; auto. Qed.

Lemma of_list_to_list_opp A n (v: t A n):
  rew length_to_list _ _ _ in of_list (to_list v) = v.
Proof.
induction v as [ | h n v IHv ].
- now apply case0 with (P := fun v => v = nil A).
- replace (length_to_list _ _ (cons _ h _ v)) with (f_equal S (length_to_list _ _ v))
    by apply (UIP_dec Nat.eq_dec).
  cbn; rewrite map_subst_map.
  f_equal.
  now etransitivity; [ | apply IHv].
Qed.

Lemma to_list_nil A : to_list (nil A) = List.nil.
Proof. reflexivity. Qed.

Lemma to_list_cons A h n (v : t A n):
  to_list (cons A h n v) = List.cons h (to_list v).
Proof. reflexivity. Qed.

Lemma to_list_nil_iff A v:
  to_list v = List.nil <-> v = nil A.
Proof.
split; intro H.
- now apply case0 with (P := fun v => v = []).
- subst. apply to_list_nil.
Qed.


Lemma to_list_inj A n (v w : t A n):
  to_list v = to_list w -> v = w.
Proof.
revert v. induction w as [| w0 n w IHw].
- apply to_list_nil_iff.
- intros v H. rewrite (eta v) in H.
  injection H as [=H0 H1%IHw]. subst. apply eta.
Qed.

Lemma to_list_hd A n (v : t A (S n)) d:
  hd v = List.hd d (to_list v).
Proof. now rewrite (eta v). Qed.

Lemma to_list_last A n (v : t A (S n)) d:
  last v = List.last (to_list v) d.
Proof.
apply rectS with (v:=v); [reflexivity|].
intros a k u IH.
rewrite to_list_cons.
simpl List.last.
now rewrite <- IH, (eta u).
Qed.

Lemma to_list_const A (a : A) n:
  to_list (const a n) = List.repeat a n.
Proof.
induction n as [ | n IHn ]; [reflexivity|].
now cbn; rewrite <- IHn.
Qed.

Lemma to_list_tl A n (v : t A (S n)):
  to_list (tl v) = List.tl (to_list v).
Proof. now rewrite (eta v). Qed.

Lemma to_list_append A n m (v1 : t A n) (v2 : t A m):
  to_list (append v1 v2) = List.app (to_list v1) (to_list v2).
Proof.
induction v1; simpl; trivial.
now rewrite to_list_cons; f_equal.
Qed.

Lemma to_list_rev_append_tail A n m (v1 : t A n) (v2 : t A m):
  to_list (rev_append_tail v1 v2) = List.rev_append (to_list v1) (to_list v2).
Proof. now revert m v2; induction v1 as [ | ? ? ? IHv1 ]; intros; [ | simpl; rewrite IHv1 ]. Qed.

Lemma to_list_rev_append A n m (v1 : t A n) (v2 : t A m):
  to_list (rev_append v1 v2) = List.rev_append (to_list v1) (to_list v2).
Proof. unfold rev_append; rewrite <- (Nat.tail_add_spec n m); apply to_list_rev_append_tail. Qed.

Lemma to_list_rev A n (v : t A n):
  to_list (rev v) = List.rev (to_list v).
Proof.
unfold rev; rewrite (plus_n_O n); unfold eq_rect_r; simpl.
now rewrite to_list_rev_append, List.rev_alt.
Qed.

Lemma to_list_map A B (f : A -> B) n (v : t A n) :
  to_list (map f v) = List.map f (to_list v).
Proof.
induction v; cbn; [reflexivity|].
now cbn; f_equal.
Qed.

Lemma to_list_fold_right A B f (b : B) n (v : t A n):
  fold_right f v b = List.fold_right f b (to_list v).
Proof. now revert b; induction v; cbn; intros; f_equal. Qed.
