Set Mangle Names.
Set Default Goal Selector "!".
Require Fin List.
Require Import RecursiveVectorDef PeanoNat Eqdep_dec.
Import RecursiveVectorNotations EqNotations.



Lemma vector_ind : forall (A : Type) (P : forall n : nat, t A n -> Prop),
    P 0 [] -> 
    (forall (h : A) (n : nat) (v : t A n), P n v -> P (S n) (h :: v)) -> 
    forall (n : nat) (v : t A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n as [|n IHn]; cbn.
  - intros [].
    apply H1.
  - intros [h v].
    apply H2.
    apply IHn.
Qed.



Definition cons_inj {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 := conj (f_equal hd eq) (f_equal tl eq).

 (*as in std*)
Definition cons_inj_std {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
   match eq in _ = x return caseS _ (fun a2' _ v2' => fun v1' => a1 = a2' /\ v1' = v2') x v1
   with | eq_refl => conj eq_refl eq_refl
   end.

Definition cons_spec {A} {a1 a2} {n} {v1 v2 : t A n} (eq: a1 = a2 /\ v1 = v2) :
   (a1 :: v1 = a2 :: v2) :=
eq_ind_r (fun a3 : A => a3 :: v1 = a2 :: v2)
(eq_ind_r (fun v3 : t A n => a2 :: v3 = a2 :: v2) eq_refl (proj2 eq))
(proj1 eq).

Lemma nil_spec {A} (v : t A 0) : v = [].
Proof.
apply (fun P E => case0 P E v). reflexivity.
Defined.

(*as in std*)
Lemma eta {A} {n} (v : t A
 (S n)) : v = hd v :: tl v.
Proof.
apply (fun P IS => caseS P IS (n := n) v); intros; reflexivity.
Defined.

Lemma eq_nth_iff A n (v1 v2: t A n):
  (forall p1 p2, p1 = p2 -> v1 [@ p1 ] = v2 [@ p2 ]) <-> v1 = v2.
Proof.
split.
- intros H.
  induction n as [|n IHn].
  + destruct v1, v2; reflexivity.
  + destruct v1, v2.
    apply cons_spec.
    split.
    * apply (H Fin.F1 Fin.F1 eq_refl).
    * apply IHn.
      intros p1 p2 H1.
      apply (H (Fin.FS p1) (Fin.FS p2) (f_equal (@Fin.FS n) H1)).
- intros v_eq p1 p2 p_eq.
  rewrite v_eq, p_eq; reflexivity.
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

(*as in std*)
Lemma nth_order_last A: forall n (v: t A (S n)) (H: n < S n),
  nth_order v H = last v.
Proof.
unfold nth_order; refine (@rectS _ _ _ _); now simpl.
Qed.

(*as in std*)
Lemma nth_order_ext A: forall n k (v : t A n) (H1 H2 : k < n),
  nth_order v H1 = nth_order v H2.
Proof.
intros n k v H1 H2; unfold nth_order.
now rewrite (Fin.of_nat_ext H1 H2).
Qed.

(*vector_ind instead of tactic*)
Lemma nth_append_L A: forall n m (v : t A n) (w : t A m) p,
  (v ++ w) [@ Fin.L m p] = v [@ p].
Proof.
intros n m v w. 
apply (vector_ind A (fun n v => forall p:Fin.t n, (v++w)[@Fin.L m p] = v[@p])).
- apply Fin.case0.
- intros h n0 v0 IHp p. now apply (Fin.caseS' p).
Qed.

(*vector_ind instead of tactic*)
Lemma nth_append_R A: forall n m (v : t A n) (w : t A m) p,
  (v ++ w) [@ Fin.R n p] = w [@ p].
Proof.
intros n m v w. 
apply (vector_ind A (fun n v => forall p : Fin.t m, (v ++ w)[@Fin.R n p] = w[@p])); auto.  
Qed.

(*vector_ind instead of tactic*)
Lemma In_nth A: forall n (v : t A n) p,
  In (nth v p) v.
Proof.
intros n v. 
apply (vector_ind A (fun n v => forall p : Fin.t n, In v[@p] v)).
- apply Fin.case0.
- intros h n0 v0 IH p. apply (Fin.caseS' p).
  + apply In_cons_hd.
  + intros q. apply In_cons_tl, IH.
Qed.


(*vector_ind instead of tactic*)
Lemma nth_replace_eq A: forall n p (v : t A n) a,
  nth (replace v p a) p = a.
Proof.
intros n p v a. revert p. apply (vector_ind A (fun n v => forall p: Fin.t n, (replace v p a)[@p] = a)).
- now apply Fin.case0.
- intros h n0 v0 IH p. now apply (Fin.caseS' p).
Qed.


(*vector_ind instead of tactic*)
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

(*as in std*)
Lemma nth_order_replace_eq A: forall n k (v : t A n) a (H1 : k < n) (H2 : k < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = a.
Proof.
intros n k v a H1 H2.
rewrite (Fin.of_nat_ext H2 H1).
apply nth_replace_eq.
Qed.

(*as in std*)
Lemma nth_order_replace_neq A: forall n k1 k2, k1 <> k2 ->
  forall (v : t A n) a (H1 : k1 < n) (H2 : k2 < n),
  nth_order (replace v (Fin.of_nat_lt H2) a) H1 = nth_order v H1.
Proof.
intros n k1 k2 H v a H1 H2.
unfold nth_order. rewrite nth_replace_neq; [reflexivity|].
intros E. apply H.
apply (f_equal (fun p => proj1_sig (Fin.to_nat p))) in E.
now rewrite !Fin.to_nat_of_nat in E.
Qed.

(*as in std*)
Lemma replace_id A: forall n p (v : t A n),
  replace v p (nth v p) = v.
Proof.
intros n p; induction p as [|? p IHp]; intros v; rewrite (eta v); simpl; [reflexivity|].
now rewrite IHp.
Qed.

(*as in std*)
Lemma replace_replace_eq A: forall n p (v : t A n) a b,
  replace (replace v p a) p b = replace v p b.
Proof.
intros n p v a b.
induction p as [|? p IHp]; rewrite (eta v); simpl; [reflexivity|].
now rewrite IHp.
Qed.

(*as in std*)
Lemma replace_replace_neq A: forall n p1 p2 (v : t A n) a b, p1 <> p2 ->
  replace (replace v p1 a) p2 b = replace (replace v p2 b) p1 a.
Proof.
apply (Fin.rect2 (fun n p1 p2 => forall v a b,
  p1 <> p2 -> replace (replace v p1 a) p2 b = replace (replace v p2 b) p1 a)).
- intros n v a b Hneq.
  now contradiction Hneq.
- intros n p2 v; revert n v p2.
  refine (@rectS _ _ _ _); auto.
- intros n p1 v; revert n v p1.
  refine (@rectS _ _ _ _); auto.
- intros n p1 p2 IH v; revert n v p1 p2 IH.
  refine (@rectS _ _ _ _); simpl; intro n; [| do 3 intro]; intros ? ? IH p1 p2; intro Hneq;
    f_equal; apply IH; intros Heq; apply Hneq; now subst.
Qed.

(*vector_ind instead of tactic*)
Lemma replace_append_L A: forall n m (v : t A n) (w : t A m) p a,
  replace (v ++ w) (Fin.L m p) a = (replace v p a) ++ w.
Proof.
intros n m v.
revert m.
apply (vector_ind A (fun n v => forall (m : nat) (w : t A m) (p : Fin.t n) (a : A), replace (v ++ w) (Fin.L m p) a = replace v p a ++ w)).
- intros. now apply Fin.case0.
- intros h n' v' IH m w p a. apply (Fin.caseS' p).
  + reflexivity.
  + intros p'. cbn. apply f_equal, IH.
Qed.

(*vector_ind instead of tactic*)
Lemma replace_append_R A: forall n m (v : t A n) (w : t A m) p a,
  replace (v ++ w) (Fin.R n p) a = v ++ (replace w p a).
Proof.
intros n m v.
revert m.
apply (vector_ind A (fun n v => forall (m : nat) (w : t A m) (p : Fin.t m) (a : A), replace (v ++ w) (Fin.R n p) a = v ++ replace w p a)).
- intros; reflexivity.
- intros h n' v' IH m w p a. cbn. apply f_equal, IH.
Qed.


(*as in std*)
Lemma const_nth A (a: A) n (p: Fin.t n): (const a n)[@ p] = a.
Proof.
now induction p.
Qed.

(*as in std*)
Lemma append_const A (a : A) n m : (const a n) ++ (const a m) = const a (n + m).
Proof.
induction n as [|n IH].
- reflexivity.
- cbn. apply f_equal, IH.
Qed.

(*vector_ind instead of tactic*)
Lemma map_id A: forall n (v : t A n),
  map (fun x => x) v = v.
Proof.
apply vector_ind.
- auto.
- intros h n v IHv.  
simpl; rewrite IHv; auto.
Qed.

(*vector_ind instead of tactic*)
Lemma map_map A B C: forall (f:A->B) (g:B->C) n (v : t A n),
  map g (map f v) = map (fun x => g (f x)) v.
Proof.
intros f g n v.
revert f g.
apply (vector_ind A (fun n v => forall (f : A -> B) (g : B -> C), map g (map f v) = map (fun x : A => g (f x)) v)).
- auto.
- intros h n' v' IHv f g.
  simpl; rewrite IHv; auto.
Qed.

(*vector_ind instead of tactic*)
Lemma map_ext_in A B: forall (f g:A->B) n (v : t A n),
  (forall a, In a v -> f a = g a) -> map f v = map g v.
Proof.
intros f g n v H. 
revert f g H.
apply (vector_ind A (fun n v => forall f g : A -> B, (forall a : A, In a v -> f a = g a) -> map f v = map g v)).
- intros; reflexivity.
- intros h n' v' IHv f g H. cbn. now f_equal; [|apply IHv; intros ??]; apply H; [left|right].
Qed.

(*as in std*)
Lemma map_ext A B: forall (f g:A->B), (forall a, f a = g a) ->
  forall n (v : t A n), map f v = map g v.
Proof.
intros; apply map_ext_in; auto.
Qed.

(*as in std*)
Lemma nth_map {A B} (f: A -> B) {n} v (p1 p2: Fin.t n) (eq: p1 = p2):
  (map f v) [@ p1] = f (v [@ p2]).
Proof.
subst p2; induction p1 as [n|n p1 IHp1].
- revert n v; refine (@caseS _ _ _); reflexivity.
- revert n v p1 IHp1; refine (@caseS _  _ _); now simpl.
Qed.

(*vector_ind instead of tactic*)
Lemma map_append A B: forall (f:A->B) n m (v: t A n) (w: t A m),
  (map f (v ++ w)) = map f v ++ map f w.
Proof.
intros f n m v w.
apply (vector_ind A (fun n v => map f (v ++ w) = map f v ++ map f w)).
- reflexivity.
- intros h n' v' IHv. cbn. apply f_equal, IHv.
Qed.

(*as in std*)
Lemma nth_map2 {A B C} (f: A -> B -> C) {n} v w (p1 p2 p3: Fin.t n):
  p1 = p2 -> p2 = p3 -> (map2 f v w) [@p1] = f (v[@p2]) (w[@p3]).
Proof.
intros; subst p2; subst p3; revert n v w p1.
refine (@rect2 _ _ _ _ _); simpl.
- exact (Fin.case0 _).
- intros n v1 v2 H a b p; revert n p v1 v2 H; refine (@Fin.caseS _ _ _);
    now simpl.
Qed.

(*as in std*)
Lemma map2_ext A B C: forall (f g:A->B->C), (forall a b, f a b = g a b) ->
  forall n (v : t A n) (w : t B n), map2 f v w = map2 g v w.
Proof.
intros f g Hfg n v w.
apply (fun P H1 H2 => rect2 P H1 H2 v w).
- reflexivity.
- cbn. intros ??? IH ??. now rewrite IH, Hfg.
Qed.

(** ** Properties of [fold_left] *)

(*vector_ind instead of tactic*)
Lemma fold_left_right_assoc_eq {A B} {f: A -> B -> A}
  (assoc: forall a b c, f (f a b) c = f (f a c) b)
  {n} (v: t B n): forall a, fold_left f a v = fold_right (fun x y => f y x) v a.
Proof.
assert (forall n h (v: t B n) a, fold_left f (f a h) v = f (fold_left f a v) h).
- intros n0 h v0. 
  apply (vector_ind B (fun n0 v0 => forall a : A, fold_left f (f a h) v0 = f (fold_left f a v0) h)).
  + now simpl.
  + intros h0 n1 v1 IHv0 a; simpl. rewrite<- IHv0, assoc. now f_equal.
- apply (vector_ind B (fun n v => forall a : A, fold_left f a v = fold_right (fun (x : B) (y : A) => f y x) v a)).
  + reflexivity.
  + intros h n' v' IHv a;  simpl. intros; now rewrite<- (IHv).
Qed.

(** ** Properties of [take] *)

(*had to destuct n not shure why*)
Lemma take_O : forall {A} {n} le (v:t A n), take 0 le v = [].
Proof.
intros A n le v. destruct n; reflexivity.
Qed.

(*destruct n*)
Lemma take_idem : forall {A} p n (v:t A n) le le',
  take p le' (take p le v) = take p le v.
Proof.
  intros A p; induction p as [|p IHp]; intros n v le le'.
  - destruct n; reflexivity.
  - destruct n; destruct v.
    + inversion le.
    + simpl. apply f_equal, IHp.
Qed.


(*****************************************************************)
