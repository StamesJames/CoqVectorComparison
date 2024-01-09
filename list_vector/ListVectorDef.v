Require Import fin_utils.
Require Import lia_utils.
Require Import list_utils.
Require Import Fin.
Require Import Eqdep_dec Lia.
Require Import Arith_base.
Import EqNotations.
Local Open Scope nat_scope.

Record t (A : Type) (n : nat) := 
  mk_vector { elts : list A; elts_spec : length elts = n }.
Arguments mk_vector {A n}.
Arguments elts {A n}.
Arguments elts_spec {A n}.

Definition nil (A : Type) : t A 0 := mk_vector  (Datatypes.nil) eq_refl.

Definition cons (A : Type) (h : A) (n : nat) (v : t A n) : t A (S n) :=
  mk_vector (h :: (elts v))%list (f_equal S (elts_spec v)).

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Require Import Lia.

Lemma vec_spec_eq: forall {A:Type} {n:nat}, forall (v1 v2: t A n), elts v1 = elts v2 <-> v1 = v2.
Proof.
intros.
split.
- intros H.
  destruct v1, v2.
  cbn in *.
  destruct H.
  enough (elts_spec0 = elts_spec1).
  + rewrite H.
    reflexivity.
  + Check Eqdep_dec.UIP_dec.
    apply Eqdep_dec.UIP_dec.
    apply PeanoNat.Nat.eq_dec.
- intros H.
  destruct v1, v2.
  apply (f_equal elts) in H.
  cbn in *.
  apply H.
Qed.


Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
(bas: forall a: A, P (a :: []))
(rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) 
: forall (n:nat) (v:t A (S n)), P v.
Proof.
refine (fix rectS_fix (n:nat) (v:t A (S n)) : @P n v := _).
destruct v.
destruct elts0.
- refine (match lia_utils.S_not_0 n elts_spec0 with end).
- destruct elts0.
  + apply (f_equal pred) in elts_spec0 as H.
    cbn in H.
    destruct H.
    rewrite (lia_utils.nat_uip elts_spec0 eq_refl).
    refine (bas a).
  + destruct n.
    * apply (f_equal pred) in elts_spec0 as H.
      refine (match lia_utils.S_not_0 _ (eq_sym H) with end).
    * apply (f_equal pred) in elts_spec0 as H.
      change (Init.Nat.pred (length (a :: a0 :: elts0)) = Init.Nat.pred (S (S n))) with (length (a0::elts0) = S n) in H.
      specialize (rect a n {|elts := a0 :: elts0; elts_spec := H|}).
      specialize (rectS_fix n {| elts := a0 :: elts0; elts_spec := H |}).
      specialize (rect rectS_fix).
      unfold cons in rect.
      cbn in rect.
      rewrite (lia_utils.nat_uip elts_spec0 (f_equal S H)).
      refine (rect).
Defined.

Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v:=
match v with | {| elts := l; elts_spec := l_sp |} => 
  match l return (forall l_sp, P {| elts := l; elts_spec := l_sp |}) with
  | Datatypes.nil => fun l_sp => 
    rew <- [fun l_sp => P {| elts := Datatypes.nil; elts_spec := l_sp |}] nat_uip l_sp eq_refl in H
  | (a :: l)%list => fun l_sp => match S_not_0 _ (eq_sym l_sp) with end
  end l_sp
end.

Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with {| elts := l; elts_spec := l_sp |} => 
    match l return (forall l_sp : length l = S n, P {| elts := l; elts_spec := l_sp |}) with
    | Datatypes.nil => fun l_sp => match S_not_0 n l_sp with end
    | (a :: l)%list => fun l_sp => 
          rew [fun e => P {| elts := a :: l; elts_spec := e |}] nat_uip (f_equal S (f_equal pred l_sp)) l_sp in 
          H a {| elts := l; elts_spec := f_equal pred l_sp |}
    end l_sp
end.
  
Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
(H : forall h t, P (h :: t)), P v :=
match v with
| h :: t => fun P H => H h t
| _ => fun devil => False_rect (@IDProp) devil
end.

Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
(bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
  forall a b, P (a :: v1) (b :: v2)) :=
fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
match v1 with
| [] => fun v2 => case0 _ bas v2
| @cons _ h1 n' t1 => fun v2 =>
  caseS' v2 (fun v2' => P (h1::t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
end.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, t A n -> Prop),
  P 0 (nil _) -> (forall (h : A) (n : nat) (v : t A n), P n v -> P (S n) (cons _ h n v)) ->
  forall (n : nat) (v : t A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n; cbn.
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


Definition hd {A:Type} {n:nat} (v:t A (S n)) : A :=
  match elts_spec v with
  | H => 
    match elts v with 
    | l => 
      match l return (length (l) = S n -> A) with
      | Datatypes.nil => fun H: length Datatypes.nil = S n => match S_not_0 n H  with end 
      | (h :: t)%list => fun _ => h
      end H
    end
  end. 

Lemma tl_aux {A:Type} {n:nat} (l:list A) (H:length l = n) : length (List.tl l) = pred n.
Proof.
destruct l, n; cbn; cbn in H; lia.
Qed.

Definition tl {A:Type} {n:nat} (v:t A (S n)) : t A n :=
{| elts := List.tl (elts v); elts_spec := tl_aux (elts v) (elts_spec v)|}.

Definition last {A:Type} {n:nat} (v:t A (S n)) : A :=
    match elts_spec v with
    | H => 
      match elts v with 
      | l => 
        match l return (length (l) = S n -> A) with
        | Datatypes.nil => fun H: length Datatypes.nil = S n => match S_not_0 n H  with end 
        | (h :: t)%list => fun _ => List.last t h
        end H
      end
    end. 

Fixpoint const {A:Type} (a:A) (n:nat): t A n :=
match n with
| 0 => nil _
| S n' => cons _ a n' (const a n')
end.

Definition nth {A:Type} {n:nat} (v:t A n) (f:Fin.t n) : A :=
match n return (t A n) -> (Fin.t n) -> A with 
| 0 => fun (v:t A 0) (f:Fin.t 0) => match f with end
| S n' => fun (v:t A (S n')) (f:Fin.t (S n')) =>
  match v with 
  | {| elts := Datatypes.nil ; elts_spec := p |} => match S_not_0 n' p with end
  | {| elts := (x::xs)%list ; elts_spec := p |} => List.nth (fin_to_nat f) (elts v) x
  end
end v f.

Lemma replace_aux {A:Type} {n:nat}: forall (l:list A) (p:length l = n) (i:nat) (a:A), length (list_utils.list_replace l i a) = n.
Proof.
intros.
rewrite <- (list_utils.list_replace_len_eq l i a).
apply p.
Qed.

Definition replace {A:Type} {n:nat} (v:t A n) (f:Fin.t n) (a:A) : t A n := 
match v with
| {| elts := l; elts_spec := p|} => {| elts := (list_replace l (fin_to_nat f) a); elts_spec := (replace_aux l p (fin_to_nat f) a)|} 
end.

Lemma take_aux {i n m:nat}: forall (p:i<=n) (H:m = n), i<=m.
Proof.
intros.
rewrite H.
apply p.
Qed.

Definition take {A:Type} {n:nat} : forall i : nat, (i <= n) -> t A n -> t A i :=
fun (i:nat) (p:i <= n) (v: t A n) =>
match v with
| {|elts := l ; elts_spec := s|} => 
  {|elts := List.firstn i l; elts_spec := (List.firstn_length_le l (take_aux p s))|}
end.

Lemma append_aux{x n m n' m': nat}: forall(pn:n = n') (pm: m = m') (H: x = n + m), x = n' + m'.  
Proof. lia. Qed.

Definition append {A:Type} {n:nat} {p:nat} (v:t A n) (w:t A p) : t A (n + p) :=
match v with {| elts := elts_v; elts_spec := elts_spec_v |} => match w with {| elts := elts_w ; elts_spec:=elts_spec_w|} => 
  {|elts := elts_v ++ elts_w; elts_spec := append_aux elts_spec_v elts_spec_w (List.app_length elts_v elts_w)|} end end.

Definition rev {A:Type} {n:nat} (v:t A n) : t A n := 
match v with {|elts:=l;elts_spec:=p|} => 
{|elts:= List.rev l ; elts_spec:= eq_trans (List.rev_length l) p |}
end.

Definition map {A:Type} {B:Type} (f:A->B) : forall n: nat, t A n -> t B n :=
fun (n:nat) (v:t A n) => 
match v with {|elts:=l;elts_spec:=p|} => 
{|elts:=List.map f l; elts_spec:= eq_trans (List.map_length f l) p|}
end.

Definition fold_right {A:Type} {B:Type} (f:A->B->B) : forall n:nat, t A n -> B -> B :=
fun (n:nat) (v:t A n) (b:B) =>
match v with {|elts:=l;elts_spec:=p|} => 
List.fold_right f b l
end.

Definition of_list {A:Type} : forall l : list A, t A (length l) := 
fun (l:list A) =>
{| elts := l; elts_spec := eq_refl |}.

Definition to_list {A:Type} {n:nat} (v:t A n) : list A :=
match v with {|elts:=l;elts_spec:=p|} => 
l
end.
















(*others*)
Definition hd' {A:Type} {n:nat} (v:t A n) : option A :=
match (elts v) with
| Datatypes.nil => None
| (x::l)%list => Some x
end.


Definition tl' {A:Type} {n:nat} (v:t A n) : t A (pred n):=
match n return (t A n -> t A (pred n)) with
| 0 => fun (v':t A 0) => nil _
| S m' as m => fun (v':t A m) =>
    match v' with
    | {|elts := l; elts_spec := H |} => mk_vector (List.tl l) (tl_aux l H)
    end
end v.

Definition last' {A:Type} {n:nat} (v:t A n ) : option A := 
match elts v with
| Datatypes.nil => None
| (h::t)%list => Some(List.last t h)
end.

Module ListVectorNotations.
Declare Scope list_vector_scope.
Delimit Scope list_vector_scope with list_vector.
Notation "[ ]" := [] (format "[ ]") : list_vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
  : list_vector_scope.
Notation "[ x ]" := (x :: []) : list_vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : list_vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : list_vector_scope.
Infix "++" := append : list_vector_scope.
Open Scope list_vector_scope.
End ListVectorNotations.