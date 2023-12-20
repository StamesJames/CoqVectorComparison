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