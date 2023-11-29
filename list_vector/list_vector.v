Require Import fin_utils.
Require Import lia_utils.
Require Import Fin.

Require Import Eqdep_dec Lia.
Require Import List.
Import ListNotations.

Record vector (A : Type) (n : nat) := 
  mk_vector { elts : list A; elts_spec : length elts = n }.
Arguments mk_vector {A n}.
Arguments elts {A n}.
Arguments elts_spec {A n}.

Check mk_vector.
Check elts_spec.

(*
nil
*)
Definition nil (A : Type) : vector A 0 := mk_vector  (Datatypes.nil) eq_refl.

(*
cons
*)
Definition cons (A : Type) (h : A) (n : nat) (v : vector A n) : vector A (S n) :=
  mk_vector (Datatypes.cons h (elts v)) (f_equal S (elts_spec v)).

Arguments nil {A}%type_scope.
Arguments cons {A}%type_scope _ {n}%type_scope.
Arguments cons {A} h n / !v.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, vector A n -> Prop),
  P 0 nil -> (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (cons h n v)) ->
  forall (n : nat) (v : vector A n), P n v.
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

(*
hd
*)
Require Import Lia.

Open Scope list.

Definition hd_as_proof {A:Type} {n:nat} (v:vector A (S n)) : A.
Proof.
assert (H := elts_spec v).
destruct (elts v).
- cbn in H.
  abstract(lia).
- apply a.
Defined.
Definition hd {A:Type} {n:nat} (v:vector A (S n)) : A :=
  match elts_spec v with
  | H => 
    match elts v with 
    | l => 
      match l return (length (l) = S n -> A) with
      | [] => fun H: length [] = S n => match S_not_0 n H  with end 
      | h :: t => fun _ => h
      end H
    end
  end. 
Definition hd' {A:Type} {n:nat} (v:vector A n) : option A :=
match (elts v) with
| [] => None
| x::l => Some x
end.


(*
tl
*)
Lemma tail_spec {A:Type} {n:nat} (l:list A) (H:length l = n) : length (List.tl l) = pred n.
Proof.
destruct l, n; cbn; cbn in H; lia.
Qed.
Definition tl_asProof {A:Type} {n:nat} (v:vector A (S n)) : vector A n.
Proof.
unshelve econstructor.
- apply (List.tl (elts v)).
- apply (tail_spec (elts v) (elts_spec v)).
Defined.
Print tl_asProof.
Definition tl {A:Type} {n:nat} (v:vector A (S n)) : vector A n :=
{| elts := tl (elts v); elts_spec := tail_spec (elts v) (elts_spec v)|}.

Definition tl' {A:Type} {n:nat} (v:vector A n) : vector A (pred n):=
match n return (vector A n -> vector A (pred n)) with
| 0 => fun (v':vector A 0) => nil
| S m' as m => fun (v':vector A m) =>
    match v' with
    | {|elts := l; elts_spec := H |} => mk_vector (List.tl l) (tail_spec l H)
    end
end v.


(*
last
*)

Definition last {A:Type} {n:nat} (v:vector A (S n)) : A :=
    match elts_spec v with
    | H => 
      match elts v with 
      | l => 
        match l return (length (l) = S n -> A) with
        | [] => fun H: length [] = S n => match S_not_0 n H  with end 
        | h :: t => fun _ => List.last t h
        end H
      end
    end. 


Definition last' {A:Type} {n:nat} (v:vector A n ) : option A := 
match elts v with
| [] => None
| h::t => Some(List.last t h)
end.

(*
const
*)

Fixpoint const {A:Type} (a:A) (n:nat): vector A n :=
match n with
| 0 => nil
| S n' => cons a n' (const a n')
end.

(*
nth
*)

Definition nth {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) : A :=
match n return (vector A n) -> (Fin.t n) -> A with 
| 0 => fun (v:vector A 0) (f:Fin.t 0) => match f with end
| S n' => fun (v:vector A (S n')) (f:Fin.t (S n')) =>
  match v with 
  | {| elts := [] ; elts_spec := p |} => match S_not_0 n' p with end
  | {| elts := x::xs ; elts_spec := p |} => nth (fin_to_nat f) (elts v) x
  end
end v f.


Fixpoint list_replace {A:Type} (l:list A) (n:nat) (a:A) : list A := 
match l with
| [] => []
| x::xs => match n with 
  | 0 => a::xs
  | S n' => a::list_replace xs n' a
  end 
end.

Lemma list_replace_len_eq {A:Type}: forall (l:list A) (i:nat) (a:A), length l = length (list_replace l i a).
Proof.
intros l.
induction l.
- intros i a. 
  cbn.
  reflexivity.
- intros i a'.
  cbn.
  destruct i.
  + cbn.
    reflexivity.
  + rewrite (IHl i a').
    cbn.
    reflexivity.
Qed.

Lemma get_replace_len_spec {A:Type} {n:nat}: forall (l:list A) (p:length l = n) (i:nat) (a:A), length (list_replace l i a) = n.
Proof.
intros.
rewrite <- (list_replace_len_eq l i a).
apply p.
Qed.

(*
replace
*)
Definition replace {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) (a:A) : vector A n := 
match v with
| {| elts := l; elts_spec := p|} => {| elts := (list_replace l (fin_to_nat f) a); elts_spec := (get_replace_len_spec l p (fin_to_nat f) a)|} 
end.

Fixpoint list_take {A:Type} (l:list A) (n:nat) : list A := 
match l with
| [] => []
| x::xs => match n with 
  | 0 => x::xs
  | S n' => x:: list_take xs n'
  end 
end.

Print firstn_length_le.
Check firstn_length_le.

Lemma apply_eq_in_leq_R {i n m:nat}: forall (p:i<=n) (H:m = n), i<=m.
Proof.
intros.
rewrite H.
apply p.
Qed.

(*
take
*)
Definition take {A:Type} {n:nat} : forall i : nat, (i <= n) -> vector A n -> vector A i :=
fun (i:nat) (p:i <= n) (v: vector A n) =>
match v with
| {|elts := l ; elts_spec := s|} => 
  {|elts := firstn i l; elts_spec := (firstn_length_le l (apply_eq_in_leq_R p s))|}
end.

(*
append
*)
Lemma apply_eq_in_add_L {i n m x:nat}: forall (p:i = n) (H: x = i + m), x = n + m.
Proof.
lia.
Qed.

Lemma apply_eq_in_add_R {i n m x:nat}: forall (p:i = n) (H: x = m + i), x = m + n.
Proof.
lia.
Qed.

Definition append {A:Type} {n:nat} {p:nat} (v:vector A n) (w:vector A p) : vector A (n + p) :=
match v with {| elts := elts_v; elts_spec := elts_spec_v |} => match w with {| elts := elts_w ; elts_spec:=elts_spec_w|} => 
  {|elts := elts_v ++ elts_w; elts_spec := apply_eq_in_add_R elts_spec_w (apply_eq_in_add_L elts_spec_v (app_length elts_v elts_w))|} end end.

(*
rev
*)
Print eq_trans.

Definition rev {A:Type} {n:nat} (v:vector A n) : vector A n := 
match v with {|elts:=l;elts_spec:=p|} => 
{|elts:= rev l ; elts_spec:= eq_trans (rev_length l) p |}
end.

(*
map
*)
Definition map {A:Type} {B:Type} (f:A->B) : forall n: nat, vector A n -> vector B n :=
fun (n:nat) (v:vector A n) => 
match v with {|elts:=l;elts_spec:=p|} => 
{|elts:=map f l; elts_spec:= eq_trans (map_length f l) p|}
end.

(*
fold_right
*)
Definition fold_right {A:Type} {B:Type} (f:A->B->B) : forall n:nat, vector A n -> B -> B :=
fun (n:nat) (v:vector A n) (b:B) =>
match v with {|elts:=l;elts_spec:=p|} => 
fold_right f b l
end.

(*
of_list
*)
Definition of_list {A:Type} : forall l : list A, vector A (length l) := 
fun (l:list A) =>
{| elts := l; elts_spec := eq_refl |}.

(*
to_list
*)
Definition to_list {A:Type} {n:nat} (v:vector A n) : list A :=
match v with {|elts:=l;elts_spec:=p|} => 
l
end.