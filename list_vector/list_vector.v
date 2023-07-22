
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

Definition nil (A : Type) : vector A 0 := mk_vector  (Datatypes.nil) eq_refl.

Definition cons (A : Type) (h : A) (n : nat) (v : vector A n) : vector A (S n) :=
  mk_vector (Datatypes.cons h (elts v)) (f_equal S (elts_spec v)).

Arguments nil {A}%type_scope.
Arguments cons {A}%type_scope _ {n}%type_scope.

Definition vec_0:vector nat 0 := nil.
Definition vec_1 := cons 0 nil.
Definition vec_2 := cons 0 (cons 1 nil).
Definition vec_3 := cons 0 (cons 1 (cons 2 nil)).

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

Definition hd {A:Type} {n:nat} (v:vector A (S n)) : A.
Proof.
assert (H := elts_spec v).
destruct (elts v).
- cbn in H.
  abstract(lia).
- apply a.
Defined.

Check elts_spec.
Print hd.
(*
match (elts v) with
| [] => 
| x::_ => x
end.
*)

Definition hd' {A:Type} {n:nat} (v:vector A n) : option A :=
match (elts v) with
| [] => None
| x::l => Some x
end.

Goal hd' vec_0 = None.   reflexivity. Qed.
Goal hd' vec_1 = Some 0. reflexivity. Qed.
Goal hd' vec_2 = Some 0. reflexivity. Qed.
Goal hd' vec_3 = Some 0. reflexivity. Qed.

Lemma tail_spec {A:Type} {n:nat} (l:list A) (H:length l = n) : length (List.tl l) = pred n.
Proof.
destruct l, n; cbn; cbn in H; lia.
Qed.


Definition tl' {A:Type} {n:nat} (v:vector A n) : vector A (pred n):=
match n return (vector A n -> vector A (pred n)) with
| 0 => fun (v':vector A 0) => nil
| S m' as m => fun (v':vector A m) =>
    match v' with
    | {|elts := l; elts_spec := H |} => mk_vector (List.tl l) (tail_spec l H)
    end
end v.

Definition tl {A:Type} {n:nat} (v:vector A (S n)) : vector A n.
unshelve econstructor.
- apply (List.tl (elts v)).
- apply (tail_spec (elts v) (elts_spec v)).
Defined.

Print tl.

Lemma vec_eq {A:Type} {n:nat} : forall (v w: vector A n), elts v = elts w -> v = w.
Proof.
Admitted.

Goal tl vec_1 = nil. Proof. apply vec_eq. reflexivity. Qed.
Goal tl vec_2 = @cons nat 1 0 nil.          apply vec_eq. reflexivity. Qed.
Goal tl vec_3 = @cons nat 1 1 (@cons nat 2 0 nil). apply vec_eq. reflexivity. Qed.
(*
*)
(*
Definition last {A:Type} {n:nat} (v:vector A n) : option A :=


Goal last vec_0 = None.   reflexivity. Qed.
Goal last vec_1 = Some 0. reflexivity. Qed.
Goal last vec_2 = Some 1. reflexivity. Qed.
Goal last vec_3 = Some 2. reflexivity. Qed.
*)
(*
induction
last {A:Type} {n:nat} (v:vector A n) : option A :=
const const {A:Type} (a:A) (n:nat) : vector A n :=
nth
replace
take
append
rev
map
fold_right
of_list, to_list
*)
