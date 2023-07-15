Module FunctionalVector.

Inductive fin : nat -> Type :=
  | F0 : forall {n}, fin (S n)
  | FS : forall {n}, fin n -> fin (S n).

Definition vector (A : Type) (n : nat) := fin n -> A.

Check False_rect.
Check IDProp.
Print IDProp.
Definition fin_case0 (P: fin 0 -> Type) (p : fin 0) : P p :=
match p with 
| F0 | FS _ => fun devil:False => False_rect (forall A : Prop, A -> A) devil 
end.
Print fin_case0.
Check fin_case0.

Definition fin_caseS {n : nat} (p : fin (S n)) : 
forall  (P : fin (S n) -> Type)
        (P1 : P F0) (PS : forall (p : fin n), P (FS p)), 
          P p :=
match p with
| F0 => fun P P1 PS => P1
| FS p' => fun P P1 PS => PS p'
end.

Check fin_caseS.

Definition nil (A : Type) : vector A 0 := 
  fun i => fin_case0 (fun _ => A) i.

Definition cons (A : Type) (h : A) (n : nat) (v : vector A n) : vector A (S n) :=
  fun i : fin (S n) =>
    match i in (fin n') return (vector A (Nat.pred n') -> A) with
    | F0 => fun _ => h
    | FS i' => fun v' => v' i'
    end v.
Arguments nil {A}%type_scope.
Arguments cons {A}%type_scope _ {n}%type_scope.


Definition vec_0:vector nat 0 := nil.
Definition vec_1 := cons 0 nil.
Definition vec_2 := cons 0 (cons 1 nil).
Definition vec_3 := cons 0 (cons 1 (cons 2 nil)).

Definition hd {A : Type} {n : nat} (v : vector A (S n)) : A := v F0.

Definition hd'{A : Type} {n : nat} (v : vector A n) : option A :=
match n return (vector A n -> option A)with
| 0 => fun _:vector A 0 => None
| S n' => fun v':vector A (S n') => Some (v' F0)
end v.

Goal hd' vec_0 = None.   reflexivity. Qed.
Goal hd' vec_1 = Some 0. reflexivity. Qed.
Goal hd' vec_2 = Some 0. reflexivity. Qed.
Goal hd' vec_3 = Some 0. reflexivity. Qed.

Definition tl {A : Type} {n : nat} (v : vector A (S n)) : vector A n := 
  fun i:(fin n) => v (FS i).

Definition calc_fin {n:nat} (f:fin (S (pred (S n)))): fin (S n) := f.

Definition tl' {A : Type} {n : nat} (v : vector A n) : vector A (pred n) :=
match n return (vector A n -> vector A (pred n) )with
| 0 => fun _:vector A 0 => nil
| S n' => fun v':vector A (S n') => fun i:(fin n') => v' (FS i)
end v.


Goal tl' vec_0 = nil.                 reflexivity. Qed.
Goal tl' vec_1 = nil.                 reflexivity. Qed.
Goal tl' vec_2 = cons 1 nil.          reflexivity. Qed.
Goal tl' vec_3 = cons 1 (cons 2 nil). reflexivity. Qed.

Require Import FunctionalExtensionality.

Check functional_extensionality.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, vector A n -> Prop),
  P 0 nil -> (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (cons h v)) ->
  forall (n : nat) (v : vector A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n; cbn.
  - intros v.
    replace v with (@nil A).
    + apply H1.
    + apply functional_extensionality.
      apply (fin_case0 _).
  - intros v.
    replace v with (cons (hd v) (tl v)).
    + apply H2.
      apply IHn.
    + apply functional_extensionality.
      intros i.
      apply (fin_caseS i (fun i => cons (hd v) (tl v) i = v i)); reflexivity.
Qed.

Print Assumptions vector_ind.

Fixpoint nat_to_fin (n:nat) : fin (S n) :=
match n with
| 0 => F0
| S n' => FS (nat_to_fin n')
end.

Definition last {A:Type} {n:nat} (v:vector A n) : option A :=
match n return (vector A n -> option A) with
| 0 => fun _ => None
| S n' => fun (v':vector A (S n')) => Some (v' (nat_to_fin n'))
end v.

Goal last vec_0 = None.   reflexivity. Qed.
Goal last vec_1 = Some 0. reflexivity. Qed.
Goal last vec_2 = Some 1. reflexivity. Qed.
Goal last vec_3 = Some 2. reflexivity. Qed.

Definition const {A:Type} (a:A) (n:nat) : vector A n :=
fun (f: fin n) => a.
(*
Goal const 1 0 = nil.                          reflexivity. Qed.
Goal const 1 1 = cons 1 nil.                   reflexivity. Qed.
Goal const 1 2 = cons 1 (cons 1 nil).          reflexivity. Qed.
Goal const 1 3 = cons 1 (cons 1 (cons 1 nil)). reflexivity. Qed.
*)
(*
induction
nth
replace
take
append
rev
map
fold_right
of_list, to_list
*)


End FunctionalVector.