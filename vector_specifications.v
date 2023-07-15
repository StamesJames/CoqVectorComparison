(*
induction
hd, tl
last
const
nth
replace
take
append
rev
map
fold_right
of_list, to_list
*)
Module StdVector.

Require Import Vector.

Check Vector.hd.

End StdVector.

Module InductiveVector.

Inductive vector (A : Type) : nat -> Type :=
  | nil : vector A 0
  | cons : forall (h : A) (n : nat), vector A n -> vector A (S n).

Arguments nil {A}.
Arguments cons {A}.


Check vector_ind.

Definition aux {X : Type} {n : nat} (v : vector X n) :=
  match n with 0 => fun (w : vector X 0) => w = nil | S _ => fun _ => True end v.

Lemma vec_nil_spec {X : Type} : forall (v : vector X 0), v = nil.
Proof.
  intros v.
  change (aux v).
  destruct v.
  - cbn.
    reflexivity.
  - cbn.
    apply I.
Qed.
(*
Lemma vector_ind' : forall (A : Type) (P : forall n : nat, vector A n -> Prop),
  P 0 nil -> (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (cons h n v)) -> 
  forall (n : nat) (v : vector A n), P n v.
Proof.
  intros A P H0 Hi n.
  induction n; cbn.
  - intros v.
    replace v with (@nil A).
    + apply H0.
    + rewrite (vec_nil_spec v).
      reflexivity.
  - intros v.
    destruct v .
    + apply H0.
    + apply Hi.
      apply IHn.
*)
End InductiveVector.

Module RecursiveVector.

Fixpoint vector (A : Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => A * (vector A n)
  end.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, vector A n -> Prop),
  P 0 tt -> (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (h, v)) -> 
  forall (n : nat) (v : vector A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n; cbn.
  - intros [].
    apply H1.
  - intros [h v].
    apply H2.
    apply IHn.
Qed.

Definition hd {A:Type} {n:nat} (v: vector A (S n)): A :=
  match v in vector A  return vector A n0 with 
  | unit => 
  | h * (vector A n) =>
  end.

End RecursiveVector.

Module FunctionalVector.

Inductive fin : nat -> Type :=
  | F0 : forall {n}, fin (S n)
  | FS : forall {n}, fin n -> fin (S n).

Definition vector (A : Type) (n : nat) := fin n -> A.

Definition fin_case0 P (p : fin 0) : P p :=
  match p with | F0 | FS _ => fun devil => False_rect (@IDProp) devil end.

Definition fin_caseS {n : nat} (p : fin (S n)) : forall (P : fin (S n) -> Type)
  (P1 : P F0) (PS : forall (p : fin n), P (FS p)), P p :=
  match p with
  | F0 => fun P P1 PS => P1
  | FS p' => fun P P1 PS => PS p'
  end.

Check fin_caseS.

Definition nil {A : Type} : vector A 0 := fun i => fin_case0 (fun _ => A) i.

Definition cons {A : Type} (h : A) (n : nat) (v : vector A n) : vector A (S n) :=
  fun i : fin (S n) =>
    match i in (fin n') return (vector A (Nat.pred n') -> A) with
    | F0 => fun _ => h
    | FS i' => fun v' => v' i'
    end v.

Definition hd {A : Type} {n : nat} (v : vector A (S n)) : A := v F0.

Definition tl {A : Type} {n : nat} (v : vector A (S n)) : vector A n := fun i => v (FS i).

Require Import FunctionalExtensionality.

Check functional_extensionality.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, vector A n -> Prop),
  P 0 nil -> (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (cons h n v)) ->
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
    replace v with (cons (hd v) n (tl v)).
    + apply H2.
      apply IHn.
    + apply functional_extensionality.
      intros i.
      apply (fin_caseS i (fun i => cons (hd v) n (tl v) i = v i)); reflexivity.
Qed.

Print Assumptions vector_ind.

End FunctionalVector.

Module ListVector.

Require Import Eqdep_dec Lia.

Record vector (A : Type) (n : nat) := 
  mk_vector { elts : list A; elts_spec : length elts = n }.

Arguments elts {A n}.
Arguments elts_spec {A n}.

Check mk_vector.
Check elts_spec.

Definition nil {A : Type} : vector A 0 := mk_vector A 0 (Datatypes.nil) eq_refl.

Definition cons {A : Type} (h : A) (n : nat) (v : vector A n) : vector A (S n) :=
  mk_vector A (S n) (Datatypes.cons h (elts v)) (f_equal S (elts_spec v)).

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
    + specialize (H2 h n (mk_vector A n elts (f_equal pred Helts)) (IHn _)).
      cbn in H2.
      replace Helts with (f_equal S (f_equal Nat.pred Helts)).
      * apply H2.
      * apply UIP_dec.
        decide equality.
Qed.

End ListVector.

(*

Compare:

induction
hd, tl
last
const
nth
replace
take
append
rev
map
fold_right
of_list, to_list

*)
