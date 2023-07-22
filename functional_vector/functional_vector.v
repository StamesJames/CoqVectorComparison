
Require Import Fin.
Print Fin.

Definition vector (A : Type) (n : nat) := Fin.t n -> A.

Check Fin.case0.
Check Fin.caseS.

(*
nil
*)
Definition nil : forall A:Type, vector A 0 :=
  fun A i => Fin.case0 (fun _ => A) i.

(*
cons
*)
Definition cons : forall A:Type, A -> forall n:nat, vector A n -> vector A (S n) :=
  fun A h n t => fun i : Fin.t (S n) =>
  match i in (Fin.t n') return (vector A (Nat.pred n') -> A) with
  | F1 => fun _ => h
  | FS i' => fun v' => v' i'
  end t.

Arguments nil {A}%type_scope.
Arguments cons {A}%type_scope _ {n}%type_scope.

(* 
hd 
*)
Definition hd {A:Type} {n:nat} (v:vector A (S n) ) : A :=v F1.

Definition hd'{A : Type} {n : nat} (v : vector A n) : option A :=
match n return (vector A n -> option A)with
| 0 => fun _:vector A 0 => None
| S n' => fun v':vector A (S n') => Some (v' F1)
end v.

(*
tl
*)
Definition tl {A : Type} {n : nat} (v : vector A (S n)) : vector A n := 
  fun i:(Fin.t n) => v (FS i).

Definition calc_fin {n:nat} (f:Fin.t (S (pred (S n)))): Fin.t (S n) := f.

Definition tl' {A : Type} {n : nat} (v : vector A n) : vector A (pred n) :=
match n return (vector A n -> vector A (pred n) )with
| 0 => fun _:vector A 0 => nil
| S n' => fun v':vector A (S n') => fun i:(Fin.t n') => v' (FS i)
end v.

Require Import FunctionalExtensionality.

Check functional_extensionality.

Check Fin.caseS.

Definition fin_caseS {n : nat} (p : Fin.t (S n)) : forall (P : Fin.t (S n) -> Type)
  (P1 : P F1) (PS : forall (p : Fin.t n), P (FS p)), P p :=
  match p with
  | F1 => fun P P1 PS => P1
  | FS p' => fun P P1 PS => PS p'
  end.

(*
vector_ind
*)
Lemma vector_ind :
  forall (A : Type) (P : forall n : nat, vector A n -> Prop),
    P 0 nil -> 
    (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (cons h v)) -> 
    forall (n : nat) (v : vector A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n; cbn.
  - intros v.
    replace v with (@nil A).
    + apply H1.
    + apply functional_extensionality.
      apply (Fin.case0 _).
  - intros v.
    replace v with (cons (hd v) (tl v)).
    + apply H2.
      apply IHn.
    + apply functional_extensionality.
      intros i.
      Check Fin.caseS.
      apply (fin_caseS i (fun i => cons (hd v) (tl v) i = v i)); reflexivity.
Qed.

Print Assumptions vector_ind.

Fixpoint nat_to_fin (n:nat) : Fin.t (S n) :=
match n with
| 0 => F1
| S n' => FS (nat_to_fin n')
end.

Definition last' {A:Type} {n:nat} (v:vector A n) : option A :=
match n return (vector A n -> option A) with
| 0 => fun _ => None
| S n' => fun (v':vector A (S n')) => Some (v' (nat_to_fin n'))
end v.

Goal last' vec_0 = None.   reflexivity. Qed.
Goal last' vec_1 = Some 0. reflexivity. Qed.
Goal last' vec_2 = Some 1. reflexivity. Qed.
Goal last' vec_3 = Some 2. reflexivity. Qed.

Definition const {A:Type} (a:A) (n:nat) : vector A n :=
fun (f: Fin.t n) => a.
(*
Goal const 1 0 = nil.                          reflexivity. Qed.
Goal const 1 1 = cons 1 nil.                   reflexivity. Qed.
Goal const 1 2 = cons 1 (cons 1 nil).          reflexivity. Qed.
Goal const 1 3 = cons 1 (cons 1 (cons 1 nil)). reflexivity. Qed.
*)

Definition nth {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) : A := v f.

(*

Definition lower_fin_bound {n:nat} (f:fin n) (m:nat) (H:m<=n) :=

Definition take {A:Type} {n:nat} : forall p : nat, 
  (p <= n) -> (v:vector A n) -> vector A m :=
fun (p:nat) (H:p<=n) (v:vector A n) => 
  

Definition replace {A:Type} {n:nat} (v:vector A n) (f:fin n) (a:A) : vector A n :=
  fun f' => 
  match f' with
  | f => a
  | _ => v f'
  end.
(*
induction
replace
take
append
rev
map
fold_right
of_list, to_list
*)

*)