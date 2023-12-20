Require Import fin_utils.
Require Import lia_utils.
Require Import Fin.
Require Import Arith_base.
Import EqNotations.
Local Open Scope nat_scope.
Require Import FunctionalExtensionality.

Definition t (A : Type) (n : nat) := Fin.t n -> A.

Definition nil : forall A:Type, t A 0 :=
  fun A i => Fin.case0 (fun _ => A) i.

Definition cons : forall A:Type, A -> forall n:nat, t A n -> t A (S n) :=
  fun A h n i => fun i' : Fin.t (S n) =>
  match i' in (Fin.t n') return (t A (Nat.pred n') -> A) with
  | F1 => fun _ => h
  | FS i'' => fun v' => v' i''
  end i.

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Definition hd {A:Type} {n:nat} (v:t A (S n) ) : A := v F1.

Definition tl {A : Type} {n : nat} (v : t A (S n)) : t A n := 
  fun i:(Fin.t n) => v (FS i).

Lemma vec_eq_first: forall (A:Type) (v:t A 1), v = (v Fin.F1 :: []).
intros A v.
apply functional_extensionality.
intros i.
pattern i.
apply Fin.caseS'; [|intros p]; cbn.
- reflexivity.
- apply Fin.case0.
  apply p.
Qed.

Lemma vec_hd_tl_eq: forall (n:nat) (A:Type) (v:t A (S n)), v = (v Fin.F1 :: tl v). 
Proof.
intros n A v.
apply functional_extensionality.
intros i.
pattern i.
apply Fin.caseS'.
- cbn.
  reflexivity.
- intros p.
  cbn.
  unfold tl.
  reflexivity.
Qed.

Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)): forall (n : nat) (v : t A (S n)), P v :=
 fix rectS_fix (n : nat) (v : t A (S n)) : P v := 
 match n as n0 return (forall v0 : t A (S n0), @P n0 v0) with
| 0 => fun v0 : t A 1 => 
  rew <- vec_eq_first A v0 in bas (v0 F1)
| S n' => fun v0 : t A (S (S n')) => rew <- vec_hd_tl_eq (S n') A v0 in rect (v0 F1) (tl v0) (rectS_fix n' (tl v0))
end v.

Lemma nil_spec {A:Type}: forall v:t A 0, v = nil A.
Proof. intros v. apply functional_extensionality. apply Fin.case0. Qed.

Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v := rew <- nil_spec v in H.

Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
rew <- vec_hd_tl_eq n A v in H (v F1) (tl v).

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
(H : forall h t, P (h :: t)), P v :=
fun P:t A (S n) -> Type =>
  fun (H:(forall (h : A) (t : t A n), P (h :: t))) => 
    rew <- vec_hd_tl_eq n A v in H (v F1) (tl v).

Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
(bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
  forall a b, P (a :: v1) (b :: v2)) :=
fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
match v1 with
| [] => fun v2 => case0 _ bas v2
| @cons _ h1 n' t1 => fun v2 =>
  caseS' v2 (fun v2' => P (h1::t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
end.

Lemma vector_ind :
  forall (A : Type) (P : forall n : nat, t A n -> Prop),
    P 0 (nil _) -> 
    (forall (h : A) (n : nat) (v : t A n), P n v -> P (S n) (cons _ h _ v)) -> 
    forall (n : nat) (v : t A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n; cbn.
  - intros v.
    replace v with (nil A).
    + apply H1.
    + apply functional_extensionality.
      apply (Fin.case0 _).
  - intros v.
    replace v with (cons _ (hd v) _ (tl v)).
    + apply H2.
      apply IHn.
    + apply functional_extensionality.
      intros i.
      Check Fin.caseS.
      apply (fin_caseS i (fun i => cons _ (hd v) _ (tl v) i = v i)); reflexivity.
Qed.

Definition last {A:Type} {n:nat} (v:t A (S n) ) : A := v (nat_to_fin n).

Definition const {A:Type} (a:A) (n:nat) : t A n :=
fun (f: Fin.t n) => a.

Definition nth {A:Type} {n:nat} (v:t A n) (f:Fin.t n) : A := v f.

Definition replace {A:Type} {n:nat} (v:t A n) (f:Fin.t n) (a:A) : t A n :=
  fun (f':Fin.t n) => if (Fin.eqb f' f) then a else (v f).

Definition replace' {A:Type} {n:nat} (p:nat) (v:t A n) (a:A) : forall H:(p < n), t A n := fun (H:p<n) =>
  fun (f':Fin.t n) => if (Fin.eqb f' (Fin.of_nat_lt H)) then a else (v (Fin.of_nat_lt H)).

Definition take {A:Type} {n:nat} : forall p : nat, (p < n) -> (t A n) -> t A p :=
  fun (p:nat) (H: p<n) (v:t A n) =>
    fun (f:Fin.t p) => v (Fin.of_nat_lt H).

Definition append {A:Type} {n:nat} {p:nat} (v:t A n) (w:t A p) : t A (n + p) := 
  fun (i: Fin.t (n+p)) => case_L_R' (fun x => A) i (fun i:Fin.t n => v i) (fun i:Fin.t p => w i).

Definition rev {A:Type} {n:nat} (v:t A n) : t A n :=
fun f:Fin.t n => v (fin_inv f).

Definition map {A:Type} {B:Type} (f:A->B) : forall n: nat, t A n -> t B n :=
fun (n:nat) (v:t A n) => 
  fun i:Fin.t n => f (v i).

Definition fold_right {A:Type} {B:Type} (f:A->B->B) : forall n:nat, t A n -> B -> B := 
fun n v b => 
fin_fold_right b (fun i acc => f (v i) acc).

(*
of_list
uses nth wich dosn't makes sure the index isn't out bounce. 
a save_nth standart function would be nice that takes a proof that the index isn't out of bounce. 
*)

Definition of_list {A:Type} : forall l : list A, t A (length l) :=
fun l: list A => 
  match l with 
  | Datatypes.nil => fun i:Fin.t (length Datatypes.nil) => match i with end
  | (x::xs)%list => fun i:Fin.t (length (x::xs)%list) => List.nth (fin_to_nat i) l x
  end.

(*
to_list
*)
Definition to_list {A:Type} {n:nat} (v:t A n) : list A :=
fin_fold_right Datatypes.nil (fun i acc => ((v i)::acc)%list).



Module FunctionalVectorNotations.
Declare Scope functional_vector_scope.
Delimit Scope functional_vector_scope with functional_vector.
Notation "[ ]" := [] (format "[ ]") : functional_vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
  : functional_vector_scope.
Notation "[ x ]" := (x :: []) : functional_vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : functional_vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : functional_vector_scope.
Infix "++" := append : functional_vector_scope.
Open Scope functional_vector_scope.
End FunctionalVectorNotations.















(*others*)
Definition hd'{A : Type} {n : nat} (v : t A n) : option A :=
match n return (t A n -> option A)with
| 0 => fun _:t A 0 => None
| S n' => fun v':t A (S n') => Some (v' F1)
end v.

Definition tl' {A : Type} {n : nat} (v : t A n) : t A (pred n) :=
match n return (t A n -> t A (pred n) )with
| 0 => fun _:t A 0 => (nil _)
| S n' => fun v':t A (S n') => fun i:(Fin.t n') => v' (FS i)
end v.

Definition last' {A:Type} {n:nat} (v:t A n) : option A :=
match n return (t A n -> option A) with
| 0 => fun _ => None
| S n' => fun (v':t A (S n')) => Some (v' (nat_to_fin n'))
end v.

Definition nth' {A:Type} {n:nat} : forall p:nat, (p < n) -> t A n -> A :=
  fun (p:nat) (H:p<n) (v:t A n) =>
    v (Fin.of_nat_lt H).