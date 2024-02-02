Require fin_utils.
Require lia_utils.
Require Import Arith_base.
Require Fin.
Import EqNotations.
Local Open Scope nat_scope.
Require Import FunctionalExtensionality.

(*Set Universe Polymorphism.*)

Definition t (A : Type) (n : nat) := Fin.t n -> A.

Definition nil : forall A:Type, t A 0 :=
  fun A i => Fin.case0 (fun _ => A) i.

Definition cons : forall A:Type, A -> forall n:nat, t A n -> t A (S n) :=
  fun A h n v => fun i : Fin.t (S n) => 
    match i in Fin.t (S n) return t A n -> A with
    | Fin.F1 => fun _ => h 
    | Fin.FS i' => fun v' => v' i' 
    end v.

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section BASES.

Definition hd {A:Type} {n:nat} (v:t A (S n) ) : A := v Fin.F1.

Definition tl {A : Type} {n : nat} (v : t A (S n)) : t A n := 
  fun i:(Fin.t n) => v (Fin.FS i).

End BASES.

Section SCHEMES.

Lemma eta {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof. apply functional_extensionality. intros i. pattern i. apply Fin.caseS'; reflexivity. Qed.

Lemma nil_spec {A} (v : t A 0) : v = [].
Proof. apply functional_extensionality. apply Fin.case0. Qed.

Lemma rectS_aux {A}: forall (v:t A 1), v = (hd v :: []).
Proof. intros v. rewrite (eta v). rewrite (nil_spec (tl v)). reflexivity. Qed.

Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)):=
 fix rectS_fix {n} (v : t A (S n)) : P v := 
 match n return (forall v:t A (S n), P v) with 
 | 0 => fun v => rew <- rectS_aux v in bas (hd v) 
 | S n' => fun v => rew <- eta v in rect (hd v) (tl v) (rectS_fix (tl v)) 
 end v.

Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v := rew <- nil_spec v in H.

Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
rew <- eta v in H (v Fin.F1) (tl v).

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (h :: t)), P v :=
fun P:t A (S n) -> Type =>
  fun (H:(forall (h : A) (t : t A n), P (h :: t))) => 
    rew <- eta v in H (v Fin.F1) (tl v).

Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
  (bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
    forall a b, P (a :: v1) (b :: v2)) :=
    fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
    match n return forall v1:t A n, forall v2, P v1 v2 with
    | 0 => fun v1 v2 => 
      rew <- [fun v1 : t A 0 => P v1 v2] nil_spec v1 in
      rew <- [fun v2 : t B 0 => P [] v2] nil_spec v2 in bas
    | S n' => fun v1 v2 => 
      rew <- [fun v1 : t A (S n') => P  v1 v2] eta v1 in
      rew <- [fun v2 : t B (S n') => P (hd v1 :: tl v1) v2] eta v2 in
      @rect n' (tl v1) (tl v2) (rect2_fix (tl v1) (tl v2)) (hd v1) (hd v2) 
    end v1.
End SCHEMES.


Section BASES.

(*as in std*)
Definition hd_std {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd {A} {n} v.

Definition last {A:Type} {n:nat} (v:t A (S n) ) : A := v (fin_utils.nat_to_fin n).

(*as in std*)
Definition last_std {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last {A} {n} v.

Definition const {A:Type} (a:A) (n:nat) : t A n :=
fun (f: Fin.t n) => a.

(*as in std*)
Definition const_std {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).

Definition nth {A:Type} {n:nat} (v:t A n) (f:Fin.t n) : A := v f.

(*as in std*)
Definition nth_order {A} {n} (v: t A n) {p} (H: p < n) :=
(nth v (Fin.of_nat_lt H)).

Definition replace {A:Type} {n:nat} (v:t A n) (f:Fin.t n) (a:A) : t A n :=
  fun (f':Fin.t n) => if (Fin.eqb f' f) then a else (v f).

(*as in std*)
Fixpoint replace_std {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
  match p with
  | @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => a :: t)
  | @Fin.FS k p' => fun v' : t A (S k) =>
    (caseS' v' (fun _ => t A (S k)) (fun h t => h :: (replace_std t p' a)))
  end v.

(*as in std*)
Definition replace_order {A n} (v: t A n) {p} (H: p < n) :=
replace v (Fin.of_nat_lt H).

(*as in std*)
Definition tl_std {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
Global Arguments tl {A} {n} v.

(*as in std*)
Definition uncons {A} {n : nat} (v : t A (S n)) : A * t A n := (hd v, tl v).

(*as in std*)
Definition shiftout {A} := @rectS _ (fun n _ => t A n) (fun a => [])
  (fun h _ _ H => h :: H).
Global Arguments shiftout {A} {n} v.

Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) := 
match n return t A n -> t A (S n) with
| 0 => fun v => a :: [] 
| S n' => fun v => hd v :: (shiftin a (tl v))
end v.

(*as in std*)
Definition shiftrepeat {A} := @rectS _ (fun n _ => t A (S (S n)))
  (fun h =>  h :: h :: []) (fun h _ _ H => h :: H).
Global Arguments shiftrepeat {A} {n} v.

Definition take {A:Type} {n:nat} : forall p : nat, (p < n) -> (t A n) -> t A p :=
  fun (p:nat) (H: p<n) (v:t A n) =>
    fun (f:Fin.t p) => v (Fin.of_nat_lt H).

(*as in std*)
Lemma trunc : forall {A} {n} (p:nat), n > p -> t A n
  -> t A (n - p).
Proof.
    intros A n p; induction p as [| p f]; intros H v.
    - rewrite Nat.sub_0_r.
      exact v.
    - apply shiftout.
      rewrite <- Nat.sub_succ_l.
      + exact (f (Nat.lt_le_incl _ _ H) v).
      + exact (Nat.lt_le_incl _ _ H).
Defined.


Definition append {A:Type} {n:nat} {p:nat} (v:t A n) (w:t A p) : t A (n + p) := 
  fun (i: Fin.t (n+p)) => Fin.case_L_R' (fun x => A) i (fun i:Fin.t n => v i) (fun i:Fin.t p => w i).

Infix "++" := append.

Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p) 
  : t A (Nat.tail_add n p) :=
match n return t A n -> t A (Nat.tail_add n p) with 
| 0 => fun v => w
| S n' => fun v => rev_append_tail (tl v) (hd v :: w)
end v.

(*as in std*)
Definition rev_append {A n p} (v: t A n) (w: t A p)
  :t A (n + p) :=
  rew (Nat.tail_add_spec n p) in (rev_append_tail v w).


Definition rev {A:Type} {n:nat} (v:t A n) : t A n :=
fun f:Fin.t n => v (fin_utils.fin_inv f).

(*as in std*)
Definition rev_std {A n} (v : t A n) : t A n :=
 rew <- (plus_n_O _) in (rev_append v []).
End BASES.
Local Notation "v [@ p ]" := (nth v p) (at level 1).

Section ITERATORS.

Definition map {A} {B} (f : A -> B) : forall {n} (v:t A n), t B n :=
fun (n:nat) (v:t A n) => 
  fun i:Fin.t n => f (v i).

(*as in std*)
Definition map2 {A B C} (g:A -> B -> C) :
  forall (n : nat), t A n -> t B n -> t C n :=
@rect2 _ _ (fun n _ _ => t C n) (nil C) (fun _ _ _ H a b => (g a b) :: H).
Global Arguments map2 {A B C} g {n} v1 v2.

Definition fold_left {A B:Type} (f:B->A->B): forall (b:B) {n} (v:t A n), B :=
fix fold_left_fix (b:B) {n} (v : t A n) : B := 
  match n return t A n -> B with
  | 0 => fun v => b
  | S n' => fun v => fold_left_fix (f b (hd v)) (tl v)
  end v.

Definition fold_right {A B : Type} (f : A->B->B) :=
  fix fold_right_fix {n} (v : t A n) (b:B)
  {struct n} : B :=
  match n return t A n -> B with
  | 0 => fun v => b
  | S n' => fun v => f (hd v) (fold_right_fix (tl v) b)
  end v.

(*as in std*)
Definition fold_right2 {A B C} (g:A -> B -> C -> C) (c: C) :=
  @rect2 _ _ (fun _ _ _ => C) c (fun _ _ _ H a b => g a b H).

Definition fold_left2 {A B C: Type} (f : A -> B -> C -> A) :=
  fix fold_left2_fix (a : A) {n} (v : t B n) : t C n -> A :=
  match n return t B n -> t C n -> A with
    | 0 => fun v w => case0 (fun _ => A) a w
    | S n' => fun v w => 
      caseS' w (fun _ => A) (fun wh wt => fold_left2_fix (f a (hd v) (hd w)) (tl v) (tl w))
  end v.

End ITERATORS.

(*as in std*)
Section SCANNING.
Inductive Forall {A} (P: A -> Prop): forall {n} (v: t A n), Prop :=
 |Forall_nil: Forall P []
 |Forall_cons {n} x (v: t A n): P x -> Forall P v -> Forall P (x::v).
#[local]
Hint Constructors Forall : core.

Inductive Exists {A} (P:A->Prop): forall {n}, t A n -> Prop :=
 |Exists_cons_hd {m} x (v: t A m): P x -> Exists P (x::v)
 |Exists_cons_tl {m} x (v: t A m): Exists P v -> Exists P (x::v).
#[local]
Hint Constructors Exists : core.

Inductive In {A} (a:A): forall {n}, t A n -> Prop :=
 |In_cons_hd {m} (v: t A m): In a (a::v)
 |In_cons_tl {m} x (v: t A m): In a v -> In a (x::v).
#[local]
Hint Constructors In : core.

Inductive Forall2 {A B} (P:A->B->Prop): forall {n}, t A n -> t B n -> Prop :=
 |Forall2_nil: Forall2 P [] []
 |Forall2_cons {m} x1 x2 (v1:t A m) v2: P x1 x2 -> Forall2 P v1 v2 ->
    Forall2 P (x1::v1) (x2::v2).
#[local]
Hint Constructors Forall2 : core.

Inductive Exists2 {A B} (P:A->B->Prop): forall {n}, t A n -> t B n -> Prop :=
 |Exists2_cons_hd {m} x1 x2 (v1: t A m) (v2: t B m): P x1 x2 -> Exists2 P (x1::v1) (x2::v2)
 |Exists2_cons_tl {m} x1 x2 (v1:t A m) v2: Exists2 P v1 v2 -> Exists2 P (x1::v1) (x2::v2).
#[local]
Hint Constructors Exists2 : core.
End SCANNING.

Section VECTORLIST.
Definition of_list {A:Type} : forall l : list A, t A (length l) :=
fun l: list A => 
  match l with 
  | Datatypes.nil => fun i:Fin.t (length Datatypes.nil) => match i with end
  | (x::xs)%list => fun i:Fin.t (length (x::xs)%list) => List.nth (fin_utils.fin_to_nat i) l x
  end.

(*as in std*)
Fixpoint of_list_std {A} (l : list A) : t A (length l) :=
  match l as l' return t A (length l') with
    |Datatypes.nil => []
    |(h :: tail)%list => (h :: (of_list_std tail))
  end.

Definition to_list {A}{n} (v : t A n) : list A :=
  fin_utils.fin_fold_right Datatypes.nil (fun i acc => ((v i)::acc)%list).

  (*as in std*)
Definition to_list_std {A}{n} (v : t A n) : list A :=
  Eval cbv delta beta in fold_right (fun h H => Datatypes.cons h H) v Datatypes.nil.
End VECTORLIST.


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

