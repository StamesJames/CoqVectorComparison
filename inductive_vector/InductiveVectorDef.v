
Require Import Arith_base.
Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.

Inductive t A : nat -> Type :=
  |nil : t A 0
  |cons : forall (h:A) (n:nat), t A n -> t A (S n).

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :=
 fix rectS_fix {n} (v: t A (S n)) : P v :=
 match v with
 |@cons _ a 0 v =>
   match v with
     |nil _ => bas a
     |_ => fun devil => False_ind (@IDProp) devil
   end
 |@cons _ a (S nn') v => rect a v (rectS_fix v)
 |_ => fun devil => False_ind (@IDProp) devil
 end.

 Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v :=
match v with
  |[] => H
  |_ => fun devil => False_ind (@IDProp) devil
end.

Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
  |h :: t => H h t
  |_ => fun devil => False_ind (@IDProp) devil
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

Definition hd {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd {A} {n} v.

Definition tl {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
Global Arguments tl {A} {n} v.

Definition last {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last {A} {n} v.

Definition const {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).

Definition nth {A} :=
  fix nth_fix {n : nat} (v : t A n) {struct v} : Fin.t n -> A :=
    match v with
    | nil _ => fun p => False_rect A (Fin.case0 _ p)
    | cons _ x m v' => fun p =>
      match p in (Fin.t m') return t A (pred m') -> A with
      | Fin.F1 => fun _ => x
      | Fin.FS p' => fun v' => nth_fix v' p'
      end v'
    end.

Fixpoint replace {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
  match p with
  | @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => a :: t)
  | @Fin.FS k p' => fun v' : t A (S k) =>
    (caseS' v' (fun _ => t A (S k)) (fun h t => h :: (replace t p' a)))
  end v.

Fixpoint take {A} {n} (p:nat) (le:p <= n) (v:t A n) : t A p :=
  match p as p return p <= n -> t A p with
  | 0 => fun _ => []
  | S p' => match v in t _ n return S p' <= n -> t A (S p') with
    | []=> fun le => False_rect _ (Nat.nle_succ_0 p' le)
    | x::xs => fun le => x::take p' (le_S_n p' _ le) xs
    end
  end le.

Fixpoint append {A}{n}{p} (v:t A n) (w:t A p):t A (n+p) :=
match v with
| [] => w
| a :: v' => a :: (append v' w)
end.

Infix "++" := append.

Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p)
  : t A (Nat.tail_add n p) :=
  match v with
  | [] => w
  | a :: v' => rev_append_tail v' (a :: w)
  end.

Definition rev_append {A n p} (v: t A n) (w: t A p)
  :t A (n + p) :=
  rew (Nat.tail_add_spec n p) in (rev_append_tail v w).

Definition rev {A n} (v : t A n) : t A n :=
 rew <- (plus_n_O _) in (rev_append v []).

Local Notation "v [@ p ]" := (nth v p) (at level 1).

Definition map {A} {B} (f : A -> B) : forall {n} (v:t A n), t B n :=
  fix map_fix {n} (v : t A n) : t B n := match v with
  | [] => []
  | a :: v' => (f a) :: (map_fix v')
  end.

Definition fold_right {A B : Type} (f : A->B->B) :=
  fix fold_right_fix {n} (v : t A n) (b:B)
  {struct v} : B :=
  match v with
    | [] => b
    | a :: w => f a (fold_right_fix w b)
  end.

Fixpoint of_list {A} (l : list A) : t A (length l) :=
match l as l' return t A (length l') with
  |Datatypes.nil => []
  |(h :: tail)%list => (h :: (of_list tail))
end.

Definition to_list {A}{n} (v : t A n) : list A :=
Eval cbv delta beta in fold_right (fun h H => Datatypes.cons h H) v Datatypes.nil.

Module InductiveVectorNotations.
Declare Scope inductive_vector_scope.
Delimit Scope inductive_vector_scope with inductive_vector.
Notation "[ ]" := [] (format "[ ]") : inductive_vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
  : inductive_vector_scope.
Notation "[ x ]" := (x :: []) : inductive_vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : inductive_vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : inductive_vector_scope.
Infix "++" := append : inductive_vector_scope.
Open Scope inductive_vector_scope.
End InductiveVectorNotations.

Fixpoint splitat {A} (l : nat) {r : nat} :
  t A (l + r) -> t A l * t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (v1, v2) := splitat l' (tl v) in
    (hd v::v1, v2)
  end.

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

Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) :=
match v with
  |[] => a :: []
  |h :: t => h :: (shiftin a t)
end.