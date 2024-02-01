Require Import fin_utils.
Require Import lia_utils.
Require Import Arith_base.
Import EqNotations.
Local Open Scope nat_scope.
Require Import Fin.

(*Set Universe Polymorphism.*)

Fixpoint t (A : Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => A * (t A n)
  end.

Definition nil (A:Type) : t A 0 := tt.
Definition cons (A:Type) (a:A) (n:nat) (v:t A n) : t A (S n) :=
  (a,v).

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section SCHEMES.

Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :=
 fix rectS_fix {n} (v: t A (S n)) : P v :=
 match n return forall v:t A (S n), @P n v with 
 | 0 => fun v:t A (S 0) => 
    match v with (a, tt) => bas a end
 | S n' => fun v:t A (S (S n')) => 
    match v with 
    | (a, v) => rect a v (rectS_fix v)
    end 
  end v.

Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v :=
  match v with | tt => H end.

Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with (h,t) => H h t end.

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (h :: t)), P v :=
match v with (h,t) => fun P H => H h t end.

Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
  (bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
    forall a b, P (a :: v1) (b :: v2)) :=
  fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
  match n return forall v1:t A n, forall v2 : t B n, P v1 v2 with 
    | 0 => 
      fun v1:t A 0 => 
        fun v2:t B 0 => 
          match v1 with tt => 
            match v2 with tt => case0 _ bas tt 
            end 
          end
  | S n' => 
    fun v1:t A (S n') => 
      match v1 with (h1, t1) => 
        fun v2 => caseS' v2 (fun v2' => P (h1 :: t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
      end
  end v1.

End SCHEMES.

Section BASES.

Definition hd {A n} (v:t A (S n) ) : A := 
match v with
| (h,t) => h
end.

(*as in std*)
Definition hd_std {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd_std {A} {n} v.

Fixpoint last {A n} (v:t A (S n) ) : A :=
match n return (t A (S n) -> A) with
| 0 => fun v':t A (S 0) => 
  match v' with (h, tt) => h end
| S n' => fun v':t A (S (S n')) => 
  match v' with (h, t) => last t end
end v.

(*as in std*)
Definition last_std {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last_std {A} {n} v.

Fixpoint const {A} (a:A) (n:nat) : t A n := 
match n with 
| 0 => []
| S n' => a :: (const a n')
end.

(*as in std*)
Definition const_std {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).

Fixpoint nth {A n} (v:t A n) (f:Fin.t n) : A := 
match n return Fin.t n -> t A n -> A 
with | 0 => fun f _ => match f with end 
| S n' => fun f v => 
  match f in Fin.t (S n') return t A (S n') -> A with 
  |Fin.F1 => fun v => match v with (h,t) => h end 
  | Fin.FS f' => fun v =>  match v with (h,t) => nth t f' end 
  end v 
end f v.

(*as in std*)
Definition nth_order {A} {n} (v: t A n) {p} (H: p < n) :=
(nth v (Fin.of_nat_lt H)).

Fixpoint replace {A n} (v:t A n) (p:Fin.t n) (a:A) : t A n :=
match n return Fin.t n -> t A n -> t A n with 
| 0 => fun f _ => match f with end
| S n' => fun (f:Fin.t (S n')) (v:t A (S n')) => 
  match f in Fin.t (S n') return t A (S n') -> t A (S n') with 
  | @Fin.F1 n' => fun (v: t A (S n')) => match v with (x,xs) => (a,xs) end
  | @Fin.FS n' f' => fun (v: t A (S n')) => 
    match v with (x,xs) => (x,replace xs f' a) end
  end v
end p v.

(*as in std*)
Definition replace_order {A n} (v: t A n) {p} (H: p < n) :=
replace v (Fin.of_nat_lt H).

(*as in std*)
Fixpoint replace_std {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
  match p with
  | @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => a :: t)
  | @Fin.FS k p' => fun v' : t A (S k) =>
    (caseS' v' (fun _ => t A (S k)) (fun h t => h :: (replace_std t p' a)))
  end v.

Definition tl {A:Type} {n:nat} (v:t A (S n)) : t A n :=
  match v with (h,t) => t end.

(*as in std*)
Definition tl_std {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
Global Arguments tl_std {A} {n} v.

(*as in std*)
Definition uncons {A} {n : nat} (v : t A (S n)) : A * t A n := (hd v, tl v).

(*as in std*)
Definition shiftout {A} := @rectS _ (fun n _ => t A n) (fun a => [])
  (fun h _ _ H => h :: H).
Global Arguments shiftout {A} {n} v.

Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) :=
match n return t A n -> t A (S n) with
| 0 => fun v => match v with tt => a :: [] end
| S n' => fun v => match v with (h,t) => h :: (shiftin a t) end
end v.

(*as in std*)
Definition shiftrepeat {A} := @rectS _ (fun n _ => t A (S (S n)))
  (fun h =>  h :: h :: []) (fun h _ _ H => h :: H).
Global Arguments shiftrepeat {A} {n} v.

Fixpoint take {A} {n} (p:nat) (le:p <= n) (v:t A n) : t A p := 
match p return p <= n -> t A p with
| 0 => fun _ => [] 
| S p' => fun (H:(S p'<= n)) => 
  match n return (S p'<= n) -> t A n -> t A (S p') with 
  | 0 => fun (H:(S p'<= 0)) _ => match (Sn_not_leq_0 p' H) with end
  | S n' => fun (H:(S p'<= S n')) (v:t A (S n')) => 
    (hd v, @take A n' p' (leq_S p' n' H) (tl v))
  end H v
end le.

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

Fixpoint append {A}{n}{p} (v:t A n) (w:t A p):t A (n+p) :=
match n return t A n -> t A (n + p) with
| 0 => fun _ => w
| S n' => fun (v:t A (S n')) => match v with (x,xs) => (x, append xs w) end 
end v.

Infix "++" := append.

(*as in std*)
Fixpoint splitat {A} (l : nat) {r : nat} :
  t A (l + r) -> t A l * t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (v1, v2) := splitat l' (tl v) in
    (hd v::v1, v2)
  end.

Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p)
{struct n} : t A (Nat.tail_add n p) :=
(match n return t A n -> t A (Nat.tail_add n p) with 
| 0 => fun v => w
| S n' => fun v => match v with (a,v') => rev_append_tail v' (a :: w) end 
end v).

(*as in std*)
Definition rev_append {A n p} (v: t A n) (w: t A p)
  :t A (n + p) :=
  rew (Nat.tail_add_spec n p) in (rev_append_tail v w).

(*as in std*)
Definition rev {A n} (v : t A n) : t A n :=
  rew <- (plus_n_O _) in (rev_append v []).

Fixpoint snoc {A:Type} {n:nat} (v:t A n) (a:A): t A (S n) :=
  match n return t A n -> t A (S n) with
  | 0 => fun _ => a :: []
  | S n' => fun (v:t A (S n')) => match v with (x,xs) => (x,snoc xs a) end
  end v.
  
Fixpoint rev_with_snoc {A:Type} {n:nat} (v:t A n) : t A n :=
  match n return t A n -> t A n with
  | 0 => fun _ => []
  | S n' => fun (v:t A (S n')) => match v with (x,xs) => snoc (rev_with_snoc xs) x end
  end v.

End BASES.
Local Notation "v [@ p ]" := (nth v p) (at level 1).

Section ITERATORS.

Definition map {A} {B} (f:A->B) : forall {n} (v:t A n), t B n :=
fix map_fix {n} (v:t A n) : t B n :=
match n return t A n -> t B n with
| 0 => fun _ => []
| S n' => fun v => match v with (x,xs) => (f x, map_fix xs) end
end v.

Definition map2 {A B C} (g:A -> B -> C) :
  forall (n : nat), t A n -> t B n -> t C n :=
@rect2 _ _ (fun n _ _ => t C n) (nil C) (fun _ _ _ H a b => (g a b) :: H).
Global Arguments map2 {A B C} g {n} v1 v2.


Definition fold_left {A B:Type} (f:B->A->B): forall (b:B) {n} (v:t A n), B :=
  fix fold_left_fix (b:B) {n} (v : t A n) : B := match n return t A n -> B with
    | 0 => fun _ => b
    | S n' => fun v => match v with (a,w) => (fold_left_fix (f b a) w) end
  end v.

(*
fold_right
*)
Definition fold_right {A B : Type} (f : A->B->B) :=
  fix fold_right_fix {n} (v : t A n) (b:B)
  {struct n} : B :=
  match n return t A n -> B with
  | 0 => fun _ => b 
  | S n' => fun v => match v with (x,xs) => f x (fold_right_fix xs b) end
  end v.

(*as in std*)
Definition fold_right2 {A B C} (g:A -> B -> C -> C) (c: C) :=
@rect2 _ _ (fun _ _ _ => C) c (fun _ _ _ H a b => g a b H).

Definition fold_left2 {A B C: Type} (f : A -> B -> C -> A) :=
fix fold_left2_fix (a : A) {n} (v : t B n) : t C n -> A :=
match n return t B n -> t C n -> A with
  | 0 => fun v w => case0 (fun _ => A) a w
  | S n' => fun v w => match v with (vh,vt) => 
    caseS' w (fun _ => A) (fun wh wt => fold_left2_fix (f a vh wh) vt wt) end
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

(*as in std*)
Fixpoint of_list {A} (l : list A) : t A (length l) :=
match l as l' return t A (length l') with
  |Datatypes.nil => []
  |(h :: tail)%list => (h :: (of_list tail))
end.

Fixpoint to_list {A:Type} {n:nat} (v:t A n) : list A :=
match n return t A n -> list A with
| 0 => fun _ => List.nil
| S n' => fun (v:t A (S n')) => match v with (x,xs) => List.cons x (to_list xs) end
end v.

(*as in std*)
Definition to_list_std {A}{n} (v : t A n) : list A :=
Eval cbv delta beta in fold_right (fun h H => Datatypes.cons h H) v Datatypes.nil.
End VECTORLIST.


Module RecursiveVectorNotations.
Declare Scope recursive_vector_scope.
Delimit Scope recursive_vector_scope with recursive_vector.
Notation "[ ]" := [] (format "[ ]") : recursive_vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
  : recursive_vector_scope.
Notation "[ x ]" := (x :: []) : recursive_vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : recursive_vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : recursive_vector_scope.
Infix "++" := append : recursive_vector_scope.
Open Scope recursive_vector_scope.
End RecursiveVectorNotations.


