Require Import fin_utils.
Require Import lia_utils.
Require Import Arith_base.
Import EqNotations.
Local Open Scope nat_scope.
Require Import Fin.

Fixpoint t (A : Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => A * (t A n)
  end.

Definition nil (A:Type) : t A 0 := tt.
Definition cons (A:Type) (a:A) (n:nat) (v:t A n) : t A (S n) :=
  (a,v).
Arguments nil {A}%type_scope.
Arguments cons {A}%type_scope _ {n}%type_scope.

Local Notation "[ ]" := (nil) (format "[ ]").
Local Notation "h :: t" := (cons h t) (at level 60, right associativity).

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

Definition case0 {A} (P:t A 0 -> Type) (H:P nil) v:P v :=
match v with
  | tt => H
end.

Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with (h,t) => H h t end.

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
  (H : forall h t, P (h :: t)), P v :=
match v with (h,t) => fun P H => H h t end.

Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
  (bas : P nil nil) (rect : forall {n v1 v2}, P v1 v2 ->
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

Definition hd_std {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd_std {A} {n} v.

Definition last_std {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last_std {A} {n} v.

Definition const_std {A} (a:A) := nat_rect _ nil (fun n x => a :: x).

Definition tl_std {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
Global Arguments tl_std {A} {n} v.

Fixpoint replace_std {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
  match p with
  | @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => a :: t)
  | @Fin.FS k p' => fun v' : t A (S k) =>
    (caseS' v' (fun _ => t A (S k)) (fun h t => h :: (replace_std t p' a)))
  end v.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, t A n -> Prop),
    P 0 nil -> 
    (forall (h : A) (n : nat) (v : t A n), P n v -> P (S n) (h, v)) -> 
    forall (n : nat) (v : t A n), P n v.
Proof.
  intros A P H1 H2 n.
  induction n; cbn.
  - intros [].
    apply H1.
  - intros [h v].
    apply H2.
    apply IHn.
Qed.

(*
hd
*)
Definition hd {A:Type} {n:nat} (v:t A (S n) ) : A := 
match v with
| (h,t) => h
end.

Definition hd' {A:Type} {n:nat} (v:t A n): option A :=
match n with
| 0     => fun _ : t A 0 => None
| S n'  => 
  fun (v':t A (S n')) => match v' with (a,b) => Some a end
end v.

(*
tl
*)
Definition tl {A:Type} {n:nat} (v:t A (S n)) : t A n :=
match v with (h,t) => t end.

Definition tl' {A:Type} {n:nat} (v:t A n) : t A (pred n):=
match n return (t A n -> t A (pred n)) with 
| 0 => fun _ : t A 0 => tt
| S n' => 
  fun (v':t A (S n')) => match v' with (a,b) => b end
end v.

Definition tl'' {A:Type} {n:nat} (v:t A n) : option (t A (pred n)):=
match n return (t A n -> option (t A (pred n))) with 
| 0 => fun _ : t A 0 => None
| S n' => 
  fun (v':t A (S n')) => match v' with (h,t) => Some t end
end v.


(*
last
*)
Fixpoint last {A:Type} {n:nat} (v:t A (S n) ) : A :=
match n return (t A (S n) -> A) with
| 0 => fun v':t A (S 0) => 
  match v' with (h, tt) => h end
| S n' => fun v':t A (S (S n')) => 
  match v' with (h, t) => last t end
end v.

Fixpoint last' {A:Type} {n:nat} (v:t A n ) : option A :=
match n return (t A n -> option A) with
| 0 => (fun _: t A 0 => None)
| S n' => (fun (v':t A (S n')) => 
  match n' with
  | 0 => match v' with (h,t) => Some h end
  | S n'' => match v' with (h,t) => last' t end
  end
)
end v.

(*
const
*)
Definition const {A:Type} (a:A) : forall n:nat, t A n := 
fix const_fix (n:nat) : t A n :=
match n with 
| 0 => nil
| S n' => a :: (const_fix n')
end.

Print Fin.

(*
nth
*)
Fixpoint nth {A:Type} {n:nat} (v:t A n) (f:Fin.t n) : A :=
match n return Fin.t n -> t A n -> A with 
| 0 => fun f _ => match f with end
| S n' => fun (f:Fin.t (S n')) (v:t A (S n')) => 
  match f in Fin.t (S n') return t A n' -> A with 
  | @Fin.F1 n' => fun _ => match v with (x,_) => x end
  | @Fin.FS n' f' => fun (v: t A n') => nth v f'
  end (tl v)
end f v. 

(*
replace
*)
Fixpoint replace {A:Type} {n:nat} (v:t A n) (f:Fin.t n) (a:A) : t A n :=
match n return Fin.t n -> t A n -> t A n with 
| 0 => fun f _ => match f with end
| S n' => fun (f:Fin.t (S n')) (v:t A (S n')) => 
  match f in Fin.t (S n') return t A (S n') -> t A (S n') with 
  | @Fin.F1 n' => fun (v: t A (S n')) => match v with (x,xs) => (a,xs) end
  | @Fin.FS n' f' => fun (v: t A (S n')) => 
    match v with (x,xs) => (x,replace xs f' a) end
  end v
end f v.

(*
take
*)
Fixpoint take {A:Type} {n:nat} : forall p : nat, (p <= n) -> (t A n) -> t A p := 
fun (p:nat) (H:p<=n) (v:t A n) =>
match p return p <= n -> t A p with
| 0 => fun _ => nil 
| S p' => fun (H:(S p'<= n)) => 
  match n return (S p'<= n) -> t A n -> t A (S p') with 
  | 0 => fun (H:(S p'<= 0)) _ => match (Sn_not_leq_0 p' H) with end
  | S n' => fun (H:(S p'<= S n')) (v:t A (S n')) => 
    (hd v, @take A n' p' (leq_S p' n' H) (tl v))
  end H v
end H.

(*
append
*)
Fixpoint append {A:Type} {n:nat} {p:nat} (v:t A n) (w:t A p) : t A (n + p) :=
match n return t A n -> t A (n + p) with
| 0 => fun _ => w
| S n' => fun (v:t A (S n')) => match v with (x,xs) => (x, append xs w) end 
end v.

(*
rev
*)
Fixpoint snoc {A:Type} {n:nat} (v:t A n) (a:A): t A (S n) :=
match n return t A n -> t A (S n) with
| 0 => fun _ => a :: nil
| S n' => fun (v:t A (S n')) => match v with (x,xs) => (x,snoc xs a) end
end v.

Infix "++" := append.

Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p)
  : t A (Nat.tail_add n p) :=
  match n return t A n -> t A (Nat.tail_add n p) with 
  | 0 => fun v => match v with tt => w end
  | S n' => fun v => match v with (a, v') => rev_append_tail v' (a :: w) end
  end v.

Definition rev_append {A n p} (v: t A n) (w: t A p)
  :t A (n + p) :=
  rew (Nat.tail_add_spec n p) in (rev_append_tail v w).

Definition rev {A n} (v : t A n) : t A n :=
 rew <- (plus_n_O _) in (rev_append v []).

Fixpoint rev_with_snoc {A:Type} {n:nat} (v:t A n) : t A n :=
match n return t A n -> t A n with
| 0 => fun _ => nil
| S n' => fun (v:t A (S n')) => match v with (x,xs) => snoc (rev_with_snoc xs) x end
end v.

(*
map
*)

Definition map {A:Type} {B:Type} (f:A->B) : forall {n: nat}, t A n -> t B n :=
fix map_fix {n} v :=
match n return t A n -> t B n with
| 0 => fun _ => nil
| S n' => fun (v:t A (S n')) => match v with (x,xs) => (f x, @map_fix n' xs) end
end v.

(*
fold_right
*)
Definition fold_right {A:Type} {B:Type} (f:A->B->B) : forall {n:nat}, t A n -> B -> B :=
fix fold_right_fix {n} v b := 
match n return t A n -> B with
| 0 => fun _ => b 
| S n' => fun (v:t A (S n')) => match v with (x,xs) => f x (@fold_right_fix n' xs b) end
end v.


(*
of_list
*)
Definition of_list {A:Type} : forall l : list A, t A (length l) :=
fix of_list_fix l :=
match l with
| List.nil => nil
| List.cons x xs => (x,of_list_fix xs)
end.

(*
to_list
*)
Fixpoint to_list {A:Type} {n:nat} (v:t A n) : list A :=
match n return t A n -> list A with
| 0 => fun _ => List.nil
| S n' => fun (v:t A (S n')) => match v with (x,xs) => List.cons x (to_list xs) end
end v.

(*
shiftin
*)
Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) :=
match n return t A n -> t A (S n) with
| 0 => fun v => match v with tt => a :: [] end
| S n' => fun v => match v with (h,t) => h :: (shiftin a t) end
end v.

(*
splitat
*)

Fixpoint splitat {A} (l : nat) {r : nat} :
  t A (l + r) -> t A l * t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (v1, v2) := splitat l' (tl v) in
    (hd v::v1, v2)
  end.

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