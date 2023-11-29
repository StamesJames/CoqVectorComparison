Require Import fin_utils.
Require Import lia_utils.
Require Import Fin. 

Fixpoint vector (A : Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => A * (vector A n)
  end.

Definition nil (A:Type) : vector A 0 := tt.
Definition cons (A:Type) (a:A) (n:nat) (v:vector A n) : vector A (S n) :=
  (a,v).
Arguments nil {A}%type_scope.
Arguments cons {A}%type_scope _ {n}%type_scope.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, vector A n -> Prop),
    P 0 nil -> 
    (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (h, v)) -> 
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

(*
hd
*)
Definition hd {A:Type} {n:nat} (v:vector A (S n) ) : A := 
match v with
| (h,t) => h
end.

Definition hd' {A:Type} {n:nat} (v:vector A n): option A :=
match n with
| 0     => fun _ : vector A 0 => None
| S n'  => 
  fun (v':vector A (S n')) => match v' with (a,b) => Some a end
end v.

(*
tl
*)
Definition tl {A:Type} {n:nat} (v:vector A (S n)) : vector A n :=
match v with (h,t) => t end.

Definition tl' {A:Type} {n:nat} (v:vector A n) : vector A (pred n):=
match n return (vector A n -> vector A (pred n)) with 
| 0 => fun _ : vector A 0 => tt
| S n' => 
  fun (v':vector A (S n')) => match v' with (a,b) => b end
end v.

Definition tl'' {A:Type} {n:nat} (v:vector A n) : option (vector A (pred n)):=
match n return (vector A n -> option (vector A (pred n))) with 
| 0 => fun _ : vector A 0 => None
| S n' => 
  fun (v':vector A (S n')) => match v' with (h,t) => Some t end
end v.


(*
last
*)
Fixpoint last {A:Type} {n:nat} (v:vector A (S n) ) : A :=
match n return (vector A (S n) -> A) with
| 0 => fun v':vector A (S 0) => 
  match v' with (h, tt) => h end
| S n' => fun v':vector A (S (S n')) => 
  match v' with (h, t) => last t end
end v.

Fixpoint last' {A:Type} {n:nat} (v:vector A n ) : option A :=
match n return (vector A n -> option A) with
| 0 => (fun _: vector A 0 => None)
| S n' => (fun (v':vector A (S n')) => 
  match n' with
  | 0 => match v' with (h,t) => Some h end
  | S n'' => match v' with (h,t) => last' t end
  end
)
end v.

(*
const
*)
Definition const {A:Type} (a:A) : forall n:nat, vector A n := 
fix const_fix (n:nat) : vector A n :=
match n with 
| 0 => nil
| S n' => cons a (const_fix n')
end.

Print Fin.

(*
nth
*)
Fixpoint nth {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) : A :=
match n return Fin.t n -> vector A n -> A with 
| 0 => fun f _ => match f with end
| S n' => fun (f:Fin.t (S n')) (v:vector A (S n')) => 
  match f in Fin.t (S n') return vector A n' -> A with 
  | @Fin.F1 n' => fun _ => match v with (x,_) => x end
  | @Fin.FS n' f' => fun (v: vector A n') => nth v f'
  end (tl v)
end f v. 

(*
replace
*)
Fixpoint replace {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) (a:A) : vector A n :=
match n return Fin.t n -> vector A n -> vector A n with 
| 0 => fun f _ => match f with end
| S n' => fun (f:Fin.t (S n')) (v:vector A (S n')) => 
  match f in Fin.t (S n') return vector A (S n') -> vector A (S n') with 
  | @Fin.F1 n' => fun (v: vector A (S n')) => match v with (x,xs) => (a,xs) end
  | @Fin.FS n' f' => fun (v: vector A (S n')) => 
    match v with (x,xs) => (x,replace xs f' a) end
  end v
end f v.

(*
take
*)
Fixpoint take {A:Type} {n:nat} : forall p : nat, (p <= n) -> (vector A n) -> vector A p := 
fun (p:nat) (H:p<=n) (v:vector A n) =>
match p return p <= n -> vector A p with
| 0 => fun _ => nil 
| S p' => fun (H:(S p'<= n)) => 
  match n return (S p'<= n) -> vector A n -> vector A (S p') with 
  | 0 => fun (H:(S p'<= 0)) _ => match (Sn_not_leq_0 p' H) with end
  | S n' => fun (H:(S p'<= S n')) (v:vector A (S n')) => 
    (hd v, @take A n' p' (leq_S p' n' H) (tl v))
  end H v
end H.

(*
append
*)
Fixpoint append {A:Type} {n:nat} {p:nat} (v:vector A n) (w:vector A p) : vector A (n + p) :=
match n return vector A n -> vector A (n + p) with
| 0 => fun _ => w
| S n' => fun (v:vector A (S n')) => match v with (x,xs) => (x, append xs w) end 
end v.


Fixpoint snoc {A:Type} {n:nat} (v:vector A n) (a:A): vector A (S n) :=
match n return vector A n -> vector A (S n) with
| 0 => fun _ => cons a nil
| S n' => fun (v:vector A (S n')) => match v with (x,xs) => (x,snoc xs a) end
end v.

(*
rev
*)
Fixpoint rev {A:Type} {n:nat} (v:vector A n) : vector A n :=
match n return vector A n -> vector A n with
| 0 => fun _ => nil
| S n' => fun (v:vector A (S n')) => match v with (x,xs) => snoc (rev xs) x end
end v.


Definition map {A:Type} {B:Type} (f:A->B) : forall n: nat, vector A n -> vector B n :=
fix map_fix n v :=
match n return vector A n -> vector B n with
| 0 => fun _ => nil
| S n' => fun (v:vector A (S n')) => match v with (x,xs) => (f x, map_fix n' xs) end
end v.

(*
fold_right
*)
Definition fold_right {A:Type} {B:Type} (f:A->B->B) : forall n:nat, vector A n -> B -> B :=
fix fold_right_fix n v b := 
match n return vector A n -> B with
| 0 => fun _ => b 
| S n' => fun (v:vector A (S n')) => match v with (x,xs) => f x (fold_right_fix n' xs b) end
end v.


(*
of_list
*)
Definition of_list {A:Type} : forall l : list A, vector A (length l) :=
fix of_list_fix l :=
match l with
| List.nil => nil
| List.cons x xs => (x,of_list_fix xs)
end.

(*
to_list
*)
Fixpoint to_list {A:Type} {n:nat} (v:vector A n) : list A :=
match n return vector A n -> list A with
| 0 => fun _ => List.nil
| S n' => fun (v:vector A (S n')) => match v with (x,xs) => List.cons x (to_list xs) end
end v.

