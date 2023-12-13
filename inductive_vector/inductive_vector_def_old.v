Require Import fin_utils.
Require Import lia_utils.
Require Import Fin.

Print Vector.t. 

Inductive vector (A : Type) : nat -> Type :=
  | nil : vector A 0
  | cons : forall (h : A) (n : nat), vector A n -> vector A (S n).

Arguments vector A%type_scope _%nat_scope.
Arguments nil A%type_scope.
Arguments cons A%type_scope h n%nat_scope _.
Print Vector.caseS.

Print IDProp.

Definition caseS: 
  forall (A:Type) (P : forall n : nat, vector A (S n) -> Type),
    (forall (h : A) (n : nat) (t : vector A n), P n (@cons A h n t)) ->
    forall (n : nat) (v : vector A (S n)), P n v :=
    fun 
    (A:Type) 
    (P:forall n:nat, vector A (S n) -> Type)
    (H:forall (h:A) (n:nat) (t:vector A n), P n (@cons A h n t))
    (n:nat)
    (v:vector A (S n)) =>
    match v as v0 in (vector _ n0)
      return (  match n0 as x return (vector A x -> Type) with
                | 0 => fun _:vector A 0 => False -> IDProp
                | S n1 => fun v1:vector A (S n1) => P n1 v1
                end v0)
    with 
    | nil => fun devil:False => False_ind IDProp devil
    | @cons _ h n0 t => H h n0 t
    end.
Print IDProp.
Check IDProp.

Print False_ind.
  
Arguments caseS {A}%type_scope (P H)%function_scope {n}%nat_scope v.
  (*
vector_ind
*)

(*
hd
*)
Definition hd {A:Type} {n:nat} (v:vector A (S n) ) : A :=
  match v with cons h t => h end.

Definition hd' {A:Type} {n:nat} (v:vector A n ) : option A := 
match v with 
| nil => None
| cons h t => Some h
end.


(*
tl
*)
Definition tl {A:Type} {n:nat} (v:vector A (S n)) : vector A n :=
match v with
| cons h t => t
end.

(*
last
*)
Fixpoint last {A:Type} {n:nat} (v:vector A (S n) ) : A :=
match n return vector A (S n) -> A with 
| 0 => fun (v:vector A (S 0)) => match v with cons h t => h end 
| S n' => fun (v:vector A (S (S n'))) => @last A n' (tl v)
end v.

(*
const
*)
Definition const {A:Type} (a:A) : forall n:nat, vector A n :=
fix f (n:nat) :=
match n with
| 0 => nil
| S n' => cons a (f n')
end.

(*
nth
*)
Fixpoint nth {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) : A := 
match f in (Fin.t m') return (vector A m' -> A) with
  | @Fin.F1 n =>
	  caseS (fun (n0 : nat) (_ : vector A (S n0)) => A)
        (fun (h : A) (n0 : nat) (_ : vector A n0) => h)
  | @Fin.FS n f' =>
      fun v : vector A (S n) =>
      caseS (fun (n0 : nat) (_ : vector A (S n0)) => Fin.t n0 -> A)
        (fun (_ : A) (n0 : nat) (t : vector A n0) (p0 : Fin.t n0) =>
         @nth A n0 t p0) v f'
  end v.

(*
replace
*)
Fixpoint replace {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) (a:A) : vector A n := 
match f in (Fin.t m') return (vector A m' -> vector A m') with
  | @Fin.F1 n =>
    caseS (fun (n0 : nat) (_ : vector A (S n0)) => vector A (S n0))
          ((fun (_ : A) (n0 : nat) (t : vector A n0) => cons a t))
  | @Fin.FS n f' => fun v : vector A (S n) =>
    caseS (fun (n0 : nat) (_ : vector A (S n0)) => Fin.t n0 -> vector A (S n0))
      (fun (h : A) (n0 : nat) (t : vector A n0) (p0 : Fin.t n0) =>
      cons h (@replace A n0 t p0 a)) v f'
  end v.

(*
take
*)

(*
Definition take {A:Type} {n:nat} : forall p : nat, (p <= n) -> (v:vector A n) -> vector A p := 
fun (p:nat) (H: p <= n) => 
match p with 
| 0 => nil
| S p' => 
  match v with
  | nil => match 
  | cons h t => cons h (take p' (leq_S p' ()) t )
  end 
end.  
*)
