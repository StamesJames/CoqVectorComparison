
Require Import Vector.

Check Vector.nil.
Print Vector.nil.
(*
Definition nil : forall A:Type, vector A 0 :=
*)

Check Vector.cons.
Print Vector.cons.
(*
Definition cons : forall A:Type, A -> forall n:nat, vector A n -> vector A (S n) :=
*)

Search "ind" in Vector.
(*
Lemma vector_ind :
  forall (A : Type) (P : forall n : nat, vector A n -> Prop),
    P 0 nil -> 
    (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (cons h v)) -> 
    forall (n : nat) (v : vector A n), P n v.
*)

Check Vector.hd.
Print Vector.hd.
(* 
Definition hd {A:Type} {n:nat} (v:vector A (S n) ) : A :=
Definition hd' {A:Type} {n:nat} (v:vector A n ) : option A := 
*)
Check Vector.tl.
Print Vector.tl.
(* 
Definition tl {A:Type} {n:nat} (v:vector A (S n)) : vector A n :=
Definition tl' {A:Type} {n:nat} (v:vector A n) : vector A (pred n) :=
Definition tl'' {A:Type} {n:nat} (v:vector A n) : option (vector A (pred n))
*)
Check Vector.last.
Print Vector.last.
(* 
Definition last {A:Type} {n:nat} (v:vector A (S n) ) : A :=
*)
(* 
Definition last' {A:Type} {n:nat} (v:vector A n ) : option A :=
*)
Check Vector.const.
Print Vector.const.
(* 
Definition const {A:Type} (a:A) : forall n:nat, vector A n :=
*)
Check Vector.nth.
Print Vector.nth.
Print Fin.
(* 
Definition nth {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) : A :=
Definition nth' {A:Type} {n:nat} : forall p:nat, (p <= n) -> vector A n -> A :=
*)
Check Vector.replace.
Print Vector.replace.
Print Fin.
(* 
Definition replace {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) (a:A) : vector A n :=
*)
(*
Definition replace {A:Type} {n:nat} : forall p:nat, (p <= n) -> vector A n -> A -> vector A n 
*)
Check Vector.take.
Print Vector.take. 
(* 
Definition take {A:Type} {n:nat} : forall p : nat, (p <= n) -> (vector A n) -> vector A n 
*)
(*
Definition take' {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) : vector A (fin_to_nat f) 
*)
Check Vector.append.
Print Vector.append.
(* 
Definition append {A:Type} {n:nat} {p:nat} (v:vector A n) (w:vector A p) : vector A (n + p) :=
*)
Check Vector.rev.
Print Vector.rev.
(* 
Definition rev {A:Type} {n:nat} (v:vector A n) : vector A n :=
*)
Check Vector.map.
Print Vector.map.
(* 
Definition map {A:Type} {B:Type} (f:A->B) : forall n: nat, vector A n -> vector B n :=
*)
Check Vector.fold_right.
Print Vector.fold_right.
(* 
Definition fold_right {A:Type} {B:Type} (f:A->B->B) : forall n:nat, vector A n -> B -> B :=
*)
Check Vector.of_list.
Print Vector.of_list.
(* 
Definition of_list {A:Type} : forall l : list A, vector A (length l) :=
*)
Check Vector.to_list.
Print Vector.to_list.
(* 
Definition to_list {A:Type} {n:nat} (v:vector A n) : list A
*)


