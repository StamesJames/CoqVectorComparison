Module StdVector.

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
Definition hd : {A:Type} {n:nat} (v:vector A (S n) ) -> A 
*)
(* hd' : {A:Type} {n:nat} (v:vector A n ) -> option A *)
Check Vector.tl.
Print Vector.tl.
(* tl : {A:Type} {n:nat} (v:vector A (S n)) -> vector A n *)
(* tl' : {A:Type} {n:nat} (v:vector A n) -> vector A n *)
(* tl'' : {A:Type} {n:nat} (v:vector A n) -> option (vector A (pred n))*)
Check Vector.last.
Print Vector.last.
(* last : {A:Type} {n:nat} (v:vector A (S n) ) -> A *)
(* last' : {A:Type} {n:nat} (v:vector A n ) -> option A *)
Check Vector.const.
Print Vector.const.
(* const : {A:Type} (a:A) -> forall n:nat, vector A n *)
Check Vector.nth.
Print Vector.nth.
Print Fin.
(* nth : {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) -> A *)
(* nth' : {A:Type} {n:nat} forall p:nat, (p <= n) -> vector A n -> A *)
Check Vector.replace.
Print Vector.replace.
Print Fin.
(* replace : {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) (a:A) -> vector A n *)
(* replace : {A:Type} {n:nat} forall p:nat, (p <= n) -> vector A n -> A -> vector A n *)
Check Vector.take.
Print Vector.take. 
(* take : {A:Type} {n:nat} forall p : nat, (p <= n) -> (v:vector A n) -> vector A m *)
(* take : {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) -> vector A (fin_to_nat f) *)
Check Vector.append.
Print Vector.append.
(* append : {A:Type} {n:nat} {p:nat} (v:vector A n) (w:vector A p) -> vector A (n + p) *)
Check Vector.rev.
Print Vector.rev.
(* rev : {A:Type} {n:nat} (v:vector A n) -> vector A n *)
Check Vector.map.
Print Vector.map.
(* map : {A:Type} {B:Type} -> forall n: nat, vector A n -> vector B n *)
Check Vector.fold_right.
Print Vector.fold_right.
(* fold_right : {A:Type} {B:Type} (f:A->B->B) -> forall n:nat, vector A n -> B -> B *)
Check Vector.of_list.
Print Vector.of_list.
(* of_list : {A:Type} forall l : list A, vector A (length l)*)
Check Vector.to_list.
Print Vector.to_list.
(* to_list : {A:Type} {n:nat} vector A n -> list A*)


End StdVector.


