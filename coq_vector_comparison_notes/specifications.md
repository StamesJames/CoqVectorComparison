  
Definition nil : forall A:Type, vector A 0 :=

Definition cons : forall A:Type, A -> forall n:nat, vector A n -> vector A (S n) :=


Lemma vector_ind :
forall (A : Type) (P : forall n : nat, vector A n -> Prop),
    P 0 nil ->
    (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (cons h v)) ->
    forall (n : nat) (v : vector A n), P n v.

Definition hd {A:Type} {n:nat} (v:vector A (S n) ) : A :=
Definition hd' {A:Type} {n:nat} (v:vector A n ) : option A :=

Definition tl {A:Type} {n:nat} (v:vector A (S n)) : vector A n :=
Definition tl' {A:Type} {n:nat} (v:vector A n) : vector A (pred n) :=
Definition tl'' {A:Type} {n:nat} (v:vector A n) : option (vector A (pred n))

Definition last {A:Type} {n:nat} (v:vector A (S n) ) : A :=
Definition last' {A:Type} {n:nat} (v:vector A n ) : option A :=

Definition const {A:Type} (a:A) : forall n:nat, vector A n :=

Definition nth {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) : A :=
Definition nth' {A:Type} {n:nat} : forall p:nat, (p < n) -> vector A n -> A :=

Definition replace {A:Type} {n:nat} (v:vector A n) (f:Fin.t n) (a:A) : vector A n :=
Definition replace' {A:Type} {n:nat} (p:nat) (v:vector A n) (a:A) : forall H:(p < n), vector A n :=

Definition take {A:Type} {n:nat} : forall p : nat, (p < n) -> (vector A n) -> vector A p :=

Definition append {A:Type} {n:nat} {p:nat} (v:vector A n) (w:vector A p) : vector A (n + p) := 

Definition rev {A:Type} {n:nat} (v:vector A n) : vector A n :=

Definition map {A:Type} {B:Type} (f:A->B) : forall n: nat, vector A n -> vector B n :=

Definition fold_right {A:Type} {B:Type} (f:A->B->B) : forall n:nat, vector A n -> B -> B :=

Definition of_list {A:Type} : forall l : list A, vector A (length l) :=

Definition to_list {A:Type} {n:nat} (v:vector A n) : list A :=
