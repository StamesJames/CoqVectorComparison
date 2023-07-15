Module InductiveVector.

Inductive vector (A : Type) : nat -> Type :=
  | nil : vector A 0
  | cons : forall (h : A) (n : nat), vector A n -> vector A (S n).

Arguments nil {A}%type_scope.
Arguments cons {A}%type_scope _ {n}%type_scope.

Definition vec_0:vector nat 0 := nil.
Definition vec_1 := cons 0 nil.
Definition vec_2 := cons 0 (cons 1 nil).
Definition vec_3 := cons 0 (cons 1 (cons 2 nil)).

Check vector_ind.

Definition hd {A:Type} {n:nat} (v:vector A (S n)) : A := 

Definition hd' {A:Type} {n:nat} (v:vector A n) : option A := 
match v with 
| nil => None
| cons h t => Some h
end.

Goal hd' vec_0 = None.   reflexivity. Qed.
Goal hd' vec_1 = Some 0. reflexivity. Qed.
Goal hd' vec_2 = Some 0. reflexivity. Qed.
Goal hd' vec_3 = Some 0. reflexivity. Qed.

Definition tl {A:Type} {n:nat} (v:vector A n) : vector A (pred n):=
match v with
| nil => nil
| cons h t => t
end.

Goal tl vec_0 = nil.                  reflexivity. Qed.
Goal tl vec_1 = nil.                  reflexivity. Qed.
Goal tl vec_2 = cons 1 nil.           reflexivity. Qed.
Goal tl vec_3 = cons 1 (cons 2 nil).  reflexivity. Qed.

Fixpoint last {A:Type} {n:nat} (v:vector A n) : option A :=
match v with 
| nil => None 
| cons h nil => Some h
| cons h t => last t
end.

Goal last vec_0 = None.   reflexivity. Qed.
Goal last vec_1 = Some 0. reflexivity. Qed.
Goal last vec_2 = Some 1. reflexivity. Qed.
Goal last vec_3 = Some 2. reflexivity. Qed.

Fixpoint const {A:Type} (a:A) (n:nat) : vector A n :=
match n with
| 0 => nil
| S n' => cons a (const a n')
end.

Goal const 1 0 = nil. reflexivity. Qed.
Goal const 1 1 = cons 1 nil. reflexivity. Qed.
Goal const 1 2 = cons 1 (cons 1 nil). reflexivity. Qed.
Goal const 1 3 = cons 1 (cons 1 (cons 1 nil)). reflexivity. Qed.

(*
induction
nth
replace
take
append
rev
map
fold_right
of_list, to_list

*)

End InductiveVector.