Module RecursiveVector.

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


Definition vec_0 : vector nat 0 := nil.
Definition tail_0: vector nat 0 := nil.
Definition vec_1 : vector nat 1 := cons 0 nil.
Definition tail_1: vector nat 0 := nil.
Definition vec_2 : vector nat 2 := cons 0 (cons 1 nil).
Definition tail_2: vector nat 1 := cons 1 nil.
Definition vec_3 : vector nat 3 := cons 0 (cons 1 (cons 2 nil)).
Definition tail_3: vector nat 2 := cons 1 (cons 2 nil).

Definition hd {A:Type} {n:nat} (v:vector A (S n) ) : A := 
match v with
| (h,t) => h
end.

Goal hd vec_1 = 0. Proof. reflexivity. Qed.
Goal hd vec_2 = 0. Proof. reflexivity. Qed.
Goal hd vec_3 = 0. Proof. reflexivity. Qed.

Definition hd' {A:Type} {n:nat} (v:vector A n): option A :=
match n with
| 0     => fun _ : vector A 0 => None
| S n'  => 
  fun (v':vector A (S n')) => match v' with (a,b) => Some a end
end v.

Goal hd' vec_0 = None.    Proof. reflexivity. Qed.
Goal hd' vec_1 = Some 0.  Proof. reflexivity. Qed.
Goal hd' vec_2 = Some 0.  Proof. reflexivity. Qed.
Goal hd' vec_3 = Some 0.  Proof. reflexivity. Qed. 

Definition tl {A:Type} {n:nat} (v:vector A (S n)) : vector A n :=
match v with (h,t) => t end.

Goal tl vec_1 = tail_1. Proof. reflexivity. Qed.
Goal tl vec_2 = tail_2. Proof. reflexivity. Qed.
Goal tl vec_3 = tail_3. Proof. reflexivity. Qed.

Definition tl' {A:Type} {n:nat} (v:vector A n) : vector A (pred n):=
match n return (vector A n -> vector A (pred n)) with 
| 0 => fun _ : vector A 0 => tt
| S n' => 
  fun (v':vector A (S n')) => match v' with (a,b) => b end
end v.

Goal tl' vec_0 = tail_0. Proof. reflexivity. Qed.
Goal tl' vec_1 = tail_1. Proof. reflexivity. Qed.
Goal tl' vec_2 = tail_2. Proof. reflexivity. Qed.
Goal tl' vec_3 = tail_3. Proof. reflexivity. Qed.

Definition tl'' {A:Type} {n:nat} (v:vector A n) : option (vector A (pred n)):=
match n return (vector A n -> option (vector A (pred n))) with 
| 0 => fun _ : vector A 0 => None
| S n' => 
  fun (v':vector A (S n')) => match v' with (h,t) => Some t end
end v.

Goal tl'' vec_0 = None.        Proof. reflexivity. Qed.
Goal tl'' vec_1 = Some tail_1. Proof. reflexivity. Qed.
Goal tl'' vec_2 = Some tail_2. Proof. reflexivity. Qed.
Goal tl'' vec_3 = Some tail_3. Proof. reflexivity. Qed.

Fixpoint last {A:Type} {n:nat} (v:vector A (S n) ) : A :=
match n return (vector A (S n) -> A) with
| 0 => fun v':vector A (S 0) => 
  match v' with (h, tt) => h end
| S n' => fun v':vector A (S (S n')) => 
  match v' with (h, t) => last t end
end v.

Goal last vec_1 = 0. Proof. reflexivity. Qed.
Goal last vec_2 = 1. Proof. reflexivity. Qed.
Goal last vec_3 = 2. Proof. reflexivity. Qed.

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

Goal last' vec_0 = None.   Proof. reflexivity. Qed.
Goal last' vec_1 = Some 0. Proof. reflexivity. Qed.
Goal last' vec_2 = Some 1. Proof. reflexivity. Qed.
Goal last' vec_3 = Some 2. Proof. reflexivity. Qed.

Fixpoint const {A:Type} (a:A) : forall n:nat, vector A n:=
fun n:nat =>
match n return (vector A n) with
| 0 => tt
| S n' => (a, (const a n'))
end.

Goal const 1 0 = nil.                          reflexivity. Qed.
Goal const 1 1 = cons 1 nil.                   reflexivity. Qed.
Goal const 1 2 = cons 1 (cons 1 nil).          reflexivity. Qed.
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

End RecursiveVector.