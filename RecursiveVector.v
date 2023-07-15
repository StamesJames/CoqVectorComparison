Module RecursiveVector.

Fixpoint vector (A : Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => A * (vector A n)
  end.

Lemma vector_ind : forall (A : Type) (P : forall n : nat, vector A n -> Prop),
  P 0 tt -> (forall (h : A) (n : nat) (v : vector A n), P n v -> P (S n) (h, v)) -> 
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
Definition nil (A:Type) : vector A 0 := tt.
Definition cons (A:Type) (a:A) (n:nat) (v:vector A n) : vector A (S n) :=
  (a,v).
Arguments nil {A}%type_scope.
Arguments cons {A}%type_scope _ {n}%type_scope.

Definition vec_0:vector nat 0 := nil.
Definition vec_1 := cons 0 nil.
Definition vec_2 := cons 0 (cons 1 nil).
Definition vec_3 := cons 0 (cons 1 (cons 2 nil)).

Definition hd {A:Type} {n:nat} (v:vector A  (S n)): A := 
match v with
| (h,t) => h
end.

Definition hd' {A:Type} {n:nat} (v:vector A n): option A.
  intros.
  destruct n.
  - apply None.
  - cbn in v.
    destruct v.
    apply (Some a).
Defined.

Print hd'.

Definition hd'' {A:Type} {n:nat} (v:vector A n): option A :=
match n with
| 0     => fun _ : vector A 0 => None
| S n'  => 
  fun (v':vector A (S n')) => 
  let (a,b) := v' in Some a
end v.

(*
Goal hd vec_0 = None.   reflexivity. Qed.
Goal hd vec_1 = Some 0. reflexivity. Qed.
Goal hd vec_2 = Some 0. reflexivity. Qed.
Goal hd vec_3 = Some 0. reflexivity. Qed.
*)


Definition tl {A:Type} {n:nat} (v:vector A n) : vector A (pred n):=
match n return (vector A n -> vector A (pred n)) with 
| 0 => fun _ : vector A 0 => tt
| S n' => 
  fun (v':vector A (S n')) => let (a,b) := v' in b
end v.

Goal tl vec_0 = nil.                 reflexivity. Qed.
Goal tl vec_1 = nil.                 reflexivity. Qed.
Goal tl vec_2 = cons 1 nil.          reflexivity. Qed.
Goal tl vec_3 = cons 1 (cons 2 nil). reflexivity. Qed.

Fixpoint last {A:Type} {n:nat} (v:vector A n) : option A :=
match n return (vector A n -> option A) with
| 0 => (fun _: vector A 0 => None)
| S n' => (fun (v':vector A (S n')) => 
  match n' with
  | 0 => let (h,t) := v' in Some h
  | S n'' => let (h,t) := v' in last t
  end
)
end v.

Goal last vec_0 = None.   reflexivity. Qed.
Goal last vec_1 = Some 0. reflexivity. Qed.
Goal last vec_2 = Some 1. reflexivity. Qed.
Goal last vec_3 = Some 2. reflexivity. Qed.

Fixpoint const {A:Type} (a:A) (n:nat) : vector A n :=
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