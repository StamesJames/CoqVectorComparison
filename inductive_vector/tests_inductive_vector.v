Require Import inductive_vector.


Definition vec_0:vector nat 0 := nil.
Definition vec_1 := cons 0 nil.
Definition vec_2 := cons 0 (cons 1 nil).
Definition vec_3 := cons 0 (cons 1 (cons 2 nil)).

Goal hd vec_1 = 0. Proof. reflexivity. Qed.
Goal hd vec_2 = 0. Proof. reflexivity. Qed.
Goal hd vec_3 = 0. Proof. reflexivity. Qed.


Goal hd' vec_0 = None.   Proof. reflexivity. Qed.
Goal hd' vec_1 = Some 0. Proof. reflexivity. Qed.
Goal hd' vec_2 = Some 0. Proof. reflexivity. Qed.
Goal hd' vec_3 = Some 0. Proof. reflexivity. Qed.

Goal tl vec_1 = nil.                 Proof. reflexivity. Qed.
Goal tl vec_2 = cons 1 nil.          Proof. reflexivity. Qed.
Goal tl vec_3 = cons 1 (cons 2 nil). Proof. reflexivity. Qed.

Goal tl' vec_0 = nil.                 Proof. reflexivity. Qed.
Goal tl' vec_1 = nil.                 Proof. reflexivity. Qed.
Goal tl' vec_2 = cons 1 nil.          Proof. reflexivity. Qed.
Goal tl' vec_3 = cons 1 (cons 2 nil). Proof. reflexivity. Qed.

Goal last vec_1 = 0. Proof. reflexivity. Qed.
Goal last vec_2 = 1. Proof. reflexivity. Qed.
Goal last vec_3 = 2. Proof. reflexivity. Qed.

Goal last' vec_0 = None.   Proof. reflexivity. Qed.
Goal last' vec_1 = Some 0. Proof. reflexivity. Qed.
Goal last' vec_2 = Some 1. Proof. reflexivity. Qed.
Goal last' vec_3 = Some 2. Proof. reflexivity. Qed.

Goal const 1 0 = nil.                          Proof. reflexivity. Qed.
Goal const 1 1 = cons 1 nil.                   Proof. reflexivity. Qed.
Goal const 1 2 = cons 1 (cons 1 nil).          Proof. reflexivity. Qed.
Goal const 1 3 = cons 1 (cons 1 (cons 1 nil)). Proof. reflexivity. Qed.