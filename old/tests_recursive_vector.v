Definition vec_0 : vector nat 0 := nil.
Definition tail_0: vector nat 0 := nil.
Definition vec_1 : vector nat 1 := cons 0 nil.
Definition tail_1: vector nat 0 := nil.
Definition vec_2 : vector nat 2 := cons 0 (cons 1 nil).
Definition tail_2: vector nat 1 := cons 1 nil.
Definition vec_3 : vector nat 3 := cons 0 (cons 1 (cons 2 nil)).
Definition tail_3: vector nat 2 := cons 1 (cons 2 nil).

Goal hd vec_1 = 0. Proof. reflexivity. Qed.
Goal hd vec_2 = 0. Proof. reflexivity. Qed.
Goal hd vec_3 = 0. Proof. reflexivity. Qed.

Goal hd' vec_0 = None.    Proof. reflexivity. Qed.
Goal hd' vec_1 = Some 0.  Proof. reflexivity. Qed.
Goal hd' vec_2 = Some 0.  Proof. reflexivity. Qed.
Goal hd' vec_3 = Some 0.  Proof. reflexivity. Qed. 


Goal tl vec_1 = tail_1. Proof. reflexivity. Qed.
Goal tl vec_2 = tail_2. Proof. reflexivity. Qed.
Goal tl vec_3 = tail_3. Proof. reflexivity. Qed.


Goal last vec_1 = 0. Proof. reflexivity. Qed.
Goal last vec_2 = 1. Proof. reflexivity. Qed.
Goal last vec_3 = 2. Proof. reflexivity. Qed.

Goal last' vec_0 = None.   Proof. reflexivity. Qed.
Goal last' vec_1 = Some 0. Proof. reflexivity. Qed.
Goal last' vec_2 = Some 1. Proof. reflexivity. Qed.
Goal last' vec_3 = Some 2. Proof. reflexivity. Qed.

Goal tl' vec_0 = tail_0. Proof. reflexivity. Qed.
Goal tl' vec_1 = tail_1. Proof. reflexivity. Qed.
Goal tl' vec_2 = tail_2. Proof. reflexivity. Qed.
Goal tl' vec_3 = tail_3. Proof. reflexivity. Qed.

Goal tl'' vec_0 = None.        Proof. reflexivity. Qed.
Goal tl'' vec_1 = Some tail_1. Proof. reflexivity. Qed.
Goal tl'' vec_2 = Some tail_2. Proof. reflexivity. Qed.
Goal tl'' vec_3 = Some tail_3. Proof. reflexivity. Qed.
