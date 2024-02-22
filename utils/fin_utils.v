Require Import Fin.
Require Import lia_utils.

Definition aux {n : nat} (v : t n) :=
  match n with 
  | 0 => fun (w : t 0) => True 
  | S 0 => fun (w : t 1) => w = @Fin.F1 0
  | S _ => fun _ => True 
  end v.

Lemma fin_1_spec (f:t 1): f = Fin.F1.
Proof.
change (aux f).
destruct f. 
- destruct n. 
  + cbn.
    reflexivity.
  + cbn.
    constructor.
- destruct n. 
  + apply Fin.case0.
    apply f. 
  + cbn.
    constructor.
Qed.


Inductive either (A B : Type) : Type :=
  | Left : A -> either A B
  | Right : B -> either A B.
Global Arguments Left {A} {B} a.
Global Arguments Right {A} {B} b.

Fixpoint fin_either_L_R {l r} (f:Fin.t (l+r)) : either (Fin.t l) (Fin.t r) :=
  match l return t (l+r) -> either (t l) (t r) with 
  | 0 => fun f => Right f
  | S l' => fun f => 
    Fin.caseS' f (fun f:t (S (l' + r)) => either (t (S l')) (t r)) 
      (Left Fin.F1 )
      (fun f' => match fin_either_L_R f' with 
      | Left l_f => Left (Fin.FS l_f)
      | Right r_f => Right r_f
      end)
  end f.

Fixpoint fin_lift {n:nat} (f:Fin.t n) : Fin.t (S n) :=
match f with
| F1 => F1 
| FS f' => FS (fin_lift f')
end.


Fixpoint fin_fold_right_fix {B:Type} {n:nat} (i:nat) (p:i<n) (acc:B) (f:Fin.t n -> B -> B) : B := 
match i return i<n -> B with
| 0 => fun _ => f (Fin.of_nat_lt p) acc
| S i' => fun p:(S i')<n => fin_fold_right_fix i' (Sn_lt_m_impl_n_lt_m i' n p) (f (Fin.of_nat_lt p) acc) f
end p.  

Definition fin_fold_right {B:Type} {n:nat} (b:B) (f:Fin.t n -> B -> B) : B := 
match n return (Fin.t n -> B -> B) -> B with
| 0 => fun _ => b
| S n' => fun f:(Fin.t (S n') -> B -> B) => fin_fold_right_fix n' (n_lt_Sn n') b f
end f.

Definition fin_inv {n:nat} (f:Fin.t n) : Fin.t n :=
match n return Fin.t n -> Fin.t n with 
| 0 => fun f:Fin.t 0 => match f with end
| S n => fun f:Fin.t (S n) => 
  match Fin.to_nat f with 
  | exist _ i p => Fin.of_nat_lt (m_sub_n_lt_m (S i) n)
  end
end f.

Definition calc_fin {n:nat} (f:Fin.t (S (pred (S n)))): Fin.t (S n) := f.

Definition fin_caseS {n : nat} (p : Fin.t (S n)) : forall (P : Fin.t (S n) -> Type)
  (P1 : P F1) (PS : forall (p : Fin.t n), P (FS p)), P p :=
  match p with
  | F1 => fun P P1 PS => P1
  | FS p' => fun P P1 PS => PS p'
  end.

Fixpoint nat_to_fin (n:nat) : Fin.t (S n) :=
match n with
| 0 => F1
| S n' => FS (nat_to_fin n')
end.

Fixpoint fin_to_nat {n:nat} (i:Fin.t n): nat := 
match i with
| F1 => 0
| FS i' => fin_to_nat i' + 1
end.