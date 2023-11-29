Require Import Fin.
Require Import lia_utils.
Print Fin.t.

Fixpoint fin_lift {n:nat} (f:Fin.t n) : Fin.t (S n) :=
match f with
| F1 => F1 
| FS f' => FS (fin_lift f')
end.

(*
Fin recursion von größten zum kleinsten Element implementieren
Wie bei listen rev_ind
*)


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

(*
Ähnliche lösung zu rev vector der inductiven vec implementierung suchen
*)

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