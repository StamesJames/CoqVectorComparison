Require Import List.
Require Import Lia.
Import ListNotations.
Require Import Arith_base.
Import EqNotations.

Require Import Lia.

Definition case0 {A:Type} (P: forall (l:list A) (H:length l = 0), Type) (H_nil: P [] eq_refl) (l:list A) (H:length l = 0): P l H :=
match l return forall H:length l = 0, P l H with
| [] => fun H => rew UIP_nat _ _ eq_refl H in H_nil
| x::xs => fun H => match Nat.neq_succ_0 _ H with end 
end H.

Definition caseS {A:Type} (P: forall {n} (l:list A) (H:length l = (S n)), Type)
  (H : forall h {n} t (H:length (h::t) = (S n)), @P n (h :: t) H) {n} (l: list A) (H': length l = S n) : P l H' :=
  match l return forall H': length l = S n, P l H' with 
  | [] => fun H' => match O_S _ H' with end
  | x::xs => fun H' => H x xs H'
  end H'.

Definition hd_S {A:Type} {n:nat} : forall (l:list A), (length l = S n) -> A := 
  caseS _ (fun (h:A) _ _ _  => h).

Definition tl_S {A:Type} {n:nat} : forall (l:list A), (length l = S n) -> list A := 
  caseS _ (fun _  _ (t:list A) _  => t).

Lemma list_nil_spec {A} {l:list A}: length l = 0 -> l = [].
Proof.
intros H.
destruct l; cbn in H. 
- reflexivity.
- lia. 
Qed.

Lemma list_cons_spec {A} {n} {l:list A}: length l = S n -> exists h:A, exists t:list A, l = h::t.
Proof.
intros H.
destruct l. 
- cbn in H.
  lia.
- exists a.
  exists l. 
  reflexivity.
Qed.

Lemma list_eq_cons {A:Type}: forall {a1 a2:A} (l1 l2:list A), a1 = a2 /\ l1 = l2 -> a1 :: l1 = a2 :: l2.
Proof.
intros a1 a2 l1 l2 H.
destruct H.
rewrite H.
rewrite H0.
reflexivity.
Qed.

Fixpoint list_replace {A:Type} (l:list A) (n:nat) (a:A) : list A := 
match l with
| Datatypes.nil => Datatypes.nil
| (x::xs)%list => match n with 
  | 0 => a::xs
  | S n' => a::list_replace xs n' a
  end 
end.

Lemma list_replace_len_eq {A:Type}: forall (l:list A) (i:nat) (a:A), length l = length (list_replace l i a).
Proof.
intros l.
induction l.
- intros i a. 
  cbn.
  reflexivity.
- intros i a'.
  cbn.
  destruct i.
  + cbn.
    reflexivity.
  + rewrite (IHl i a').
    cbn.
    reflexivity.
Qed.

Require lia_utils.

Lemma length_tl_lt {A n} {h:A} {t:list A}: S n < length (h::t) -> n < length t.
Proof. intros H; cbn in *; lia. Qed.

Fixpoint nth_order {A} (l: list A) n (H: n < length l): A :=
match n return n < length l -> A with
| 0 => fun H => 
  match l return 0 < length l -> A with 
  | [] => fun H => match lia_utils.not_lt_0 _ H with end
  | h::t => fun H => h 
  end H 
| S n' => fun H => 
  match l return (S n') < length l -> A with 
  | [] => fun H => match lia_utils.not_lt_0 _ H with end 
  | h::t => fun H => nth_order  t n' (length_tl_lt H) 
  end H 
end H.
 