Require Import List.
Require Import Lia.
Import ListNotations.

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

