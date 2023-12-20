Require Import List.
Require Import Lia.
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

