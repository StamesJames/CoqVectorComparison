
## cons_inj

The implementation of `cons_inj` in the standart library is 
```coq
(*as in std*)
Definition cons_inj_std {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 :=
   match eq in _ = x return caseS _ (fun a2' _ v2' => fun v1' => a1 = a2' /\ v1' = v2') x v1
   with | eq_refl => conj eq_refl eq_refl
   end.
```
This implementation also works for the RecursiveVector but not for FunctionalVector or ListVector because it relies on the fact that the Vectors are simply equal by definition but with FunctionalVectors you can have the same Vector in the sense, that the its function behaves the same but its not the same by definition. In List Vectors you can have the same elements in the list so it is behaviour wise the same Vector but the Proofs for the length can be different. 

A simple implementation:
```coq 
Definition cons_inj {A} {a1 a2} {n} {v1 v2 : t A n}
 (eq : a1 :: v1 = a2 :: v2) : a1 = a2 /\ v1 = v2 := conj (f_equal hd eq) (f_equal tl eq).
```
also works for FunctionalVectors because now coq can use eta reduction to determine that in functional vectors `tl (h::t) = t`. This Definition is still not working for ListVectors because the Proofs still can differ. To solve this List Vectors need a lemma that shows, that they are the equal iff their elements are equal.
```coq 
Lemma vec_spec_eq: forall {A:Type} {n:nat}, forall (v1 v2: t A n), elts v1 = elts v2 <-> v1 = v2.
Proof.
 intros v1 v2.
 split; intros H; destruct v1 as [el_v1 sp_v1]; destruct v2 as [el_v2 sp_v2]; cbn in *; 
 [destruct H; rewrite (lia_utils.nat_uip sp_v1 sp_v2); reflexivity| apply (f_equal elts H)].
Qed.
```

## eq_nth_iff

# dependant typing required

comparing the amount of knowledge required in dependent typing and dependent pattern matching it seems that the implementations other than the std lib implementation require more often to explicitly propagate matches. 
for example in the implementation of the tail function for ListVecors one needs to propagate the list l into the length proof 
```coq 
Definition tl {A:Type} {n:nat} (v:t A (S n)) : t A n :=
match v with
| {|elts:=l ; elts_spec:=l_sp|} =>
  match l return length l = S n -> t A n with
  | Datatypes.nil => fun l_sp => match O_S n l_sp with end
  | (h::t)%list => fun l_sp => {|elts:=t; elts_spec:= f_equal Nat.pred l_sp|}
  end l_sp
end.
```

this function is way easier in all the other implementations