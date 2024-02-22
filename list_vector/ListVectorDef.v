Set Mangle Names.
Set Default Goal Selector "!".
Require fin_utils.
Require lia_utils.
Require list_utils.
Require Fin.
Require Import Lia.
Require Import Arith_base.
Require Import List.
Import EqNotations.
Local Open Scope nat_scope.


#[universes(template)]
Record t (A : Type) (n : nat) := 
  mk_vector { elts : list A; elts_spec : length elts = n }.
Arguments mk_vector {A n}.
Arguments elts {A n}.
Arguments elts_spec {A n}.

Definition nil (A : Type) : t A 0 := mk_vector (Datatypes.nil) eq_refl.

Definition cons (A : Type) (h : A) (n : nat) (v : t A n) : t A (S n) :=
  mk_vector (h :: (elts v))%list (f_equal S (elts_spec v)).

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section BASES.
Definition hd {A:Type} {n:nat} (v:t A (S n)) : A :=
match v with
| {|elts:=l ; elts_spec:=l_sp|} => 
  match l return length l = S n -> A with
  | Datatypes.nil => fun l_sp => match O_S n l_sp with end
  | (h::t)%list => fun l_sp => h
  end l_sp 
end.

(*this behaviour could be a list function*)
Definition hd' {A:Type} {n:nat} (v:t A (S n)) : A := list_utils.hd_S (elts v) (elts_spec v).

Definition tl {A:Type} {n:nat} (v:t A (S n)) : t A n := 
match v with
| {|elts:=l ; elts_spec:=l_sp|} => 
  match l return length l = S n -> t A n with
  | Datatypes.nil => fun l_sp => match O_S n l_sp with end
  | (h::t)%list => fun l_sp => {|elts:=t; elts_spec:= f_equal Nat.pred l_sp|} 
  end l_sp 
end.

End BASES.

Section SCHEMES.

Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v:=
match v with | {| elts := l; elts_spec := l_sp |} => 
  match l return (forall l_sp, P {| elts := l; elts_spec := l_sp |}) with
  | Datatypes.nil => fun l_sp => 
    rew <- [fun l_sp => P {| elts := Datatypes.nil; elts_spec := l_sp |}] UIP_nat _ _ l_sp eq_refl in H
  | (a :: l)%list => fun l_sp => match O_S _ (eq_sym l_sp) with end
  end l_sp
end.

Lemma nil_spec {A} (v : t A 0) : v = [].
Proof.
apply (fun P E => case0 P E v). reflexivity.
Defined.


Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
  (H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with {| elts := l; elts_spec := l_sp |} => 
    match l return (forall l_sp : length l = S n, P {| elts := l; elts_spec := l_sp |}) with
    | Datatypes.nil => fun l_sp => match O_S n l_sp with end
    | (a :: l)%list => fun l_sp => 
          rew [fun e => P {| elts := a :: l; elts_spec := e |}] UIP_nat _ _ (f_equal S (f_equal pred l_sp)) l_sp in 
          H a {| elts := l; elts_spec := f_equal pred l_sp |}
    end l_sp
end.


Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
(H : forall h t, P (h :: t)), P v :=
match v with {| elts := l; elts_spec := l_sp |} => fun P H =>
    match l return (forall l_sp : length l = S n, P {| elts := l; elts_spec := l_sp |}) with
    | Datatypes.nil => fun l_sp => match O_S n l_sp with end
    | (a :: l)%list => fun l_sp => 
          rew [fun e => P {| elts := a :: l; elts_spec := e |}] UIP_nat _ _ (f_equal S (f_equal pred l_sp)) l_sp in 
          H a {| elts := l; elts_spec := f_equal pred l_sp |}
    end l_sp
end. 

Definition caseS'' {A} (P : forall {n}, t A (S n) -> Type)
  {n} (H : forall h t, @P n (h :: t)) (v: t A (S n)) : P v :=
  match v with {| elts := l; elts_spec := l_sp |} =>
      match l return (forall l_sp : length l = S n, P {| elts := l; elts_spec := l_sp |}) with
      | Datatypes.nil => fun l_sp => match O_S n l_sp with end
      | (a :: l)%list => fun l_sp => rew [fun e => P {| elts := a :: l; elts_spec := e |}] UIP_nat _ _ (f_equal S (f_equal pred l_sp)) l_sp in
            H a {| elts := l; elts_spec := f_equal pred l_sp |}
      end l_sp
  end.

Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :=
 fix rectS_fix {n} (v: t A (S n)) : P v := match n return forall (v : t A (S n)), P v with
 | 0 => caseS'' _ (fun h w => case0 (fun w => P (h :: w)) (bas h) _)
 | S m => caseS'' _ (fun h w => rect h w (rectS_fix w))
 end v.

Lemma vec_spec_eq {A n}: forall (v1 v2: t A n), elts v1 = elts v2 <-> v1 = v2.
Proof.
 intros v1 v2.
 split; intros H; destruct v1 as [el_v1 sp_v1]; destruct v2 as [el_v2 sp_v2]; cbn in *; 
 [destruct H; rewrite (UIP_nat _ _ sp_v1 sp_v2); reflexivity| apply (f_equal elts H)].
Qed.

Lemma eta {A} {n} (v : t A (S n)) : v = hd v :: tl v.
Proof.
destruct v as [l l_sp]; destruct n, l; 
try (apply vec_spec_eq; reflexivity) ; destruct (O_S _ l_sp).
Qed.

Definition rect2 {A B} 
  (P:forall {n}, t A n -> t B n -> Type)
  (bas : P [] []) 
  (rect : forall {n:nat} {v1:t A n} {v2:t B n}, P v1 v2 -> forall a b, P (a :: v1) (b :: v2)): forall {n} (v1 : t A n) (v2: t B n), P v1 v2 :=
  fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
  match n return forall v1:t A n, forall v2, P v1 v2 with
  | 0 => fun v1 v2 => 
    rew <- [fun v1 : t A 0 => P v1 v2] nil_spec v1 in
    rew <- [fun v2 : t B 0 => P [] v2] nil_spec v2 in bas
  | S n' => fun v1 v2 => 
    rew <- [fun v1 : t A (S n') => P  v1 v2] eta v1 in
    rew <- [fun v2 : t B (S n') => P (hd v1 :: tl v1) v2] eta v2 in
    @rect n' (tl v1) (tl v2) (rect2_fix (tl v1) (tl v2)) (hd v1) (hd v2) 
  end v1.

End SCHEMES.

Section BASES.

(*as in std*)
Definition hd_std {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd {A} {n} v.

Definition last {A:Type} {n:nat} (v:t A (S n)) : A :=
    match elts_spec v with
    | H => 
      match elts v with 
      | l => 
        match l return (length (l) = S n -> A) with
        | Datatypes.nil => fun H: length Datatypes.nil = S n => match O_S n H  with end 
        | (h :: t)%list => fun _ => List.last t h
        end H
      end
    end. 

(*as in std*)
Definition last_std {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last {A} {n} v.

Fixpoint const {A:Type} (a:A) (n:nat): t A n :=
match n with
| 0 => []
| S n' =>  a :: (const a n')
end.

(*as in std*)
Definition const_std {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).

Fixpoint nth {A:Type} {n:nat} (v:t A n) (f:Fin.t n) : A :=
match v with {|elts := l; elts_spec := l_sp|} => 
  match f in Fin.t n return length l = n -> A with 
  | @Fin.F1 n => fun l_sp => 
    match l return length l = S n -> A with 
    | Datatypes.nil => fun l_sp => match O_S _ l_sp with end 
    | (a::l')%list => fun l_sp =>  a 
    end l_sp
  | @Fin.FS n f' => fun l_sp => 
    match l return length l = S n -> A with 
    | Datatypes.nil => fun l_sp => match O_S _ l_sp with end 
    | (a::l')%list => fun l_sp => nth ({|elts:=l'; elts_spec:=f_equal Nat.pred l_sp |}) f' 
    end l_sp
  end l_sp
end.

(*as in std*)
Definition nth_order {A} {n} (v: t A n) {p} (H: p < n) :=
(nth v (Fin.of_nat_lt H)).

Definition nth' {A:Type} {n:nat} (v:t A n) (f:Fin.t n) : A :=
match n return (t A n) -> (Fin.t n) -> A with 
| 0 => fun v f => match f with end
| S n' => fun v f =>
  match v with 
  | {| elts := Datatypes.nil ; elts_spec := p |} => match O_S n' p with end
  | {| elts := (x::xs)%list ; elts_spec := p |} => List.nth (fin_utils.fin_to_nat f) (elts v) x
  end
end v f.

Lemma replace_aux {A:Type} {n:nat} (a a':A) (l:list A): length (a::l) = n -> length (a'::l) = n.
Proof.
intros H. cbn in *. assumption.
Qed.

Fixpoint replace {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
match p in (Fin.t n) return t A n -> t A n with 
| @Fin.F1 n' => fun v => 
  match v with {|elts:=l; elts_spec:=l_sp|} => 
    match l return length l = S n' -> t A (S n') with 
    | Datatypes.nil => fun l_sp => match O_S _ l_sp with end
    | (a'::l')%list => fun l_sp => {|elts:= a::l'; elts_spec:=replace_aux a' a l' l_sp|}
    end l_sp 
  end 
| @Fin.FS n' f' => fun v => 
  match v with {|elts:=l; elts_spec:=l_sp|} => 
    match l return length l = S n' -> t A (S n') with 
    | Datatypes.nil => fun l_sp => match O_S _ l_sp with end 
    | (a'::l')%list => fun l_sp => a'::(replace (tl v) f' a)
    end l_sp  
  end
end v.


Lemma replace_aux' {A:Type} {n:nat}: forall (l:list A) (p:length l = n) (i:nat) (a:A), length (list_utils.list_replace l i a) = n.
Proof.
intros l p i a.
rewrite <- (list_utils.list_replace_len_eq l i a).
apply p.
Qed.

Definition replace' {A:Type} {n:nat} (v:t A n) (f:Fin.t n) (a:A) : t A n := 
match v with
| {| elts := l; elts_spec := p|} => {| elts := (list_utils.list_replace l (fin_utils.fin_to_nat f) a); elts_spec := (replace_aux' l p (fin_utils.fin_to_nat f) a)|} 
end.

(*as in std*)
Definition uncons {A} {n : nat} (v : t A (S n)) : A * t A n := (hd v, tl v).

(*as in std*)
Definition shiftout {A} := @rectS _ (fun n _ => t A n) (fun a => [])
  (fun h _ _ H => h :: H).
Global Arguments shiftout {A} {n} v.

Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) :=
match n return t A n -> t A (S n) with 
| 0 => fun v => {| elts := (a::Datatypes.nil)%list; elts_spec := eq_refl|}
| S n' => fun v => (hd v) :: shiftin a (tl v)
end v.

(*as in std*)
Definition shiftrepeat {A} := @rectS _ (fun n _ => t A (S (S n)))
  (fun h =>  h :: h :: []) (fun h _ _ H => h :: H).
Global Arguments shiftrepeat {A} {n} v.

Lemma take_aux {i n m:nat}: forall (p:i<=n) (H:m = n), i<=m.
Proof. intros p H. rewrite H. apply p. Qed.

Definition take {A:Type} {n:nat} : forall i : nat, (i <= n) -> t A n -> t A i :=
fun (i:nat) (p:i <= n) (v: t A n) =>
match v with
| {|elts := l ; elts_spec := s|} => 
  {|elts := List.firstn i l; elts_spec := (List.firstn_length_le l (take_aux p s))|}
end.

(*as in std*)
Lemma trunc : forall {A} {n} (p:nat), n > p -> t A n
  -> t A (n - p).
Proof.
  intros A n p; induction p as [| p f]; intros H v.
  - rewrite Nat.sub_0_r.
    exact v.
  - apply shiftout.
    rewrite <- Nat.sub_succ_l.
    + exact (f (Nat.lt_le_incl _ _ H) v).
    + exact (Nat.lt_le_incl _ _ H).
Defined.

Lemma append_aux{x n m n' m': nat}: forall(pn:n = n') (pm: m = m') (H: x = n + m), x = n' + m'.  
Proof. lia. Qed.

Definition append {A:Type} {n:nat} {p:nat} (v:t A n) (w:t A p) : t A (n + p) :=
match v with {| elts := elts_v; elts_spec := elts_spec_v |} => match w with {| elts := elts_w ; elts_spec:=elts_spec_w|} => 
  {|elts := elts_v ++ elts_w; elts_spec := append_aux elts_spec_v elts_spec_w (List.app_length elts_v elts_w)|} end end.

(*as in std*)
Fixpoint splitat {A} (l : nat) {r : nat} :
  t A (l + r) -> t A l * t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (v1, v2) := splitat l' (tl v) in
    (hd v::v1, v2)
  end.

Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p)
  : t A (Nat.tail_add n p) :=
  match n return t A n -> t A (Nat.tail_add n p) with 
  | 0 => fun v => w 
  | S n' => fun v => rev_append_tail (tl v) ((hd v) :: w)
  end v.

(*as in std*)
Definition rev_append {A n p} (v: t A n) (w: t A p)
  :t A (n + p) :=
  rew (Nat.tail_add_spec n p) in (rev_append_tail v w).

Definition rev {A:Type} {n:nat} (v:t A n) : t A n := 
match v with {|elts:=l;elts_spec:=p|} => 
{|elts:= List.rev l ; elts_spec:= eq_trans (List.rev_length l) p |}
end.

(*as in std*)
Definition rev_std {A n} (v : t A n) : t A n :=
 rew <- (plus_n_O _) in (rev_append v []).

End BASES.
Local Notation "v [@ p ]" := (nth v p) (at level 1).


Section ITERATORS.

Definition map {A} {B} (f : A -> B) : forall {n} (v:t A n), t B n := fun (n:nat) (v:t A n) => 
match v with {|elts:=l;elts_spec:=p|} => 
{|elts:=List.map f l; elts_spec:= eq_trans (List.map_length f l) p|}
end.

(*as in std*)
Definition map2 {A B C} (g:A -> B -> C) :
  forall (n : nat), t A n -> t B n -> t C n :=
@rect2 _ _ (fun n _ _ => t C n) (nil C) (fun _ _ _ H a b => (g a b) :: H).
Global Arguments map2 {A B C} g {n} v1 v2.

Definition fold_left {A B:Type} (f:B->A->B): forall (b:B) {n} (v:t A n), B :=
  fix fold_left_fix (b:B) {n} (v : t A n) : B :=
    match n return t A n -> B with
    | 0 => fun v => b
    | S n' => fun v => (fold_left_fix (f b (hd v)) (tl v))
    end v.

Definition fold_right {A B : Type} (f : A->B->B) :=
fun {n:nat} (v:t A n) (b:B) => match v with {|elts:=l;elts_spec:=p|} => List.fold_right f b l end.

(*as in std*)
Definition fold_right2 {A B C} (g:A -> B -> C -> C) (c: C) :=
@rect2 _ _ (fun _ _ _ => C) c (fun _ _ _ H a b => g a b H).

Definition fold_left2 {A B C: Type} (f : A -> B -> C -> A) :=
fix fold_left2_fix (a : A) {n} (v : t B n) : t C n -> A := 
match n return t B n -> t C n -> A with
| 0 => fun v w => case0 (fun _ => A) a w
| S n' => fun v w => caseS' w (fun _ => A) (fun wh wt => fold_left2_fix (f a (hd v) (hd w)) (tl v) (tl w))
end v. 

End ITERATORS.

(*as in std*)
Section SCANNING.
Inductive Forall {A} (P: A -> Prop): forall {n} (v: t A n), Prop :=
 |Forall_nil: Forall P []
 |Forall_cons {n} x (v: t A n): P x -> Forall P v -> Forall P (x::v).
#[local]
Hint Constructors Forall : core.

Inductive Exists {A} (P:A->Prop): forall {n}, t A n -> Prop :=
 |Exists_cons_hd {m} x (v: t A m): P x -> Exists P (x::v)
 |Exists_cons_tl {m} x (v: t A m): Exists P v -> Exists P (x::v).
#[local]
Hint Constructors Exists : core.

Inductive In {A} (a:A): forall {n}, t A n -> Prop :=
 |In_cons_hd {m} (v: t A m): In a (a::v)
 |In_cons_tl {m} x (v: t A m): In a v -> In a (x::v).
#[local]
Hint Constructors In : core.

Inductive Forall2 {A B} (P:A->B->Prop): forall {n}, t A n -> t B n -> Prop :=
 |Forall2_nil: Forall2 P [] []
 |Forall2_cons {m} x1 x2 (v1:t A m) v2: P x1 x2 -> Forall2 P v1 v2 ->
    Forall2 P (x1::v1) (x2::v2).
#[local]
Hint Constructors Forall2 : core.

Inductive Exists2 {A B} (P:A->B->Prop): forall {n}, t A n -> t B n -> Prop :=
 |Exists2_cons_hd {m} x1 x2 (v1: t A m) (v2: t B m): P x1 x2 -> Exists2 P (x1::v1) (x2::v2)
 |Exists2_cons_tl {m} x1 x2 (v1:t A m) v2: Exists2 P v1 v2 -> Exists2 P (x1::v1) (x2::v2).
#[local]
Hint Constructors Exists2 : core.

End SCANNING.

Section VECTORLIST.

Definition of_list {A:Type} : forall l : list A, t A (length l) := 
fun (l:list A) =>
{| elts := l; elts_spec := eq_refl |}.

(*as in std*)
Fixpoint of_list_std {A} (l : list A) : t A (length l) :=
match l as l' return t A (length l') with
  |Datatypes.nil => []
  |(h :: tail)%list => (h :: (of_list_std tail))
end.

Definition to_list {A:Type} {n:nat} (v:t A n) : list A :=
match v with {|elts:=l;elts_spec:=p|} => 
l
end.

Definition to_list_std {A}{n} (v : t A n) : list A :=
Eval cbv delta beta in fold_right (fun h H => Datatypes.cons h H) v Datatypes.nil.

End VECTORLIST.


Module ListVectorNotations.
Declare Scope list_vector_scope.
Delimit Scope list_vector_scope with list_vector.
Notation "[ ]" := [] (format "[ ]") : list_vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
  : list_vector_scope.
Notation "[ x ]" := (x :: []) : list_vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : list_vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : list_vector_scope.
Infix "++" := append : list_vector_scope.
Open Scope list_vector_scope.
End ListVectorNotations.