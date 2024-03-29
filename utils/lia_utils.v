Require Import Lia.

Lemma nat_uip {x y : nat} (p q : x = y) : p = q.
Proof.
apply Eqdep_dec.UIP_dec.
exact PeanoNat.Nat.eq_dec.
Qed.
Lemma not_lt_0: forall n: nat, n < 0 -> False.
Proof.
lia.
Qed.
Lemma lt_S: forall n m:nat, S n < S m -> n < m.
Proof. lia. Qed.

Lemma S_not_0: forall n:nat, 0 = S n -> False.
Proof. lia. Qed.

Lemma leq_S: forall n m:nat, S n <= S m -> n <= m.
Proof. lia. Qed.

Lemma m_sub_n_lt_m: forall n m: nat, (S m) - (S n) < S m.
Proof. lia. Qed.

Lemma Sn_lt_m_impl_n_lt_m: forall n m:nat, (S n) < m -> n < m.
Proof. lia. Qed.

Lemma n_lt_Sn: forall n:nat, n < (S n).
Proof. lia. Qed.

Lemma Sn_not_leq_0: forall n:nat, S n <= 0 -> False.
Proof. lia. Qed.