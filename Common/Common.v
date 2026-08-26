From Stdlib Require Export Unicode.Utf8.
From Stdlib Require Import micromega.Lia.

Lemma S_le {n m} : S n ≤ m → exists m', m = S m' ∧ n ≤ m'.
Proof.
  intros le; destruct m; [exfalso|exists m]; lia.
Qed.

Lemma lt_inv_plus {n m} : n < m → exists r, m = n + S r.
Proof.
  induction 1.
  - exists 0; lia.
  - destruct IHle as [r ?]; subst.
    exists (S r); lia.
Qed.

Lemma le_inv_plus {n m} : n ≤ m → exists r, m = n + r.
Proof.
  induction 1.
  - exists 0; lia.
  - destruct IHle as [r ?]; subst.
    exists (S r); lia.
Qed.

