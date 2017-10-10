Require Import ZArith.
Open Scope Z_scope.
Require Import Psatz.

Hint Resolve Z.le_max_l : zarith.
Hint Resolve Z.le_max_r : zarith.

Lemma pow_ge_1 : forall a b,
  0 < a ->
  0 <= b ->
  1 <= a ^ b.
Proof.
  intros a b A B.
  rewrite <-(Z.pow_0_r a).
  apply Z.pow_le_mono_r; auto.
Qed.

Hint Resolve pow_ge_1 : zarith.

Lemma Zmax_rub : forall a b c,
  c <= a ->
  c <= b ->
  c <= Z.max a b.
Proof. intros. lia. Qed.

Hint Resolve Zmax_rub : zarith.
