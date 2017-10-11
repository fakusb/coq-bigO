Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibInt.
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

Lemma Zquot_mul_2 : forall x,
  0 <= x ->
  x - 1 <= 2 * (x ÷ 2) <= x.
Proof.
  intros x Hx. rewrite <-Zquot2_quot. sets half: (Z.quot2 x).
  cases_if_on (Z.odd x) as H.
  - rewrite (Zodd_quot2 x); subst half; try math. apply~ Zodd_bool_iff.
  - rewrite (Zeven_quot2 x); subst half; try math. apply~ Zeven_bool_iff.
    rewrite Zeven.Zeven_odd_bool. rewrite H; reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Base 2 logarithm. *)

Lemma Zlog2_step : forall x,
  2 <= x ->
  1 + Z.log2 (x÷2) = Z.log2 x.
Proof.
  admit. (* TODO: prove from the log2_step in LibNatExtra? *)
Qed.
