Require Import TLC.LibTactics.

Require Export ZArith.
Local Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Psatz. (* nia *)
Require Export Filter.
Require Import Dominated.
Require Import BigEnough.

Section UltimatelyGe_k.

Variable k : Z.
Hypothesis k_nonneg : 0 <= k.

Lemma ultimately_ge_cst :
  forall c,
  k <= c ->
  ultimately Z_filterType (fun _ => k <= c).
Proof.
  intros c Hc.
  apply filter_universe_alt. intros _.
  assumption.
Qed.

Lemma ultimately_ge_sum :
  forall (A : filterType) f1 f2,
  ultimately A (fun x => k <= f1 x) ->
  ultimately A (fun x => k <= f2 x) ->
  ultimately A (fun x => k <= f1 x + f2 x).
Proof.
  introv. filter_closed_under_intersection.
  intros. lia.
Qed.

Lemma ultimately_ge_max :
  forall (A : filterType) f1 f2,
  ultimately A (fun x => k <= f1 x) ->
  ultimately A (fun x => k <= f2 x) ->
  ultimately A (fun x => k <= Z.max (f1 x) (f2 x)).
Proof.
  introv. filter_closed_under_intersection.
  intros. lia.
Qed.

Lemma ultimately_ge_mul :
  forall (A : filterType) f1 f2,
  ultimately A (fun x => k <= f1 x) ->
  ultimately A (fun x => k <= f2 x) ->
  ultimately A (fun x => k <= f1 x * f2 x).
Proof.
  introv. filter_closed_under_intersection.
  intros. assert (k * k <= f1 a * f2 a) by nia.
  nia.
Qed.

Lemma ultimately_ge_id :
  ultimately Z_filterType (fun x => k <= x).
Proof.
  exists k. auto.
Qed.

Lemma ultimately_ge_limit :
  forall (A : filterType) f,
  limit A Z_filterType f ->
  ultimately A (fun x => k <= f x).
Proof.
  introv L.
  apply L. apply ultimately_ge_Z.
Qed.

End UltimatelyGe_k.

Lemma ultimately_gt_ge :
  forall (k: Z) (A : filterType) f,
  ultimately A (fun x => k + 1 <= f x) ->
  ultimately A (fun x => k < f x).
Proof.
  introv. filter_closed_under_intersection.
  intros. omega.
Qed.

Lemma ultimately_ge_cumul_Z :
  forall (k : Z) (f : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun x => 0 < f x) ->
  ultimately Z_filterType (fun x => k <= cumul f lo x).
Proof.
  introv.
  generalize (ultimately_ge_Z lo). filter_intersect.
  introv U. rewrite ZP in U.
  destruct U as (n0 & H).
  exists_big n1 Z. intros n N.
  assert (n1_ge_n0: n0 <= n1) by big.
  rewrite (cumul_split n0).
  Focus 2. apply H. auto with zarith.
  Focus 2. rewrite <-N. auto.

  assert (cumul_part_2: n - n0 <= cumul f n0 n).
  { admit. (* cf dominated.v *) }

  rewrite <-cumul_part_2.
  cut (k + n0 - cumul f lo n0 <= n). omega.
  rewrite <-N. big.
  close.
Qed.

Lemma ultimately_ge_0_cumul_nonneg_Z :
  forall (f : Z -> Z) (lo : Z),
  (forall x, 0 <= f x) ->
  ultimately Z_filterType (fun x => 0 <= cumul f lo x).
Proof.
  introv H.
  apply filter_universe_alt. intros.
  rewrite cumulP. apply big_nonneg_Z.
  intros; auto with zarith.
Qed.

Ltac ultimately_greater :=
  repeat first [
      apply ultimately_gt_ge; simpl
    | apply ultimately_ge_id
    | apply ultimately_ge_cst; auto with zarith; omega
    | apply ultimately_ge_sum; [ auto with zarith; omega | .. ]
    | apply ultimately_ge_max
    | apply ultimately_ge_mul; [ auto with zarith; omega | .. ]
    | apply ultimately_ge_0_cumul_nonneg_Z; intro; auto with zarith; omega
    | apply ultimately_ge_cumul_Z
    | apply filter_universe_alt; auto with zarith; (intros; omega)
  ].

(* FIXME: not extensible (?) *)
