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
  ultimately Z_filterType (fun n => 0 < f n) ->
  ultimately Z_filterType (fun n => k <= cumul lo n f).
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

  assert (cumul_part_2: n - n0 <= cumul n0 n f).
  { admit. (* cf dominated.v *) }

  rewrite <-cumul_part_2.
  cut (k + n0 - cumul lo n0 f <= n). omega.
  rewrite <-N. big.
  close.
Qed.

Lemma ultimately_ge_0_cumul_nonneg_Z :
  forall (f : Z -> Z -> Z) (lo : Z),
  (forall hi x, lo <= x < hi -> 0 <= f hi x) ->
  ultimately Z_filterType (fun n => 0 <= cumul lo n (f n)).
Proof.
  introv H.
  apply filter_universe_alt. intros.
  rewrite cumulP. apply big_nonneg_Z.
  intros; auto with zarith.
Qed.

Lemma ultimately_lift1 (A B : filterType) :
  forall f lo,
  ultimately A (fun x => lo <= f x) ->
  ultimately (product_filterType A B) (fun '(x, _) => lo <= f x).
Proof.
  intros f lo U.
  rewrite productP. do 2 eexists. splits; try apply U. apply filter_universe.
  tauto.
Qed.

Lemma ultimately_lift2 (A B : filterType) :
  forall f lo,
  ultimately B (fun y => lo <= f y) ->
  ultimately (product_filterType A B) (fun '(_, y) => lo <= f y).
Proof.
  intros f lo U.
  rewrite productP. do 2 eexists. splits; try apply U. apply filter_universe.
  tauto.
Qed.

(******************************************************************************)
(* Put lemmas into a base of hints [ultimately_greater] *)

(* For some lemmas, simply adding them as a [Hint Resolve] does not seem to
   work. As a workaround we manually add them using [Hint Extern].
*)
Hint Extern 0 (ultimately _ (fun _ => _ < _)) =>
  apply ultimately_gt_ge : ultimately_greater.
Hint Resolve ultimately_ge_id : ultimately_greater.
Hint Resolve ultimately_ge_cst : ultimately_greater.
Hint Extern 3 (ultimately _ (fun _ => _ <= _ + _)) =>
  simple apply ultimately_ge_sum : ultimately_greater.
Hint Extern 2 (ultimately _ (fun _ => _ <= Z.max _ _)) =>
  simple apply ultimately_ge_max : ultimately_greater.
Hint Extern 3 (ultimately _ (fun _ => _ <= _ + _)) =>
  simple apply ultimately_ge_mul : ultimately_greater.
Hint Extern 1 (ultimately Z_filterType (fun _ => 0 <= cumul _ _ _)) =>
  simple apply ultimately_ge_0_cumul_nonneg_Z : ultimately_greater.
Hint Extern 2 (ultimately Z_filterType (fun _ => _ <= cumul _ _ _)) =>
  simple apply ultimately_ge_cumul_Z.
Hint Resolve filter_universe_alt | 50 : ultimately_greater.
Hint Resolve ultimately_lift1 : ultimately_greater.
Hint Resolve ultimately_lift2 : ultimately_greater.

Hint Extern 100 => try (intros; omega) : ultimately_greater_sidegoals.

Hint Extern 999 (ultimately _ (fun _ => _ <= _)) => shelve : ultimately_greater_fallback.

(******************************************************************************)

(* The order of the hints bases given to auto seems to matter: things break if
   [zarith] is put after [ultimately_greater]... *)

(* Contrary to the standard behavior of [auto], this tactic tries to do some
   progress by applying the lemmas, and returning the side-goals it could not
   prove to the user. *)
Ltac ultimately_greater :=
  unshelve (auto with zarith
                      ultimately_greater
                      ultimately_greater_sidegoals
                      ultimately_greater_fallback).

(* This variant follows [auto]'s standard behavior. It does not modifies the
   goal if it could not prove it entirely. *)
Ltac ultimately_greater_trysolve :=
  auto with zarith
            ultimately_greater
            ultimately_greater_sidegoals.