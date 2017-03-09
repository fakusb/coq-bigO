Require Import TLC.LibTactics.

Require Export ZArith.
Local Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Psatz. (* nia *)
Require Export Filter.
Require Import Dominated.

Lemma ultimately_nonneg_cst :
  forall c,
  0 <= c ->
  ultimately Z_filterType (fun _ => 0 <= c).
Proof.
  intros c Hc.
  apply filter_universe_alt. intros _.
  assumption.
Qed.

Lemma ultimately_nonneg_sum :
  forall (A : filterType) f1 f2,
  ultimately A (fun x => 0 <= f1 x) ->
  ultimately A (fun x => 0 <= f2 x) ->
  ultimately A (fun x => 0 <= f1 x + f2 x).
Proof.
  introv. filter_closed_under_intersection.
  intros. lia.
Qed.

Lemma ultimately_nonneg_max :
  forall (A : filterType) f1 f2,
  ultimately A (fun x => 0 <= f1 x) ->
  ultimately A (fun x => 0 <= f2 x) ->
  ultimately A (fun x => 0 <= Z.max (f1 x) (f2 x)).
Proof.
  introv. filter_closed_under_intersection.
  intros. lia.
Qed.

Lemma ultimately_nonneg_mul :
  forall (A : filterType) f1 f2,
  ultimately A (fun x => 0 <= f1 x) ->
  ultimately A (fun x => 0 <= f2 x) ->
  ultimately A (fun x => 0 <= f1 x * f2 x).
Proof.
  introv. filter_closed_under_intersection.
  intros. nia.
Qed.

Lemma ultimately_nonneg_id :
  ultimately Z_filterType (fun x => 0 <= x).
Proof.
  exists 0. auto.
Qed.

Ltac nonneg_cumul_nonneg :=
  apply filter_universe_alt;
  intro;
  rewrite cumulP;
  apply big_nonneg_Z;
  intros;
  auto with zarith;
  omega.

Ltac ultimately_nonneg_cumul :=
  first [
    nonneg_cumul_nonneg
  ].

Ltac ultimately_nonneg :=
  repeat first [
      apply ultimately_nonneg_id
    | apply ultimately_nonneg_cst; auto with zarith; omega
    | apply ultimately_nonneg_sum
    | apply ultimately_nonneg_max
    | apply ultimately_nonneg_mul
    | ultimately_nonneg_cumul
  ].

(* -----------------------------------------------------------------*)

Lemma ultimately_nonneg_limit :
  forall (A : filterType) f,
  limit A Z_filterType f ->
  ultimately A (fun x => 0 <= f x).
Proof.
  introv L.
  apply L. apply ultimately_ge_Z.
Qed.
