Require Import TLC.LibTactics.

Require Import Coq.Logic.Classical_Pred_Type.
Require Import ZArith.
Local Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Psatz. (* nia *)
Require Import Filter.

(* ---------------------------------------------------------------------------- *)

(* If we have a filter on [A], then we can define a domination relation between
   functions of type [A -> Z]. *)

(* In principle, we could consider functions of type [A -> B], where [B] is an
   integral domain (see ssrnum.v). The (relative) integers form an integral
   domain; so do the reals. *)

(* [dominated f g] holds if and only if, for some constant [c], [f x] is
   ultimately bounded (in norm) by [c * g x]. We explicitly require [c] to be
   nonnegative, because this seems more convenient. *)

Section Domination.

Variable A : filterType.

Definition dominated (f g : A -> Z) :=
  exists c, (0 <= c) /\ ultimately A (fun x => Z.abs (f x) <= c * Z.abs (g x)).

(* This notion is analogous to [is_domin] in Coquelicot. *)

(* ---------------------------------------------------------------------------- *)

(* Pointwise inequality implies domination. *)

Lemma subrelation_le_dominated f g :
  (forall x, Z.abs (f x) <= Z.abs (g x)) ->
  dominated f g.
Proof.
  exists 1. split; [ eauto with zarith |].
  apply filter_universe_alt. eauto with zarith.
Qed.

(* Ultimately pointwise inequality implies domination. *)

Lemma subrelation_ultimately_le_dominated f g :
  ultimately A (fun x => Z.abs (f x) <= Z.abs (g x)) ->
  dominated f g.
Proof.
  intros U. exists 1. split; [ eauto with zarith |].
  apply (filter_closed_under_inclusion U).
  eauto with zarith.
Qed.

(* Domination is reflexive.
   (Howell's Property 4)
*)

Lemma dominated_reflexive f :
  dominated f f.
Proof.
  eauto using subrelation_le_dominated with zarith.
Qed.

(* Domination is transitive. *)

Lemma dominated_transitive f g h :
  dominated f g -> dominated g h -> dominated f h.
Proof.
  intros (c1 & c1P & U1) (c2 & c2P & U2).
  exists (c1 * c2).
  split; [ eauto with zarith |].
  apply (filter_closed_under_intersection U1 U2).
  intros. nia.
Qed.

End Domination.
Arguments dominated : clear implicits.

Section DominatedLaws.

Variable A : filterType.

(* Howell's Property 3. *)

Lemma dominated_le_transitive f g1 g2 :
  ultimately A (fun x => Z.abs (g1 x) <= Z.abs (g2 x)) ->
  dominated A f g1 ->
  dominated A f g2.
Proof.
  intros U D.
  apply dominated_transitive with g1; eauto.
  apply subrelation_ultimately_le_dominated. eauto.
Qed.

(* Domination is compatible with mul.
   (Howell's Property 5)
*)

Lemma dominated_mul f1 f2 g1 g2 :
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => (f1 x) * (f2 x)) (fun x => (g1 x) * (g2 x)).
Proof.
  intros (c1 & c1_pos & U_f1_g1) (c2 & c2_pos & U_f2_g2).
  exists (c1 * c2). split; [ eauto with zarith |].
  apply (filter_closed_under_intersection U_f1_g1 U_f2_g2).
  intros. nia.
Qed.

(* A maximum is dominated by a sum, for ultimately nonnegative functions. *)

Lemma dominated_max_sum f g :
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  dominated A (fun x => Z.max (f x) (g x)) (fun x => f x + g x).
Proof.
  intros fpos gpos. exists 1. split; [ eauto with zarith |].
  revert fpos gpos; filter_closed_under_intersection.
  intros. nia.
Qed.

(* Conversely, a sum is dominated by a maximum. [max] and [+] are asymptotically
   equivalent, for ultimately nonnegative functions. *)

Lemma dominated_sum_max f g :
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  dominated A (fun x => f x + g x) (fun x => Z.max (f x) (g x)).
Proof.
  intros fpos gpos. exists 2. split; eauto with zarith.
  revert fpos gpos; filter_closed_under_intersection.
  intros. nia.
Qed.

(* Domination is compatible with sum. *)

Lemma dominated_sum f1 f2 g1 g2 :
  ultimately A (fun x => 0 <= g1 x) ->
  ultimately A (fun x => 0 <= g2 x) ->
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => f1 x + f2 x) (fun x => g1 x + g2 x).
Proof.
  intros g1P g2P (c1 & c1P & u1) (c2 & c2P & u2).
  exists (Z.max c1 c2).
  split; [ nia |].
  revert g1P g2P u1 u2; filter_closed_under_intersection.
  intros. nia.
Qed.

End DominatedLaws.
