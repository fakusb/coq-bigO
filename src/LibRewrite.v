Require Import Coq.Program.Basics. (* [flip] *)
Require Export Coq.Setoids.Setoid. (* required for [rewrite] *)
Require Export Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import ZArith Psatz.
Require Import TLC.LibTactics.
Require Import LibNatExtra.
Obligation Tactic := idtac.

(* A tactic that helps assert a trivial arithmetic property, prove this
   property, and immediately rewrite using this property. *)

Ltac omega_rewrite P :=
  let h := fresh in
  assert (h: P); [ intros; omega | rewrite h; clear h ].

(* Addition is covariant in both arguments. *)

Program Instance proper_plus: Proper (le ++> le ++> le) plus.
Next Obligation.
  intros x1 y1 h1 x2 y2 h2. omega.
Qed.

Program Instance proper_Zplus : Proper (Z.le ++> Z.le ++> Z.le) Z.add.
Next Obligation.
  intros x1 y1 h1 x2 y2 h2. omega.
Qed.

(* Subtraction is covariant in its first argument and contravariant in
   its second argument. *)

Program Instance proper_minus: Proper (le ++> le --> le) minus.
Next Obligation.
  unfold flip. intros x1 y1 h1 x2 y2 h2. omega.
Qed.

(* Multiplication is covariant in both arguments. *)

Program Instance proper_mult: Proper (le ++> le ++> le) mult.
Next Obligation.
  intros x1 y1 h1 x2 y2 h2.
  rewrite mult_le_compat_l, mult_le_compat_r by eauto.
  reflexivity.
Qed.

(* However, multiplication on Z requires a positivity condition.

   For rewriting on the right, the following work-around works.
   However, for rewriting on the left, we do not know one...
*)
Definition ShowLater (A : Type) := A.

Hint Extern 100 (ShowLater _) =>
  (unfold ShowLater; first [assumption | shelve]) : typeclass_instances.

Program Instance proper_Zmult_left :
  forall x, ShowLater (Z.le 0 x) ->
  Proper (Z.le ++> Z.le) (Z.mul x).
Next Obligation.
  intros ? ? ? ?. unfold ShowLater in *. nia.
Qed.

(* The following does not seem to work: *)

(* Program Instance proper_Zmult_right: *)
(*   forall y, Z.le 0 y -> *)
(*   Proper (Z.le ++> Z.le) (fun x => Z.mul x y). *)
(* Next Obligation. *)
(*   intros ? ? ? ?. nia. *)
(* Qed. *)

(* Goal forall a b c d, a <= b -> 0 <= c -> b * c <= d * c -> a * c <= d * c. *)
(* introv a_le_b O_le_c bc_le_dc. *)
(* rewrite a_le_b. *)

(* Maximum is covariant in both arguments. *)

Program Instance proper_max: Proper (le ++> le ++> le) max.
Next Obligation.
  intros x1 y1 h1 x2 y2 h2. do 2 max_case; omega.
Qed.

(* Strict ordering implies lax ordering. *)

Program Instance subrelation_lt_le: subrelation lt le.
Next Obligation.
  intros x y h. omega.
Qed.

(* A quick test. *)

Goal
  forall x y z w : nat,
  x <= y ->
  w < 3 ->
  max w (x * z + 1) <= max 3 (y * z + 1).
Proof using.
  introv h1 h2. rewrite h1, h2. reflexivity.
Qed.

(* The lemma [eq_subrelation] is proved somewhere in the standard library,
   but is not added to the type class database (why?). *)

Program Instance Eq_subrelation A (R : relation A) `{Reflexive A R} :
  subrelation eq R.
Next Obligation.
  intros. eapply eq_subrelation; eauto.
Qed.

(* The pointwise extension of a relation [R] is reflexive, symmetric, and
   transitive, if [R] is. *)

Program Instance pointwise_relation_reflexive
  A B (R : relation B) `{Reflexive B R} : Reflexive (pointwise_relation A R).
Next Obligation.
  intro. reflexivity.
Qed.

Global Program Instance pointwise_relation_symmetric
  A B (R : relation B) `{Symmetric B R} : Symmetric (pointwise_relation A R).
Next Obligation.
  repeat intro. eauto.
Qed.

Program Instance pointwise_relation_transitive
  A B (R : relation B) `{Transitive B R} : Transitive (pointwise_relation A R).
Next Obligation.
  repeat intro. transitivity (y a); eauto.
Qed.

Notation pw R :=
  (pointwise_relation _ R).

Infix "%<=" := (pw le) (at level 70) : nat_scope.

(* More tests. *)

Goal
  forall x y : nat,
  x <= y ->
  (fun n : nat => n * x + n) %<= (fun n : nat => n * y + n).
Proof using.
  intros x y h. setoid_rewrite h. reflexivity.
Qed.

Goal
  forall x y : nat,
  x <= y ->
  (fun n : nat => 1 + n * x + n) %<= (fun n : nat => 2 + n * y + n).
Proof using.
  intros x y h.
  assert (f: 1 <= 2). omega.
  setoid_rewrite f at 1. (* Note: [at 1] is necessary because 2 contains 1 as a subterm! *)
  setoid_rewrite h.
  reflexivity.
Qed.

(* TEMPORARY investigate *)
Goal
  forall x y : nat,
  x <= y ->
  (fun n : nat => x) %<= (fun n : nat => y).
Proof using.
  intros x y h. (* setoid_rewrite <- h. reflexivity. *)
Abort. (* OK *) (* TEMPORARY *)

(* Rewriting lists up to permutations. *)

Program Instance app_permutation (A : Type) :
  Proper (@Permutation A ++> @Permutation A ++> @Permutation A) (@app A).
Next Obligation.
  repeat intro. eauto using Permutation_app.
Qed.

Program Instance map_permutation (A B : Type) (f : A -> B) :
  Proper (@Permutation A ++> @Permutation B) (@map A B f).
Next Obligation.
  repeat intro. eauto using Permutation_map.
Qed.

(* Test. *)

Goal
  forall {A : Type} (xs ys zs : list A) (f : A -> A),
  Permutation xs ys ->
  Permutation (map f (xs ++ zs)) (map f (ys ++ zs)).
Proof using.
  introv h. rewrite h. reflexivity.
Qed.
