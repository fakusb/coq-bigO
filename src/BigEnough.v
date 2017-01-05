Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import NArith ZArith Psatz.
Require Import TLC.LibReflect.

(* This is a simplified version of mathcomp/real-closed/bigenough.v.        *)

(****************************************************************************)
(*           pose_big i T == pose a big enough i : T                        *)
(*         exists_big i T := pose_big i T; first exists i                   *)
(*     pose_big_fun m F T == pose a big enough m : F -> T                   *)
(*   exists_big_fun m F T := pose_big_fun m F T; first exists m             *)
(*                    big == replaces x <= i by true in the goal,           *)
(*                           remembering that i should be at least x        *)
(*                close   == all "pose" tactics create a dummy subgoal to   *)
(*                           force the user to explicitly indicate that all *)
(*                           constraints have been found                    *)
(****************************************************************************)

(* ------------------------------------------------------------------------ *)

(* The following definitions are private. *)

Module Big.

(* We can work at an arbitrary type [sort], equipped with a relation [leq],
   a default element [default], and a binary operator [max]. The only two
   properties that we need are [here] and [next], which together express the
   fact that [max i j] is greater than (or equal to) both [i] and [j] and
   [leq] is transitive. *)

Structure class := Class {
  sort :> Type;
  leq : sort -> sort -> Prop;
  default: sort;
  max : sort -> sort -> sort;
  here : forall i j, leq i (max i j);
  next : forall i j k, leq i k -> leq i (max j k)
}.

(* Here is a proof of the lemma [next] at type [nat]. *)

Lemma next_nat:
  forall i j k, i <= k -> i <= Nat.max j k.
Proof. intros. lia. Qed.

(* Applying the lemma [context] allows us to find an occurrence of
   [leq i j] in the goal and replace it with [true], provided we
   can separately prove that [leq i j] holds. *)

Lemma context P (c : class) (i j : c) :
  leq i j ->
  P True ->
  P (leq i j).
Proof. intros le PT. rewrite (is_True le). assumption. Qed.

(* In order to ensure that all meta-variables are properly instantiated,
   we create a subgoal of the form [closed i], where [i] is a term that
   contains exactly one meta-variable of the max-type of interest. *)

Definition closed T (i : T) := {j : T | j = i}.

(* The tactic [big_base] is our basic machinery. It applies to a goal
   of the form [leq _ ?i], where [i] has been introduced by [pose_big], or
   [leq _ (?m _)], where [m] has been introduced by [pose_big_fun]. It solves
   the goal by iteratively applying the lemma [next] until the lemma [here]
   can be applied. In other words, it performs linear list search, followed
   with list extension, if the desired constraint has not been recorded
   already. *)

Ltac big_base :=
  (* For some reason, if the right-hand side of the goal inequality is
     an application of [m], where [m] has been introduced by [pose_big_fun],
     then it may be necessary to expand away the application of [m] before
     applying the lemmas [here] and [next]. *)
  try ( match goal with |- is_true (leq _ (?m _)) => rewrite m end );
  repeat first [ apply here | apply next ].

(* ------------------------------------------------------------------------ *)

(* The following definitions are public. *)

Module Exports.

(* This canonical structure declaration allows our machinery to be used
   at type [nat]. Other analogous declarations can be given by the user,
   if desired. *)

Canonical Structure nat_bigenough :=
  Class O Nat.le_max_l next_nat.

(* Define similar canonical structures on [N] and [Z]. *)
Section N.
Local Open Scope N_scope.

Lemma next_N : forall i j k, i <= k -> i <= N.max j k.
Proof. intros. lia. Qed.

Canonical Structure N_bigenough :=
  Class 0 N.le_max_l next_N.

End N.

Section Z.
Local Open Scope Z_scope.

Lemma next_Z : forall i j k, i <= k -> i <= Z.max j k.
Proof. intros. lia. Qed.

Canonical Structure Z_bigenough :=
  Class 0 Z.le_max_l next_Z.

End Z.

(* The tactic [close] must be used to close a goal of the form [closed ?i].
   Note that the type of the meta-variable [i] is not necessarily [T], the
   max-type of interest. It could be [F -> T], for instance, for some type
   [F]. Yet, we know that [i] is bound to some term which contains one
   meta-variable of type [T]. We instantiate this meta-variable to the default
   value of type [T], and we are done. *)

Ltac close :=
  match goal with |- closed ?i =>
    instantiate (1 := @default _) in (Value of i);
    exists i; reflexivity
  end.

(* The tactic [pose_big i T] introduces a meta-variable [i] upon which the
   user intends to accumulate constraints. It creates a sub-goal of the form
   [closed i], which can be closed (once the user is done with the main
   sub-goal) by [close]. *)

Ltac pose_big i T :=
  evar (i : T);
  cut (closed i); [ intros _ |].

Ltac exists_big i T :=
  pose_big i T; [ exists i | .. ].

(* The tactic [pose_big_fun m F T] is analogous to [pose_big], but introduces
   a meta-variable [m] of type [F -> T]. Somewhat amazingly, we will be able
   to collect constraints on the function body that may mention the function
   argument. *)

Ltac pose_big_fun m F T :=
  evar (m : F -> T);
  instantiate (1 := fun e => _) in (Value of m);
  cut (closed m); [ intros _ |].

Ltac exists_big_fun m F T :=
  pose_big_fun m F T; [ exists m | .. ].

(* The tactic [big] repeatedly finds an inequality of the form [leq x i] in
   the goal, records this constraint on [i], and replaces the inequality with
   [true]. *)

Ltac big :=
  repeat first [ apply context; [ big_base | .. ] ];
  try tauto.

(* The file mathcomp/real-closed/bigenough.v contains an additional twist,
   [big_enough_trans], which finds an ordering hypothesis and exploits the
   transitivity of [leq]. It also redefines the tactic [done] to implicitly
   use [big_enough_trans] and [big]. For simplicity, we do not do so. *)

End Exports.

End Big.

Export Big.Exports.

(* ------------------------------------------------------------------------ *)

(* Unit tests / examples. *)

Goal forall k1 k2, exists i, (k1 <= i) /\ (1 <= i) /\ (k2 <= i).
Proof.
  intros k1 k2.
  exists_big i nat.
  (* We can split manually... *)
  repeat split.
  (* ... and apply [big] to each constraint. *)
  big.
  big.
  big.
  (* We are then finished. *)
  close.
Qed.

Goal forall k1 k2, exists i, (k1 <= i) /\ (1 <= i) /\ (k2 <= i).
Proof.
  intros k1 k2.
  exists_big i nat.
  (* We can also let [big] do the work by itself! *)
  big.
  close.
Qed.

Goal forall P : Prop, P -> exists i, P /\ (2 <= i).
Proof.
  intros P H.
  exists_big i nat.
  (* The goal can contain parts that [big] does not care about. *)
  big.
  close.
Qed.

Goal exists m : nat -> nat, forall e, (e <= m e) /\ (e + 2 <= m e).
Proof.
  exists_big_fun m nat nat.
  intro e.
  (* The left-hand sides of the constraints can refer to the variable [e]. *)
  big.
  close.
Qed.


(* Check that the instances for [N] and [Z] also work... *)

Local Open Scope N_scope.
Goal forall (k1 k2 : N), exists i, (k1 <= i) /\ (1 <= i) /\ (k2 <= i).
Proof.
  intros k1 k2.
  exists_big i N.
  big.
  close.
Qed.

Local Open Scope Z_scope.
Goal forall (k1 k2 : Z), exists i, (k1 <= i) /\ (1 <= i) /\ (k2 <= i).
Proof.
  intros k1 k2.
  exists_big i Z.
  big.
  close.
Qed.
