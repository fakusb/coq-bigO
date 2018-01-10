Set Implicit Arguments.
Require Import TLC.LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
Require Pervasives_ml.
Require Array_ml.
Require Import Pervasives_proof.
Require Import ArrayCredits_proof.
(* Load the big-O library. *)
Require Import Dominated.
Require Import UltimatelyGreater.
Require Import Monotonic.
Require Import LibZExtra.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.

(* FIXME: coq bug *)
Lemma L: forall A B (x : (A * B)%type) (f g : A -> B -> Z),
             f (fst x) (snd x) = g (fst x) (snd x) ->
             (let (y,z) := x in f y z) = (let (y,z) := x in g y z).
Proof. intros ? ? x_ ? ? ?. destruct x_. simpl in *. assumption. Qed.

Goal
  specO
    (product_filterType Z_filterType Z_filterType) eq
    (fun _ => True)
    (fun '(n,m) => 0).
Proof.
  xspecO. admit.
  unfold cleanup_cost. splits.
  intro x. unfold costf. eapply L. (* simpl. *)
Abort.

(* For later: what to think about the following unification problem:

   x + y = ?f(x,y) + ?g(x,y)

   Coq doesn't know how to solve it (and there are at least two different
   solutions, (eg inserting a let or using projections)).

   Is it a feature? Is it a limitation that may be lifted in the future?
 *)
