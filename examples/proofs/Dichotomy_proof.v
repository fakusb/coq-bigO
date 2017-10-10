Set Implicit Arguments.
Require Import TLC.LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
Require Pervasives_ml.
Require Array_ml.
Require Import Pervasives_proof.
Require Import Array_proof.
(* Load the big-O library. *)
Require Import Dominated.
Require Import UltimatelyGreater.
Require Import Monotonic.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
Require Import EvarsFacts.
(* Load the CF definitions. *)
Require Import Dichotomy_ml.

Lemma bsearch_spec :
  specZ [cost \in_O (fun n => Z.log2 n)]
    (forall t (xs : list int) (v : int) (i j : int),
        app bsearch [t v i j]
        PRE (\$ (cost (length xs)) \* t ~> Array xs)
        POST (fun (k:int) => t ~> Array xs)).
Proof.
  pose_facts_evars facts a b.
  assert (0 <= a) as Ha by (prove_later facts).

  xspecO_cost (fun n => a * Z.log2 n + b) on (fun n => 0 <= n).
  intros cost' E. intros t xs v i j. rewrite E; [|math]. clear cost' E.
Abort.