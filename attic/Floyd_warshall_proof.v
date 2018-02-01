Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibListSort.
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
(* Load the CF definitions. *)
Require Import Floyd_warshall_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

(* Parameter Array : forall A, list A -> loc -> hprop. *)

(* Parameter Matrix : forall A, list (list A) -> loc -> hprop := *)
(*   forall A xxs m, *)
(*     Hexists (xs : list loc), m ~> xs \*  *)

Lemma floyd_warshall_spec :
  specZ [cost \in_O (fun n => n ^ 3)]
    (forall a (xs : list (array int)),
      app floyd_warshall [a]
      PRE (\$ cost (length xs) \* a ~> Array xs)
      POST (fun (_:unit) => Hexists (xs' : list (array int)), a ~> Array xs')).
Proof.
  xspecO. xcf. xpay.
  xapps.
  weaken. xfor_inv (fun (_:int) => Hexists (xs1 : list (array int)), a ~> Array xs1). math.
  { intros i Hi. xpull. intros xs1. xpay.
    weaken. xfor_inv (fun (_:int) => Hexists (xs2 : list (array int)), a ~> Array xs2). math.
    { intros j Hj. xpull. intros xs2. xpay.
      weaken. xfor_inv (fun (_:int) => Hexists (xs3 : list (array int)), a ~> Array xs3). math.
      { intros k Hk. xpull. intros xs3. xpay.
        xapps~. admit. xapps.
Abort.