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
Require Import Exponential_ml.

Lemma f_spec :
  specZ [cost \in_O (fun n => 2 ^ n)]
    (forall (n: int),
      0 <= n ->
      app f [n]
        PRE (\$ (cost n))
        POST (fun (tt:unit) => \[])).
Proof.
  xspecO_cost (fun n => 2^(n+1) - 1) on (fun n => 0 <= n).
  intros cost' E n N. rewrite E; [| solve [auto]]; clear E cost'. revert n N.

  intro n. induction_wf: (downto 0) n. intro N.

  xcf. xpay. hsimpl_credits. admit. math.
  xrets.
  xif. { xret~. }
       { xapp; try math. hsimpl_credits. admit. admit.
         xapp; try math. hsimpl_credits. admit. admit. }

  admit.
  monotonic.
  admit.
Qed.

Lemma f_spec2 :
  specZ [cost \in_O (fun n => 2 ^ n)]
    (forall (n: int),
      0 <= n ->
      app f [n]
        PRE (\$ (cost n))
        POST (fun (tt:unit) => \[])).
Proof.
  xspecO_cost (fun n => 2^(n+1) - 1) on (fun n => 0 <= n).
  intros cost' E n N. rewrite E; [| solve [auto]]; clear E cost'. revert n N.

  intro n. induction_wf: (downto 0) n. intro N.
  refine_credits. xcf. xpay.

  xlet as cond. xret. xpull. intro Hcond.
  xif. { xret. hsimpl. }
       { xapp; try math. admit. xapp; try math. admit. }

  clean_max0. ring_simplify.
  rewrite max0_eq; swap 1 2. admit.
  ring_simplify. admit.

  admit.
  monotonic.
  admit.
Qed.

Lemma f_spec3 :
  specZ [cost \in_O (fun n => 2 ^ n)]
    (forall (n: int),
      0 <= n ->
      app f [n]
        PRE (\$ (cost n))
        POST (fun (tt:unit) => \[])).
Proof.
  pose_facts_evars facts a b.
  assert (0 <= a) as Ha by (prove_later facts).

  xspecO_cost (fun n => a * 2^n + b) on (fun n => 0 <= n).

  intros cost' E n N. rewrite E; [| solve [auto]]; clear E cost'. revert n N.

  intro n. induction_wf: (downto 0) n. intro N.
  refine_credits. xcf. xpay.

  xlet as cond. xret. xpull. intro Hcond.
  xif.
  { xret. hsimpl. }
  { xapp; try math. generalize n N; prove_later facts.
    xapp; try math. apply facts; eauto. }

  rewrite <-max0_max_0.
  clean_max0. ring_simplify.
  generalize n N. prove_later facts.

  prove_later facts.
  monotonic.
  admit.

  intros; close_facts.

  exists 2 (-1).
  splits; try math.
  - intros. ring_simplify. admit.
  - intros n N. ring_simplify.
    rewrite max0_eq; swap 1 2.
    { ring_simplify. admit. }
    ring_simplify. admit.
  - intros x X. ring_simplify. admit.
Qed.