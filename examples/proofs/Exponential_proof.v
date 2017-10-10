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

(* This is kind of ad-hoc... *)
Lemma pow2_sub_1_nonneg :
  forall x,
  0 <= x ->
  0 <= 2^x - 1.
Proof.
  intros. apply Z.le_add_le_sub_r.
  auto with zarith.
Qed.

Hint Resolve pow2_sub_1_nonneg : zarith.

Lemma f_spec :
  specZ [cost \in_O (fun n => 2 ^ n)]
    (forall (n: int),
      0 <= n ->
      app f [n]
        PRE (\$ (cost n))
        POST (fun (tt:unit) => \[])).
Proof.
  xspecO_cost (fun n => 2^(n+1) - 1) on (fun n => 0 <= n).
  intro n. induction_wf: (downto 0) n. intro N.

  xcf. xpay. hsimpl_credits.
  (* math_debug. auto with zarith. *) (* XXX *) admit. math.
  xrets. xif.
  { xret~. }
  { xapp; try math. hsimpl_credits. admit. admit.
    xapp; try math. hsimpl_credits. admit. admit. }

  admit.
  monotonic.
  dominated.
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
  intro n. induction_wf: (downto 0) n. intro N.

  refine_credits. xcf. xpay.
  (* Using xrets here results in a loss of information in the infered cost
  function; as the xret in the first subcase records "n" as the cost instead of
  "0"... *)
  (* xret. intro H. xif. *)
  (* Unless one uses xif_guard/guard in the first case... *)
  xrets. xif_guard.
  { xret~. }
  { xapp; try math. xapp; try math. }

  clean_max0. ring_simplify. ring_simplify ((n-1)+1).
  case_if.
  { subst n. reflexivity. }
  { ring_simplify. rewrite <-pow2_succ. math. math. }

  (* ultimately_greater. *) auto with zarith.
  monotonic.
  dominated.
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
  intro n. induction_wf: (downto 0) n. intro N.

  refine_credits. xcf. xpay. xrets.
  xif_guard.
  { xret. hsimpl. }
  { xapp; try math. generalize n N C; prove_later facts.
    xapp; try math. apply facts; eauto. }

  clean_max0. ring_simplify.
  cases_if.
  { subst n. ring_simplify. prove_later facts. }
  { ring_simplify. rewrite max0_eq; [| apply~ facts].
    cut (2 * b + 1 <= b). admit. prove_later facts. }

  prove_later facts.
  monotonic.
  dominated.

  intros; close_facts.

  exists 2 (-1).
  splits; try math.
  - intros. ring_simplify. rewrite <-pow2_succ. auto with zarith. math.
  - intros. ring_simplify. rewrite <-pow2_succ. auto with zarith. math.
Qed.
