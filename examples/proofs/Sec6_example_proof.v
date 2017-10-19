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
Require Import EvarsFacts.
(* Load the CF definitions. *)
Require Import Sec6_example_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Parameter g1_spec :
  specO unit_filterType eq
    (fun cost => app g1 [tt] PRE (\$ cost tt) POST (fun (_:unit) => \[]))
    (fun (_:unit) => 1).

Hint Extern 1 (RegisterSpec g1) => Provide (provide_specO g1_spec).

Parameter g2_spec :
  specO unit_filterType eq
    (fun cost => app g2 [tt] PRE (\$ cost tt) POST (fun (_:unit) => \[]))
    (fun (_:unit) => 1).

Hint Extern 1 (RegisterSpec g2) => Provide (provide_specO g2_spec).

Ltac xspecO_evar_cost facts cost_name domain :=
  match goal with
  | |- specO ?A _ _ _ =>
    pose_facts_evars facts cost_name;
    [ let Hnonneg := fresh "cost_nonneg" in
      assert (forall (x : A), domain x -> 0 <= cost_name x)
        as Hnonneg
        by (simpl; prove_later facts);
      simpl in Hnonneg; (* [domain x] is likely a beta-redex *)
      xspecO_cost cost_name on domain;
      [ | apply Hnonneg | prove_later facts | prove_later facts ]
    | ..]
  end.

Lemma f_spec :
  specZ [cost \in_O (fun n => n)]
    (forall (n: Z),
       0 <= n ->
       app f [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[])).
Proof.
  xspecO_evar_cost facts costf (fun x => 0 <= x).

  intros n. induction_wf: (downto 1) n. intro N.
  xcf. refine_credits. xpay.
  xif_guard.
  { xret~. }
  { xapp. xapp. xapp~. }

  { clean_max0. generalize n N. prove_later facts. }
  intros; close_facts.

  pose_facts_evars facts a b.
  assert (A: 0 <= a) by (prove_later facts).
  exists (fun (n:Z_filterType) => a * n + b). splits.

  { intro. cut (0 <= b). math_nia. prove_later facts. }
  { monotonic. }
  { dominated. }
  { intros n N. cases_if; ring_simplify.
    - cut (1 <= b). math_nia. prove_later facts.
    - rewrite max0_eq by math_nia.
      ring_simplify.

      cut (cost g1_spec tt + cost g2_spec tt + 1 <= a). admit.
      prove_later facts. }

  intros; close_facts.
  simpl. exists (cost g1_spec tt + cost g2_spec tt + 1) 1.
  splits; auto with zarith.
Qed.
