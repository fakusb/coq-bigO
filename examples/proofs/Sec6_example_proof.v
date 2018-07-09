Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibIntTactics.
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
Require Import Procrastination.Procrastination.
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

Lemma f_spec :
  specZ [cost \in_O (fun n => n)]
    (forall (n: Z),
       0 <= n ->
       app f [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[])).
Proof.
  xspecO_refine recursive. intros costf ? ? ? n.

  induction_wf: (downto 1) n. intro N.
  xcf. weaken. xpay.
  xif_guard.
  { xret~. }
  { xapp. xapp. xapp~. }

  { generalize n N. defer. }
  close cost.

  begin defer assuming a b.
  defer A: (0 <= a).
  exists (fun (n:Z_filterType) => a * n + b). split.
  { intros n N. cases_if; ring_simplify.
    - cut (1 <= b). math_nia. defer.
    - ring_simplify.
      cut (cost g1_spec tt + cost g2_spec tt + 1 <= a). admit.
      defer. }

  cleanup_cost.
  { monotonic. }
  { dominated. }

  end defer.
  simpl. exists (cost g1_spec tt + cost g2_spec tt + 1) 1.
  splits; auto with zarith.
Qed.
