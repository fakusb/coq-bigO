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
Require Import LibZExtra.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
Require Import Procrastination.Procrastination.
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

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

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
  { xapp~. hsimpl_credits. admit. admit.
    xapp~. hsimpl_credits. admit. admit. }

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
  { xapp~. xapp~. }

  clean_max0. ring_simplify. ring_simplify ((n-1)+1).
  case_if.
  { subst n. reflexivity. }
  { ring_simplify. rewrite~ <-pow2_succ. }

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
  begin procrastination assuming a b.
  assert (0 <= a) as Ha by procrastinate.

  sets cost: (fun (n:Z_filterType) => a * 2^n + b).
  asserts cost_nonneg: (forall n, 0 <= n -> 0 <= cost n).
  { intros. unfold cost. (* rewrite~ <-Z.pow_pos_nonneg. *) (* TODO *)
    asserts_rewrite <-(1 <= 2^n). { forwards~: Z.pow_pos_nonneg 2 n. }
    ring_simplify. procrastinate. }

  xspecO_cost cost on (fun n => 0 <= n).
  intro n. induction_wf: (downto 0) n. intro N.

  refine_credits. xcf. xpay. xrets.
  xif_guard.
  { xret. hsimpl. }
  { xapp~. xapp~. }

  clean_max0. ring_simplify.
  cases_if; ring_simplify.
  { subst n. subst cost. ring_simplify. procrastinate. }
  { rewrite~ max0_eq. unfold cost.
    transitivity (2 * 2 ^ (n-1) * a + 2 * b + 1). { ring_simplify. reflexivity. }
    rewrite~ <-pow2_succ. ring_simplify ((n-1)+1).
    math_rewrite (forall a b, (a <= b) <-> (a - b <= 0)). ring_simplify.
    procrastinate. }

  apply cost_nonneg.
  unfold cost. monotonic.
  unfold cost. dominated.

  end procrastination.

  simpl. exists~ 2 (-1).
Qed.

Ltac xspecO_evar_cost cost_name domain :=
  match goal with
  | |- specO ?A _ _ _ =>
    begin procrastination assuming cost_name;
    [ let Hnonneg := fresh "cost_nonneg" in
      assert (forall (x : A), domain x -> 0 <= cost_name x)
        as Hnonneg
        by (simpl; procrastinate);
      simpl in Hnonneg; (* [domain x] is likely a beta-redex *)
      xspecO_cost cost_name on domain;
      [ | apply Hnonneg | procrastinate | procrastinate ]
    | ..]
  end.

Lemma f_spec4 :
  specZ [cost \in_O (fun n => 2 ^ n)]
    (forall (n: int),
      0 <= n ->
      app f [n]
        PRE (\$ (cost n))
        POST (fun (tt:unit) => \[])).
Proof.
  xspecO_evar_cost costf (fun n => 0 <= n).
  intros n. induction_wf: (downto 0) n. intro N.
  refine_credits. xcf. xpay. xrets.
  xif_guard.
  { xret. hsimpl. }
  { xapp~. xapp~. }

  clean_max0. ring_simplify. generalize n N. procrastinate.
  end procrastination.

  begin procrastination assuming a b.
  assert (0 <= a) as Ha by procrastinate.
  sets cost: (fun (n:Z_filterType) => a * 2^n + b).
  assert (cost_nonneg: forall n, 0 <= n -> 0 <= cost n).
  { intros n N. unfold cost.
    asserts_rewrite <-(1 <= 2^n). { forwards~: Z.pow_pos_nonneg 2 n. }
    ring_simplify. procrastinate. }

  exists cost. splits~.
  { unfold cost. monotonic. }
  { unfold cost. dominated. }
  { intros n N. cases_if; ring_simplify.
    { subst n. unfold cost. ring_simplify. procrastinate. }
    { rewrite~ max0_eq. unfold cost.
      transitivity (2 * 2 ^ (n-1) * a + 2 * b + 1). { ring_simplify. reflexivity. }
      rewrite~ <-pow2_succ. ring_simplify ((n-1)+1).
      math_rewrite (forall a b, (a <= b) <-> (a - b <= 0)). ring_simplify.
      procrastinate. } }

  end procrastination.

  simpl. exists~ 2 (-1).
Qed.
