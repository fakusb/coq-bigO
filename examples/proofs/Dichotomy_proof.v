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

Ltac ring_simplify' :=
  hide_evars_then ltac:(fun tt => ring_simplify).

Lemma bsearch_spec :
  specZ [cost \in_O (fun n => Z.log2 n)]
    (forall t (xs : list int) (v : int) (i j : int),
        0 <= i < length xs ->
        0 <= j <= length xs ->
        app bsearch [t v i j]
        PRE (\$ (cost (j - i)) \* t ~> Array xs)
        POST (fun (k:int) => t ~> Array xs)).
Proof.
  pose_facts_evars facts a b.
  assert (0 <= a) as Ha by (prove_later facts).

  sets cost: (fun (n:Z_filterType) => If 0 < n then a * Z.log2 n + b else 1).
  asserts cost_nonneg: (forall x, 0 <= cost x).
  { intro x. subst cost; simpl. case_if; [| math].
    rewrite <-Z.log2_nonneg. ring_simplify. prove_later facts.
  }
  asserts costPpos: (forall n, 0 < n -> cost n = a * Z.log2 n + b).
  { intro n. subst cost; simpl. case_if; math. }
  asserts costPneg: (forall n, n <= 0 -> cost n = 1).
  { intro n. subst cost; simpl. case_if; math. }

  asserts cost_monotonic: (monotonic Z.le Z.le cost).
  { intros x y H. subst cost; simpl.
    case_if. { case_if; [| exfalso; math]. monotonic. }
             { case_if; [| math]. rewrite <-Z.log2_nonneg.
               ring_simplify. prove_later facts. } }

  xspecO_cost cost.

  introv. gen_eq n: (j-i). gen i j. induction_wf IH: (downto 0) n.
  intros i j Hn Hi Hj.

  refine_credits. xcf. xpay.
  xif_guard as C. { xret~. }
  assert (C' : i < j) by math. clear C.
  xrets. xapps. { apply int_index_prove. admit. admit. }
  xrets. xif. { xret~. }
  xapps. { apply int_index_prove. admit. admit. }
  xif.
  { xapp; swap 1 2.
    - ring_simplify'. reflexivity.
    - admit.
    - math.
    - admit. }
  { xapp; swap 1 2.
    - transitivity ((j - i) - (j - i `/` 2) - 1); [| math].
      reflexivity.
    - admit.
    - admit.
    - math. }

  clean_max0. cases_if; ring_simplify.
  { rewrite costPneg; math. }
  { assert (C' : i < j) by math. clear C.
    rewrite Z.max_l; swap 1 2.
    { apply cost_monotonic. sets half: (j - i `/` 2).
      case_if_on (Z.odd (j - i)) as Hsplit.
      - (* both partitions are of equal size *)
        apply Z.eq_le_incl.
        rewrite Zodd_quot2 with (n := (j - i)); try math. ring_simplify.
        subst half. rewrite <-Zquot2_quot. math.
        apply~ Zodd_bool_iff.
      - (* the first partition is bigger (by one) *)
        rewrite Zeven_quot2 with (n := (j - i)).
        subst half. rewrite <-Zquot2_quot. math.
        apply Zeven_bool_iff. rewrite Zeven.Zeven_odd_bool.
        rewrite Hsplit. reflexivity.
    }
    cases_if_on (isTrue ((j - i) = 1)) as Hn1.
    + rewrite Hn1. assert (H: 1 `/` 2 = 0) by (compute; reflexivity). rewrite H.
      rewrite costPneg with 0 by math. rewrite costPpos with n by math.
      ring_simplify. assert (Hn': 1 <= n) by math.
      rewrite <-Z.log2_nonneg. ring_simplify. prove_later facts.
    + rewrite costPpos; [| admit]. rewrite costPpos by math.
      assert (H: Z.log2 (j - i `/` 2) = Z.log2 n - 1) by admit. rewrite H.
      ring_simplify. cut (1 <= a). math. prove_later facts.
  }

  assumption. assumption.
  { unfold cost. rewrite dominated_ultimately_eq; swap 1 2.
    rewrite ZP. exists 1. intros. cases_if; [| exfalso; math]. reflexivity.
    apply dominated_sum_distr; dominated. (* FIXME; dominated alone should work *) }

  intros; close_facts.

  simpl. exists 1 2; math.
Qed.
