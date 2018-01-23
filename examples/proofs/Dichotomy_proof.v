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
Require Import Procrastination.Procrastination.
(* Load the CF definitions. *)
Require Import Dichotomy_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Lemma bsearch_spec :
  specZ [cost \in_O Z.log2]
    (forall t (xs : list int) (v : int) (i j : int),
        0 <= i <= length xs ->
        0 <= j <= length xs ->
        app bsearch [t v i j]
        PRE (\$ (cost (j - i)) \* t ~> Array xs)
        POST (fun (k:int) => t ~> Array xs)).
Proof.
  begin procrastination assuming a b.
  assert (0 <= a) as Ha by procrastinate.

  sets cost: (fun (n:Z_filterType) => If 0 < n then a * Z.log2 n + b else 1).
  asserts cost_nonneg: (forall x, 0 <= cost x).
  { intro x. subst cost; simpl. case_if~.
    rewrite <-Z.log2_nonneg. ring_simplify. procrastinate.
  }
  (* Could be generated automatically... *)
  asserts costPpos: (forall n, 0 < n -> cost n = a * Z.log2 n + b).
  { intro n. subst cost; simpl. case_if~. }
  asserts costPneg: (forall n, n <= 0 -> cost n = 1).
  { intro n. subst cost; simpl. case_if~. }

  asserts cost_monotonic: (monotonic Z.le Z.le cost).
  { intros x y H. subst cost; simpl.
    case_if; case_if~.
    { monotonic. }
    { rewrite <-Z.log2_nonneg. ring_simplify. procrastinate. } }


  { xspecO_cost cost.

    introv. gen_eq n: (j-i). gen i j. induction_wf IH: (downto 0) n.
    intros i j Hn Hi Hj.

    refine_credits. xcf. xpay.
    (* xif_ifcost / xif_maxcost / xif = celui qui sert le plus souvent *)
    xif_guard as C. { xret~. }
    (* rewrite nle_as_gt in C. *) asserts~ C' : (i < j). clear C.
    xret ;=> Hm. assert (Hmbound: i <= m < j) by admit.
    xapps. { apply~ int_index_prove. }
    xrets. xif. { xret~. }
    xapps. { apply~ int_index_prove. }
    xif.
    { weaken. xapp~ (m - i). subst m.
      (* tactique xcost? *)
      match goal with |- cost ?x <= _ => ring_simplify x end.
      reflexivity. }
    { (* forwards: IH __ (m+1) j. Focus 2. reflexivity. *)
      weaken. xapp~ (j - (m+1)). subst m. reflexivity. }

    clean_max0. cases_if; ring_simplify.
    { rewrite~ costPneg. }
    { rewrite Z.max_l; swap 1 2.
      { apply cost_monotonic. forwards~: Zquot_mul_2 (j-i). }
      tests Hn1: (j - i = 1).
      + rewrite Hn1. asserts_rewrite~ (1 `/` 2 = 0).
        rewrite~ (costPneg 0). rewrite~ (costPpos n).
        rewrite <-Z.log2_nonneg. ring_simplify. procrastinate.
      + rewrite costPpos; [| admit]. rewrite~ costPpos.
        rewrite <-Hn. rewrite~ <-(@Zlog2_step n).
        ring_simplify. cuts~: (3 <= a). procrastinate.
    }

    assumption. assumption.
    { unfold cost. rewrite dominated_ultimately_eq; swap 1 2.
      rewrite ZP. exists 1. intros. cases_if~. reflexivity.
      apply dominated_sum_distr; dominated. (* FIXME; dominated alone should work *)
    }
  }

  end procrastination.
  simpl. exists~ 3 4.
Qed.

(* TEMPORARY: this is slightly ad-hoc *)
Ltac xspecO_evar_cost cost_name :=
  match goal with
  | |- specO ?A _ _ _ =>
    begin procrastination assuming cost_name;
    [ let Hnonneg := fresh "cost_nonneg" in
      assert (forall (x : A), 0 <= cost_name x)
        as Hnonneg
        by procrastinate;
      xspecO_cost cost_name;
      [ | apply Hnonneg | procrastinate | procrastinate ]
    | ..]
  end.

Lemma bsearch_spec2 :
  specZ [cost \in_O Z.log2]
    (forall t (xs : list int) (v : int) (i j : int),
        0 <= i <= length xs ->
        0 <= j <= length xs ->
        app bsearch [t v i j]
        PRE (\$ (cost (j - i)) \* t ~> Array xs)
        POST (fun (k:int) => t ~> Array xs)).
Proof.
  xspecO_evar_cost costf.
  { introv. gen_eq n: (j-i). gen i j. induction_wf IH: (downto 0) n.
    intros i j Hn Hi Hj.

    refine_credits. xcf. xpay.
    (* xif_ifcost / xif_maxcost / xif = celui qui sert le plus souvent *)
    xif_guard as C. { xret~. }
    (* rewrite nle_as_gt in C. *) asserts~ C' : (i < j). clear C.
    xret ;=> Hm. assert (Hmbound: i <= m < j) by admit.
    xapps. { apply~ int_index_prove. }
    xrets. xif. { xret~. }
    xapps. { apply~ int_index_prove. }
    xif.
    { weaken. xapp~ (m - i). subst m.
      (* tactique xcost? *)
      match goal with |- costf ?x <= _ => ring_simplify x end.
      reflexivity. }
    { (* forwards: IH __ (m+1) j. Focus 2. reflexivity. *)
      weaken. xapp~ (j - (m+1)). subst m. reflexivity. }

    clean_max0. cases_if; ring_simplify.
    { assert (HH: n <= 0) by math. generalize n HH. procrastinate. }
    { rewrite Z.max_l; swap 1 2.
      { already procrastinated. (* monotonicity *)
        forwards~: Zquot_mul_2 (j-i). }
      tests Hn1: (j-i = 1).
      + rewrite Hn1. asserts_rewrite~ (1 `/` 2 = 0).
        asserts_rewrite~ (n = 1). procrastinate.
      + assert (HH: 2 <= n) by math. rewrite <-Hn.
        generalize n HH. procrastinate. }
  }

  end procrastination.

  begin procrastination assuming a b.
  assert (0 <= a) as Ha by procrastinate.
  exists (fun (n:Z_filterType) => If 0 < n then a * Z.log2 n + b else 1). splits.
  { intros. cases_if~. rewrite <-Z.log2_nonneg. ring_simplify.
    procrastinate. }
  { intros x y H. cases_if; case_if~.
    { monotonic. }
    { rewrite <-Z.log2_nonneg. ring_simplify. procrastinate. } }
  { rewrite dominated_ultimately_eq; swap 1 2.
      rewrite ZP. exists 1. intros. cases_if~. reflexivity.
      apply dominated_sum_distr; dominated.
      (* FIXME; dominated alone should work *)
  }
  { intros. cases_if~. }
  { cases_if~. cases_if~. simpl. ring_simplify. procrastinate. }
  { intros n N. cases_if~; [| exfalso; admit]. cases_if~.
    rewrite~ <-(@Zlog2_step n). ring_simplify.
    cuts~: (3 <= a). procrastinate. }

  end procrastination.
  simpl. exists~ 3 4.
Qed.
