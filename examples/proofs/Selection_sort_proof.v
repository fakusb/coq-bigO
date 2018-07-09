Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibListSort.
Require Import TLC.LibListZ.
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
Require Import DominatedNary.
Require Import LimitNary.
Require Import Generic.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the CF definitions. *)
Require Import Selection_sort_ml.

Lemma swap_spec :
  specO unit_filterType eq
    (fun cost =>
      forall a (xs: list int) i j,
      index xs i -> index xs j ->
      app swap [a i j]
      PRE (\$ cost tt \* a ~> Array xs)
      POST (fun (_:unit) => a ~> Array (xs[i := xs[j]][j := xs[i]])))
    (fun (_:unit) => 1).
Proof.
  xspecO_refine straight_line. introv Ii Ij. xcf. xpay.
  xapps~. xapps~. xapp~. xapp~. apply~ index_update.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec swap) => Provide (provide_specO swap_spec).

Ltac auto_tilde ::= try solve [ eauto with maths | false; math ].

Lemma selection_sort_spec :
  specZ [cost \in_O (fun n => n ^ 2)]
    (forall a (xs : list int),
      app selection_sort [a]
      PRE (\$ cost (length xs) \* a ~> Array xs)
      POST (fun (_:unit) => Hexists (xs' : list int), a ~> Array xs')).
Proof.
  xspecO_refine straight_line. xcf. xpay.
  xapps~.
  assert (1 <= length xs) by admit. (* fix the for-loop reasoning rule *)
  weaken. xfor_inv (fun (_:int) =>
    Hexists (xs':list int), a ~> Array xs' \* \[ length xs = length xs']
  ).
  { math. }
  { intros i Hi. xpull. intros xs' L.
    xpay. xapp. xseq.
    { weaken. xfor_inv (fun (_:int) =>
        Hexists (xs'':list int) (k:int),
        a ~> Array xs'' \* p ~~> k \*
        \[index xs'' k /\ length xs = length xs'']).
      { math. }
      intros j Hj. xpull. intros xs'' k (Hk & L').
      xpay. xapps. xapps~. xapps~. apply~ int_index_prove.
      xif.
      { xapp. hsimpl. splits~. apply~ int_index_prove. }
      { xret. hsimpl. splits~. }
      hsimpl. splits~. apply~ int_index_prove.

      match goal with |- cumul _ _ (fun _ => ?X) <= _ => ring_simplify X end.
      asserts_rewrite (Z.max 0 0 = 0). reflexivity. (* FIXME? *)
      (* reflexivity. *)
      rewrite cumulP; rewrite big_const_Z.
        transitivity (3 * (length xs - i - 1)). math. reflexivity.
    }

    xpull. intros xs'' k (? & ?). xapps. xapps~. apply~ int_index_prove.
    hsimpl. rewrite !LibListZ.length_update; auto.
  }
  hsimpl~. hsimpl.

  sets len_xs: (length xs).
  assert (L: forall f g a b, f = g -> cumul a b f = cumul a b g) by admit.
  erewrite L; swap 1 2. extens. intro i.
  hide_evars_then ltac:(fun _ => ring_simplify).
  asserts_rewrite~ (3 * len_xs - 3 * i = 3 * (len_xs - i)).
  reflexivity.
  ring_simplify ((len_xs - 2) + 1). reflexivity.

  cleanup_cost.
  monotonic. admit. (* todo *)
  dominated.

  (* cumul a b (λi. f (b-i))
     = f(b-a) + f(b-(a+1)) + ... + f(b-(b-1))
     = f(b-a) + f(b-(a+1)) + ... + f(1)
     = cumul 1 (b-a-1) (λi. f i)
  *)
  assert (LL: forall a b f g,
             (forall i, g i = f (b - i)) ->
             cumul a b g = cumul 1 (b-a-1) f) by admit.
  apply dominated_eq_l with (fun (x:Z_filterType) => cumul 1 (x-2) (fun i => 3 * i + cost swap_spec tt + 1)); swap 1 2.
  { intro x.
    rewrite LL with (a := 0) (f := fun i => 3 * i + cost swap_spec tt + 1); auto.
    ring_simplify (((x-1) - 0) - 1). auto.
    intro. ring_simplify. reflexivity. (* fixme *)
  }

  etransitivity. eapply dominated_big_sum_bound'; swap 1 3.
  { apply_nary dominated_sum_distr_nary.
    apply_nary dominated_sum_distr_nary.
    dominated. apply dominated_reflexive.
    simpl. dominated.
    simpl. dominated. }

  { ultimately_greater. } { ultimately_greater. }
  { monotonic. intros ? ? H. destruct~ H. }
  { apply limit_sum_cst_r. limit. }
  { apply dominated_mul. dominated. dominated. }
Qed.