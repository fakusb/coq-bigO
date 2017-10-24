Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibListSorted.
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
Require Import Tmp.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
Require Import EvarsFacts.
(* Load the CF definitions. *)
Require Import Selection_sort_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

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
  xspecO. introv Ii Ij. xcf. xpay.
  xapps~. xapps~. xapp~. xapp~. apply~ index_update.
  cleanup_cost. monotonic. dominated.
Qed.

Hint Extern 1 (RegisterSpec swap) => Provide (provide_specO swap_spec).

Require Import TLC.LibListZ.

Lemma selection_sort_spec :
  specZ [cost \in_O (fun n => n ^ 2)]
    (forall a (xs : list int),
      app selection_sort [a]
      PRE (\$ cost (length xs) \* a ~> Array xs)
      POST (fun (_:unit) => Hexists (xs' : list int), a ~> Array xs')).
Proof.
  xspecO. xcf. xpay.
  xapps~.
  assert (1 <= length xs) by admit. (* fix the for-loop reasoning rule *)
  xfor_inv (fun (_:int) =>
    Hexists (xs':list int), a ~> Array xs' \* \[ length xs = length xs']
  ).
  { math. }
  { intros i Hi. xpull. intros xs' L.
    xapp. xseq.
    { xfor_inv (fun (_:int) =>
        Hexists (xs'':list int) (k:int),
        a ~> Array xs'' \* p ~~> k \*
        \[index xs'' k /\ length xs = length xs'']).
      { math. }
      intros j Hj. xpull. intros xs'' k (Hk & L').
      xapps. xapps~. xapps~. apply~ int_index_prove.
      xif.
      { xapp. hsimpl. splits~. apply~ int_index_prove. }
      { xret. hsimpl. splits~. }
      hsimpl. splits~. apply~ int_index_prove.

      clean_max0. match goal with |- cumul _ _ (fun _ => ?X) <= _ => ring_simplify X end.
      (* reflexivity. *)
      rewrite cumulP; rewrite big_const_Z.
        transitivity (2 * (length xs - i - 1)). math. reflexivity.
    }

    xpull. intros xs'' k (? & ?). xapps. xapps~. apply~ int_index_prove.
    hsimpl. rewrite !LibListZ.length_update; auto.
  }
  hsimpl~.

  clean_max0. sets len_xs: (length xs).
  assert (L: forall f g a b, f = g -> cumul a b f = cumul a b g) by admit.
  erewrite L; swap 1 2. extens. intro i. clean_max0.
  hide_evars_then ltac:(fun _ => ring_simplify).
  rewrite max0_eq; [| admit].
  asserts_rewrite~ ((len_xs - i) - 1 = (len_xs - 1) - i).
  reflexivity.
  ring_simplify ((len_xs - 2) + 1). reflexivity.
  hsimpl.

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
  apply dominated_eq_l with (fun (x:Z_filterType) => cumul 1 (x-2) (fun i => 2 * i + cost swap_spec tt)); swap 1 2.
  { intro x.
    rewrite LL with (a := 0) (f := fun i => 2 * i + cost swap_spec tt); auto.
    ring_simplify (((x-1) - 0) - 1). auto. }

  etransitivity. eapply dominated_big_sum_bound'.
  Focus 3. apply dominated_sum_distr_2. apply dominated_mul_cst_l_1_2.
  apply dominated_reflexive. simpl.
  apply dominated_cst_limit_2. limit.

  ultimately_greater. ultimately_greater.
  monotonic. intros ? ? H. destruct~ H.
  apply limit_sum_cst_r. limit.

  apply dominated_mul. dominated. dominated.
Qed.