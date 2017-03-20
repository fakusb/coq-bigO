Set Implicit Arguments.
Require Import TLC.LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
Require Pervasives_ml.
Require Array_ml.
Require Import Pervasives_proof.
Require Import Array_proof.
(* Load the BigO library. *)
Require Import Dominated.
Require Import BigEnough.
Require Import LibEvars.
Require Import EvarsFacts.
(* Load the examples CF definitions. *)
Require Import Max_subsequence_sum_ml.
Require Import Simple_ml.

Require Import CFMLBigO.

Lemma tick_spec :
  app tick [tt]
    PRE (\$1)
    POST (fun (tt:unit) => \[]).
Proof. xcf. xpay. xret. hsimpl. Qed.

Hint Extern 1 (RegisterSpec tick) => Provide tick_spec.

Lemma rand_spec :
  forall (n:Z),
  0 <= n ->
  app rand [n]
    PRE (\$1)
    POST (fun m => \[0 <= m <= n]).
Proof.
  intros n N.
  xcf. xpay. xret. hsimpl. math.
Qed.

Hint Extern 1 (RegisterSpec rand) => Provide rand_spec.

Lemma tick3_spec :
  specO
    unit_filterType
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  xspecO.
  xcf.
  xpay.
  xseq. xapp. hsimpl.
  xapp. hsimpl.
  xapp. hsimpl.

  cleanup_cost.
  apply dominated_cst. math.
Qed.

Lemma loop1_spec :
  specO
    Z_filterType
    (fun cost =>
       forall (n: Z),
       0 <= n ->
       app loop1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO.
  intros n N.
  xcf.
  xpay.
  xfor_ensure_evar_post ltac:(fun _ => idtac).
  eapply xfor_inv_lemma_pred_refine with (I := fun i => \[]).

  auto.
  { intros i Hi.
    xseq.
    xapp. hsimpl. xapp. hsimpl. }
  hsimpl.
  intro; xlocal.

  simpl.
(*
  rewrite cumulP. rewrite big_const_Z.
  match goal with |- _ <= ?rhs => set (toto := rhs) end. ring_simplify. subst toto. reflexivity.*)
  reflexivity.
  hsimpl.

  { cleanup_cost. }

  { apply dominated_sum_distr.
    { rewrite dominated_big_sum_bound.
      { eapply dominated_eq_l.
        eapply dominated_mul_cst_l.
        apply dominated_reflexive.
        eauto with zarith. }
      apply filter_universe_alt. math.
      apply filter_universe_alt. intros. (* monotonic_cst *) admit.
    }
    { admit. }
  }
Qed.

Lemma let1_spec :
  specO
    Z_filterType
    (fun cost =>
       forall n,
       0 <= n ->
       app let1 [n]
         PRE (\$ cost n)
         POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  destruct loop1_spec as [loop1_cost L LP LD].

  xspecO.
  intros n N.

  xcf.
  xpay.

  xlet.
  { xseq. xapp. hsimpl. xret. }
  { xpull. intro Hm. xapp. math.
    hsimpl. subst m. reflexivity. }

  cleanup_cost.
  { apply dominated_sum_distr.
    { apply dominated_transitive with (fun x => x + 1).
      - eapply dominated_comp_eq with
          (I := Z_filterType) (J := Z_filterType)
          (f := loop1_cost).
        apply LD. Focus 2. reflexivity.
        admit.
        simpl. reflexivity.
      - apply dominated_sum_distr.
        apply dominated_reflexive.
        admit. }
    admit. }
Qed.

Lemma loop2_spec :
  specO
    Z_filterType
    (fun cost =>
       forall n,
         0 <= n ->
         app loop2 [n]
             PRE (\$ cost n)
             POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO.
  intros n N.
  xcf.
  xpay.
  xlet. { xapp. auto. hsimpl. }
  xpull. intros Ha.
  apply refine_cost_setup_intro_emp.
  xlet. { xapp. math. hsimpl. }
  xpull. intros Hb.
  apply refine_cost_setup_intro_emp.
  xfor_ensure_evar_post ltac:(fun _ => idtac).
  eapply xfor_inv_lemma_pred_refine with (I := fun i => \[]).
  math.
  { intros i Hi. xapp. hsimpl. }
  hsimpl.
  intro; xlocal.
  simpl. rewrite cumulP. rewrite big_const_Z.

  hide_evars_then ltac:(fun _ => ring_simplify). (* xx *)

  (* goal a <= ?x. lemma H: forall x y, x <= y -> x <= y. apply (H e) ~> a <= e *)
  apply Hb. (* xx *)

  hsimpl.

  cleanup_cost.

  apply dominated_sum_distr.
  { apply dominated_reflexive. }
  { admit. }
Qed.
