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
(* Load the examples CF definitions. *)
Require Import Simple_ml.

(* Prove specifications for auxiliary functions [tick] and [rand].

   - [tick ()] just does one step of computation and consumes one credit

   - [rand n] returns an integer between 0 and n.

     It is used to account for the case where a function specification only
     relates the arguments and the result value with an inequality.
*)

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


(* [tick3 ()]: calls [tick ()] three times.

   First, prove a big-O specification by providing the exact cost function
   upfront (here, λ(). 4).

   The specification is stated using [specO], which takes several arguments:

   - a filter; here [unit_filterType] as [tick3] is "O(1)"
   - a (pre-order) relation on the domain (the cost function must be monotonic
     wrt this relation)
   - the specification, as a function [abstract cost function -> Prop]
   - the big-O bound for the cost function
*)
Lemma tick3_spec :
  specO
    unit_filterType eq
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  xspecO_cost (fun _ => 4).

  { xcf.
    xpay.
    (* after a [pay] or a [xapp], one needs to justify that one has enough
       credits in the precondition to pay for the operation. *)
    hsimpl_credits; math.
    xseq.
    xapp. hsimpl_credits; math.
    xapp. hsimpl_credits; math.
    xapp. hsimpl_credits; math. }

  (* Justify that the cost function is nonnegative, monotonic and dominated by
     the bound given in the specification ([fun tt => 1]). *)
  { math. }
  { monotonic. }
  { dominated. }
Qed.

Hint Extern 1 (RegisterSpec tick3) => Provide (provide_specO tick3_spec).

(* [tick3 ()]: prove the same specification, this time using the mechanism to
   refine cost functions semi-automatically.

   In simple cases like this one, [cleanup_cost] is able to completely clean up
   the refined cost function. [monotonic] is also able to automatically prove
   monotonicity of the refined cost function *before* cleanup.

   The monotonicity goal is (at the moment) about the "uncleaned" cost function,
   because the "cleaning" process produces a cost function that is not equal to the
   uncleaned one, and only dominates it.
*)
Lemma tick3_spec2 :
  specO
    unit_filterType eq
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  xspecO.
  xcf.
  xpay.
  xseq. xapp.
  xapp. xapp.

  cleanup_cost.

  monotonic.
  dominated.
Qed.

(* [tick31]: Using a big-O spec for an auxiliary function. *)
Lemma tick31_spec :
  specO
    unit_filterType eq
    (fun cost =>
       app tick31 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun _ => 1).
Proof.
  xspecO.
  xcf. xpay.
  xapp. (* usual spec *)
  xapp. (* big-O spec *)

  cleanup_cost.
  monotonic.

  dominated.
Qed.

(* [loop1 n]: loops from 1 to n, calls [tick (); tick ()] at each iteration.

   The custom rule [xfor_inv] refines the cost function to a [cumul] of the cost
   of the loop's body.

   Also, demo of a convenince wrapper notation for [specO] on [Z_filterType].
*)
Lemma loop1_spec :
  specZ [cost \in_O (fun n => n)]
    (forall (n: Z),
       0 <= n ->
       app loop1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[])).
Proof.
  xspecO.
  intros n N.
  xcf.
  xpay.

  xfor_inv (fun (i:int) => \[]). math.
  { intros i Hi.
    xseq.
    xapp. xapp. }
  hsimpl. hsimpl.

  { cleanup_cost. }

  { monotonic. }

  { dominated.
    rewrite dominated_big_sum_bound.
    { eapply dominated_eq_l.
      eapply dominated_mul_cst_l.
      apply dominated_reflexive.
      eauto with zarith. }
    ultimately_greater.
    apply filter_universe_alt. monotonic.
  }
Qed.

Hint Extern 1 (RegisterSpec loop1) => Provide (provide_specO loop1_spec).

(* [let1]: a program of the form [let m = ... in ...] where the cost of the body
   of the [let] depends on [m].

   As [m] is a locally-bound variable, one needs to come up with a cost for the
   body that is independent from [m]. In this simple example, it suffices to
   inline the definition of [m]. *)
Lemma let1_spec :
  specO
    Z_filterType Z.le
    (fun cost =>
       forall n,
       0 <= n ->
       app let1 [n]
         PRE (\$ cost n)
         POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO.
  intros n N.

  xcf.
  xpay.

  xlet.
  { xseq. xapp. xret. }
  { xpull. intro Hm. xapp. math.
    (* This sub-goal is produced by our custom [xlet], and requires the user to
    come up with a cost-function (hence the meta-variable) which only depends on
    [n]. *)
    (* Here, it suffices to inline the definition of [m]. *)
    subst m.
    (* [reflexivity] then unifies both sides, instantiating the meta-variable
    and solving the goal. *)
    reflexivity. }

  cleanup_cost.
  monotonic.
  dominated.
Qed.

(* In the previous example, we got away with using [reflexivity] to instantiate
   the evar in [... <= ?Goal{x:=n}].

   In more general cases, we want to manually give an instantiation for the
   evar. One way of doing that is by applying the following (trivial) lemma,
   giving an instantiation for [b]. *)
Lemma le_than (b: Z): forall a, a <= b -> a <= b.
Proof. auto. Qed.

Arguments le_than : clear implicits.

(* [let2]: of the form [let m = ... in ...], where the cost of the body depends
   on [m].

   This time however, [m] is only related to [n] by an inequality (we
   know [m <= n]). We cannot simply [subst] the definition of [m]. Instead we
   use monotonicity of cost functions and [le_than].
*)
Lemma let2_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         0 <= n ->
         app let2 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO.
  intros n N.

  xcf.
  xpay.

  xlet.
  { xapp~. }
  { xpull. intro Hm. xapp. math.
    apply (le_than (cost loop1_spec n)). apply cost_monotonic. math.
  }

  cleanup_cost.
  monotonic.
  dominated.
Qed.


(* [loop2]: Similarly, we can have a for-loop where the value of the starting
   and finishing indices is not precisely known, but one can bound their
   difference. *)
Lemma loop2_spec :
  specO
    Z_filterType Z.le
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

  xcf. xpay.

  xlet. { xapp~. }
  xpull. intros Ha.
  xlet. { xapp~. }
  xpull. intros Hb.

  xfor_inv (fun (i:int) => \[]). math.
  { intros i Hi. xapp. }
  { hsimpl. }
  { simpl.
    (* At this point, we can simply reduce [cumul] of a constant to a product.
    *)
    rewrite cumulP. rewrite big_const_Z.
    (* Do some cleanup, and work around the fact that [ring_simplify] chokes on
    evars... *)
    hide_evars_then ltac:(fun _ => ring_simplify).
    apply (le_than n).
    math. }

  hsimpl.

  cleanup_cost.

  monotonic.
  dominated.
Qed.

(* [if1]: Similarly, a program of the form [if cond then ... else ...], where
   the cost of branches can only be related to the input parameter by an
   inequality. *)
Lemma if1_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n (cond: bool),
         0 <= n ->
         app if1 [n cond]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO.
  intros n cond N.
  xcf. xpay.
  xapp~. intro Ha.
  xapp~. intro Hb.

  xif.
  { xapp. math.
    (* Bound the cost of the branch by something that only depends on [n], using
    the fact that [loop1_cost] is monotonic. *)
    apply (le_than (cost loop1_spec n)). apply cost_monotonic. math. }
  { xapp. math. apply (le_than (cost loop1_spec n)). apply cost_monotonic. math. }

  cleanup_cost.
  monotonic.
  dominated.
Qed.

(* [looploop]: nested for-loops *)
Lemma looploop_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
       0 <= n ->
       app looploop [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n ^ 2).
Proof.
  xspecO.
  intros n N.
  xcf. xpay.

  xfor_inv (fun (i:int) => \[]). auto.
  { intros i I.
    xfor_inv (fun (j:int) => \[]). math.
    { intros j J. xapp. }
    { hsimpl. }
    { simpl.
      (* reflexivity. *) (* fixme? *)
      apply Z.le_refl. }
    { hsimpl. }
  }
  { hsimpl. }
  { hsimpl. }

  cleanup_cost.
  monotonic.

  dominated.
  { rewrite dominated_big_sum_bound.
    { apply dominated_mul. reflexivity.
      rewrite dominated_big_sum_bound. reflexivity.
      ultimately_greater.
      (* todo: improve *)
      eapply ultimately_monotonic_of_monotonic.
      monotonic. }
    ultimately_greater.
    (* todo: improve *)
    eapply ultimately_monotonic_of_monotonic.
    monotonic.
  }
Qed.

(**
   WIP: attempts at abstracting the big-O cost of the inner loop, in the middle
   of the proof.
 *)

Lemma cutO_refine :
  forall (A : filterType) le (bound : A -> Z) (F: A -> hprop -> Prop) H (a: A),
  forall S : specO A le (fun mycost => forall a, F a (\$ max0 (mycost a) \* H)) bound,
  F a (\$ max0 ((cost S) a) \* H).
Proof.
  admit.
Qed.

Lemma xfor_inv_lemma_pred_refine :
  forall
    (I : int -> hprop) (loop_cost : int)
    (bound : int -> int)
    (a : int) (b : int) (F : int-> ~~unit) H H',
  (a <= b) ->
  forall S :
  specO Z_filterType Z.le (fun mycost =>
    forall i, a <= i < b -> F i (\$ max0 (mycost i) \* I i) (# I(i+1))) bound,
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (cumul a b (fun i => max0 (cost S i)) <= loop_cost) ->
  (For i = a To (b - 1) Do F i Done_) (\$ max0 loop_cost \* H) (# I b \* H').
Proof.
  admit.
Qed.

(*
Lemma looploop_spec' :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
       0 <= n ->
       app looploop [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n ^ 2).
Proof.
  xspecO.
  intros n N.
  xcf. xpay.

  xfor_inv (fun (i:int) => \[]).
  math. intros i Hi.
  Set Printing Existential Instances.


  unshelve eapply cutO_refine with (A := Z_filterType) (a := i) (le := Z.le)
  (bound := fun (i:int) => n). simpl.

  admit. hsimpl. hsimpl.
  cleanup_cost.
  admit.
*)

(* XXX *)
Lemma dominated_max0_product : forall A B f g,
  dominated (product_filterType A B) (fun '(a, b) => f a b) g ->
  dominated (product_filterType A B) (fun '(a, b) => max0 (f a b)) g.
Proof. admit. Qed.

(*
Lemma looploop_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
       0 <= n ->
       app looploop [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n ^ 2).
Proof.
  xspecO.
  intros n N.
  xcf. xpay.

  xfor_pre_ensure_evar_post ltac:(fun _ => idtac).
  unshelve eapply xfor_inv_lemma_pred_refine
  with (bound := fun _ => n)
       (I := fun i => \[]).
  shelve.
  - admit.
  - auto.
  - hsimpl.
  - intro. xlocal.
  - reflexivity.
  - hsimpl.
  - subst cost.
    unfold cleanup_cost.
    apply dominated_max0.
    eapply dominated_sum. Focus 3. apply dominated_reflexive. ultimately_greater.
    Focus 2.
    apply dominated_max0.
    apply dominated_big_sum' with (g := fun n i => n).
    Focus 3.
    (* apply dominated_max0. *) (* ehhh *)
    apply dominated_max0_product.

    Check cost_dominated.

    apply dominated_reflexive.

    ultimately_greater.
    apply filter_universe_alt. auto using cost_nonneg.
    intros. apply monotonic_after_of_monotonic. monotonic. applys cost_monotonic Z_filterType. (* xx *)
    limit.

    simpl.
    apply ultimately_ge_0_cumul_nonneg_Z. auto using cost_nonneg.

  - admit.
  - simpl.
    apply dominated_sum_distr. apply dominated_cst_id.
    eapply dominated_transitive.
    { apply dominated_big_sum'.
      { apply filter_universe_alt. auto using cost_nonneg. }
      Focus 2.
      {
*)

(**
   WIP: attempts at semi-manually handling recursive functions.
*)

(* zify fails to process e.g. Z.max 0 0; as a workaround, add a [unmaxify]
   that postprocess those.

   See https://coq.inria.fr/bugs/show_bug.cgi?id=5439
*)

Ltac unmaxify_core a b :=
  pose proof (Z.max_spec a b);
  let z := fresh "z" in
  set (z := Z.max a b) in *;
  clearbody z.

Ltac unmaxify_step :=
  match goal with
  | |- context [ Z.max ?a ?b ] => unmaxify_core a b
  | H : context [ Z.max ?a ?b ] |- _ => unmaxify_core a b
  end.

Ltac unmaxify := repeat unmaxify_step.
Ltac zify_op ::= repeat zify_op_1; unmaxify.

(* FIXME *)
Ltac clean_max0_math ::=
  try cases_if; auto with zarith; try math_lia; math_nia.

(* NB: Adding the precondition [0 <= n] to the specification doesn't help
   simplifying the cost functions and getting rid of the Z.max. Indeed, [specO]
   requires that the provided cost function is always nonnegative — which is not
   the case of e.g. [fun n => n + 1].
*)
Lemma rec1_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO_cost (fun n => Z.max 0 n + 1).
  intro n.
  induction_wf: (downto 0) n.

  xcf. refine_credits.
  xpay.
  (* when the sub-cost functions for the branches of the if need to talk about of/depend on
  the condition... *)
  xif_guard. (* xif *) xret. hsimpl. (* xguard C *) xapp. math.

  clean_max0. cases_if; math_lia.

  math_lia.
  monotonic.
  dominated.
Qed.

Require Import EvarsFacts.

Lemma rec1_spec2 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  pose_facts facts.

  evar (a : int). evar (b : int).
  assert (a_nonneg : 0 <= a) by (prove_later facts).
  assert (b_nonneg : 0 <= b) by (prove_later facts).

  xspecO_cost (fun n => a * Z.max 0 n + b).
  intro n.
  induction_wf: (int_downto_wf 0) n.

  xcf. refine_credits.
  xpay. xif. xret. hsimpl. xguard C. xapp. math.

  clean_max0. cases_if.
  { generalize n C. prove_later facts. }
  { generalize n C. prove_later facts. }

  math_nia.
  monotonic.
  dominated.
  close_facts.

  (* XX *)
Abort.

Lemma rec1_spec3 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  pose_facts_evars facts a b.

  assert (a_nonneg : 0 <= a) by (prove_later facts).
  assert (b_nonneg : 0 <= b) by (prove_later facts).

  xspecO_cost (fun n => a * Z.max 0 n + b).
  intro n.
  induction_wf: (int_downto_wf 0) n.

  xcf. refine_credits.
  xpay. xif. xret. hsimpl. xguard C. xapp. math.

  clean_max0. cases_if.
  { generalize n C. prove_later facts. }
  { generalize n C. prove_later facts. }

  math_nia.
  monotonic.
  dominated.
  intros. close_facts.

  simpl. exists 1 1. splits; math_nia.
Qed.

Lemma rec1_spec4 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         0 <= n ->
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  pose_facts_evars facts a b.

  assert (a_nonneg : 0 <= a) by (prove_later facts).
  assert (b_nonneg : 0 <= b) by (prove_later facts).

  xspecO_cost (fun n => Z.max 0 (a * n + b)).
  intros n.
  induction_wf: (int_downto_wf 0) n. intro N.

  xcf. refine_credits.
  xpay. xif. xret. hsimpl. xguard C. xapp. math. math.

  clean_max0. cases_if.
  { generalize n N C. prove_later facts. }
  { generalize n N C. prove_later facts. }

  math_nia.
  monotonic.
  dominated.
  intros. close_facts.

  simpl. exists 1 1. splits.
  math. math. math_nia. math_nia.
Qed.

Lemma rec1_spec5 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         0 <= n ->
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  pose_facts_evars facts a b.

  assert (a_nonneg : 0 <= a) by (prove_later facts).
  assert (b_nonneg : 0 <= b) by (prove_later facts).

  xspecO_cost (fun n => a * n + b) on (fun n => 0 <= n).
  intro n. induction_wf: (int_downto_wf 0) n. intro N.

  xcf. refine_credits.
  xpay. xif. xret. hsimpl. xguard C. xapp. math. math.

  clean_max0. cases_if.
  { generalize n N C. prove_later facts. }
  { generalize n N C. prove_later facts. }

  math_nia.
  monotonic.
  dominated.
  intros. close_facts.

  simpl. exists 1 1. splits.
  math. math. math_nia. math_nia.
Qed.
