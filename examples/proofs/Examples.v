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
Require Import BigEnough.
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
    unit_filterType (fun _ _ => True)
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  (* TODO: it would be nice if the type annotation for "_:unit_filterType"
     wasn't needed. If we unfold the definition of the tactic (which simply
     applies the [SpecO] lemma), it is not needed. Defining [xspecO] as a tactic
     or a tactic notation apparently makes it necessary. *)
  xspecO (fun (_:unit_filterType) => 4).

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
  { apply dominated_cst. math. }
Qed.

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
    unit_filterType (fun _ _ => True)
    (fun cost =>
       app tick3 [tt]
           PRE (\$ cost tt)
           POST (fun (tt:unit) => \[]))
    (fun tt => 1).
Proof.
  xspecO_refine.
  xcf.
  xpay.
  xseq. xapp.
  xapp. xapp.

  cleanup_cost.

  monotonic.
  apply dominated_cst. math.
Qed.

(* [loop1 n]: loops from 1 to n, calls [tick (); tick ()] at each iteration.

   The custom rule [xfor_inv] refines the cost function to a [cumul] of the cost
   of the loop's body.  *)
Lemma loop1_spec :
  specO
    Z_filterType Z.le
    (fun cost =>
       forall (n: Z),
       0 <= n ->
       app loop1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO_refine.
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

  { apply dominated_sum_distr.
    { rewrite dominated_big_sum_bound.
      { eapply dominated_eq_l.
        eapply dominated_mul_cst_l.
        apply dominated_reflexive.
        eauto with zarith. }
      ultimately_greater.
      apply filter_universe_alt. monotonic.
    }
    { apply dominated_cst_id. }
  }
Qed.

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
  (* At the moment, we have no tooling for automatically using
     specifications-with-bigO for auxiliary functions. As a workaround, we
     import the specs into the environment beforehand.
  *)
  destruct loop1_spec as [loop1_cost L LP LM LD].

  xspecO_refine.
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

  { apply dominated_sum_distr.
    { eapply dominated_transitive.
      - eapply dominated_comp_eq with
          (I := Z_filterType) (J := Z_filterType)
          (f := loop1_cost).
        apply LD. Focus 2. reflexivity.
        limit.
        simpl. reflexivity.
      - apply dominated_sum_distr.
        apply dominated_reflexive.
        apply dominated_cst_id. }
    apply dominated_cst_id. }
Qed.

(* In the previous example, we got away with using [reflexivity] to instantiate
the evar in [... <= ?Goal{x:=n}].

   In more general cases, we want to manually give an instantiation for the
evar. One way of doing that is by applying the following (trivial) lemma, giving
an instantiation for [b].
*)
Lemma le_than (b: Z): forall a, a <= b -> a <= b.
Proof. auto. Qed.

Arguments le_than : clear implicits.

(* [let2]: of the form [let m = ... in ...], where the cost of the body depends
on [m]. This time however, [m] is only related to [n] by an inequality (we know
[m <= n]). We cannot simply [subst] the definition of [m]. Instead we use
monotonicity of cost functions and [le_than].
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
  destruct loop1_spec as [loop1_cost L LP LM LD].

  xspecO_refine.
  intros n N.

  xcf.
  xpay.

  xlet.
  { xapp~. }
  { xpull. intro Hm. xapp. math.
    apply (le_than (loop1_cost n)). apply LM. math.
  }

  cleanup_cost.
  monotonic.

  apply dominated_sum_distr.
  { apply LD. }
  { apply dominated_cst_id. }
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
  xspecO_refine.
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

  apply dominated_sum_distr.
  { apply dominated_reflexive. }
  { apply dominated_cst_id. }
Qed.

(* [if1]: Similarly, a program of the form [if cond then ... else ...], where
the cost of branches can only be related to the input parameter by an
inequality.
*)
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
  destruct loop1_spec as [loop1_cost L LP LM LD].

  xspecO_refine.
  intros n cond N.
  xcf. xpay.
  xapp~. intro Ha.
  xapp~. intro Hb.

  xif.
  { xapp. math.
    (* Bound the cost of the branch by something that only depends on [n], using
    the fact that [loop1_cost] is monotonic. *)
    apply (le_than (loop1_cost n)). apply LM. math. }
  { xapp. math. apply (le_than (loop1_cost n)). apply LM. math. }

  cleanup_cost.
  monotonic.

  apply dominated_sum_distr.
  - apply~ dominated_max_distr.
  - apply dominated_cst_id.
Qed.


Lemma cutO_refine :
  forall (A : filterType) le (bound : A -> Z) (F: A -> hprop -> Prop) H (a: A),
  forall S : specO A le (fun mycost => forall a, F a (\$ ceil (mycost a) \* H)) bound,
  F a (\$ ceil ((cost S) a) \* H).
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
    forall i, a <= i < b -> F i (\$ ceil (mycost i) \* I i) (# I(i+1))) bound,
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (cumul a b (fun i => ceil (cost S i)) <= loop_cost) ->
  (For i = a To (b - 1) Do F i Done_) (\$ ceil loop_cost \* H) (# I b \* H').
Proof.
  admit.
Qed.

(*
Lemma looploop_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
       0 <= n ->
       app looploop [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  xspecO_refine.
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
Lemma dominated_ceil_product : forall A B f g,
  dominated (product_filterType A B) (fun '(a, b) => f a b) g ->
  dominated (product_filterType A B) (fun '(a, b) => ceil (f a b)) g.
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
  xspecO_refine.
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
    apply dominated_ceil.
    eapply dominated_sum. Focus 3. apply dominated_reflexive. ultimately_greater.
    Focus 2.
    apply dominated_ceil.
    apply dominated_big_sum' with (g := fun n i => n).
    Focus 3.
    (* apply dominated_ceil. *) (* ehhh *)
    apply dominated_ceil_product.

    Check cost_dominated.

    apply dominated_reflexive.

    ultimately_greater.
    apply filter_universe_alt. auto using cost_nonneg.
    intros. apply monotonic_after_of_monotonic. monotonic. applys cost_mon Z_filterType. (* xx *)
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


Lemma rec1_spec :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  apply SpecO with (cost := (fun (n:int) => Z.max 0 n + 1)).
  intro n.
  (* xspecO_refine. intro n. *)
  induction_wf: (downto 0) n.

  xcf. refine_credits.
  xpay.
  (* when the sub-cost functions for the branches of the if need to talk about of/depend on
  the condition... *)
  xif_guard. (* xif *) xret. hsimpl. (* xguard C *) xapp. math. math_lia.

  simpl. clean_ceil. cases_if; math_lia.

  math_lia.
  monotonic.

  apply dominated_sum_distr.
  { apply dominated_max_distr.
    apply dominated_cst_id.
    apply dominated_reflexive. }
  { apply dominated_cst_id. }
Qed.

Lemma rec1_spec2 :
  specO
    Z_filterType Z.le
    (fun cost => forall n,
         app rec1 [n]
           PRE (\$ cost n)
           POST (fun (tt:unit) => \[]))
    (fun n => n).
Proof.
  evar (a : int). evar (b : int).
  cut (0 <= a /\ 0 <= b). intros (a_nonneg & b_nonneg).
  apply SpecO with (cost := (fun (n:int) => a * Z.max 0 n + b)).
  intro n.
  (* xspecO_refine. intro n. *)
  induction_wf: (int_downto_wf 0) n.

  xcf. refine_credits.
  xpay. xif. xret. hsimpl. xguard C. xapp. math. math_nia.

  clean_ceil. cases_if.
  (* Focus 2. rewrite !Z.max_l by math_lia. ring_simplify. *)
  { rewrite !Z.max_r by math_nia. ring_simplify.
    instantiate (1 := 1) in (Value of a).
    instantiate (1 := 1) in (Value of b).
    subst a b. math_nia. }
  { subst a b. math_nia. }

  math_nia.
  monotonic.

  subst a b. admit.

  subst a b. math.
Qed.
