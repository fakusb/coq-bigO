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
Require Import UltimatelyGreater.

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
    unit_filterType (fun _ _ => True)
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
  admit. (* monotonic *)
  apply dominated_cst. math.
Qed.

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
  xspecO.
  intros n N.
  xcf.
  xpay.

  xfor_inv (fun (i:int) => \[]). math.
  { intros i Hi.
    xseq.
    xapp. hsimpl. xapp. hsimpl. }
  hsimpl. hsimpl.

  { cleanup_cost. }

  { admit. (* monotonic *) }

  { apply dominated_sum_distr.
    { rewrite dominated_big_sum_bound.
      { eapply dominated_eq_l.
        eapply dominated_mul_cst_l.
        apply dominated_reflexive.
        eauto with zarith. }
      ultimately_greater.
      apply filter_universe_alt. intros. (* monotonic_cst *) admit.
    }
    { apply dominated_cst_id. }
  }
Qed.

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
  destruct loop1_spec as [loop1_cost L LP LM LD].

  xspecO.
  intros n N.

  xcf.
  xpay.

  xlet.
  { xseq. xapp. hsimpl. xret. }
  { xpull. intro Hm. xapp. math.
    hsimpl. subst m. reflexivity. }

  cleanup_cost.
  admit. (* monotonic *)
  { apply dominated_sum_distr.
    { apply dominated_transitive with (fun x => x + 1).
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

Lemma le_than (b: Z): forall a, a <= b -> a <= b.
Proof. auto with zarith. Qed.

Arguments le_than : clear implicits.

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
  xcf.
  xpay.
  xlet. { xapp. auto. hsimpl. }
  xpull. intros Ha.
  xlet. { xapp. math. hsimpl. }
  xpull. intros Hb.

  xfor_inv (fun (i:int) => \[]). math.
  { intros i Hi. xapp. hsimpl. }
  hsimpl.
  simpl. rewrite cumulP. rewrite big_const_Z.
  apply (le_than n).
  math.

  hsimpl.

  cleanup_cost.
  admit. (* monotonic *)

  apply dominated_sum_distr.
  { apply dominated_reflexive. }
  { apply dominated_cst_id. }
Qed.

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

  xspecO.
  intros n cond N.
  xcf. xpay.
  xapp. auto. hsimpl. intro Ha.
  xapp. auto. hsimpl. intro Hb.

  xif.
  xapp. math. hsimpl. apply (le_than (loop1_cost n)). apply LM. math.
  xapp. math. hsimpl. apply (le_than (loop1_cost n)). apply LM. math.

  cleanup_cost.
  admit. (* monotonic *)

  apply dominated_sum_distr.
  - apply~ dominated_max_distr.
  - apply dominated_cst_id.
Qed.

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

  xspecO.
  intros n N.
  xcf. xpay.
  xapp. auto. hsimpl.
  intro Ha.
  xapp. math. hsimpl. apply (le_than (loop1_cost n)). apply LM. math.

  cleanup_cost.
  admit. (* monotonic *)
  apply dominated_sum_distr.
  { apply LD. }
  { apply dominated_cst_id. }
Qed.

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


Ltac clean_ceil_math :=
  try cases_if; auto with zarith; try math_lia; math_nia.

(* Simple tactic to eliminate occurences of [ceil x] when x is proved
   nonnegative by [clean_ceil_math].
*)
Ltac clean_ceil :=
   repeat match goal with
   | |- context[ ceil ?x ] => rewrite (@ceil_eq x) by clean_ceil_math
   end.

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
  (* xspecO. intro n. *)
  induction_wf: (int_downto_wf 0) n.

  xcf. refine_credits.
  xpay. xif_guard. (* xif *) xret. hsimpl. (* xguard C *) xapp. math. hsimpl. math_lia.

  simpl. clean_ceil. cases_if; math_lia.

  math_lia.
  admit. (* monotonic *)

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
  (* xspecO. intro n. *)
  induction_wf: (int_downto_wf 0) n.

  xcf. refine_credits.
  xpay. xif. xret. hsimpl. xguard C. xapp. math. hsimpl. math_nia.

  clean_ceil. cases_if.
  (* Focus 2. rewrite !Z.max_l by math_lia. ring_simplify. *)
  { rewrite !Z.max_r by math_nia. ring_simplify.
    instantiate (1 := 1) in (Value of a).
    instantiate (1 := 1) in (Value of b).
    subst a b. math_nia. }
  { subst a b. math_nia. }

  math_nia.
  admit. (* monotonic *)

  subst a b. admit.

  subst a b. math.
Qed.
