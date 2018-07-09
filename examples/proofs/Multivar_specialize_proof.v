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
Require Import DominatedNary.
Require Import LimitNary.
Require Import Generic.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the CF definitions. *)
Require Import Multivar_specialize_ml.

Close Scope Int_scope.
Bind Scope Z_scope with Z.
Open Scope Z_scope.
Undelimit Scope Int_scope.

Notation "'int'" := Z.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

(*----------------------------------------------------------------------------*)

(* Symmetric product "everywhere x order". Does not work: see proofs below *)
Notation product_everywhere_order :=
  (product_filterType (everywhere_filterType Z) Z_filterType) (only parsing).

Lemma not_product_everywhere_order_limit :
  limit product_everywhere_order Z_filterType
    (fun '(m,n) => n * m + n) ->
  False.
Proof.
  intro L. rewrite limitP in L. simpl in L.
  specializes L (fun x => 1 <= x) ultimately_ge_Z.
  rewrite productP in L. destruct L as (P1 & P2 & UP1 & UP2 & H). simpl in *.
  rewrite (@ZP_ultimately (fun x => 1 <= x)) in UP2 by (apply ultimately_ge_Z).
  destruct UP2 as (n0 & H21 & H22).
  rewrite everywhereP in UP1.
  specializes H (-2) n0 UP1 H22.
Qed.

Lemma not_product_everywhere_order_domin_cst :
  dominated product_everywhere_order
    (fun '(_,_) => 1) (fun '(m,n) => n * m + n) ->
  False.
Proof.
  intro D. destruct D as (c & U).
  rewrite productP in U. destruct U as (P1 & P2 & UP1 & UP2 & H). simpl in *.
  rewrite (@ZP_ultimately (fun x => 1 <= x)) in UP2 by (apply ultimately_ge_Z).
  destruct UP2 as (n0 & H21 & H22).
  rewrite everywhereP in UP1.
  specializes H (-1) n0 UP1 H22.
  rewrite~ Z.abs_eq in H. rewrite~ Z.abs_eq in H. ring_simplify in H.
  math.
Qed.

(*----------------------------------------------------------------------------*)

(* Asymmetric product "everywhere x order". Better, but still does not work.
   dominated 1 (m * n + n)  does not hold since one could chose m = -1.
*)
Notation asymproduct_everywhere_order :=
  (asymproduct_filterType (everywhere_filterType Z) Z_filterType) (only parsing).

Lemma not_asymproduct_everywhere_order_domin_cst :
  dominated asymproduct_everywhere_order
    (fun '(_,_) => 1) (fun '(m,n) => n * m + n) ->
  False.
Proof.
  intro D. destruct D as (c & U).
  rewrite asymproductP in U. rewrite everywhereP in U.
  specializes U (-1). rewrite ZP in U. destruct U as (n0 & H).
  specializes H n0 ___. repeat (rewrite~ Z.abs_eq in H). math_lia.
Qed.

Lemma positive_inhab : exists x, 0 <= x.
Proof. exists 0. math. Qed.

(*----------------------------------------------------------------------------*)

(* Symmetric product restricting 0 <= m : Works *)
Notation product_positive_order :=
  (product_filterType (on_filterType positive_inhab) Z_filterType) (only parsing).

Lemma product_positive_order_limit :
  limit product_positive_order Z_filterType
    (fun '(m,n) => n * m + n).
Proof.
  rewrite limitP. intros P UP.
  rewrite ZP_ultimately with (cond := fun x => 0 <= x) in UP
    by (apply ultimately_ge_Z).
  destruct UP as (n0 &_N0 & H).
  rewrite productP. exists (fun x => 0 <= x) (fun x => n0 <= x). splits.
  rewrite~ onP. apply ultimately_ge_Z.
   simpl. intros. apply H. math_nia.
Qed.

Lemma g_spec :
  specO
    product_positive_order
    eq (* dummy *)
    (fun cost =>
      (forall m n,
         0 <= n -> 0 <= m -> (* FIXME (need more xfor lemmas) *)
         app g [(m, n)]
         PRE (\$ cost (m, n))
         POST (fun (_:unit) => \[])))
    (fun '(m, n) => n * m + n).
Proof.
  xspecO_refine straight_line.
  xcf. xpay. xmatch.
  weaken. xfor_inv (fun (_:int) => \[]). math.
  { intros i I. xpay.
    weaken. xfor_inv (fun (_:int) => \[]). math.
    intros j J. xpay. xret. hsimpl. hsimpl. hsimpl.
    { simpl. rewrite cumulP. rewrite big_const_Z.
      hide_evars_then ltac:(fun _ => ring_simplify). reflexivity. }
  }
  hsimpl. hsimpl.
  { simpl. rewrite cumulP. rewrite big_const_Z.
    hide_evars_then ltac:(fun _ => ring_simplify). reflexivity. }

  cleanup_cost.
  admit.

  apply_nary dominated_sum_distr_nary.
  { (* FIXME *) (*dominated.*) admit. }
  { apply_nary dominated_cst_limit_nary.
    apply product_positive_order_limit. }
Qed.

(* TODO: make xapp_spec work with a specO *)
Hint Extern 1 (RegisterSpec g) => Provide (provide_specO g_spec).

Lemma f_spec :
  specO
    Z_filterType
    eq (* dummy *)
    (fun cost =>
      (forall n,
         0 <= n ->
         app f [n]
         PRE (\$ cost n)
         POST (fun (_:unit) => \[])))
    (fun n => n).
Proof.
  xspecO_refine straight_line. xcf. xpay. xapp~.
  cleanup_cost.
  admit.
  { dominated.
    eapply dominated_comp_eq. applys cost_dominated g_spec.
    2: intros; reflexivity.
    2: intros; simpl; math.
    rewrite limitP. simpl. intros P UP. rewrite productP in UP. simpl in UP.
    destruct UP as (P1 & P2 & UP1 & UP2 & H). rewrite onP in UP1. revert UP2.
    filter_closed_under_intersection. auto with zarith. }
Qed.

(*----------------------------------------------------------------------------*)

(* Asymmetric product restricting 0 <= m : Also works *)
Definition asymproduct_positive_order :=
  (asymproduct_filterType (on_filterType positive_inhab) Z_filterType).

Lemma asymproduct_positive_order_limit :
  limit asymproduct_positive_order Z_filterType
    (fun '(m,n) => n * m + n).
Proof.
  rewrite limitP. intros P UP.
  rewrite ZP_ultimately with (cond := fun x => 0 <= x) in UP
    by (apply ultimately_ge_Z).
  destruct UP as (n0 & N0 & H).
  unfold asymproduct_positive_order. rewrite asymproductP.
  rewrite onP. intros x Hx. rewrite ZP. exists n0.
  intros. apply H. math_nia.
Qed.

Lemma g_spec' :
  specO
    asymproduct_positive_order
    eq (* dummy *)
    (fun cost =>
      (forall m n,
         0 <= n -> 0 <= m -> (* FIXME (need more xfor lemmas) *)
         app g [(m, n)]
         PRE (\$ cost (m, n))
         POST (fun (_:unit) => \[])))
    (fun '(m, n) => n * m + n).
Proof.
  xspecO_refine straight_line.
  xcf. xpay. xmatch.
  weaken. xfor_inv (fun (_:int) => \[]). math.
  { intros i I. xpay.
    weaken. xfor_inv (fun (_:int) => \[]). math.
    intros j J. xpay. xret. hsimpl. hsimpl. hsimpl.
    { simpl. rewrite cumulP. rewrite big_const_Z.
      hide_evars_then ltac:(fun _ => ring_simplify). reflexivity. }
  }
  hsimpl. hsimpl.
  { simpl. rewrite cumulP. rewrite big_const_Z.
    hide_evars_then ltac:(fun _ => ring_simplify). reflexivity. }

  cleanup_cost.
  admit.

  apply_nary dominated_sum_distr_nary.
  { (* FIXME dominated. *) admit. }
  { apply_nary dominated_cst_limit_nary. apply asymproduct_positive_order_limit. }
Qed.

(* TODO: make xapp_spec work with a specO *)
Hint Extern 1 (RegisterSpec g) => Provide (provide_specO g_spec').

Lemma f_spec' :
  specO
    Z_filterType
    eq (* dummy *)
    (fun cost =>
      (forall n,
         0 <= n ->
         app f [n]
         PRE (\$ cost n)
         POST (fun (_:unit) => \[])))
    (fun n => n).
Proof.
  xspecO_refine straight_line. xcf. xpay. xapp~.
  cleanup_cost.
  admit.
  { dominated.
    eapply dominated_comp_eq. applys cost_dominated g_spec'.
    2: intros; reflexivity.
    2: intros; simpl; math.
    rewrite limitP. simpl. intros P UP.
    unfold asymproduct_positive_order in UP. rewrite asymproductP in UP. simpl in UP.
    rewrite onP in UP. apply~ UP. }
Qed.

(*----------------------------------------------------------------------------*)

(* There is also the solution of quantifying m outside the specO... This
   trivially ensures we can instantiate it later.

   It works (we can prove that [forall m, g is O(n)]), but this is basically a
   uni-variate specification now. The O() constant can (and does) depend on m...

   Question: Does using the proper previous filters give us additionnal
   properties?...
*)

(* We can do this... or directly have a univariate specO, as below. *)
Definition product_singleton_order (m : Z) : filterType.
  refine (product_filterType (@on_filterType _ (fun x => x = m) _) Z_filterType).
  abstract (exists m; reflexivity).
Defined.

Lemma g_spec'' :
  forall m,
  specO
    (product_singleton_order m)
    eq (* dummy *)
    (fun cost =>
      (forall m n,
         0 <= n -> 0 <= m -> (* FIXME (need more xfor lemmas) *)
         app g [(m, n)]
         PRE (\$ cost (m, n))
         POST (fun (_:unit) => \[])))
    (fun '(m, n) => n).
Proof.
  intro m. xspecO_refine straight_line.
  xcf. xpay. xmatch.
  weaken. xfor_inv (fun (_:int) => \[]). math.
  { intros i I. xpay.
    weaken. xfor_inv (fun (_:int) => \[]). math.
    intros j J. xpay. xret. hsimpl. hsimpl. hsimpl.
    { simpl. rewrite cumulP. rewrite big_const_Z.
      hide_evars_then ltac:(fun _ => ring_simplify). reflexivity. }
  }
  hsimpl. hsimpl.
  { simpl. rewrite cumulP. rewrite big_const_Z.
    hide_evars_then ltac:(fun _ => ring_simplify). reflexivity. }

  cleanup_cost.
  admit.

  apply_nary dominated_sum_distr_nary.
  { dominated. apply_nary dominated_sum_distr_nary.
    { exists (Z.abs m). (*rewrite productP.*) (* FIXME *)
      exists (fun x => x = m) (fun x => 0 <= x). splits.
      rewrite onP. auto.
      apply ultimately_ge_Z.
      simpl. intros m' n E H. subst m'. math_nia. }
    apply dominated_reflexive.
  }
  { dominated. }
Qed.

Lemma g_spec''' :
  forall (m:Z), 0 <= m ->
  specO Z_filterType Z.le
    (fun cost =>
      (forall n,
         0 <= n -> (* FIXME (need more xfor lemmas) *)
         app g [(m, n)]
         PRE (\$ cost n)
         POST (fun (_:unit) => \[])))
    (fun n => n).
Proof.
  intros m M. xspecO_refine straight_line.
  xcf. xpay. xmatch.
  weaken. xfor_inv (fun (_:int) => \[]). math.
  { intros i I. xpay.
    weaken. xfor_inv (fun (_:int) => \[]). math.
    intros j J. xpay. xret. hsimpl. hsimpl. hsimpl.
    { simpl. rewrite cumulP. rewrite big_const_Z.
      hide_evars_then ltac:(fun _ => ring_simplify). reflexivity. }
  }
  hsimpl. hsimpl.
  { simpl. rewrite cumulP. rewrite big_const_Z.
    hide_evars_then ltac:(fun _ => ring_simplify). reflexivity. }

  cleanup_cost.
  monotonic.
  dominated.
Qed.

(* --------------------------------------------------------------------------
   --------------------------------------------------------------------------
   -------------------------------------------------------------------------- *)

Definition f2_spec_forallF :=
  forall (M : Filter.mixin_of (Z * Z)%type),
  ultimately (FilterType _ M) (fun '(m,n) => 0 <= m /\ 0 <= n) ->
  specO (FilterType _ M) eq (* dummy *)
    (fun cost =>
      forall m n,
      0 <= m -> 0 <= n ->
      app f2 [m n]
        PRE (\$ cost (m, n))
        POST (fun (_:unit) => \[]))
    (fun '(m,n) => m + n + 1).

Definition positive_ZZ_filterType : filterType.
  refine (@on_filterType (Z*Z) (fun '(m,n) => 0 <= m /\ 0 <= n) _).
  abstract (exists (0,0)%Z; simpl; math).
Defined.

Definition f2_spec_on_positives :=
  specO positive_ZZ_filterType eq (* dummy *)
    (fun cost =>
      forall m n,
      0 <= m -> 0 <= n ->
      app f2 [m n]
        PRE (\$ cost (m, n))
        POST (fun (_:unit) => \[]))
    (fun '(m,n) => m + n + 1).

(* [f2_spec_forallF] and [f2_spec_on_positives] are equivalent *)

Goal f2_spec_forallF -> f2_spec_on_positives.
  unfold f2_spec_forallF, f2_spec_on_positives.
  intro S. apply S. hnf. intros [m n]. auto.
Qed.

Goal f2_spec_on_positives -> f2_spec_forallF.
  unfold f2_spec_forallF, f2_spec_on_positives.
  intro S.
  intros M U. destruct S. simpl in cost.
  apply (@SpecO (FilterType (int * int) M) _ _ _ cost); auto.

  destruct cost_dominated as [c UD]. exists c.
  simpl in *.
  revert U. filter_closed_under_intersection. apply UD.
Qed.

Lemma f2_spec_1 : f2_spec_forallF.
Proof.
  unfold f2_spec_forallF. intros M U.
  xspecO_refine recursive. intros ? ? ? ?.
  intros m n.
  pose (p := (n,m)).
  change n with (fst p). change m with (snd p).
  induction_wf IH: (lexico2 (downto 0) (downto 0)) p. (* ugh *)
  clear m n. destruct p as [n m]. simpl.

  intros Hm Hn. weaken. xcf.
  xpay. xif_guard as C1.
  { forwards IH': IH ((n-1), (m+1)); try (simpl; math).
    { simpl. left~. }
    xapplys IH'. }
  xif_guard as C2.
  { forwards IH': IH (0, (m-1)); try (simpl; math).
    { simpl. right~. }
    xapplys IH'. }
  xret. hsimpl.

  generalize n m Hm Hn. defer.
  close cost.

  begin defer assuming a b c. exists (fun '(m,n) => a * m + b * n + c).
  split.
  { intros n m Hm Hn. repeat cases_if; ring_simplify.
    - cut (a - b + 1 <= 0). math. defer.
    - cut (-a + 1 <= b*n). math. rewrite <-Hn. ring_simplify.
      cut (1 <= a). math. defer. defer.
    - rewrite <-Hm. rewrite <-Hn. ring_simplify.
      defer. defer. defer. }
  cleanup_cost.
  admit.
  { apply_nary dominated_sum_nary.
    { revert U; filter_closed_under_intersection. intros [? ?]. math. }
    { apply filter_universe_alt. intros [_ _]. math. }
    { apply_nary dominated_sum_nary.
      { revert U; filter_closed_under_intersection. intros [? ?]. math. }
      { revert U; filter_closed_under_intersection. intros [? ?]. math. }
      { dominated. }
      { dominated. } }
    { dominated. } }

  end defer.
  exists 1 2 1. math.
Qed.

(* -------------------------------------------------------------------------- *)

Definition f2_spec_asym_1 :=
  specO (asymproduct_filterType positive_filterType positive_filterType) eq (* dummy *)
    (fun cost =>
      forall m n,
      0 <= m -> 0 <= n ->
      app f2 [m n]
        PRE (\$ cost (m, n))
        POST (fun (_:unit) => \[]))
    (fun '(m, n) => m + n + 1).

Goal f2_spec_forallF -> f2_spec_asym_1.
Proof.
  intro S. apply S.
  setoid_rewrite asymproductP. repeat (rewrite positiveP; intro). math.
Qed.

Definition f2_spec_specialize_m :=
  forall m, 0 <= m ->
  specO positive_filterType eq (* dummy *)
    (fun cost =>
      forall n,
      0 <= n ->
      app f2 [m n]
        PRE (\$ cost n)
        POST (fun (_:unit) => \[]))
    (fun n => n + 1).

Goal f2_spec_asym_1 -> f2_spec_specialize_m.
Proof.
  unfold f2_spec_specialize_m. intros S m M.
  destruct S. simpl in cost.
  apply (@SpecO positive_filterType _ _ _ (fun n => cost (m, n))); auto.
  admit.
  { etransitivity. eapply dominated_comp_eq. eapply cost_dominated.
    2: intro; reflexivity.
    2: intro; simpl; reflexivity.
    admit. (* ok *)
    setoid_rewrite <-Z.add_assoc. apply dominated_sum_distr.
    { (* TODO: lemma *) exists m. rewrite positiveP. math_nia. }
    { reflexivity. } }
Qed.
