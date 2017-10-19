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
Require Import EvarsFacts.
(* Load the CF definitions. *)
Require Import Multivar_specialize_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Hypothesis pay1 : forall B (F : ~~B) (H: hprop) (Q: B -> hprop) c,
  F (\$ max0 c \* H) Q -> F (\$ max0 (1 + c) \* H) Q.




Lemma dominated_max0_2 : forall A B f g,
    dominated (product_filterType A B) (fun '(a,b) => f a b) g ->
    dominated (product_filterType A B) (fun '(a,b) => max0 (f a b)) g.
Proof.
  introv H. applys_eq dominated_max0 2. apply H. extens. intros [? ?].
  reflexivity.
Qed.

Lemma dominated_max0_a2 : forall A B f g,
    dominated (asymproduct_filterType A B) (fun '(a,b) => f a b) g ->
    dominated (asymproduct_filterType A B) (fun '(a,b) => max0 (f a b)) g.
Proof.
  introv H. applys_eq dominated_max0 2. apply H. extens. intros [? ?].
  reflexivity.
Qed.

Lemma dominated_sum_distr_2 (A B : filterType) f g h :
  dominated (product_filterType A B) (fun '(a,b) => f a b) h ->
  dominated (product_filterType A B) (fun '(a,b) => g a b) h ->
  dominated (product_filterType A B) (fun '(a,b) => (f a b) + (g a b)) h.
Proof.
  intros Hf Hg. applys_eq dominated_sum_distr 2. apply Hf. apply Hg.
  extens. intros [? ?]. reflexivity.
Qed.

Lemma dominated_sum_distr_a2 (A B : filterType) f g h :
  dominated (asymproduct_filterType A B) (fun '(a,b) => f a b) h ->
  dominated (asymproduct_filterType A B) (fun '(a,b) => g a b) h ->
  dominated (asymproduct_filterType A B) (fun '(a,b) => (f a b) + (g a b)) h.
Proof.
  intros Hf Hg. applys_eq dominated_sum_distr 2. apply Hf. apply Hg.
  extens. intros [? ?]. reflexivity.
Qed.

Lemma dominated_cst_limit_2 A B c g :
  limit (product_filterType A B) Z_filterType g ->
  dominated (product_filterType A B) (fun '(_,_) => c) g.
Admitted.

Lemma dominated_cst_limit_a2 A B c g :
  limit (asymproduct_filterType A B) Z_filterType g ->
  dominated (asymproduct_filterType A B) (fun '(_,_) => c) g.
Admitted.

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
  xspecO.
  xcf. xpay. xmatch.
  xfor_inv (fun (_:int) => \[]). math.
  { intros i I. apply pay1.
    xfor_inv (fun (_:int) => \[]). math.
    intros j J. apply pay1. xret. hsimpl. hsimpl.
    simpl. clean_max0. rewrite cumulP. rewrite big_const_Z. ring_simplify.
    apply Z.le_refl.
    hsimpl.
  }
  hsimpl.
  simpl. rewrite cumulP. rewrite big_const_Z. rewrite~ max0_eq.
  hide_evars_then ltac:(fun _ => ring_simplify). apply Z.le_refl.
  hsimpl.

  cleanup_cost.
  admit.

  apply dominated_sum_distr_2.
  { apply dominated_max0_2. apply dominated_reflexive. }
  { apply dominated_cst_limit_2. apply product_positive_order_limit. }
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
  xspecO. xcf. xpay. xapp~.
  cleanup_cost.
  admit.
  { dominated.
    eapply dominated_comp_eq. applys cost_dominated g_spec.
    Focus 2. intros. reflexivity.
    Focus 2. intros. simpl. math.
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
  xspecO.
  xcf. xpay. xmatch.
  xfor_inv (fun (_:int) => \[]). math.
  { intros i I. apply pay1.
    xfor_inv (fun (_:int) => \[]). math.
    intros j J. apply pay1. xret. hsimpl. hsimpl.
    simpl. clean_max0. rewrite cumulP. rewrite big_const_Z. ring_simplify.
    apply Z.le_refl.
    hsimpl.
  }
  hsimpl.
  simpl. rewrite cumulP. rewrite big_const_Z. rewrite~ max0_eq.
  hide_evars_then ltac:(fun _ => ring_simplify). apply Z.le_refl.
  hsimpl.

  cleanup_cost.
  admit.

  apply dominated_sum_distr_a2.
  { apply dominated_max0_a2. apply dominated_reflexive. }
  { apply dominated_cst_limit_a2. apply asymproduct_positive_order_limit. }
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
  xspecO. xcf. xpay. xapp~.
  cleanup_cost.
  admit.
  { dominated.
    eapply dominated_comp_eq. applys cost_dominated g_spec'.
    Focus 2. intros. reflexivity.
    Focus 2. intros. simpl. math.
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
  intro m. xspecO.
  xcf. xpay. xmatch.
  xfor_inv (fun (_:int) => \[]). math.
  { intros i I. apply pay1.
    xfor_inv (fun (_:int) => \[]). math.
    intros j J. apply pay1. xret. hsimpl. hsimpl.
    simpl. clean_max0. rewrite cumulP. rewrite big_const_Z. ring_simplify.
    apply Z.le_refl.
    hsimpl.
  }
  hsimpl.
  simpl. rewrite cumulP. rewrite big_const_Z. rewrite~ max0_eq.
  hide_evars_then ltac:(fun _ => ring_simplify). apply Z.le_refl.
  hsimpl.

  cleanup_cost.
  admit.

  apply dominated_sum_distr_2.
  { apply dominated_max0_2. apply dominated_sum_distr_2.
    { exists (Z.abs m). rewrite productP.
      exists (fun x => x = m) (fun x => 0 <= x). splits.
      rewrite onP. auto.
      apply ultimately_ge_Z.
      simpl. intros m' n E H. subst m'. math_nia. }
    apply dominated_reflexive.
  }
  { apply dominated_cst_limit_2.
    rewrite limitP. intros P UP. rewrite productP.
    exists (fun x => x = m) P. splits~. rewrite~ onP.
  }
Qed.