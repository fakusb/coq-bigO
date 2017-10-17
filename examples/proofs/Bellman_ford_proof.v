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
Require Import Bellman_ford_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

(* FIXME: coq bug *)
Lemma L: forall A B (x : (A * B)%type) (f g : A -> B -> Z),
             f (fst x) (snd x) = g (fst x) (snd x) ->
             (let (y,z) := x in f y z) = (let (y,z) := x in g y z).
Proof. intros ? ? x_ ? ? ?. destruct x_. simpl in *. assumption. Qed.

Goal
  specO
    (product_filterType Z_filterType Z_filterType) eq
    (fun _ => True)
    (fun '(n,m) => 0).
Proof.
  xspecO. admit.
  unfold cleanup_cost. splits.
  intro x. unfold costf. eapply L. (* simpl. *)
Abort.

(* For later: what to think about the following unification problem:

   x + y = ?f(x,y) + ?g(x,y)

   Coq doesn't know how to solve it (and there are at least two different
   solutions, (eg inserting a let or using projections)).

   Is it a feature? Is it a limitation that may be lifted in the future?
 *)

Lemma dominated_sum_distr2 (A B : filterType) f g h :
  dominated (product_filterType A B) (fun '(a,b) => f a b) h ->
  dominated (product_filterType A B) (fun '(a,b) => g a b) h ->
  dominated (product_filterType A B) (fun '(a,b) => (f a b) + (g a b)) h.
Proof.
  intros Hf Hg. applys_eq dominated_sum_distr 2. apply Hf. apply Hg.
  extens. intros [? ?]. reflexivity.
Qed.

Lemma dominated_max0_2 : forall A B f g,
    dominated (product_filterType A B) (fun '(a,b) => f a b) g ->
    dominated (product_filterType A B) (fun '(a,b) => max0 (f a b)) g.
Proof.
  introv H. applys_eq dominated_max0 2. apply H. extens. intros [? ?].
  reflexivity.
Qed.

Lemma dominated_product_swap : forall (A B : filterType) f g,
  dominated (product_filterType A B) (fun '(a,b) => f a b) (fun '(a,b) => g a b) ->
  dominated (product_filterType B A) (fun '(b,a) => f a b) (fun '(b,a) => g a b).
Proof.
  introv H. destruct H as [c U].
  exists c. rewrite productP in *. destruct U as (P1 & P2 & UP1 & UP2 & UU).
  exists P2 P1. splits~.
Qed.

Lemma dominated_mul_cst_l_2_2 A B c f g :
  dominated (product_filterType A B) (fun '(a,b) => f a b) g ->
  dominated (product_filterType A B) (fun '(a,b) => (f a b) * c) g.
Proof.
  introv H. applys_eq dominated_mul_cst_l_2 2. apply H. extens. intros [? ?].
  reflexivity.
Qed.

Lemma dominated_mul_2 A B f1 f2 g1 g2 :
  dominated (product_filterType A B) (fun '(a,b) => f1 a b) (fun '(a,b) => g1 a b) ->
  dominated (product_filterType A B) (fun '(a,b) => f2 a b) (fun '(a,b) => g2 a b) ->
  dominated (product_filterType A B) (fun '(a,b) => (f1 a b) * (f2 a b)) (fun '(a,b) => (g1 a b) * (g2 a b)).
Proof.
  introv H1 H2. applys_eq dominated_mul 2 1. apply H1. apply H2.
  extens. intros [? ?]. reflexivity.
  extens. intros [? ?]. reflexivity.
Qed.

Lemma dominated_cst_limit_2 A B c g :
  limit (product_filterType A B) Z_filterType g ->
  dominated (product_filterType A B) (fun '(_,_) => c) g.
Proof. Admitted.

Definition ZZle (p1 p2 : Z * Z) :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  1 <= x1 <= x2 /\ 0 <= y1 <= y2.

Lemma bellman_ford2_spec :
  specO
    (product_filterType Z_filterType Z_filterType)
    ZZle
    (fun cost =>
      forall (inf : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
        (* TODO: smthg about inf? *)
        1 <= nb_nodes ->
        app bellman_ford2 [inf t nb_nodes]
        PRE (\$ (cost (nb_nodes, LibListZ.length edges)) \* t ~> Array edges)
        POST (fun (_: array int) => t ~> Array edges))
    (fun '(n,m) => n * m).
Proof.
  xspecO costf.
  xcf. xpay.

  xapp~. intros ds Hds. subst ds. xseq.
  { xfor_inv (fun (_:int) => Hexists (ds: list int), t ~> Array edges \* d ~> Array ds). math.
    { intros i Hi. xpull. intros ds.
      xapp as edges_nb. intro Hedges_nb.
      xfor_inv (fun (_:int) => Hexists (ds: list int), t ~> Array edges \* d ~> Array ds). math.
      { intros j Hj. xpull. intros ds'.
        xapps. apply~ int_index_prove.
        xmatch.
        xapp as d1. admit. (* TODO *) intro Hd1.
        xapp as d2. admit. (* TODO *) intro Hd2.
        xapp. admit. (* TODO *) }
      { hsimpl. }

      { subst edges_nb. clean_max0.
        match goal with |- cumul _ _ (fun _ => ?x) <= _ => ring_simplify x end.
        reflexivity. }
      { hsimpl. }
    }
    { hsimpl. } { sets edges_nb: (LibListZ.length edges). reflexivity. }
  }
  { xpull. intros ds. xret. hsimpl. }

  cleanup_cost.

  admit. (* TODO monotonic *)

  eapply dominated_sum_distr2; swap 1 2.
  apply dominated_cst_limit_2. admit. (* TODO limit *)

  eapply dominated_sum_distr2.
  eapply dominated_max0_2.
  eapply dominated_sum_distr2.
  (* TODO *) admit.
  apply dominated_cst_limit_2. admit.

  eapply dominated_max0_2.
  eapply dominated_transitive.
  apply dominated_product_swap.
  apply Product.dominated_big_sum_bound_with.
  { ultimately_greater. }
  { monotonic. }
  { limit. admit. }
  simpl.

  eapply dominated_mul_2.
  eapply dominated_sum_distr2.
  eapply dominated_sum_distr2.
  reflexivity.
  apply dominated_cst_limit_2. admit.
  apply dominated_cst_limit_2. admit.

  eapply dominated_sum_distr2.
  apply dominated_cst_limit_2. admit.
  eapply dominated_max0_2.
  eapply dominated_transitive.
  apply Product.dominated_big_sum_bound.
  { ultimately_greater. } { monotonic. }
  simpl. eapply dominated_mul_cst_l_2_2. reflexivity.
Qed.

Definition domain := (fun '(n,m) => m <= n ^ 2).

Lemma domain_often :
  often
    (product_filterType Z_filterType Z_filterType)
    domain.
Proof.
  unfold often. simpl. intros Q U.
  rewrite productP in U. destruct U as (P1 & P2 & U1 & U2 & H).
  rewrite (ZP_ultimately (ultimately_ge_Z 1)) in U1.
  rewrite (ZP_ultimately (ultimately_ge_Z 1)) in U2.
  destruct U2 as (m0 & M0 & Hm0). destruct U1 as (n0 & N0 & Hn0).
  exists (Z.max n0 m0, (Z.max n0 m0) ^ 2).
  split; swap 1 2.
  - apply H. apply Hn0. math_lia. apply Hm0. math_nia.
  - unfold domain. reflexivity.
Qed.

Lemma bellman_ford2_spec_within :
  specO
    (within_filterType
      (product_filterType Z_filterType Z_filterType)
      domain
      domain_often)
    ZZle
    (fun cost =>
      forall (inf : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
        1 <= nb_nodes ->
        app bellman_ford2 [inf t nb_nodes]
        PRE (\$ (cost (nb_nodes, LibListZ.length edges)) \* t ~> Array edges)
        POST (fun (_: array int) => t ~> Array edges))
    (fun '(n,m) => n ^ 3).
Proof.
  econstructor; try apply bellman_ford2_spec.
  eapply dominated_transitive.
  { destruct (cost_dominated bellman_ford2_spec) as [c U].
    exists c. applys within_finer U. }
  { exists 1. rewrite withinP.
    rewrite productP. do 2 exists (fun x => 0 <= x).
    splits; try apply ultimately_ge_Z.
    intros n m N M D. unfold domain in D.
    rewrite Z.abs_eq; [| math_nia].
    rewrite Z.abs_eq; swap 1 2. apply~ Z.pow_nonneg.
    rewrite D. math_nia. }
Qed.

Lemma bellman_ford2_spec_derived :
  specO
    Z_filterType
    Z.le
    (fun cost =>
      forall (inf : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
        1 <= nb_nodes ->
        LibListZ.length edges <= nb_nodes ^ 2 ->
        app bellman_ford2 [inf t nb_nodes]
        PRE (\$ (cost nb_nodes) \* t ~> Array edges)
        POST (fun (_: array int) => t ~> Array edges))
    (fun n => n ^ 3).
Proof.
  xspecO_cost (fun n =>
    let m := If 0 < n then n^2 else 0 in
    cost bellman_ford2_spec (n, m)).
  { introv Hnodes Hedges. xapply~ (spec bellman_ford2_spec).
    hsimpl_credits; swap 1 2;
    (asserts_rewrite (forall (x y : Z), ge x y <-> y <= x); [math|..]).
    apply (cost_nonneg bellman_ford2_spec).
    apply (cost_monotonic bellman_ford2_spec).
    unfolds ZZle. splits~. cases_if~.
  }
  { ultimately_greater. }
  { eapply monotonic_comp. monotonic.
    intros x1 x2 H. unfold ZZle. splits~.
    cases_if~. cases_if~. apply~ Z.pow_le_mono. cases_if~. math_nia. }
  { eapply dominated_transitive.
    eapply dominated_ultimately_eq.
    { exists 1. intros. cases_if~. reflexivity. }
    eapply dominated_comp_eq.
    apply (cost_dominated bellman_ford2_spec).
    Focus 2. intro. reflexivity.
    Focus 2. intro. reflexivity.
    limit. }
Qed.
