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

Lemma bellman_ford2_spec :
  specO
    (product_filterType Z_filterType Z_filterType)
    eq (* TODO *)
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

  intros ? ? E. rewrite E. reflexivity.

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