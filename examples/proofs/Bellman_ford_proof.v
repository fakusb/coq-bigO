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
Require Import DominatedNary.
Require Import FilterNary.
Require Import LimitNary.
Require Import UltimatelyGreater.
Require Import Monotonic.
Require Import LibZExtra.
Require Import Generic.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
(* Load the CF definitions. *)
Require Import Bellman_ford_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

Definition ZZle (p1 p2 : Z * Z) :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  1 <= x1 <= x2 /\ 0 <= y1 <= y2.

Lemma bellman_ford2_spec :
  specO
    (product_filterType Z_filterType Z_filterType)
    ZZle
    (fun cost =>
      forall (inf source : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
        0 <= source < nb_nodes ->
        1 <= nb_nodes ->
        app bellman_ford2 [inf source t nb_nodes]
        PRE (\$ (cost (nb_nodes, LibListZ.length edges)) \* t ~> Array edges)
        POST (fun (_: array int) => t ~> Array edges))
    (fun '(n,m) => n * m).
Proof.
  xspecO_refine straight_line. xcf.
  xpay.

  xapp~. intros ds Hds. subst ds.
  xapp~. apply index_make. apply~ int_index_prove.
  xseq.

  { xfor_inv (fun (_:int) => Hexists (ds: list int), t ~> Array edges \* d ~> Array ds). math.
    { intros i Hi. xpay.
      xpull. intros ds.

      xapp as edges_nb. intro Hedges_nb.
      weaken. xfor_inv (fun (_:int) => Hexists (ds: list int), t ~> Array edges \* d ~> Array ds). math.
      { intros j Hj. xpull. intros ds'.
        xpay. xapps. apply~ int_index_prove.
        xmatch.
        xapp as d1. admit. (* TODO *) intro Hd1.
        xapp as d2. admit. (* TODO *) intro Hd2.
        xapp. admit. (* TODO *) }
      { hsimpl. } { hsimpl. }

      { subst edges_nb.
        match goal with |- cumul _ _ (fun _ => ?x) <= _ => ring_simplify x end.
        sets edges_nb: (LibListZ.length edges). (* workaround *)
        reflexivity. }
    }
    { hsimpl. }
  }
  { xpull. intros ds. xret. hsimpl. }
  cleanup_cost.

  admit. (* TODO monotonic *)

  apply_nary dominated_sum_distr_nary; swap 1 2.
  dominated.

  apply_nary dominated_sum_distr_nary.
  { apply dominated_transitive with (fun '(x, y) => x * 1).
    - (* TODO: improve using some setoid rewrite instances? *)
      apply dominated_eq. intros [? ?]. math.
    - apply_nary dominated_mul_nary; dominated. }
  { eapply dominated_transitive.
    apply dominated_product_swap.
    apply Product.dominated_big_sum_bound_with.
    { (* ultimately_greater. *) (* FIXME *) admit. }
    { monotonic. }
    { limit. (* FIXME *) apply limit_sum_cst_r. limit. }

    simpl. dominated.

    apply_nary dominated_sum_distr_nary.
    { apply_nary dominated_sum_distr_nary.
      { reflexivity. }
      { dominated. } }
    { dominated. }

    apply_nary dominated_sum_distr_nary.
    { dominated. }
    { apply_nary dominated_sum_distr_nary.
      { dominated. }
      { dominated.
        eapply dominated_transitive.
        apply Product.dominated_big_sum_bound.
        { ultimately_greater. } { monotonic. }
        simpl. dominated. } } }
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
      forall (inf source : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
        0 <= source < nb_nodes ->
        1 <= nb_nodes ->
        app bellman_ford2 [inf source t nb_nodes]
        PRE (\$ (cost (nb_nodes, LibListZ.length edges)) \* t ~> Array edges)
        POST (fun (_: array int) => t ~> Array edges))
    (fun '(n,m) => n ^ 3).
Proof.
  econstructor; try (intros; apply~ bellman_ford2_spec).
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
      forall (inf source : int) t (edges : list (int * int * int)%type) (nb_nodes : int),
        0 <= source < nb_nodes ->
        1 <= nb_nodes ->
        LibListZ.length edges <= nb_nodes ^ 2 ->
        app bellman_ford2 [inf source t nb_nodes]
        PRE (\$ (cost nb_nodes) \* t ~> Array edges)
        POST (fun (_: array int) => t ~> Array edges))
    (fun n => n ^ 3).
Proof.
  xspecO (fun n =>
    let m := If 0 < n then n^2 else 0 in
    let n' := If 0 < n then n else 1 in
    cost bellman_ford2_spec (n', m)).
  { introv Hnodes Hedges. intros; xapply~ (spec bellman_ford2_spec).
    hsimpl_credits; swap 1 2;
    (asserts_rewrite (forall (x y : Z), le 0 (x - y) <-> y <= x); [math|..]).
    apply (cost_monotonic bellman_ford2_spec).
    unfolds ZZle. splits~. cases_if~. cases_if~.
  }
  { eapply monotonic_comp. monotonic.
    intros x1 x2 H. unfold ZZle. splits~.
    - cases_if; cases_if~.
    - cases_if~. apply~ Z.pow_nonneg.
    - cases_if; cases_if~. apply~ Z.pow_le_mono. apply~ Z.pow_nonneg. }
  { eapply dominated_transitive.
    eapply dominated_ultimately_eq.
    { exists 1. intros. cases_if~. reflexivity. }
    eapply dominated_comp_eq.
    apply (cost_dominated bellman_ford2_spec).
    2: intro; reflexivity.
    2: intro; reflexivity.
    limit. }
Qed.
