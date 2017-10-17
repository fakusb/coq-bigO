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
Require Import LibZExtra.
(* Load the custom CFML tactics with support for big-Os *)
Require Import CFMLBigO.
Require Import EvarsFacts.
(* Load the CF definitions. *)
Require Import Bellman_ford_ml.

Ltac auto_tilde ::= try solve [ auto with maths | false; math ].

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
  xspecO foo.
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

      { subst edges_nb. clean_max0. (* hummm.... *)
        match goal with |- cumul _ _ (fun _ => ?x) <= _ => ring_simplify x end.
        reflexivity. }
      { hsimpl. }
    }
    { hsimpl. } { sets edges_nb: (LibListZ.length edges). reflexivity. }
  }
  { xpull. intros ds. xret. hsimpl. }

Abort.