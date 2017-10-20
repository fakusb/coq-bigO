Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import CFML.CFLibCredits.
Require Import Dominated.
Require Import Monotonic.
Require Import CFMLBigO.

Parameter (elem data : Type).

Implicit Types x : elem.

Implicit Types D : set elem.
Implicit Types R : elem -> elem.
Implicit Types V : elem -> data.

Parameter card : set elem -> Z.
Hypothesis card_nonneg : forall D, 0 <= card D.
Hint Resolve card_nonneg : zarith.

Parameter UF : set elem -> (elem -> elem) -> (elem -> data) -> hprop.

Parameter UnionFind_ml_find : func.

Parameter alpha : Z -> Z.

Hypothesis alpha_nonneg : forall (x: Z), 0 <= x -> 0 <= alpha x.
Hint Resolve alpha_nonneg : zarith.

Hypothesis alpha_monotonic : monotonic Z.le Z.le alpha.
Hint Resolve alpha_monotonic : monotonic.

Hypothesis alpha_limit : limit Z_filterType Z_filterType alpha.
Hint Resolve alpha_limit : limit.

Parameter find_spec : forall D R V x, x \in D ->
  app UnionFind_ml_find [x]
    PRE  (UF D R V \* \$(2 * alpha (card D) + 4))
    POST (fun y => UF D R V \* \[ R x = y ]).

Theorem find_specO :
  specO Z_filterType Z.le
    (fun cost =>
      (forall D R V x, x \in D ->
       app UnionFind_ml_find [x]
         PRE  (UF D R V \* \$(cost (card D)))
         POST (fun y => UF D R V \* \[ R x = y ])))
    alpha.
Proof using.
  xspecO. intros. xapply find_spec. apply H. hsimpl. sets cD: (card D). reflexivity.
  hsimpl~. cleanup_cost. monotonic. dominated.
Qed.
