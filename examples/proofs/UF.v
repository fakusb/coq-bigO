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

Parameter UF : set elem -> (elem -> elem) -> (elem -> data) -> hprop.

Parameter UnionFind_ml_find : func.
Parameter alpha : nat -> nat.

Hypothesis alpha_monotonic : monotonic Nat.le Nat.le alpha.
Hypothesis alpha_limit : limit nat_filterType nat_filterType alpha.

Parameter find_spec : forall D R V x, x \in D ->
  app UnionFind_ml_find [x]
    PRE  (UF D R V \* \$(2 * alpha (card D) + 4))
    POST (fun y => UF D R V \* \[ R x = y ]).

Theorem find_specO :
  specO nat_filterType Nat.le
    (fun cost =>
      (forall D R V x, x \in D ->
       app UnionFind_ml_find [x]
         PRE  (UF D R V \* \$(cost (card D)))
         POST (fun y => UF D R V \* \[ R x = y ])))
    alpha.
Proof using.
  xspecO. intros.
  xapply find_spec. apply H. hsimpl. sets cD: (card D). reflexivity.
  hsimpl~.

  cleanup_cost.
  { monotonic. eapply monotonic_comp; swap 1 2. apply alpha_monotonic.
    admit. (* ... *) }
  { dominated. apply dominated_cst_limit.
    eapply limit_comp_eq. apply alpha_limit. Focus 2. intro. reflexivity.
    admit. (* ... *) }
Qed.
