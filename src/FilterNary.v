Require Export ZArith.
Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Filter.
Require Import Generic.

Definition nFilterType (domain : list Type) M :=
  FilterType (Rtuple domain) M.

Arguments nFilterType : clear implicits.
Hint Unfold nFilterType : generic.

Lemma ultimately_eta A P :
  ultimately A P <-> ultimately A (fun x => P x).
Proof. tauto. Qed.

Hint Rewrite ultimately_eta : nary_prepare.


(******************************************************************************)

(* Applying n-ary filter lemmas *)

Ltac domain_of_filter F :=
  let S := constr:(Filter.sort F) in
  let S := eval simpl in S in
  list_of_tuple S.
