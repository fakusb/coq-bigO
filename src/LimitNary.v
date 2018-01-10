Require Export ZArith.
Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import FilterNary.
Require Import UltimatelyGreater.
Require Import Generic.
Require Import Limit.

(* Proving n-ary versions of [limit] lemmas *)

Lemma limit_eta A B f :
  limit A B f <-> limit A B (fun x => f x).
Proof. tauto. Qed.

Hint Rewrite limit_eta : nary_prepare.

(******************************************************************************)
(* FUTURE WORK: all this could be automatically generated from the lemmas in
   [Limit.v], maybe using coq-elpi. *)

(* nary limit lemmas *)

Lemma limit_mul_nary domain M f g :
  limit (nFilterType domain M) Z_filterType (Uncurry f) ->
  limit (nFilterType domain M) Z_filterType (Uncurry g) ->
  limit (nFilterType domain M) Z_filterType (Fun' (fun p => (App f p) * (App g p))).
Proof. prove_nary limit_mul. Qed.

Lemma limit_sum_nary domain M f g :
  limit (nFilterType domain M) Z_filterType (Uncurry f) ->
  limit (nFilterType domain M) Z_filterType (Uncurry g) ->
  limit (nFilterType domain M) Z_filterType (Fun' (fun p => (App f p) + (App g p))).
Proof. prove_nary limit_sum. Qed.

(******************************************************************************)

(* Applying n-ary limit lemmas *)

Ltac limit_domain G :=
  match G with
  | limit ?F _ _ =>
    let L := domain_of_filter F in
    exact (Mk_domain_of_goal L)
  end.

Hint Extern 0 Domain_of_goal =>
  (mk_domain_getter limit_domain) : domain_of_goal.

Goal
  limit (product_filterType Z_filterType Z_filterType) Z_filterType
    (fun '(x, y) => x * y).
Proof.
  apply_nary limit_mul_nary.
  admit. admit.
Admitted.

(******************************************************************************)
(* FIXME: generalize to other arities. The lemmas themselves work with any
   arity, but not the hint patterns. *)

Hint Extern 2 (limit _ _ (fun '(_, _) => Z.mul _ _)) =>
  apply_nary limit_mul_nary : limit.
Hint Extern 2 (limit _ _ (fun '(_, _) => Z.add _ _)) =>
  apply_nary limit_sum_nary : limit.