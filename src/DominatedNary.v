Require Export ZArith.
Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import FilterNary.
Require Import UltimatelyGreater.
Require Import Dominated.
Require Import Generic.

(* Proving n-ary versions of [dominated] lemmas *)

Lemma dominated_eta A f g :
  dominated A f g <-> dominated A (fun x => f x) (fun x => g x).
Proof. tauto. Qed.

Hint Rewrite dominated_eta : nary_prepare.

(******************************************************************************)
(* FUTURE WORK: all this could be automatically generated from the lemmas in
   [Dominated.v], maybe using coq-elpi. *)

(* nary dominated lemmas *)

Local Arguments Const' [domain] [range] cst.

Lemma dominated_cst_nary (domain : list Type) M c1 c2 :
  c2 <> 0 ->
  dominated (nFilterType domain M) (Const' c1) (Const' c2).
Proof. prove_nary dominated_cst. Qed.

Lemma dominated_cst_limit_nary (domain : list Type) M c g :
  limit (nFilterType domain M) Z_filterType g ->
  dominated (nFilterType domain M) (Const' c) g.
Proof.
  prove_nary dominated_cst_limit.
  Restart.
  intros;
  eapply dominated_eq_l;
  [| intro; autounfold with generic; autorewrite with generic; reflexivity ].
  generalize dependent (nFilterType domain M).
  intros. apply dominated_cst_limit; assumption.
Qed.

Lemma dominated_mul_nary (domain : list Type) M f1 f2 g1 g2 :
  dominated (nFilterType domain M) (Uncurry f1) (Uncurry g1) ->
  dominated (nFilterType domain M) (Uncurry f2) (Uncurry g2) ->
  dominated (nFilterType domain M)
    (Fun' (fun p => (App f1 p) * (App f2 p)))
    (Fun' (fun p => (App g1 p) * (App g2 p))).
Proof. prove_nary dominated_mul. Qed.

Lemma dominated_mul_cst_nary domain M c1 c2 f g :
  c2 <> 0 ->
  dominated (nFilterType domain M) (Uncurry f) (Uncurry g) ->
  dominated (nFilterType domain M)
    (Fun' (fun p => c1 * (App f p)))
    (Fun' (fun p => c2 * (App g p))).
Proof. prove_nary dominated_mul_cst. Qed.

Lemma dominated_mul_cst_l_1_nary domain M c f g :
  dominated (nFilterType domain M) (Uncurry f) (Uncurry g) ->
  dominated (nFilterType domain M) (Fun' (fun p => c * (App f p))) (Uncurry g).
Proof. prove_nary dominated_mul_cst_l_1. Qed.

Lemma dominated_mul_cst_l_2_nary domain M c f g :
  dominated (nFilterType domain M) (Uncurry f) (Uncurry g) ->
  dominated (nFilterType domain M) (Fun' (fun p => (App f p) * c)) (Uncurry g).
Proof. prove_nary dominated_mul_cst_l_2. Qed.

Lemma dominated_mul_cst_r_1_nary domain M c f g :
  dominated (nFilterType domain M) (Uncurry f) (Uncurry g) ->
  c <> 0 ->
  dominated (nFilterType domain M) (Uncurry f) (Fun' (fun p => c * (App g p))).
Proof. prove_nary dominated_mul_cst_r_1. Qed.

Lemma dominated_mul_cst_r_2_nary domain M c f g :
  dominated (nFilterType domain M) (Uncurry f) (Uncurry g) ->
  c <> 0 ->
  dominated (nFilterType domain M) (Uncurry f) (Fun' (fun p => (App g p) * c)).
Proof. prove_nary dominated_mul_cst_r_2. Qed.

Lemma dominated_max_nary domain M f1 f2 g1 g2 :
  ultimately (nFilterType domain M) (Fun' (fun p => 0 <= App g1 p)) ->
  ultimately (nFilterType domain M) (Fun' (fun p => 0 <= App g2 p)) ->
  dominated (nFilterType domain M) (Uncurry f1) (Uncurry g1) ->
  dominated (nFilterType domain M) (Uncurry f2) (Uncurry g2) ->
  dominated (nFilterType domain M)
    (Fun' (fun p => Z.max (App f1 p) (App f2 p)))
    (Fun' (fun p => Z.max (App g1 p) (App g2 p))).
Proof. prove_nary dominated_max. Qed.

Lemma dominated_max_distr_nary domain M f g h :
  dominated (nFilterType domain M) (Uncurry f) (Uncurry h) ->
  dominated (nFilterType domain M) (Uncurry g) (Uncurry h) ->
  dominated (nFilterType domain M)
    (Fun' (fun p => Z.max (App f p) (App g p))) (Uncurry h).
Proof. prove_nary dominated_max_distr. Qed.

Lemma dominated_sum_distr_nary domain M f g h :
  dominated (nFilterType domain M) (Uncurry f) (Uncurry h) ->
  dominated (nFilterType domain M) (Uncurry g) (Uncurry h) ->
  dominated (nFilterType domain M)
    (Fun' (fun p => Z.add (App f p) (App g p))) (Uncurry h).
Proof. prove_nary dominated_sum_distr. Qed.

Lemma dominated_sum_nary domain M f1 f2 g1 g2 :
  ultimately (nFilterType domain M) (Fun' (fun p => 0 <= App g1 p)) ->
  ultimately (nFilterType domain M) (Fun' (fun p => 0 <= App g2 p)) ->
  dominated (nFilterType domain M) (Uncurry f1) (Uncurry g1) ->
  dominated (nFilterType domain M) (Uncurry f2) (Uncurry g2) ->
  dominated (nFilterType domain M)
    (Fun' (fun p => Z.add (App f1 p) (App f2 p))) (Fun' (fun p => Z.add (App g1 p) (App g2 p))).
Proof. prove_nary dominated_sum. Qed.

Lemma dominated_sum_r_nonneg_1_nary domain M f g1 g2 :
  ultimately (nFilterType domain M) (Fun' (fun p => 0 <= App g1 p)) ->
  ultimately (nFilterType domain M) (Fun' (fun p => 0 <= App g2 p)) ->
  dominated (nFilterType domain M) (Uncurry f) (Uncurry g1) ->
  dominated (nFilterType domain M) (Uncurry f)
    (Fun' (fun p => Z.add (App g1 p) (App g2 p))).
Proof. prove_nary dominated_sum_r_nonneg_1. Qed.

Lemma dominated_sum_r_nonneg_2_nary domain M f g1 g2 :
  ultimately (nFilterType domain M) (Fun' (fun p => 0 <= App g1 p)) ->
  ultimately (nFilterType domain M) (Fun' (fun p => 0 <= App g2 p)) ->
  dominated (nFilterType domain M) (Uncurry f) (Uncurry g2) ->
  dominated (nFilterType domain M) (Uncurry f)
    (Fun' (fun p => Z.add (App g1 p) (App g2 p))).
Proof. prove_nary dominated_sum_r_nonneg_2. Qed.

(* ... *)

(******************************************************************************)

(* Applying n-ary dominated lemmas *)

Ltac dominated_domain G :=
  match G with
  | dominated ?F _ _ =>
    let L := domain_of_filter F in
    exact (Mk_domain_of_goal L)
  end.

Hint Extern 0 Domain_of_goal =>
  (mk_domain_getter dominated_domain) : domain_of_goal.

Goal
  dominated
    (product_filterType (product_filterType Z_filterType nat_filterType) Z_filterType)
    (fun '(_, _, _) => 2) (fun '(_, _, _) => 3).

  apply_nary dominated_cst_nary.
  omega.
Qed.

Goal
  dominated
    (product_filterType Z_filterType Z_filterType)
    (fun '(x, y) => 2*x + 3*y) (fun '(x, y) => x+y).
  apply_nary dominated_sum_nary.
  - admit.
  - admit.
  - apply_nary dominated_mul_cst_l_1_nary.
    apply dominated_reflexive.
  - apply_nary dominated_mul_cst_l_1_nary.
    apply dominated_reflexive.
Admitted.

(******************************************************************************)
(* FIXME: generalize to other arities. The lemmas themselves work with any
   arity, but not the hint patterns. *)

Hint Extern 1 (dominated _ (fun '(_, _) => ?a) (fun '(_, _) => ?b)) =>
  apply_nary dominated_cst_nary : dominated.
Hint Extern 2 (dominated _ (fun '(_, _) => ?c) _) =>
  apply_nary dominated_cst_limit_nary : dominated.
Hint Extern 2 (dominated _ (fun '(_, _) => Z.mul _ _) (fun '(_, _) => Z.mul _ _)) =>
  apply_nary dominated_mul_nary : dominated.
Hint Extern 2 (dominated _ (fun '(_, _) => Z.mul ?c1 _) (fun '(_, _) => Z.mul ?c2 _)) =>
  apply_nary dominated_mul_cst_nary : dominated.
Hint Extern 1 (dominated _ (fun '(_, _) => Z.mul ?c _) _) =>
  apply_nary dominated_mul_cst_l_1_nary : dominated.
Hint Extern 1 (dominated _ (fun '(_, _) => Z.mul _ ?c) _) =>
  apply_nary dominated_mul_cst_l_2_nary : dominated.
Hint Extern 2 (dominated _ _ (fun '(_, _) => Z.mul ?c _)) =>
  apply_nary dominated_mul_cst_r_1_nary : dominated.
Hint Extern 2 (dominated _ _ (fun '(_, _) => Z.mul _ ?c)) =>
  apply_nary dominated_mul_cst_r_2_nary : dominated.
Hint Extern 4 (dominated _ (fun '(_, _) => Z.max _ _) (fun '(_, _) => Z.max _ _)) =>
  apply_nary dominated_max_nary : dominated.
Hint Extern 2 (dominated _ (fun '(_, _) => Z.max _ _) _) =>
  apply_nary dominated_max_distr_nary : dominated.

Hint Extern 4 (dominated _ (fun '(_, _) => Z.add _ _) (fun '(_, _) => Z.add _ _)) =>
  apply_nary dominated_sum_nary : dominated.

Goal
  dominated
    (product_filterType Z_filterType Z_filterType)
    (fun '(x, y) => (2*x) * (3*y)) (fun '(x, y) => x*y).

  apply_nary dominated_mul_nary.
  - apply_nary dominated_mul_cst_l_1_nary.
    apply dominated_reflexive.
  - apply_nary dominated_mul_cst_l_1_nary.
    apply dominated_reflexive.
  Restart.
  dominated.
Qed.
