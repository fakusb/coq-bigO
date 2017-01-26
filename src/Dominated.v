Require Import TLC.LibTactics.

Require Import Coq.Logic.Classical_Pred_Type.
Require Import ZArith.
Local Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Psatz. (* nia *)
Require Export Filter.
Require Import Big.
Require Export LibFunOrd.
Require Import BigEnough.
Require Import TLC.LibAxioms.
Require Import TLC.LibLogic.

(* -------------------------------------------------------------------------- *)

(* If we have a filter on [A], then we can define a domination relation between
   functions of type [A -> Z]. *)

(* In principle, we could consider functions of type [A -> B], where [B] is an
   integral domain (see ssrnum.v). The (relative) integers form an integral
   domain; so do the reals. *)

(* [dominated f g] holds if and only if, for some constant [c], [f x] is
   ultimately bounded (in norm) by [c * g x]. We explicitly require [c] to be
   nonnegative, because this seems more convenient. *)

Section Domination.

Variable A : filterType.

Definition dominated (f g : A -> Z) :=
  exists c, ultimately A (fun x => Z.abs (f x) <= c * Z.abs (g x)).

(* This notion is analogous to [is_domin] in Coquelicot. *)

(* -------------------------------------------------------------------------- *)

(* The multiplicative constant of [dominated] can always be assumed to be
   non-negative.
*)

Lemma dominated_nonneg_const (f g : A -> Z) :
  dominated f g ->
  exists c, (0 <= c) /\ ultimately A (fun x => Z.abs (f x) <= c * Z.abs (g x)).
Proof.
  intros (c & U).
  destruct (Z.neg_nonneg_cases c) as [c_neg | c_nonneg].
  - exists 0. splits; [ omega |].
    revert U; filter_closed_under_intersection.
    intros. nia.
  - eauto.
Qed.

(* Pointwise inequality implies domination. *)

Lemma subrelation_le_dominated f g :
  (forall x, Z.abs (f x) <= Z.abs (g x)) ->
  dominated f g.
Proof.
  exists 1. apply filter_universe_alt. eauto with zarith.
Qed.

(* Asymptotic pointwise inequality implies domination. *)

Lemma subrelation_ultimately_le_dominated f g :
  ultimately A (fun x => Z.abs (f x) <= Z.abs (g x)) ->
  dominated f g.
Proof.
  intros U. exists 1.
  apply (filter_closed_under_inclusion U).
  eauto with zarith.
Qed.

(* Domination is reflexive. *)

Lemma dominated_reflexive f :
  dominated f f.
Proof.
  eauto using subrelation_le_dominated with zarith.
Qed.

(* Domination is transitive. *)

Lemma dominated_transitive f g h :
  dominated f g -> dominated g h -> dominated f h.
Proof.
  intros D1 D2.
  forwards (c1 & c1P & U1): dominated_nonneg_const D1.
  forwards (c2 & c2P & U2): dominated_nonneg_const D2.
  exists (c1 * c2).
  apply (filter_closed_under_intersection U1 U2).
  intros. nia.
Qed.

End Domination.
Arguments dominated : clear implicits.

Add Parametric Relation (A : filterType) : (A -> Z) (dominated A)
  reflexivity proved by (@dominated_reflexive A)
  transitivity proved by (@dominated_transitive A)
  as dominated_preorder.

Section DominatedLaws.

Variable A : filterType.

(* Domination is compatible with asymptotic pointwise inequality. *)

Lemma dominated_le f1 f2 g1 g2 :
  ultimately A (fun x => Z.abs (f2 x) <= Z.abs (f1 x)) ->
  ultimately A (fun x => Z.abs (g1 x) <= Z.abs (g2 x)) ->
  dominated A f1 g1 ->
  dominated A f2 g2.
Proof.
  intros Uf Ug D.
  assert (D': dominated A f1 g2).
  { rewrite D. applys subrelation_ultimately_le_dominated Ug. }
  rewrite <-D'. applys subrelation_ultimately_le_dominated Uf.
Qed.

Lemma dominated_le_l f1 f2 g :
  ultimately A (fun x => Z.abs (f2 x) <= Z.abs (f1 x)) ->
  dominated A f1 g ->
  dominated A f2 g.
Proof.
  intros U D. applys dominated_le U D.
  apply filter_universe_alt. intro; reflexivity.
Qed.

Lemma dominated_le_r f g1 g2 :
  ultimately A (fun x => Z.abs (g1 x) <= Z.abs (g2 x)) ->
  dominated A f g1 ->
  dominated A f g2.
Proof.
  intros U D. applys dominated_le U D.
  apply filter_universe_alt. intro; reflexivity.
Qed.

(* Asymptotic pointwise equality implies domination.

   This is trivially true, but comes in handy to "patch" non-asymptotic parts of
   a function that appear in a [dominated] goal, typically so that it has nicer
   properties.

   For example, this allows to change a goal

     [dominated _ f g]

   into

     [dominated _ (fun x => max 0 (f x)) g]

   when f is ultimately nonnegative. Now [fun x => max 0 (f x)] is always
   nonnegative, which may be more convenient to handle.
*)

Lemma dominated_ultimately_eq :
  forall (A : filterType) f f',
  ultimately A (fun x => f x = f' x) ->
  dominated A f f'.
Proof.
  introv U.
  exists 1. revert U; filter_closed_under_intersection.
  intros. lia.
Qed.

(* Domination is compatible with mul. *)

Lemma dominated_mul f1 f2 g1 g2 :
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => (f1 x) * (f2 x)) (fun x => (g1 x) * (g2 x)).
Proof.
  intros D1 D2.
  forwards (c1 & c1_pos & U1): dominated_nonneg_const D1.
  forwards (c2 & c2_pos & U2): dominated_nonneg_const D2.
  exists (c1 * c2).
  revert U1 U2; filter_closed_under_intersection.
  intros. rewrite !Z.abs_mul. nia.
Qed.

(* Dominated is compatible with max. *)

Lemma dominated_max f1 f2 g1 g2 :
  ultimately A (fun x => 0 <= g1 x) ->
  ultimately A (fun x => 0 <= g2 x) ->
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => Z.max (f1 x) (f2 x)) (fun x => Z.max (g1 x) (g2 x)).
Proof.
  intros P1 P2 D1 D2.
  forwards (c1 & c1_pos & U1): dominated_nonneg_const D1.
  forwards (c2 & c2_pos & U2): dominated_nonneg_const D2.
  exists (Z.max c1 c2).
  revert P1 P2 U1 U2; filter_closed_under_intersection.
  introv (? & ? & ? & ?). nia.
Qed.

(* One can "distribute" dominated over max, that is, a max is dominated by some
   function if both its components are dominated by it.
*)

Lemma dominated_max_distr f g h :
  dominated A f h ->
  dominated A g h ->
  dominated A (fun x => Z.max (f x) (g x)) h.
Proof.
  intros (c1 & U1) (c2 & U2).
  exists (Z.max c1 c2).
  revert U1 U2; filter_closed_under_intersection.
  intros. nia.
Qed.

(* A maximum is dominated by a sum, for ultimately nonnegative functions. *)

Lemma dominated_max_sum f g :
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  dominated A (fun x => Z.max (f x) (g x)) (fun x => f x + g x).
Proof.
  intros fpos gpos. exists 1.
  revert fpos gpos; filter_closed_under_intersection.
  intros. nia.
Qed.

(* Conversely, a sum is dominated by a maximum. [max] and [+] are asymptotically
   equivalent, for ultimately nonnegative functions. *)

Lemma dominated_sum_max f g :
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  dominated A (fun x => f x + g x) (fun x => Z.max (f x) (g x)).
Proof.
  intros fpos gpos. exists 2.
  revert fpos gpos; filter_closed_under_intersection.
  intros. nia.
Qed.

(* Domination is compatible with sum. *)

Lemma dominated_sum f1 f2 g1 g2 :
  ultimately A (fun x => 0 <= g1 x) ->
  ultimately A (fun x => 0 <= g2 x) ->
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => f1 x + f2 x) (fun x => g1 x + g2 x).
Proof.
  intros g1P g2P (c1 & u1) (c2 & u2).
  exists (Z.max c1 c2).
  revert g1P g2P u1 u2; filter_closed_under_intersection.
  intros. nia.
Qed.

Lemma dominated_sum_distr f g h :
  dominated A f h ->
  dominated A g h ->
  dominated A (fun x => f x + g x) h.
Proof.
  intros (c1 & U1) (c2 & U2).
  exists (c1 + c2).
  revert U1 U2; filter_closed_under_intersection.
  introv (? & ?). nia.
Qed.

(* This lemma offers a general mechanism for transforming the parameters
   of the asymptotic analysis. *)

(* Let [f] and [g] be functions of a parameter [j]. Assume [f] is dominated
   by [g]. Now, let [p] be a function of [I] into [J], which defines [j] in
   terms of [i]. Assume that [p i] becomes arbitrarily large as [i] grows.
   Then, [f . p] is dominated by [g . p]. These are functions of [i]. *)

(* The converse implication is false, as the image of the function [p] could
   lie in a subset of well-chosen values of [j] outside of which [f] is not
   dominated by [g]. *)

(* This lemma is analogous to [domin_comp] in Coquelicot. *)

Lemma dominated_comp :
  forall (I J : filterType) (f g : J -> Z),
  dominated J f g ->
  forall p : I -> J,
  limit I J p ->
  dominated I (fun i => f (p i)) (fun i => g (p i)).
Proof.
  (* The statement is really quite obvious, since [dominated] is defined
     in terms of [ultimately], and [limit _ _ p] means precisely that [p]
     maps [ultimately] to [ultimately]. *)
  introv ( c & u ) hp.
  (* The multiplicative factor is unaffected by the transformation. *)
  exists c.
  (* The hypothesis [u] states that for large enough [j], [f j] is
     bounded by [c] times [g j]. The hypothesis [hp] states that
     [p i] becomes arbitrarily large as [i] becomes large enough.
     The result follows directly from the combination of these
     hypotheses. *)
  eapply filter_closed_under_inclusion.
    eapply hp. eexact u.
    simpl. eauto.
Qed.

(* Alternative formulation of [dominated_comp], that doesn't require the goal to
   syntactically match the composition of [f] (resp. [g]) and [p].

   It only requires the user to prove the pointwise equality between the
   functions that appear in the goal and the composition of [f] (resp. [g]) and
   [p].
*)

Lemma dominated_comp_eq :
  forall (I J : filterType) (f g : J -> Z),
  dominated J f g ->
  forall (p : I -> J) (fp gp : I -> Z),
  limit I J p ->
  (forall i, fp i = f (p i)) ->
  (forall i, gp i = g (p i)) ->
  dominated I fp gp.
Proof.
  introv domfg limitp fp_eq gp_eq.
  forwards: func_ext_dep fp_eq.
  forwards: func_ext_dep gp_eq.
  subst. apply dominated_comp; eauto.
Qed.

(* Note: the conclusion of [dominated_comp] could be rephrased as follows. *)

Goal
  forall (I J : filterType),
  forall f g : J -> Z,
  forall p : I -> J,
  dominated I (fun i => f (p i)) (fun i => g (p i)) <->
  dominated (image_filterType I p) f g.
Proof.
  intros. unfold dominated, image. tauto.
Qed.

(* TODO: move *)

Lemma dominated_shift :
  forall f g x0,
  dominated Z_filterType f g <->
  dominated Z_filterType (fun x => f (Zshift x0 x)) (fun x => g (Zshift x0 x)).
Proof.
  intros. unfold dominated.
  split; intros (c & U); exists c. simpl in *.
  rewrite~ <-(ZshiftP x0) in U.
  rewrite~ <-(ZshiftP x0).
Qed.

End DominatedLaws.

(* ---------------------------------------------------------------------------- *)

(* TEMPORARY *)

Definition interval (lo hi : Z) : list Z.
Proof. admit. Admitted.

Lemma in_interval_lo :
  forall x lo hi,
  List.In x (interval lo hi) ->
  lo <= x.
Proof. admit. Admitted.

Lemma in_interval_hi :
  forall x lo hi,
  List.In x (interval lo hi) ->
  x < hi.
Proof. admit. Admitted.

Lemma big_const_Z :
  forall lo hi c,
  \big[Z.add]_(_ <- interval lo hi) c = (hi - lo) * c.
Proof. admit. (* TODO *) Admitted.

Lemma big_nonneg_Z :
  forall lo hi (f : Z -> Z),
  (forall x, lo <= x -> x < hi -> 0 <= f x) ->
  0 <= \big[Z.add]_(i <- interval lo hi) f i.
Proof.
  intros.
  rewrite <-big_covariant with
    (R := Z.le)
    (f := fun _ => 0);
  try typeclass.
  { rewrite big_const_Z. nia. }
  { introv HIn.
    forwards~: in_interval_lo HIn.
    forwards~: in_interval_hi HIn. }
Qed.

Lemma pack_forall_pair_eq :
  forall (A B C : Type) (P Q : A * B -> C),
  (forall (a : A) (b : B), P (a, b) = Q (a, b)) -> (forall x, P x = Q x).
Proof.
  introv H. intros [? ?]. eauto.
Qed.

Definition rel_after (A : Type) (a : A) (rel : A -> A -> Prop) : A -> A -> Prop :=
  fun (x y : A) => rel a x /\ rel a y /\ rel x y.

Module Product.

Section ProductLaws.

Variable A : filterType.

Definition cumul (A : Type) (f : A * Z -> Z) (lo : Z) : A * Z -> Z :=
  fun '(a, n) => \big[Z.add]_(i <- interval lo n) f (a, i).

Definition cumul_with (h : Z -> Z) (A : Type) (f : A * Z -> Z) (lo : Z) :
  A * Z -> Z :=
  fun '(a, n) => cumul f lo (a, h n).

Lemma cumulP :
  forall A (f : A * Z -> Z) lo a n,
  cumul f lo (a, n) = \big[Z.add]_(i <- interval lo n) f (a, i).
Proof. reflexivity. Qed.

Lemma cumul_withP :
  forall h A (f : A * Z -> Z) lo a n,
  cumul_with h f lo (a, n) = \big[Z.add]_(i <- interval lo (h n)) f (a, i).
Proof. reflexivity. Qed.

Lemma cumul_split (k : Z) :
  forall (A : Type) (f : A * Z -> Z) lo a n,
  Z.le lo k ->
  Z.le k n ->
  cumul f lo (a, n) = cumul f lo (a, k) + cumul f k (a, n).
Proof. admit. (* TODO *) Admitted.

Arguments cumul_split k [A] f [lo] a [n] _ _.

Lemma cumul_ge_single_term (k : Z) :
  forall (A : Type) (f : A * Z -> Z) lo a n,
  Z.le lo k ->
  Z.le k n ->
  f (a, k) <= cumul f lo (a, n).
Proof. admit. (* TODO *) Admitted.

Arguments cumul_ge_single_term k [A] f [lo] a [n] _ _ _.

Lemma big_op_compat :
  forall (A : Type) op `{Unit A op, Commutative A op, Associative A op} f1 f2 (xs : list A),
  \big[op]_(x <- xs) (op (f1 x) (f2 x)) =
  op (\big[op]_(x <- xs) (f1 x)) (\big[op]_(x <- xs) (f2 x)).
Proof. admit. Qed.

Ltac asserts_applys P :=
  let H := fresh in
  asserts H : P; [ | applys H; clear H ].

Ltac math_apply P :=
  asserts_applys P; [ intros; omega | .. ].

(* Under some assumptions, domination is compatible with [cumul] (i.e "big sum").

   Note that [f] and [g] are functions over [A * Z]. Moreover, their sums are
   also functions over [A * Z]. Domination is expressed wrt. the product filter
   of [A] and [Z], both for [f], [g] and their sums.

   Note that the hypothesis:

     [forall a, monotonic (rel_after lo Z.le) Z.le (fun i => f (a, i))]

   cannot be relaxed to:

     [forall a, ultimately (fun x =>
        monotonic (rel_after x Z.le) Z.le (fun i => f (a, i))].

   I.e, [f] really has to be monotonic starting at the summation index.

   For example, if we take:
     f (a, x) = x if x > 10, -a*x + 20 otherwise
     g (a, x) = x

   then:
     - dominated f g holds
     - for all a, f is monotonic for x big enough
     - however, for a fixed x > 10 and a going to infinity, Σf (a, x) goes
       to infinity while Σg (a, x) remains constant.
*)
Lemma dominated_big_sum :
  forall (f g : A * Z -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  ultimately A (fun a => forall i, lo <= i -> 0 <= g (a, i)) ->
  dominated (product_filterType A Z_filterType) f g ->
  (forall a, monotonic (rel_after lo Z.le) Z.le (fun i => f (a, i))) ->
  dominated (product_filterType A Z_filterType) (cumul f lo) (cumul g lo).
Proof.
  introv Uf_nonneg Ug_nonneg dom_f_g f_mon. simpl in *.
  forwards (c & c_pos & U_f_le_g): dominated_nonneg_const dom_f_g.
  clear dom_f_g.

  rewrite productP in U_f_le_g.
  destruct U_f_le_g as (P1 & P2 & UP1 & UP2 & H).

  rewrite (ZP_ultimately (filter_conj_alt (ultimately_ge_Z 0) (ultimately_ge_Z lo))) in UP2.
  destruct UP2 as (N & (Nnonneg & lo_le_N) & HN).

  exists (c * (N - lo + 1)). rewrite productP.
  revert Uf_nonneg Ug_nonneg UP1; filter_intersect; intro UP1'.

  eexists. exists (fun n => Z.le N n). splits.
  { apply UP1'. }
  { apply ultimately_ge_Z. }
  intros a n (f_nonneg & g_nonneg & P1_a) N_le_n.
  clear UP1'.

  asserts~ H' : (forall x, N <= x -> Z.abs (f (a, x)) <= c * Z.abs (g (a, x))).
  clear H HN P1_a.

  (* Product filter dance done. *)

  (* Eliminate [Z.abs] in the goal, as [f] and [g] are nonnegative. *)
  rewrite Z.abs_eq; [| apply big_nonneg_Z; eauto].
  rewrite Z.abs_eq; [| apply big_nonneg_Z; eauto].

  (* Eliminate [Z.abs] in H', for the same reason. *)
  assert (Hfg : (forall x, N <= x -> f (a, x) <= c * g (a, x))). {
    intros x N_le_x.
    specializes H' x N_le_x.
    rewrite Z.abs_eq in H'; [| apply f_nonneg; lia].
    rewrite Z.abs_eq in H'; [| apply g_nonneg; lia].
    assumption.
  }
  clear H'.

  (* Start proving the main inequality, by splitting [cumul]s, and rewriting
     under [Z.le]. *)

  rewrite (cumul_split N) with (f := f) by omega.
  rewrite cumulP with (f := f) (lo := N).
  rewrite big_covariant with
    (xs := interval N n)
    (g := (fun i => c * g (a, i)))
    (R := Z.le);
  try typeclass.
  Focus 2. eauto using in_interval_lo.

  rewrite <-big_map_distributive; try typeclass.
  rewrite <-cumulP with (f := g).
  rewrite cumulP with (f := f) (lo := lo).
  rewrite big_covariant with
    (xs := interval lo N)
    (g := (fun _ => f (a, N))); try typeclass.
  Focus 2.
  { introv inI.
    forwards x_lt_N: in_interval_hi inI.
    forwards lo_le_x: in_interval_lo inI.
    forwards x_le_N: Z.lt_le_incl x_lt_N.
    apply f_mon. unfold rel_after. lia. } Unfocus.

  rewrite big_const_Z.
  rewrite Hfg by omega.

  asserts_rewrite
    (c * (N - lo + 1) * cumul g lo (a, n) =
     c * (N - lo + 1) * cumul g lo (a, N) +
     c * (N - lo) * cumul g N (a, n) +
     c * cumul g N (a, n)).
  { match goal with |- _ = ?r => remember r as rhs end.
    rewrite (cumul_split N) by omega.
    rewrite Z.mul_add_distr_l.

    subst rhs. rewrite Zplus_assoc_reverse.
    apply Zplus_eq_compat; eauto.

    match goal with |- _ = ?r => remember r as rhs end.
    rewrite Z.mul_add_distr_l.
    rewrite Z.mul_add_distr_r.
    rewrite Z.mul_1_r.
    subst rhs. reflexivity. }

  apply Zplus_le_compat_r.

  asserts_rewrite <-(0 <= c * (N - lo + 1) * cumul g lo (a, N)). {
    apply Z.mul_nonneg_nonneg.
    { nia. }
    { apply big_nonneg_Z. intros.
      apply g_nonneg. lia. }
  }
  rewrite Zplus_0_l.
  rewrite Z.mul_assoc with (m := c).
  rewrite Z.mul_comm with (m := c).

  apply Zmult_le_compat_l.
  - apply cumul_ge_single_term; omega.
  - nia.
Qed.

(* Corollary of the previous lemma, where the summation is done up to some
   function [h], which is required to grow to infinity.
*)

Lemma dominated_big_sum_with (h : Z -> Z) :
  forall (f g : A * Z -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  ultimately A (fun a => forall i, lo <= i -> 0 <= g (a, i)) ->
  dominated (product_filterType A Z_filterType) f g ->
  (forall a, monotonic (rel_after lo Z.le) Z.le (fun i => f (a, i))) ->
  limit Z_filterType Z_filterType h ->
  dominated (product_filterType A Z_filterType)
    (cumul_with h f lo) (cumul_with h g lo).
Proof.
  introv Ufnonneg Ugnonneg dom_f_g f_mon h_lim.
  eapply dominated_comp_eq.
  - applys~ dominated_big_sum lo dom_f_g.
  - eapply limit_liftr. apply h_lim.
  - intros [? ?]. reflexivity.
  - intros [? ?]. reflexivity.
Qed.

(* The iterated sum of [f] is dominated by [f] times the number of
   iterations. *)

Lemma dominated_big_sum_bound :
  forall (f : A * Z -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  (forall a, monotonic (rel_after lo Z.le) Z.le (fun i => f (a, i))) ->
   dominated (product_filterType A Z_filterType)
    (cumul f lo)
    (fun '(a, n) => n * f (a, n)).
Proof.
  introv U_f_nonneg f_mon.
  eexists (Z.max 1 (1 - lo)). rewrite productP. do 2 eexists. splits.
  { apply U_f_nonneg. }
  { apply (filter_conj_alt (ultimately_ge_Z 1) (ultimately_ge_Z (lo + 1))). }
  { intros a n f_nonneg [one_le_n lo_le_n].
    rewrite Z.abs_eq; [| apply big_nonneg_Z; eauto].
    rewrite Z.abs_eq; [| eauto with zarith].
    rewrite cumulP.
    rewrite big_covariant with
      (g := (fun p => f (a, n-1)));
    try typeclass.
    Focus 2.
    { intros x I. apply f_mon. unfold rel_after.
      forwards~: in_interval_lo I. forwards~: in_interval_hi I. lia. }
    Unfocus.

    rewrite big_const_Z.
    assert (f_le: f (a, n - 1) <= f (a, n))
      by (apply f_mon; unfold rel_after; lia).
    rewrite f_le; [| lia].
    assert (f_an_nonneg: 0 <= f (a, n)) by (apply f_nonneg; lia).

    destruct (Z.le_gt_cases 0 lo) as [O_le_lo | lo_lt_O].
    { rewrite Z.max_l; [| lia]. ring_simplify. nia. }
    { rewrite Z.max_r; [| lia]. rewrite Z.mul_assoc.
      apply Zmult_le_compat_r; nia. } }
Qed.

Lemma dominated_big_sum_bound_with (h : Z -> Z) :
  forall (f : A * Z -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  (forall a, monotonic (rel_after lo Z.le) Z.le (fun i => f (a, i))) ->
  limit Z_filterType Z_filterType h ->
  dominated (product_filterType A Z_filterType)
    (cumul_with h f lo)
    (fun '(a, n) => h n * f (a, h n)).
Proof.
  introv U_f_nonneg f_mon lim_h.
  forwards~ dom_bound: dominated_big_sum_bound f lo.
  applys dominated_comp_eq dom_bound.
  - eapply limit_liftr. exact lim_h.
  - intros [? ?]. reflexivity.
  - intros [? ?]. reflexivity.
Qed.

End ProductLaws.

End Product.

Definition cumul (f : Z -> Z) (lo : Z) : Z -> Z :=
  fun n => \big[Z.add]_(i <- interval lo n) f i.

Definition cumul_with (h : Z -> Z) (f : Z -> Z) (lo : Z) : Z -> Z :=
  fun n => cumul f lo (h n).

Lemma cumulP :
  forall (f : Z -> Z) lo n,
  cumul f lo n = \big[Z.add]_(i <- interval lo n) f i.
Proof. reflexivity. Qed.

(* TEMPORARY bigops *)

Lemma cumul_split (k : Z) :
  forall (f : Z -> Z) lo n,
  Z.le lo k ->
  Z.le k n ->
  cumul f lo n = cumul f lo k + cumul f k n.
Proof. admit. (* TODO *) Admitted.

Arguments cumul_split k f [lo] [n] _ _.

(* TEMPORARY move? *)
Ltac asserts_applys P :=
  let H := fresh in
  asserts H : P; [ | applys H; clear H ].

Ltac math_apply P :=
  asserts_applys P; [ intros; omega | .. ].

(* Asymptotic pointwise equality implies domination of iterated sums.

   Similarly to [dominated_ultimately_eq], this allows to "patch"
   non-asymptotic parts of functions, which iterated sum appears in
   a dominated goal.

   Note:
   The [ultimately (fun x => 0 < f' x)] assumption is really required.

   Otherwise, take [f := fun x => if x = 0 then 1 else 0] and [f' := 0].

   [ultimately (fun x => f x = f' x)] holds, but
   [dominated (cumul f 0) (cumul f' 0)] doesn't.

   This is not completely tight; [often (fun x => 0 < f' x)] may be enough.
   However, in practice the functions we handle tend to be ultimately
   monotonic, in which case this boils down to the same thing.
*)
Lemma dominated_cumul_ultimately_eq :
  forall (f f' : Z -> Z) lo,
  ultimately Z_filterType (fun x => f x = f' x) ->
  ultimately Z_filterType (fun x => 0 < f' x) ->
  dominated Z_filterType (cumul f lo) (cumul f' lo).
Proof.
  introv.
  generalize (ultimately_ge_Z lo). filter_intersect. rewrite ZP.
  intros (N & HN).

  exists 2. rewrite ZP.
  exists_big n0 Z. intros n n0_le_n.

  assert (N_le_n : N <= n) by (rewrite <-n0_le_n; big).
  assert (lo_le_N : lo <= N) by (apply HN; omega).

  assert (cumul_f'_ge_n : forall n, N <= n -> n - N <= cumul f' N n). {
    assert (
      cumul_minus_one : forall f lo x,
        cumul f lo x = (x - lo) + cumul (fun x => f x - 1) lo x
    ).
    { admit. }

    assert (cumul_minus_ge_0 :
      forall n, 0 <= cumul (fun x => f' x - 1) N n
    ).
    { intros. unfold cumul. apply big_nonneg_Z.
      intros x ? ?. forwards~ (? & ? & ?): HN x ___.
      omega. }

    intros x H.
    rewrite cumul_minus_one.
    rewrite <-cumul_minus_ge_0. omega.
  }

  assert (cumul_past_N_ge_0 : forall n, 0 <= cumul f N n).
  { intros. unfold cumul. apply big_nonneg_Z.
    intros x ? ?. forwards~ (? & ? & ?) : HN x ___.
    omega. }

  assert (cumul_past_N_eq : forall n,
    N <= n -> cumul f' N n = cumul f N n
  ).
  { intros. unfold cumul. apply big_covariant; try typeclass.
    introv I. symmetry. apply HN. applys* in_interval_lo. }

  assert (cumul_f'_pos : 0 <= cumul f' lo n). {
    rewrite (cumul_split N) by auto.
    rewrite <-cumul_f'_ge_n; auto.
    math_apply (forall a b c, c - a <= b -> 0 <= a + (b - c)).
    rewrite <-n0_le_n. big.
  }

  rewrite Z.abs_eq with (cumul f' lo n) by auto.
  rewrite (cumul_split N) with (f := f) by auto.
  rewrite Z.abs_triangle.
  rewrite Z.abs_eq with (cumul f N n) by auto.
  rewrite (cumul_split N) with (f := f') by auto.
  rewrite Z.mul_add_distr_l.
  rewrite cumul_past_N_eq by auto.
  math_apply (forall a b c, a <= c + b -> a + b <= c + 2 * b).
  rewrite <-cumul_past_N_eq by auto.
  rewrite <-cumul_f'_ge_n by auto.
  math_apply (forall a b c d, a - b + d <= c -> a <= b + (c - d)).
  rewrite <-n0_le_n. big.
  close.
Qed.

(* We could deduce a [dominated_big_sum] lemma for the one parameter case from
   [Product.dominated_big_sum], by instantiating [A] by [unit].

   However, thanks to the previous lemma [dominated_cumul_ultimately_eq], we can
   do better, and replace the monotonocity hypothesis by a "ultimately positive"
   hypothesis.
*)
Lemma dominated_big_sum :
  forall (f g : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun i => 0 < f i) ->
  ultimately Z_filterType (fun i => 0 < g i) ->
  dominated Z_filterType f g ->
  dominated Z_filterType (cumul f lo) (cumul g lo).
Proof.
  introv Uf_pos Ug_pos dom_f_g. simpl in *.
  forwards (c & c_pos & U_f_le_g): dominated_nonneg_const dom_f_g.
  clear dom_f_g.

  revert Uf_pos Ug_pos U_f_le_g. filter_intersect.
  rewrite (ZP_ultimately (filter_conj_alt (ultimately_ge_Z 0) (ultimately_ge_Z lo))).
  intros (N & (N_nonneg & lo_le_N) & HN).

  (* "patch" [f] and [g] to make them equal to [0] between [lo] and [N].
     [dominated_cumul_ultimately_eq] allows us to do precisely that. *)

  pose (f' := fun x => If lo <= x < N then 0 else f x).
  pose (g' := fun x => If lo <= x < N then 0 else g x).
  apply dominated_transitive with (cumul f' lo).
  { apply dominated_cumul_ultimately_eq;
    subst f'; simpl; rewrite ZP; exists N; intros.
    { cases_if; [omega | tauto]. }
    { cases_if; [omega | applys~ HN]. } }
  apply dominated_transitive with (cumul g' lo).
  Focus 2.
  { apply dominated_cumul_ultimately_eq;
    subst g'; simpl; rewrite ZP; exists N; intros.
    cases_if; [omega | tauto]. applys~ HN. }
  Unfocus.

  (* Instantiate the big-O constant, and do some cleanup. *)

  exists c. rewrite ZP. exists N. intros n N_le_n.

  assert (f_g_nonneg : forall n, N <= n -> 0 <= f n /\ 0 <= g n).
  { intros. splits; apply Z.lt_le_incl; applys~ HN. }
  assert (cumul_f'_nonneg : forall n, 0 <= cumul f' lo n).
  { intros. subst f'. apply big_nonneg_Z. intros.
    cases_if~; [| apply f_g_nonneg]; auto with zarith. }
  assert (cumul_g'_nonneg : forall n1 n2, lo <= n1 -> 0 <= cumul g' n1 n2).
  { intros. subst g'. apply big_nonneg_Z. intros.
    cases_if~; [| apply f_g_nonneg]; auto with zarith. }

  (* Eliminate [Z.abs] in the goal and HN, as [f] and [g] are nonnegative. *)
  rewrite Z.abs_eq by auto.
  rewrite Z.abs_eq by (apply cumul_g'_nonneg; auto with zarith).
  assert (Hf'g' : forall x, N <= x -> f' x <= c * (g' x)). {
    intros x N_le_x. specializes HN x N_le_x.
    rewrite Z.abs_eq in HN by applys~ f_g_nonneg.
    rewrite Z.abs_eq in HN by applys~ f_g_nonneg.
    subst f' g'. simpl. cases_if~; omega.
  }
  clear HN.

  (* Start proving the main inequality by splitting [cumul]s.
     [cumul f' lo N] and [cumul g' lo N] are equal to 0, and
     after [N], [f x <= c * g x] holds.
  *)

  rewrite (cumul_split N) with (f := f') by omega.
  rewrite cumulP with (f := f') (lo := lo).
  rewrite big_covariant with (g := fun _ => 0) (R := eq); try typeclass.
  Focus 2.
  { introv I. forwards: in_interval_lo I. forwards: in_interval_hi I.
    subst f'; simpl. cases_if~. omega. }
  Unfocus.
  rewrite big_const_Z. ring_simplify.

  rewrite (cumul_split N) with (f := g') by omega.
  rewrite Z.mul_add_distr_l.
  rewrite cumulP with (f := g') (lo := lo).
  rewrite big_covariant with (g := fun _ => 0) (R := eq); try typeclass.
  Focus 2.
  { introv I. forwards: in_interval_lo I. forwards: in_interval_hi I.
    subst g'; simpl. cases_if~. omega. }
  Unfocus.
  rewrite big_const_Z. ring_simplify.

  rewrite cumulP with (f := f').
  rewrite big_covariant with (R := Z.le) (g := (fun i => c * g' i));
  try typeclass.
  Focus 2. { intros. apply Hf'g'. applys* in_interval_lo. } Unfocus.
  rewrite <-big_map_distributive; try typeclass.
  rewrite <-cumulP.
  omega.
Qed.

Lemma dominated_big_sum_with (h : Z -> Z) :
  forall (f g : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun i => 0 < f i) ->
  ultimately Z_filterType (fun i => 0 < g i) ->
  dominated Z_filterType f g ->
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType (cumul_with h f lo) (cumul_with h g lo).
Proof.
  introv Ufpos Ugpos dom_f_g h_lim.
  eapply dominated_comp_eq.
  - applys~ dominated_big_sum lo dom_f_g.
  - apply h_lim.
  - reflexivity.
  - reflexivity.
Qed.

Lemma dominated_big_sum_bound :
  forall (f : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun i => 0 < f i) ->
  ultimately Z_filterType (fun i => monotonic (rel_after i Z.le) Z.le f) ->
  dominated Z_filterType (cumul f lo) (fun n => n * f n).
Proof.
  introv. generalize (ultimately_ge_Z lo). filter_intersect.
  rewrite ZP. intros (N & HN).

  (* "Patch" [f] to be always monotonic. *)
  pose (f' := fun x => If x < N then f N else f x).

  eapply dominated_transitive with (cumul f' lo).
  { apply dominated_cumul_ultimately_eq; exists N; intros; subst f'; simpl.
    cases_if~; omega.
    cases_if~; applys~ HN. auto with zarith. }

  eapply dominated_transitive with (fun n => n * f' n).
  Focus 2.
  { apply dominated_ultimately_eq; exists N; intros; subst f'; simpl.
    cases_if~; omega. }
  Unfocus.

  (* Use the version of this lemma on product filters. *)

  pose (f'' := fun '((_, n) : Z * Z) => f' n).

  forwards~ D: @Product.dominated_big_sum_bound Z_filterType f'' lo.
  { apply filter_universe_alt. intros. subst f'' f'. simpl.
    cases_if; apply Z.lt_le_incl; apply HN; omega. }
  { intros. subst f'' f'. simpl.
    specializes HN N ___. omega. destruct HN as (? & ? & fmon).
    unfold monotonic, rel_after in *. intros.
    cases_if; cases_if; auto with zarith. }
  simpl in *. destruct D as [c U]. rewrite productP in U.
  destruct U as (P1 & P2 & UP1 & UP2 & H).
  exists c. revert UP1 UP2; filter_closed_under_intersection.
  introv (? & ?). applys* H.
Qed.

Lemma dominated_big_sum_bound_with (h : Z -> Z) :
  forall (f : Z -> Z) (lo : Z),
  ultimately Z_filterType (fun i => 0 < f i) ->
  ultimately Z_filterType (fun i => monotonic (rel_after i Z.le) Z.le f) ->
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType (cumul_with h f lo) (fun n => h n * f (h n)).
Proof.
  introv U_f_nonneg f_mon lim_h.
  forwards~ dom_bound: dominated_big_sum_bound f lo.
  applys~ dominated_comp_eq dom_bound lim_h.
Qed.

(* Special case of [dominated_big_sum_bound], where the function in the big sum
   is constant.
*)

Lemma dominated_big_sum_cst_bound : forall (c : Z) (lo : Z),
  dominated Z_filterType (cumul (fun (_ : Z) => c) lo) (fun n => n).
Proof.
  intros. exists_big k Z.
  generalize (ultimately_ge_Z 1) (ultimately_ge_Z lo); filter_closed_under_intersection.
  intros x (one_le_x & lo_le_x).
  rewrite cumulP. rewrite big_const_Z.
  rewrite Z.mul_sub_distr_r.
  cut (Z.abs c + Z.abs (lo * c) <= k). { generalize k; clear k. intros. nia. }
  big. close.
Qed.

Lemma dominated_big_sum_cst_bound_with (h : Z -> Z) : forall (c : Z) (lo : Z),
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType (cumul_with h (fun (_ : Z) => c) lo) (fun n => h n).
Proof.
  introv lim_h.
  forwards D: dominated_big_sum_cst_bound c lo.
  applys~ dominated_comp_eq D lim_h.
Qed.