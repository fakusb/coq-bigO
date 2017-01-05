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
Require Import TLC.LibAxioms.

(* ---------------------------------------------------------------------------- *)

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

(* ---------------------------------------------------------------------------- *)

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

(* Ultimately pointwise inequality implies domination. *)

Lemma subrelation_ultimately_le_dominated f g :
  ultimately A (fun x => Z.abs (f x) <= Z.abs (g x)) ->
  dominated f g.
Proof.
  intros U. exists 1.
  apply (filter_closed_under_inclusion U).
  eauto with zarith.
Qed.

(* Domination is reflexive.
   (Howell's Property 4)
*)

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

Section DominatedLaws.

Variable A : filterType.

(* Howell's Property 3. *)

Lemma dominated_le_compat_r f g1 g2 :
  ultimately A (fun x => Z.abs (g1 x) <= Z.abs (g2 x)) ->
  dominated A f g1 ->
  dominated A f g2.
Proof.
  intros U D.
  apply dominated_transitive with g1; eauto.
  apply subrelation_ultimately_le_dominated. eauto.
Qed.

Lemma dominated_le_compat_l f1 f2 g :
  ultimately A (fun x => Z.abs (f2 x) <= Z.abs (f1 x)) ->
  dominated A f1 g ->
  dominated A f2 g.
Proof.
  intros U D.
  apply dominated_transitive with f1; eauto.
  apply subrelation_ultimately_le_dominated. eauto.
Qed.

(* Domination is compatible with mul.
   (Howell's Property 5)
*)

Lemma dominated_mul f1 f2 g1 g2 :
  dominated A f1 g1 ->
  dominated A f2 g2 ->
  dominated A (fun x => (f1 x) * (f2 x)) (fun x => (g1 x) * (g2 x)).
Proof.
  intros D1 D2.
  forwards (c1 & c1_pos & U_f1_g1): dominated_nonneg_const D1.
  forwards (c2 & c2_pos & U_f2_g2): dominated_nonneg_const D2.
  exists (c1 * c2).
  apply (filter_closed_under_intersection U_f1_g1 U_f2_g2).
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

(* Note: the conclusion of the above lemma could be rephrased as follows. *)

Goal
  forall (I J : filterType),
  forall f g : J -> Z,
  forall p : I -> J,
  dominated I (fun i => f (p i)) (fun i => g (p i)) <->
  dominated (image_filterType I p) f g.
Proof.
  intros. unfold dominated, image. tauto.
Qed.

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

Lemma pack_forall_pair_eq :
  forall (A B C : Type) (P Q : A * B -> C),
  (forall (a : A) (b : B), P (a, b) = Q (a, b)) -> (forall x, P x = Q x).
Proof.
  introv H. intros [? ?]. eauto.
Qed.

Module Product.

Section ProductLaws.

Variable A : filterType.

(* Property 2

  pour f, g: NxB → Z, si f ∈ O (g), f croissante sur la première composante,
  f, g positives sur [0, +infini[, alors
  λ(x, y). Σᵢ₌₀ˣ f(i, y) ∈ O(λ(x, y). Σᵢ₌₀ˣ g(i, y))
*)

Definition cumul (A : Type) (f : A * Z -> Z) (lo : Z) : A * Z -> Z :=
  fun an => let (a, n) := an in
  \big[Z.add]_(i <- interval lo n) f (a, i).

Definition cumul_with (h : Z -> Z) (A : Type) (f : A * Z -> Z) (lo : Z) :
  A * Z -> Z :=
  fun an => let (a, n) := an in
  \big[Z.add]_(i <- interval lo (h n)) f (a, i).

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

Lemma big_const_Z :
  forall lo hi c,
  \big[Z.add]_(_ <- interval lo hi) c = (hi - lo) * c.
Proof. admit. (* TODO *) Admitted.


(* Lemma dominated_cumul_ultimately_eq : *)
(*   forall (A : filterType) (f f' : A * Z -> Z) lo, *)
(*   ultimately (product_filterType A Z_filterType) (fun p => f p = f' p) -> *)
(*   dominated (product_filterType A Z_filterType) (cumul f lo) (cumul f' lo). *)
(* Proof. *)


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

Lemma dominated_big_sum :
  forall (f g : A * Z_filterType -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  ultimately A (fun a => forall i, lo <= i -> 0 <= g (a, i)) ->
  dominated (product_filterType A Z_filterType) f g ->
  (forall a, monotonic Z.le Z.le (fun i => f (a, i))) ->
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

  rewrite (cumul_split N) with (f := f); try omega.
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
    forwards x_le_N: Z.lt_le_incl x_lt_N.
    applys f_mon x_le_N. } Unfocus.

  rewrite big_const_Z.
  rewrite Hfg; try omega.

  asserts_rewrite
    (c * (N - lo + 1) * cumul g lo (a, n) =
     c * (N - lo + 1) * cumul g lo (a, N) +
     c * (N - lo) * cumul g N (a, n) +
     c * cumul g N (a, n)).
  { match goal with |- _ = ?r => remember r as rhs end.
    rewrite (cumul_split N); try omega.
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

Lemma dominated_big_sum_with (h : Z -> Z) :
  forall (f g : A * Z_filterType -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  ultimately A (fun a => forall i, lo <= i -> 0 <= g (a, i)) ->
  dominated (product_filterType A Z_filterType) f g ->
  (forall a, monotonic Z.le Z.le (fun i => f (a, i))) ->
  limit Z_filterType Z_filterType h ->
  dominated (product_filterType A Z_filterType)
    (cumul_with h f lo) (cumul_with h g lo).
Proof.
  introv Ufnonneg Ugnonneg dom_f_g f_mon h_lim.
  forwards~ dom_cumul: dominated_big_sum lo dom_f_g.
  eapply dominated_comp_eq.
  - exact dom_cumul.
  - eapply limit_liftr. apply h_lim.
  - intros [? ?]. reflexivity.
  - intros [? ?]. reflexivity.
Qed.

Lemma dominated_big_sum_eq :
  forall (f g sum_f sum_g : A * Z_filterType -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  ultimately A (fun a => forall i, lo <= i -> 0 <= g (a, i)) ->
  dominated (product_filterType A Z_filterType) f g ->
  (forall a, monotonic Z.le Z.le (fun i => f (a, i))) ->
  (forall a i, sum_f (a, i) = cumul f lo (a, i)) ->
  (forall a i, sum_g (a, i) = cumul g lo (a, i)) ->
  dominated (product_filterType A Z_filterType) sum_f sum_g.
Proof.
  introv ? ? ? ? sum_f_eq sum_g_eq.
  forwards: func_ext_dep (pack_forall_pair_eq sum_f_eq).
  forwards: func_ext_dep (pack_forall_pair_eq sum_g_eq).
  subst. applys dominated_big_sum; eauto.
Qed.

Lemma dominated_big_sum_with_eq (h : Z -> Z) :
  forall (f g sum_f sum_g : A * Z_filterType -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  ultimately A (fun a => forall i, lo <= i -> 0 <= g (a, i)) ->
  dominated (product_filterType A Z_filterType) f g ->
  (forall a, monotonic Z.le Z.le (fun i => f (a, i))) ->
  limit Z_filterType Z_filterType h ->
  (forall a i, sum_f (a, i) = cumul_with h f lo (a, i)) ->
  (forall a i, sum_g (a, i) = cumul_with h g lo (a, i)) ->
  dominated (product_filterType A Z_filterType) sum_f sum_g.
Proof.
  introv ? ? ? ? ? sum_f_eq sum_g_eq.
  forwards: func_ext_dep (pack_forall_pair_eq sum_f_eq).
  forwards: func_ext_dep (pack_forall_pair_eq sum_g_eq).
  subst. applys dominated_big_sum_with; eauto.
Qed.

Lemma dominated_big_sum_bound :
  forall (f : A * Z_filterType -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  (forall a, monotonic Z.le Z.le (fun i => f (a, i))) ->
  dominated (product_filterType A Z_filterType)
    (cumul f lo)
    (fun p => let (a, n) := p in n * f (a, n)).
Proof.
  introv U_f_nonneg f_mon.
  eexists (Z.max 1 (1 - lo)). rewrite productP. do 2 eexists. splits.
  { apply U_f_nonneg. }
  { apply (filter_conj_alt (ultimately_ge_Z 1) (ultimately_ge_Z lo)). }
  { intros a n f_nonneg [one_le_n lo_le_n].
    rewrite Z.abs_eq; [| apply big_nonneg_Z; eauto].
    rewrite Z.abs_eq; [| eauto with zarith].
    rewrite cumulP.
    rewrite big_covariant with
      (g := (fun p => f (a, n-1)));
    try typeclass.
    Focus 2.
    { intros x ?. apply f_mon.
      cut (x < n); [lia |]. applys* in_interval_hi. }
    Unfocus.

    rewrite big_const_Z.
    assert (f_le: f (a, n - 1) <= f (a, n)) by (apply f_mon; lia).
    rewrite f_le; [| lia].
    assert (f_an_nonneg: 0 <= f (a, n)) by (apply f_nonneg; lia).

    destruct (Z.le_gt_cases 0 lo) as [O_le_lo | lo_lt_O].
    { rewrite Z.max_l; [| lia]. ring_simplify. nia. }
    { rewrite Z.max_r; [| lia]. rewrite Z.mul_assoc.
      apply Zmult_le_compat_r; nia. } }
Qed.

Lemma dominated_big_sum_bound_with (h : Z -> Z) :
  forall (f : A * Z_filterType -> Z) (lo : Z),
  ultimately A (fun a => forall i, lo <= i -> 0 <= f (a, i)) ->
  (forall a, monotonic Z.le Z.le (fun i => f (a, i))) ->
  limit Z_filterType Z_filterType h ->
  dominated (product_filterType A Z_filterType)
    (cumul_with h f lo)
    (fun p => let (a, n) := p in h n * f (a, h n)).
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
  fun n => \big[Z.add]_(i <- interval lo (h n)) f i.

Lemma dominated_big_sum_with (h : Z -> Z) :
  forall (f g : Z_filterType -> Z) (lo : Z),
  (forall i, lo <= i -> 0 <= f i) ->
  (forall i, lo <= i -> 0 <= g i) ->
  dominated Z_filterType f g ->
  monotonic Z.le Z.le f ->
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType (cumul_with h f lo) (cumul_with h g lo).
Proof.
  introv f_nonneg g_nonneg dom_f_g f_mon h_lim.
  pose (f' := fun (nn : Z_filterType * Z) => let (_, n) := nn in f n).
  pose (g' := fun (nn : Z_filterType * Z) => let (_, n) := nn in g n).
  forwards~ D: Product.dominated_big_sum_with h f' g' lo.
  { apply filter_universe_alt. eauto. }
  { apply filter_universe_alt. eauto. }
  { destruct dom_f_g as [c U]. exists c.
    rewrite productP. exists (fun (_ : Z) => True). eexists. splits.
    { apply filter_universe. }
    { apply U. }
    eauto. }
  destruct D as [c U]. rewrite productP in U.
  destruct U as (P1 & P2 & UP1 & UP2 & U).
  exists c. revert UP1 UP2; filter_closed_under_intersection.
  introv (P1a & P2a). applys~ U P1a P2a.
Qed.

Lemma dominated_big_sum :
  forall (f g : Z_filterType -> Z) (lo : Z),
  (forall i, lo <= i -> 0 <= f i) ->
  (forall i, lo <= i -> 0 <= g i) ->
  dominated Z_filterType f g ->
  monotonic Z.le Z.le f ->
  dominated Z_filterType (cumul f lo) (cumul g lo).
Proof.
  intros. forwards~ D: dominated_big_sum_with (fun (i : Z) => i) f g lo.
  unfold limit, finer. simpl. intros. rewrite imageP. eauto.
Qed.

Lemma dominated_big_sum_eq :
  forall (f g sum_f sum_g : Z_filterType -> Z) (lo : Z),
  (forall i, lo <= i -> 0 <= f i) ->
  (forall i, lo <= i -> 0 <= g i) ->
  dominated Z_filterType f g ->
  monotonic Z.le Z.le f ->
  (forall i, sum_f i = cumul f lo i) ->
  (forall i, sum_g i = cumul g lo i) ->
  dominated Z_filterType sum_f sum_g.
Proof.
  introv ? ? ? ? sum_f_eq sum_g_eq.
  forwards: func_ext_dep sum_f_eq.
  forwards: func_ext_dep sum_g_eq.
  subst. applys dominated_big_sum; eauto.
Qed.

Lemma dominated_big_sum_with_eq (h : Z -> Z) :
  forall (f g sum_f sum_g : Z_filterType -> Z) (lo : Z),
  (forall i, lo <= i -> 0 <= f i) ->
  (forall i, lo <= i -> 0 <= g i) ->
  dominated Z_filterType f g ->
  monotonic Z.le Z.le f ->
  limit Z_filterType Z_filterType h ->
  (forall i, sum_f i = cumul_with h f lo i) ->
  (forall i, sum_g i = cumul_with h g lo i) ->
  dominated Z_filterType sum_f sum_g.
Proof.
  introv ? ? ? ? ? sum_f_eq sum_g_eq.
  forwards: func_ext_dep sum_f_eq.
  forwards: func_ext_dep sum_g_eq.
  subst. applys dominated_big_sum_with; eauto.
Qed.

Lemma dominated_big_sum_bound :
  forall (f : Z_filterType -> Z) (lo : Z),
  (forall i, lo <= i -> 0 <= f i) ->
  monotonic Z.le Z.le f ->
  dominated Z_filterType (cumul f lo) (fun n => n * f n).
Proof.
  introv f_nonneg f_mon.
  pose (f' := fun (p : Z_filterType * Z) => let (_, n) := p in f n).
  forwards~ D: Product.dominated_big_sum_bound f' lo.
  { apply filter_universe_alt. eauto. }
  simpl in *. destruct D as [c U]. rewrite productP in U.
  destruct U as (P1 & P2 & UP1 & UP2 & H).
  exists c. revert UP1 UP2; filter_closed_under_intersection.
  introv (? & ?). applys* H.
Qed.

Lemma dominated_big_sum_bound_with (h : Z -> Z) :
  forall (f : Z_filterType -> Z) (lo : Z),
  (forall i, lo <= i -> 0 <= f i) ->
  monotonic Z.le Z.le f ->
  limit Z_filterType Z_filterType h ->
  dominated Z_filterType (cumul_with h f lo) (fun n => h n * f (h n)).
Proof.
  introv U_f_nonneg f_mon lim_h.
  forwards~ dom_bound: dominated_big_sum_bound f lo.
  applys~ dominated_comp_eq dom_bound lim_h.
Qed.
