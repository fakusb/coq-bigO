Require Import TLC.LibTactics.

Require Import Coq.Logic.Classical_Pred_Type.
Require Import ZArith.
Local Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Psatz. (* nia *)
Require Import Filter.
Require Import Big.
Require Import LibFunOrd.

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
  exists c, (0 <= c) /\ ultimately A (fun x => Z.abs (f x) <= c * Z.abs (g x)).

(* This notion is analogous to [is_domin] in Coquelicot. *)

(* ---------------------------------------------------------------------------- *)

(* Pointwise inequality implies domination. *)

Lemma subrelation_le_dominated f g :
  (forall x, Z.abs (f x) <= Z.abs (g x)) ->
  dominated f g.
Proof.
  exists 1. split; [ eauto with zarith |].
  apply filter_universe_alt. eauto with zarith.
Qed.

(* Ultimately pointwise inequality implies domination. *)

Lemma subrelation_ultimately_le_dominated f g :
  ultimately A (fun x => Z.abs (f x) <= Z.abs (g x)) ->
  dominated f g.
Proof.
  intros U. exists 1. split; [ eauto with zarith |].
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
  intros (c1 & c1P & U1) (c2 & c2P & U2).
  exists (c1 * c2).
  split; [ eauto with zarith |].
  apply (filter_closed_under_intersection U1 U2).
  intros. nia.
Qed.

End Domination.
Arguments dominated : clear implicits.

Section DominatedLaws.

Variable A : filterType.

(* Howell's Property 3. *)

Lemma dominated_le_transitive f g1 g2 :
  ultimately A (fun x => Z.abs (g1 x) <= Z.abs (g2 x)) ->
  dominated A f g1 ->
  dominated A f g2.
Proof.
  intros U D.
  apply dominated_transitive with g1; eauto.
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
  intros (c1 & c1_pos & U_f1_g1) (c2 & c2_pos & U_f2_g2).
  exists (c1 * c2). split; [ eauto with zarith |].
  apply (filter_closed_under_intersection U_f1_g1 U_f2_g2).
  intros. nia.
Qed.

(* A maximum is dominated by a sum, for ultimately nonnegative functions. *)

Lemma dominated_max_sum f g :
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  dominated A (fun x => Z.max (f x) (g x)) (fun x => f x + g x).
Proof.
  intros fpos gpos. exists 1. split; [ eauto with zarith |].
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
  intros fpos gpos. exists 2. split; eauto with zarith.
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
  intros g1P g2P (c1 & c1P & u1) (c2 & c2P & u2).
  exists (Z.max c1 c2).
  split; [ nia |].
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
  forall (I J: filterType) (f g: J -> Z),
  dominated J f g ->
  forall p : I -> J,
  limit I J p ->
  dominated I (fun i => f (p i)) (fun i => g (p i)).
Proof.
  (* The statement is really quite obvious, since [dominated] is defined
     in terms of [ultimately], and [limit _ _ p] means precisely that [p]
     maps [ultimately] to [ultimately]. *)
  introv ( c & cpos & u ) hp.
  (* The multiplicative factor is unaffected by the transformation. *)
  exists c. split; eauto.
  (* The hypothesis [u] states that for large enough [j], [f j] is
     bounded by [c] times [g j]. The hypothesis [hp] states that
     [p i] becomes arbitrarily large as [i] becomes large enough.
     The result follows directly from the combination of these
     hypotheses. *)
  eapply filter_closed_under_inclusion.
    eapply hp. eexact u.
    simpl. eauto.
Qed.

(* Note: the conclusion of the above lemma could be rephrased as follows. *)

Goal
  forall (I J: filterType),
  forall f g : J -> Z,
  forall p : I -> J,
  dominated I (fun i => f (p i)) (fun i => g (p i)) <->
  dominated (image_filterType I p) f g.
Proof.
  intros. unfold dominated, image. tauto.
Qed.


(* Property 2

  pour f, g: NxB → R⁺, si ultimately x, g(x) > 0 et f ∈ O (g), alors
  λ(x, y). Σᵢ₌₀ˣ f(i, y) ∈ O(λ(x, y). Σᵢ₌₀ˣ g(i, y))
*)

Obligation Tactic := try solve [ intros; ring_simplify; omega ].
Program Instance unit_plus : Unit Z.add := { unit := 0 }.
Program Instance commutative_plus : Commutative Z.add.
Program Instance associative_plus : Associative Z.add.
Program Instance unit_mult : Unit Z.mul := { unit := 1 }.
Program Instance commutative_mult : Commutative Z.mul.
Program Instance associative_mult : Associative Z.mul.

Definition cumul (A: Type) (lo: nat) (f: A * nat -> Z) : A * nat -> Z :=
  fun an => let (a, n) := an in
  \big[Z.add]_(i <- interval lo n) f (a, i).

Lemma cumulP :
  forall A lo (f: A * nat -> Z) a n,
  cumul lo f (a, n) = \big[Z.add]_(i <- interval lo n) f (a, i).
Proof. reflexivity. Qed.

Lemma cumul_split (k: nat) :
  forall (A: Type) lo (f : A * nat -> Z) a n,
  le lo k ->
  le k n ->
  cumul lo f (a, n) = cumul lo f (a, k)%nat + cumul k f (a, n).
Proof. admit. (* TODO *) Admitted.

Arguments cumul_split k [A] [lo] f a [n] _ _.

Lemma cumul_ge_single_term (k: nat) :
  forall (A: Type) lo (f : A * nat -> Z) a n,
  le lo k ->
  le k n ->
  f (a, k) <= cumul lo f (a, n).
Proof. admit. (* TODO *) Admitted.

Arguments cumul_ge_single_term k [A] [lo] f a [n] _ _ _.

Lemma big_const_Z :
  forall lo hi c,
  \big[Z.add]_(_ <- interval lo hi) c = (Z.of_nat hi - Z.of_nat lo) * c.
Proof. admit. (* TODO *) Admitted.


Require Export Coq.Setoids.Setoid. (* required for [rewrite] *)
Require Export Coq.Classes.Morphisms.

Program Instance proper_Zplus: Proper (Z.le ++> Z.le ++> Z.le) Z.add.
Next Obligation.
  intros x1 y1 h1 x2 y2 h2. omega.
Qed.

Goal (forall a b c d, a <= b -> c + b <= c + d -> c + a <= c + d).
Proof.
  introv a_le_b cb_le_cd.
  rewrite a_le_b.
  assumption.
Qed.

Program Instance proper_Zmult_left:
  forall x, 0 <= x ->
  Proper (Z.le ++> Z.le) (Z.mul x).
Next Obligation.
  intros x1 y1 h1. nia.
Qed.

(* Program Instance proper_Zmult_right: *)
(*   forall y, 0 <= y -> *)
(*   forall y, Proper (Z.le ++> Z.le) (fun x => Z.mul x y). *)
(* Next Obligation. *)
(*   intros x2 y2 h2. nia. *)
(* Qed. *)

Hint Extern 100 (0 <= _) => assumption : typeclass_instances.

Goal forall a b c d, a <= b -> 0 <= c -> c * b <= c * d -> c * a <= c * d.
Proof.
  introv a_le_b O_le_c cb_le_cd.
  rewrite a_le_b.
  assumption.
Qed.

(* Goal forall a b c d, a <= b -> 0 <= c -> b * c <= d * c -> a * c <= d * c. *)
(* introv a_le_b O_le_c bc_le_dc. *)
(* rewrite a_le_b. *)

Obligation Tactic := intros; simpl; ring_simplify; omega.
Program Instance distributive_mul_add : Distributive Z.mul Z.add.

Lemma big_nonneg_Z :
  forall lo hi (f: nat -> Z),
  (forall x, 0 <= f x) ->
  0 <= \big[Z.add]_(i <- interval lo hi) f i.
Proof.
  intros.
  rewrite <-big_covariant with
    (R := Z.le)
    (f := fun (_:nat) => 0);
  try typeclass.
  rewrite big_const_Z. nia.
Qed.

Lemma dominated_big_sum :
  forall (A: filterType) (f g : A * nat_filterType -> Z),
    (forall x, 0 <= f x) ->
    (forall x, 0 <= g x) ->
    dominated (product_filterType A nat_filterType) f g ->
    (forall a, monotonic le Z.le (fun i => f (a, i))) ->
    dominated (product_filterType A nat_filterType) (cumul 0 f) (cumul 0 g).
Proof.
  introv f_nonneg g_nonneg dom_f_g f_mon. simpl in *.
  destruct dom_f_g as (c & c_pos & U_f_le_g).

  rewrite productP in U_f_le_g.
  destruct U_f_le_g as (P1 & P2 & UP1 & UP2 & H).
  rewrite natP in UP2. destruct UP2 as [N HN].

  pose (N_ := Z.of_nat N).
  exists (c * (N_ + 1)). splits; [ subst N_; nia |].
  rewrite productP.

  exists P1 (fun n => le N n). splits~.
  { rewrite natP. exists N. eauto. }

  intros a n P1_a N_le_n.
  rewrite Z.abs_eq; [| apply big_nonneg_Z; eauto].
  rewrite Z.abs_eq; [| apply big_nonneg_Z; eauto].

  rewrite (cumul_split N) with (f := f); try omega.
  assert (Hfg: forall i, le N i -> f (a, i) <= c * g (a, i)). {
    introv N_le_i.
    forwards HN_i: HN N_le_i.
    forwards H': H P1_a HN_i.
    do 2 (rewrite Z.abs_eq in H'); eauto.
  }

  rewrite cumulP with (f := f) (lo := N).
  rewrite big_covariant with
    (xs := interval N n)
    (g := (fun i => c * g (a, i)))
    (R := Z.le);
  try typeclass.
  Focus 2. eauto using in_interval_lo.

  rewrite <-big_map_distributive; try typeclass.
  rewrite cumulP with (f := f) (lo := 0%nat).
  rewrite big_covariant with
    (xs := interval 0 N)
    (g := (fun _ => f (a, N))); try typeclass.
  Focus 2.
  { introv inI.
    forwards x_lt_N: in_interval_hi inI.
    forwards x_le_N: Nat.lt_le_incl x_lt_N.
    applys f_mon x_le_N. } Unfocus.

  rewrite big_const_Z. fold N_. rewrite Z.sub_0_r.
  assert (O_le_N: 0 <= N_) by (subst N_; lia).
  rewrite Hfg; try omega. clear O_le_N. (* meh *)
  rewrite <-cumulP.

  assert (split_cumul_g:
            c * (N_ + 1) * cumul 0 g (a, n) =
            c * (N_ + 1) * cumul 0 g (a, N) +
            c * N_ * cumul N g (a, n) +
            c * cumul N g (a, n)).
  { match goal with |- _ = ?r => remember r as rhs end.
    rewrite (cumul_split N); try omega.
    rewrite Z.mul_add_distr_l.

    subst rhs. rewrite Zplus_assoc_reverse.
    apply Zplus_eq_compat; eauto.

    match goal with |- _ = ?r => remember r as rhs end.
    rewrite Z.mul_add_distr_l.
    rewrite Z.mul_add_distr_r.
    ring_simplify.
    subst rhs. reflexivity. }

  rewrite split_cumul_g.
  apply Zplus_le_compat_r.

  assert (g_le_cumul: c * N_ * g (a, N) <= c * N_ * cumul N g (a, n)).
  { apply Zmult_le_compat_l.
    - apply cumul_ge_single_term; omega.
    - subst N_. nia. }

  rewrite <-g_le_cumul.
  assert (cancel_lemma: forall a b c, a = c -> 0 <= b -> a <= b + c)
    by (intros; nia).
  apply cancel_lemma. nia.
  apply Z.mul_nonneg_nonneg.
  { subst N_. nia. }
  { apply big_nonneg_Z. eauto. }
Qed.

End DominatedLaws.
