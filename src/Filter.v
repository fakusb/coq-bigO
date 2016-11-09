Require Import Coq.Logic.Classical_Pred_Type.
Require Import Arith. (* Lemmas about Nat.max *)
Require Import Relations. (* reflexive, transitive *)
Require Import Omega.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TEMPORARY *)
Axiom prop_ext:
  forall P Q : Prop,
  P <-> Q -> P = Q.

Module Filter.

(* We could in principle perform this construction using [bool] instead of [Prop]
   as the codomain of predicates. However, [bool] does not support quantification
   over an infinite set, whereas [Prop] does. *)

Notation pred A := (A -> Prop).

(* ---------------------------------------------------------------------------- *)

(* Technically, a filter is a nonempty set of nonempty subsets of A, which is
   closed under inclusion and (finite) intersection. *)

Definition filter A := pred (pred A).

(* Let us write [ult] for a filter. (This is short for ``ultimately''.)
   A filter is a modality: if [P] is a predicate, then [ult P] is a
   proposition. In other words, a filter is a quantifier: if [P] is a
   predicate, then [ult (fun x => P x)] is a proposition. Intuitively,
   this proposition means that ``ultimately'' [P] holds. In other words,
   for every sufficiently ''large'' [x], [P] holds. *)

Record filterMixin A (ult : filter A) := FilterMixin {

  (* A filter is nonempty. In fact, it contains the universe. In other words,
     [ultimately x => True] is just [True]. Thus, the quantifier [ultimately]
     is weaker than a universal quantifier: [forall x, P x] implies
     [ultimately x, P x]. *)
  _ :
    ult (fun _ => True);

  (* A filter does not have the empty set as a member. In other words, every
     member of the filter is nonempty. Thus, the quantifier [ultimately] is
     stronger than an existential quantifier: [ultimately x, P x] implies
     [exists x, P x]. *)
  _ :
    forall P, ult P -> exists a, P a;

  (* A filter is closed by inclusion and by (finite) intersection. In other
     words, the quantifier [ultimately] is covariant and commutes with (finite)
     conjunction. The last condition means that [ultimately] is universal in
     nature, as opposed to existential. In particular, the universal quantifier
     can be viewed as a filter, but the existential quantifier cannot. *)
  _ :
    forall P1 P2 P : pred A,
    ult P1 ->
    ult P2 ->
    (forall a, P1 a -> P2 a -> P a) ->
    ult P

}.

Record filterType := FilterType {
  sort :> Type;
  ultimately : filter sort;
  mixin : filterMixin ultimately
}.

Arguments ultimately : clear implicits.

(* ---------------------------------------------------------------------------- *)

Section Laws.

Variable A : filterType.

Implicit Type P : pred A.

(* Re-statement of the defining laws. *)

Lemma filter_universe:
  ultimately A (fun _ => True).
Proof. destruct A as [? ? M]. destruct M. eauto. Qed.

Lemma filter_member_nonempty:
  forall P, ultimately A P -> exists a, P a.
Proof. destruct A as [? ? M]. destruct M. eauto. Qed.

Lemma filter_closed_under_intersection:
  forall P1 P2 P,
  ultimately A P1 ->
  ultimately A P2 ->
  (forall a, P1 a -> P2 a -> P a) ->
  ultimately A P.
Proof. destruct A as [? ? M]. destruct M. eauto. Qed.

(* A filter is closed by subset inclusion.
   That is, [ultimately] is covariant. *)

Lemma filter_closed_under_inclusion:
  forall P1 P2,
  ultimately A P1 ->
  (forall a, P1 a -> P2 a) ->
  ultimately A P2.
Proof.
  eauto using filter_closed_under_intersection.
Qed.

(* If [P] holds everywhere, then [ultimately P] holds. *)

Lemma filter_universe_alt:
  forall P,
  (forall a, P a) ->
  ultimately A P.
Proof.
  (* A filter is nonempty, so it has one inhabitant. *)
  pose filter_universe.
  (* A filter is closed by inclusion, so the universe is also
     an inhabitant of the filter. *)
  eauto using filter_closed_under_inclusion.
Qed.

(* [ultimately] commutes with conjunction. *)

Lemma filter_conj:
  forall P1 P2,
  ultimately A P1 /\ ultimately A P2 <-> ultimately A (fun x => P1 x /\ P2 x).
Proof.
  intros P1 P2. split.
  { intros [ h1 h2 ].
    apply (filter_closed_under_intersection h1 h2).
    tauto. }
  { intros h. split;
    apply (filter_closed_under_inclusion h);
    tauto. }
Qed.

(* An existential quantifier can be pushed into [ultimately]. That is,
   [exists/ultimately] implies [ultimately/exists]. The converse is false; to
   see this, replace [ultimately] with [forall], which is one possible
   interpretation of [ultimately]. *)

Lemma ultimately_exists:
  forall B (Q : A -> pred B),
  (exists y, ultimately A (fun x => Q x y)) ->
  ultimately A (fun x => exists y, Q x y).
Proof.
  intros B Q [ y HQ ].
  eapply filter_closed_under_inclusion.
  { exact HQ. }
  simpl. intros. exists y. assumption.
Qed.

(* [ultimately] can be pushed into a universal quantifier. That is,
   [ultimately/forall] implies [forall/ultimately]. The converse is false:
   for instance, on the natural numbers, [forall x, [ultimately y, x <= y]]
   obviously holds, whereas [ultimately y, forall x, x <= y] does not.
   A fortiori, two [ultimately] quantifiers do not in general commute. *)

Lemma forall_ultimately:
  forall B (Q : B -> pred A),
  ultimately A (fun y => forall x, Q x y) ->
  forall x, ultimately A (fun y => Q x y).
Proof.
  intros. eapply filter_closed_under_inclusion; eauto.
Qed.

End Laws.

End Filter.

Export Filter. (* TEMPORARY define Exports *)

(* TEMPORARY define rewriting-rule versions of these laws? *)

(* ---------------------------------------------------------------------------- *)

(* The dual of [ultimately] is [often]. Whereas [ultimately x, P x] intuitively
   means that, once [x] is large enough, [P x] holds always, [often x, P x]
   means that it is not the case that, once [x] is large enough, [P x] is false
   always. In other words, [often x, P x] means that there exist arbitrarily
   large [x]'s such that [P x] holds. We use the positive formulation as a
   definition. The fact this is equivalent to the doubly-negated form can be
   proved by exploiting the principle of excluded middle. *)

Section Often.

Variable A : filterType.

Implicit Type P Q : pred A.

Definition often P :=
  forall Q, ultimately A Q -> exists a, P a /\ Q a.

Lemma often_characterization:
  forall P,
  ~ ultimately A (fun x => ~ P x) <-> often P.
Proof.
  unfold often. split.

  (* Left-to-right implication. *) {
  (* Reductio ad absurdum. If there did not exist [a] that satisfies [P /\ Q],
     then [~ (P /\ Q)] would hold everywhere. *)
  intros oftenP Q ultQ.
  apply not_all_not_ex. intros nPQ.
  (* Thus, [~ (P /\ Q)] would hold ultimately. *)
  specialize (filter_universe_alt nPQ). intro nPQ'.
  (* However, by hypothesis, [Q] holds ultimately. By combining these facts,
     we find that [~P] holds ultimately. *)
  assert (ultimately A (fun a => ~ P a)).
  { eapply filter_closed_under_intersection.
    - exact ultQ.
    - exact nPQ'.
    - eauto. }
  (* This contradicts the hypothesis [~ ultimately ~ P]. *)
  tauto. }

  (* Right-to-left implication. *)
  { intros H unP. destruct (H _ unP). tauto. }
Qed.

(* TEMPORARY the definition of [often] looks like a [limit] assertion. Is it one?
   Is there a connection? *)

End Often.

Arguments often : clear implicits.

(* ---------------------------------------------------------------------------- *)

(* Inclusion of filters. *)

Definition finer A (ult1 ult2 : filter A) :=
  forall P, ult2 P -> ult1 P.

(* ---------------------------------------------------------------------------- *)

(* The filter [on Q] represents validity everywhere in the set [Q].
   In other words, [on Q P] holds if and only if [Q] implies [P]. *)

Section On.

Variable A : Type.

Variable Q : pred A.

Hypothesis Qx : exists x, Q x.

Definition on : filter A :=
  fun P => forall x, Q x -> P x.

Definition mixin_on : filterMixin on.
Proof.
  unfold on.
  constructor; eauto.
  destruct Qx as [ x ? ]; exists x; eauto.
Qed.

Definition filter_on := FilterType mixin_on.

Goal ultimately filter_on = on.
Proof. reflexivity. Qed.

Lemma onP:
  forall P : pred A,
  ultimately filter_on P =
  forall x, Q x -> P x.
Proof. reflexivity. Qed.

End On.

(* ---------------------------------------------------------------------------- *)

(* As a special case, [on (fun _ => True)] is the universal quantifier. *)

Section Forall.

Variable A : Type.

Variable x : A.

Definition _forall :=
  on (fun (_: A) => True).

Definition filter_forall :=
  filter_on (ex_intro _ x I).

Goal ultimately filter_forall = _forall.
Proof. reflexivity. Qed.

Lemma forallP:
  forall P : pred A,
  ultimately filter_forall P =
  forall x, P x.
Proof.
  intros P. unfold filter_forall. rewrite onP.
  apply prop_ext. intuition.
Qed.

End Forall.

(* ---------------------------------------------------------------------------- *)

(* The (infinite) union of a decreasing family of filters is a filter. *)

Section Union.

Variable A : Type.

Variable ult : nat -> filter A.

Variable mixin : forall i, filterMixin (ult i).

Variable decreasing : forall i j, i <= j -> finer (ult j) (ult i).

Definition union : filter A :=
  fun P => exists i, ult i P.

Definition mixin_union : filterMixin union.
Proof.
  unfold union.
  constructor.
  { exists 0. destruct (mixin 0). eauto. }
  { intros P [ i ? ]. destruct (mixin i). eauto. }
  { intros P1 P2 P [ i1 h1 ] [ i2 h2 ] ?.
    exists (max i1 i2).
    destruct (mixin (max i1 i2)) as [ _ _ inter ].
    eapply inter; [| | eauto].
    { eapply decreasing; [ |eauto].
      apply Nat.le_max_l. }
    { eapply decreasing; [ |eauto].
      apply Nat.le_max_r. }
  }
Qed.

Definition filter_union := FilterType mixin_union.

Goal ultimately filter_union = union.
Proof. reflexivity. Qed.

Lemma unionP:
  forall P,
  ultimately filter_union P =
  exists i, ult i P.
Proof. reflexivity. Qed.

End Union.

(* ---------------------------------------------------------------------------- *)

(* Going up in an ordered set. *)

(* TEMPORARY maybe define [at_and_above i] first, then take the union? *)

Section Up.

Variable A : Type.

Variable le : A -> A -> Prop.

Hypothesis le_refl : reflexive A le.
Hypothesis le_trans : transitive A le.

Variable x : nat -> A.

Variable increasing : forall i j, i <= j -> le (x i) (x j).

Definition up : filter A :=
  union (fun i => on (le (x i))).

Definition mixin_up : filterMixin up.
Proof.
  apply mixin_union.
  { intros i. apply mixin_on. eauto. }
  { unfold on. intros i j ij P. eauto. }
Qed.

Definition filter_up := FilterType mixin_up.

Goal ultimately filter_up = up.
Proof. reflexivity. Qed.

Lemma upP:
  forall P,
  ultimately filter_up P =
  exists i, forall y, le (x i) y -> P y.
Proof. reflexivity. Qed.

(* TEMPORARY used? *)
Lemma prove_up:
  forall i,
  ultimately filter_up (fun y => le (x i) y).
Proof. intros i. unfold filter_up. exists i. unfold on. eauto. Qed.

End Up.

(* ---------------------------------------------------------------------------- *)

(* The standard filter on [nat]. *)

Definition up_nat : filter nat :=
  up le id.

Definition filter_up_nat :=
  filter_up le_refl le_trans (fun i j : nat => id).

Goal
  forall P : pred nat,
  (ultimately filter_up_nat P) =
  exists n, forall x, n <= x -> P x.
Proof.
  intros P. unfold filter_up_nat. rewrite upP. reflexivity.
Qed.

Goal ultimately filter_up_nat (fun x => 42 <= x).
Proof. exists 42. unfold on. tauto. Qed.

Goal ultimately filter_up_nat (fun x => 42 <= x).
Proof. unfold filter_up_nat. rewrite upP. exists 42. tauto. Qed.

(* ---------------------------------------------------------------------------- *)

(* Canonical filter for a preorder (with upper-bounds). *)

(* TEMPORARY this should be defined somewhere else *)
Definition with_upper_bounds A (le: A -> A -> Prop) :=
  forall x y, exists z, le x z /\ le y z.

Arguments with_upper_bounds : clear implicits.

Definition inhab A :=
  exists (x: A), True.

Section Canonical.

Variable A : Type.

Hypothesis A_inhab: inhab A.

Variable le : A -> A -> Prop.

Hypothesis le_refl : reflexive A le.
Hypothesis le_trans : transitive A le.
Hypothesis le_ub : with_upper_bounds A le.

Definition canonical : filter A :=
  fun P => exists x0, forall x, le x0 x -> P x.

Definition mixin_canonical : filterMixin canonical.
Proof.
  unfold canonical.
  constructor.
  { destruct A_inhab as [ x0 _ ]. exists x0. tauto. }
  { intros P [ x0 H ]. exists x0. apply H. apply le_refl. }
  { intros P1 P2 P [ x0 H1 ] [ y0 H2 ] H.
    pose proof (le_ub x0 y0) as [z0 [le_x0_z0 le_y0_z0]].
    exists z0. intros.
    apply H; [apply H1 | apply H2]; apply (@le_trans _ z0); tauto. }
Qed.

Definition filter_canonical := FilterType mixin_canonical.

Goal ultimately filter_canonical = canonical.
Proof. reflexivity. Qed.

Lemma canonicalP:
  forall P,
  ultimately filter_canonical P =
  exists x0, forall x, le x0 x -> P x.
Proof. reflexivity. Qed.

End Canonical.

(* ---------------------------------------------------------------------------- *)

(* The standard filter on [nat], defined using [canonical]. *)

Definition canonical_nat : filter nat :=
  canonical le.

Lemma le_ub : with_upper_bounds nat le.
Proof.
  unfold with_upper_bounds. intros x y.
  exists (max x y). split.
  - apply Nat.le_max_l.
  - apply Nat.le_max_r.
Qed.

Definition filter_canonical_nat :=
  filter_canonical (ex_intro _ 0 I) le_refl le_trans le_ub.

Goal
  forall P : pred nat,
  (ultimately filter_canonical_nat P) =
  exists n, forall x, n <= x -> P x.
Proof.
  intros P. unfold filter_canonical_nat. rewrite canonicalP. reflexivity.
Qed.

Goal ultimately filter_canonical_nat (fun x => 42 <= x).
Proof. exists 42. tauto. Qed.

Goal ultimately filter_canonical_nat (fun x => 42 <= x).
Proof. unfold filter_canonical_nat. rewrite canonicalP. exists 42. tauto. Qed.

(* ---------------------------------------------------------------------------- *)

(* Applying a function [f] to a filter [ult] produces another filter, known as
   the image of [ult] under [f]. *)

Section Image.

  Variables A B : Type.

  Variable f : A -> B.

  Variable ult : filter A.

  Definition image : filter B :=
    fun P => ult (fun x => P (f x)).

  Definition mixin_image : filterMixin ult -> filterMixin image.
  Proof.
    intros [ Huniverse Hnonempty Hclosed ].
    unfold image.
    econstructor; eauto.
    intros P H. pose proof (Hnonempty _ H) as [ ? ? ].
    eauto.
  Qed.

End Image.

Definition filter_image (A : filterType) B (f : A -> B) :=
  FilterType (mixin_image f (mixin A)).

Lemma imageP:
  forall (A : filterType) B (f : A -> B),
  forall P,
  ultimately (filter_image f) P =
  ultimately A (fun x => P (f x)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)

(* A notion of limit, or convergence, or divergence -- it all depends on which
   filters one uses. The assertion [limit f] states that any property [P] that
   is ultimately true of [y] is ultimately true of [f x]. If [f] is a function
   from [nat] to [nat], equipped with its standard filter, this means that [f x]
   tends to infinity as [x] tends to infinity. *)

(* [limit] could take two arguments of type [filter A] and [filter B]. Instead,
   we take two arguments of type [filterType]. *)

Section Limit.

Variables A B : filterType.

Variable f : A -> B.

Definition limit :=
  finer (ultimately (filter_image f)) (ultimately B).

Lemma limitP:
  limit =
  forall P,
  (ultimately B (fun y => P y)) ->
  (ultimately A (fun x => P (f x))).
Proof.
  reflexivity.
Qed.

End Limit.

Arguments limit : clear implicits.

Lemma limit_id:
  forall A : filterType,
  limit A A (fun a : A => a).
Proof.
  intros A. rewrite limitP. tauto.
Qed.

(* TEMPORARY how about proving on a lemma on the limit of a
   function composition? *)

Goal limit filter_up_nat filter_up_nat (fun x => x + 1).
Proof.
  intros P. unfold filter_up_nat. rewrite upP. rewrite imageP.
  intros [ n Px ]. exists n.
  intros x ?. apply Px.
  auto with arith.
Qed.

(* ---------------------------------------------------------------------------- *)

Section Within.

(* If we have a filter on [A], and if [P] is a subset of [A], then [within P] is
   also a filter on [A]. By definition, a formula [Q] is ultimately holds within
   [P] if and only if [P -> Q] is ultimately true. *)

(* There is a condition on [P], though. The formula [P] must not forbid `going
   to the limit' in the sense of [ultimately]. To take a concrete example, if
   our initial filter is [up_nat], then it would not make sense for [P] to be
   the property [fun n => n <= k]. If we did choose such a [P], then [within P]
   would be a filter that says ``when [n] tends towards infinity while remaining
   under [k]''. This makes no sense.

   What is an appropriate condition on [P]? We could require [ultimately P], but
   that would be too strong; if ultimately [P] holds, then ultimately [P -> Q]
   is equivalent to ultimately [Q]. (Another way to see that this is wrong is to
   take an example where [P] is [fun (i, n) => i <= n]. This property does not
   hold ultimately, yet it does make sense.)

   An appropriate condition seems to be [~ ultimately ~ P], also known as [often
   P]. Indeed, if [P] is ultimately false, this means that [P] `forbids going to
   the limit'. We can see that if [P] is ultimately false, then [P -> Q] is
   ultimately true, regardless of [Q], and that is not a good thing, as we
   expect [ultimately (P -> Q)] to imply something about [Q]. Technically, the
   condition [often P] seems to be exactly what is needed in order to prove that
   [within P] does not accept an empty [Q]. *)

Variable A : filterType.

Variable P : pred A.

Hypothesis oftenP : often A P.

Definition within : filter A :=
  fun Q => ultimately A (fun x => P x -> Q x).

Definition mixin_within : filterMixin within.
Proof.
  unfold within.
  constructor.
  { apply filter_universe_alt. tauto. }
  { intros Q hPQ. destruct (oftenP hPQ) as [x [? ?]].
    eauto. }
  { intros Q1 Q2 Q hPQ1 hPQ2 ?.
    eapply filter_closed_under_intersection.
    - exact hPQ1.
    - exact hPQ2.
    - eauto. }
Qed.

Definition filter_within := FilterType mixin_within.

Goal ultimately filter_within = within.
Proof. reflexivity. Qed.

Lemma withinP:
  forall Q,
  ultimately filter_within Q =
  ultimately A (fun x => P x -> Q x).
Proof. reflexivity. Qed.

End Within.

Arguments within : clear implicits.

(* ---------------------------------------------------------------------------- *)

(* The product of two filters. *)

(* The members of the product filter are all subsets [P] which contain a product
   [P1] * [P2], where [P1] and [P2] are members of the left-hand and right-hand
   filters, respectively. *)

(* This is a symmetric notion of product. It is *not* the same as writing
   [ultimately a1, [ultimately a2, P (a1, a2)]], which is dissymmetric. *)

Section FilterProduct.

Variable A1 A2 : filterType.

Definition product : filter (A1 * A2) :=
  fun P =>
    exists P1 P2,
    ultimately A1 P1 /\ ultimately A2 P2 /\
    forall a1 a2, P1 a1 -> P2 a2 -> P (a1, a2).

Definition mixin_product: filterMixin product.
Proof.
  unfold product.
  constructor.
  (* The universe is a member. *)
  { do 2 (exists (fun _ => True)).
    repeat split; apply filter_universe. }
  (* The members are nonempty. *)
  { intros P (P1 & P2 & H1 & H2 & ?).
    pose proof (filter_member_nonempty H1) as [ a1 H1' ].
    pose proof (filter_member_nonempty H2) as [ a2 H2' ].
    exists (a1, a2). eauto. }
  (* Closure under intersection and inclusion. *)
  { intros P Q R.
    intros (P1 & P2 & uP1 & uP2 & ?).
    intros (Q1 & Q2 & uQ1 & uQ2 & ?).
    intros HH.
    exists (fun a1 => P1 a1 /\ Q1 a1).
    exists (fun a2 => P2 a2 /\ Q2 a2).
    repeat split.
    { eapply filter_closed_under_intersection.
      exact uP1. exact uQ1. eauto. }
    { eapply filter_closed_under_intersection.
      exact uP2. exact uQ2. eauto. }
    intuition eauto. }
Qed.

Definition filter_product := FilterType mixin_product.

(* When the pair [a1, a2] goes to infinity, its components go to infinity. *)

Lemma limit_fst:
  limit filter_product A1 fst.
Proof.
  unfold limit. simpl. unfold image. unfold product. simpl. unfold finer.
  intros P1 ?.
  exists P1. exists (fun _ => True).
  repeat split; eauto. apply filter_universe.
Qed.

Lemma limit_snd:
  limit filter_product A2 snd.
Proof.
  unfold limit. simpl. unfold image. unfold product. simpl. unfold finer.
  intros P2 ?.
  exists (fun _ => True). exists P2.
  repeat split; eauto. apply filter_universe.
Qed.

(* When both components go to infinity, the pair goes to infinity. *)

(* The limit of a pair is a pair of the limits. *)

Lemma limit_pair :
  forall A : filterType,
  forall (f1 : A -> A1) (f2 : A -> A2),
  limit A A1 f1 ->
  limit A A2 f2 ->
  limit A filter_product (fun a => (f1 a, f2 a)).
Proof.
  unfold limit. simpl. unfold image. unfold product. unfold finer.
  intros A f1 f2 lf1 lf2 P (P1 & P2 & uP1 & uP2 & ?).
  eapply filter_closed_under_intersection.
  { apply lf1. apply uP1. }
  { apply lf2. apply uP2. }
  eauto.
Qed.

End FilterProduct.

Arguments product : clear implicits.

(* ---------------------------------------------------------------------------- *)

(* The product of two [up]-filters is the [up]-filter for the product ordering. *)

Section FilterProductUp.


Variable A1 A2 : Type.

Variable le1 : A1 -> A1 -> Prop.
Variable le2 : A2 -> A2 -> Prop.

Hypothesis le_refl1 : reflexive A1 le1.
Hypothesis le_trans1 : transitive A1 le1.
Hypothesis le_refl2 : reflexive A2 le2.
Hypothesis le_trans2 : transitive A2 le2.

Variable x1 : nat -> A1.
Variable x2 : nat -> A2.

Variable increasing1 : forall i j, i <= j -> le1 (x1 i) (x1 j).
Variable increasing2 : forall i j, i <= j -> le2 (x2 i) (x2 j).

Notation filter1 := (filter_up le_refl1 le_trans1 increasing1).
Notation filter2 := (filter_up le_refl2 le_trans2 increasing2).
Notation filter  := (filter_product filter1 filter2).

(* TEMPORARY this is not the right place to define the product of two orderings
   and prove its basic properties. *)
Definition prod_le (x y : A1 * A2) : Prop :=
  let (x1, x2) := x in
  let (y1, y2) := y in
  le1 x1 y1 /\ le2 x2 y2.

Lemma prod_le_refl: reflexive (A1 * A2) prod_le.
Proof. intros [? ?]. unfold prod_le. split. apply le_refl1. apply le_refl2. Qed.

Lemma prod_le_trans: transitive (A1 * A2) prod_le.
Proof.
  do 3 (intros [ ? ? ]). unfold prod_le.
  intros [ h1 h2 ]. intros [ i1 i2 ].
  split; [eapply le_trans1 | eapply le_trans2]; eauto.
Qed.

Lemma prod_le_increasing:
  forall i j, i <= j -> prod_le (x1 i, x2 i) (x1 j, x2 j).
Proof. intros i j ?. unfold prod_le. eauto. Qed.

Lemma product_upP:
  forall Q : pred (A1 * A2),
  ultimately filter Q =
  ultimately (filter_up prod_le_refl prod_le_trans prod_le_increasing) Q.
Proof.
  intros Q.
  (* RHS. *)
  rewrite upP.
  (* LHS. *)
  unfold ultimately. simpl. unfold product.
  (* Split. *)
  apply prop_ext. split.

  (* Left to right. *)
  { intros (P1 & P2 & uP1 & uP2 & hQ).
    rewrite upP in uP1. destruct uP1 as [ i1 hP1 ].
    rewrite upP in uP2. destruct uP2 as [ i2 hP2 ].
    exists (max i1 i2).
    intros [ y1 y2 ].
    intros [ hy1 hy2 ].
    apply hQ.
    { apply hP1. apply (@le_trans1 _ (x1 (max i1 i2))).
      apply increasing1. apply Nat.le_max_l. assumption. }
    { apply hP2. apply (@le_trans2 _ (x2 (max i1 i2))).
      apply increasing2. apply Nat.le_max_r. assumption. }
  }

  (* Right to left. *)
  { intros [ i hQ ].
    exists (le1 (x1 i)).
    exists (le2 (x2 i)).
    repeat split; try (exists i; unfold on; tauto).
    intros a1 a2 ha1 ha2.
    apply hQ. split; [apply ha1 | apply ha2]. }
Qed.

End FilterProductUp.

Goal
  ultimately (filter_product filter_up_nat filter_up_nat)
    (fun p : nat * nat =>
      let (x, y) := p in
      (42 <= x) /\ (64 <= y)).
Proof.
  unfold filter_up_nat.
  rewrite product_upP. rewrite upP.
  exists 64.
  intros [ x y ].
  unfold prod_le.
  omega.
Qed.

Goal
  ultimately (filter_product filter_up_nat filter_up_nat)
    (fun p : nat * nat =>
      let (x, y) := p in
      (42 <= x) /\ (64 <= y)).
Proof.
  simpl. unfold product.
  exists (fun x	=> 42 <= x).
  exists (fun y => 64 <= y).
  unfold filter_up_nat.
  repeat split.
  { rewrite upP. eauto. }
  { rewrite upP. eauto. }
  eauto. eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The product of two [canonical]-filters is the [canonical]-filter for the
   product ordering. *)

Section FilterProductCanonical.

Variable A1 A2 : Type.

Hypothesis A1_inhab : inhab A1.
Hypothesis A2_inhab : inhab A2.

Variable le1 : A1 -> A1 -> Prop.
Variable le2 : A2 -> A2 -> Prop.

Hypothesis le_refl1 : reflexive A1 le1.
Hypothesis le_trans1 : transitive A1 le1.
Hypothesis le_refl2 : reflexive A2 le2.
Hypothesis le_trans2 : transitive A2 le2.
Hypothesis le_ub1 : with_upper_bounds A1 le1.
Hypothesis le_ub2 : with_upper_bounds A2 le2.

Notation filter1 := (filter_canonical A1_inhab le_refl1 le_trans1 le_ub1).
Notation filter2 := (filter_canonical A2_inhab le_refl2 le_trans2 le_ub2).
Notation filter  := (filter_product filter1 filter2).

(* TEMPORARY this should be defined someplace else *)
Lemma A1A2_inhab : inhab (A1 * A2).
Proof.
  destruct A1_inhab as [ a1 _ ]. destruct A2_inhab as [ a2 _ ].
  exists (a1, a2). tauto.
Qed.

Lemma prod_le_ub : with_upper_bounds (A1 * A2) (prod_le le1 le2).
Proof.
  unfold with_upper_bounds.
  intros [x0 y0] [x1 y1].
  pose proof (le_ub1 x0 x1) as [zx [? ?]].
  pose proof (le_ub2 y0 y1) as [zy [? ?]].
  exists (zx, zy). unfold prod_le. eauto.
Qed.

Lemma product_canonicalP:
  forall Q : pred (A1 * A2),
  ultimately filter Q =
  ultimately
    (filter_canonical
       A1A2_inhab
       (prod_le_refl le_refl1 le_refl2)
       (prod_le_trans le_trans1 le_trans2)
       prod_le_ub)
    Q.
Proof.
  intros Q.
  (* RHS. *)
  rewrite canonicalP.
  (* LHS. *)
  unfold ultimately. simpl. unfold product.
  (* Split. *)
  apply prop_ext. split.

  (* Left to right. *)
  { intros (P1 & P2 & uP1 & uP2 & hQ).
    rewrite canonicalP in uP1. destruct uP1 as [ x0 hP1 ].
    rewrite canonicalP in uP2. destruct uP2 as [ y0 hP2 ].
    exists (x0, y0).
    intros [ x y ]. unfold prod_le.
    intros [ hx hy ].
    apply hQ; eauto. }

  (* Right to left. *)
  { intros [ [ x0 y0 ] hQ ].
    exists (le1 x0).
    exists (le2 y0).
    repeat split. rewrite canonicalP.
    - exists x0. tauto.
    - exists y0. tauto.
    - intros a1 a2 ha1 ha2.
      apply hQ. split; [apply ha1 | apply ha2]. }
Qed.

End FilterProductCanonical.

Goal
  ultimately (filter_product filter_canonical_nat filter_canonical_nat)
    (fun p : nat * nat =>
      let (x, y) := p in
      (42 <= x) /\ (64 <= y)).
Proof.
  unfold filter_canonical_nat.
  rewrite product_canonicalP. rewrite canonicalP.
  exists (42, 64).
  intros [ x y ].
  unfold prod_le.
  tauto.
Qed.

Goal
  ultimately (filter_product filter_canonical_nat filter_canonical_nat)
    (fun p : nat * nat =>
      let (x, y) := p in
      (42 <= x) /\ (64 <= y)).
Proof.
  simpl. unfold product.
  exists (fun x	=> 42 <= x).
  exists (fun y => 64 <= y).
  unfold filter_canonical_nat.
  repeat split.
  { rewrite canonicalP. eauto. }
  { rewrite canonicalP. eauto. }
  eauto. eauto.
Qed.
