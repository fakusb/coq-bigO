Require Import Coq.Logic.Classical_Pred_Type.
Require Import TLC.LibTactics.
Require Import TLC.LibAxioms.
Require Import TLC.LibLogic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ZArith.
Require Import Psatz.

(* We could in principle perform this construction using [bool] instead of [Prop]
   as the codomain of predicates. However, [bool] does not support quantification
   over an infinite set, whereas [Prop] does. *)

Notation pred A := (A -> Prop) (only parsing).

(* ---------------------------------------------------------------------------- *)

Module Filter.

(* Technically, a filter is a nonempty set of nonempty subsets of A, which is
   closed under inclusion and (finite) intersection. *)

Definition filter A := pred (pred A).

Record mixin_of (A : Type) := Mixin {

(* Let us write [ultimately] for a filter.  A filter is a modality: if [P] is a
   predicate, then [ultimately P] is a proposition. In other words, a filter is
   a quantifier: if [P] is a predicate, then [ultimately (fun x => P x)] is a
   proposition. Intuitively, this proposition means that ``ultimately'' [P]
   holds. In other words, for every sufficiently ''large'' [x], [P] holds. *)

  ultimately : filter A;

(* A filter is nonempty. In fact, it contains the universe. In other words,
   [ultimately x => True] is just [True]. Thus, the quantifier [ultimately]
   is weaker than a universal quantifier: [forall x, P x] implies
   [ultimately x, P x]. *)

  _ :
    ultimately (fun _ => True);

(* A filter does not have the empty set as a member. In other words, every
   member of the filter is nonempty. Thus, the quantifier [ultimately] is
   stronger than an existential quantifier: [ultimately x, P x] implies
   [exists x, P x]. *)

  _ :
    forall P, ultimately P -> exists a, P a;

(* A filter is closed by inclusion and by (finite) intersection. In other
   words, the quantifier [ultimately] is covariant and commutes with (finite)
   conjunction. The last condition means that [ultimately] is universal in
   nature, as opposed to existential. In particular, the universal quantifier
   can be viewed as a filter, but the existential quantifier cannot. *)

  _ :
    forall P1 P2 P : pred A,
    ultimately P1 ->
    ultimately P2 ->
    (forall a, P1 a -> P2 a -> P a) ->
    ultimately P
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
  Record type : Type := Pack { sort : Type ; class : class_of sort }.
End ClassDef.

Module Exports.
  Coercion sort : type >-> Sortclass.
  Notation filterType := type.
  Notation FilterMixin := Mixin.
  Notation FilterType T m := (@Pack T m).
End Exports.

End Filter.
Export Filter.Exports.

Definition ultimately T := Filter.ultimately (Filter.class T).
Arguments ultimately : clear implicits.

(* ---------------------------------------------------------------------------- *)

Section FilterLaws.

Variable A : filterType.

Implicit Type P : pred A.

(* Re-statement of the defining laws. *)

Lemma filter_universe:
  ultimately A (fun _ => True).
Proof. destruct A as [? M]. destruct M. eauto. Qed.

Lemma filter_member_nonempty:
  forall P, ultimately A P -> exists a, P a.
Proof. destruct A as [? M]. destruct M. eauto. Qed.

Lemma filter_closed_under_intersection:
  forall P1 P2 P,
  ultimately A P1 ->
  ultimately A P2 ->
  (forall a, P1 a -> P2 a -> P a) ->
  ultimately A P.
Proof. destruct A as [? M]. destruct M. eauto. Qed.

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

Lemma filter_conj_alt :
  forall P1 P2,
    ultimately A P1 ->
    ultimately A P2 ->
    ultimately A (fun x => P1 x /\ P2 x).
Proof. intros. apply filter_conj. tauto. Qed.

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

End FilterLaws.

(* TEMPORARY define rewriting-rule versions of these laws? *)

(* ---------------------------------------------------------------------------- *)
(* A set of tactics useful to intersect an arbitrary number of filters.

   [filter_intersect] turns a goal of the form:

     ultimately A P1 -> ... ultimately A Pn -> Q

   into:

     ultimately A (P1 /\ ... /\ Pn) -> Q



   [filter_closed_under_intersection] turns a goal of the form:

     ultimately A P1 -> ... ultimately A Pn -> ultimately A P

   into:

     forall x, P1 x /\ ... /\ Pn x -> P
 *)

Ltac filter_intersect_two_base I U1 U2 :=
  lets I: filter_conj_alt U1 U2.

Ltac filter_intersect_two :=
  let U1 := fresh in
  let U2 := fresh in
  let U := fresh in
  intros U1 U2;
  filter_intersect_two_base U U1 U2;
  revert U; clear U1; clear U2.

Ltac filter_intersect :=
  match goal with
  | |- (ultimately ?A _) -> (ultimately ?A _) -> _ =>
    let U := fresh in
    intro U;
    filter_intersect;
    revert U;
    filter_intersect_two
  | |- (ultimately ?A _) -> (ultimately ?B _) -> _ =>
    idtac
  | |- (ultimately _ _) -> _ =>
    idtac
  end.

Ltac filter_closed_under_intersection :=
  filter_intersect;
  let U := fresh in
  intro U;
  applys filter_closed_under_inclusion U;
  clear U.

(* Test goals *)

Goal
  forall A P1 P2 P3 B P4 P5,
  (ultimately A (fun x => P1 x /\ P2 x /\ P3 x) -> ultimately B P4 -> ultimately B P5 -> False) ->
  ultimately A P1 ->
  ultimately A P2 ->
  ultimately A P3 ->
  ultimately B P4 ->
  ultimately B P5 ->
  False.
Proof.
  do 8 intro.
  filter_intersect.
  assumption.
Qed.

Goal
  forall (A: filterType) (P1 P2 P3 P4 : A -> Prop),
  (forall x, (P1 x /\ P2 x /\ P3 x) -> P4 x) ->
  ultimately A P1 ->
  ultimately A P2 ->
  ultimately A P3 ->
  ultimately A P4.
Proof.
  do 6 intro.
  filter_closed_under_intersection.
  assumption.
Abort.

(* ---------------------------------------------------------------------------- *)

(* Inclusion of filters. *)

Definition finer A (ult1 ult2 : Filter.filter A) :=
  forall P, ult2 P -> ult1 P.

(* ---------------------------------------------------------------------------- *)

(* Applying a function [f] to a filter [ult] produces another filter, known as
   the image of [ult] under [f]. *)

Section Image.

  Variable A : filterType.
  Variable B : Type.

  Variable f : A -> B.

  Definition image : Filter.filter B :=
    fun P => ultimately A (fun x => P (f x)).

  Definition image_filterMixin : Filter.mixin_of B.
  Proof.
    eapply Filter.Mixin with image.
    { apply filter_universe. }
    { intros ? I. pose proof (filter_member_nonempty I) as [? ?].
      eauto. }
    { intros P1 P2 P I1 I2 H.
      unfold image in *.
      apply (filter_closed_under_intersection I1 I2).
      eauto. }
  Defined.

  Definition image_filterType :=
    FilterType B image_filterMixin.

End Image.
Arguments image A [B] f P.
Arguments image_filterType A [B] f.

Lemma imageP :
  forall (A : filterType) B (f : A -> B),
  forall (P: B -> Prop),
  ultimately (image_filterType A f) P =
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
  finer (ultimately (image_filterType A f)) (ultimately B).

Lemma limitP:
  forall (A: filterType) (B: Type) (f: A -> B) P,
  ultimately (@image_filterType A B f) P =
  ultimately A (fun x => P (f x)).
Proof. reflexivity. Qed.

End Limit.
Arguments limit : clear implicits.

Lemma limit_id:
  forall A : filterType,
  limit A A (fun a : A => a).
Proof.
  intros. unfold limit. unfold finer.
  intros. rewrite limitP. eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* If the type A is inhabited, then the singleton set that contains just the set
   [A] is a filter. We call this modality [everywhere]. *)

Section FilterEverywhere.

Variable A : Type.
Context `{IA: Inhab A}.

Definition everywhere_filterMixin : Filter.mixin_of A.
Proof.
  eapply Filter.Mixin with
    (fun (P: A -> Prop) => forall a, P a);
  eauto.
  Unshelve.
  forwards IA': indefinite_description IA.
  destruct IA' as (a & _). apply a.
Defined.

Definition everywhere_filterType := FilterType A everywhere_filterMixin.

End FilterEverywhere.

Arguments everywhere_filterType A [IA].

Lemma everywhereP A `{Inhab A} :
  forall (P : A -> Prop),
  ultimately (everywhere_filterType A) P =
  forall a, P a.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)

(* The standard filter on [nat]. *)

Definition nat_filterMixin : Filter.mixin_of nat.
Proof.
  eapply Filter.Mixin with
    (fun (P: nat -> Prop) => exists n0, forall n, le n0 n -> P n).
  - exists 0%nat. eauto with arith.
  - intros ? [n0 ?]. exists n0. eauto with arith.
  - { introv [n0 H0] [n1 H1] H. exists (max n0 n1).
      intros n ?. apply H.
      - apply H0. lia.
      - apply H1. lia. }
Defined.

Definition nat_filterType := FilterType nat nat_filterMixin.

Lemma natP :
  forall (P : nat -> Prop),
  ultimately nat_filterType P =
  exists n0, forall n, le n0 n -> P n.
Proof. reflexivity. Qed.

Lemma ultimately_ge_nat (n0: nat) :
  ultimately nat_filterType (fun n => le n0 n).
Proof.
  rewrite natP. exists n0. eauto.
Qed.

Lemma natP_ultimately (cond : nat -> Prop) :
  forall (P : nat -> Prop),
  ultimately nat_filterType cond ->
  ultimately nat_filterType P =
  exists x0, cond x0 /\ forall x, le x0 x -> P x.
Proof.
  intros P Ucond. rewrite natP. rewrite natP in Ucond.
  destruct Ucond as (ncond & Hcond).
  apply prop_ext. split.
  { intros [n0 H]. exists (max ncond n0). splits.
    - apply Hcond. lia.
    - intros. apply H. lia. }
  { intros (n0 & lo_le_n0 & H). eauto. }
Qed.

Arguments natP_ultimately [cond] [P] _.

(* ---------------------------------------------------------------------------- *)

(* The standard filter on [Z]. *)

Definition Z_filterMixin : Filter.mixin_of Z.
Proof.
  eapply Filter.Mixin with
    (fun (P: Z -> Prop) => exists n0, forall n, Z.le n0 n -> P n).
  - exists 0%Z. eauto with arith.
  - intros ? [n0 ?]. exists n0. eauto with zarith.
  - { introv [n0 H0] [n1 H1] H. exists (Z.max n0 n1).
      intros n ?. apply H.
      - apply H0. lia.
      - apply H1. lia. }
Defined.

Definition Z_filterType := FilterType Z Z_filterMixin.

Lemma ZP :
  forall (P : Z -> Prop),
  ultimately Z_filterType P =
  exists n0, forall n, Z.le n0 n -> P n.
Proof. reflexivity. Qed.

Lemma ultimately_ge_Z (x0: Z) :
  ultimately Z_filterType (fun x => Z.le x0 x).
Proof.
  rewrite ZP. exists x0. eauto.
Qed.

Lemma ZP_ultimately (cond : Z -> Prop) :
  forall (P : Z -> Prop),
  ultimately Z_filterType cond ->
  ultimately Z_filterType P =
  exists x0, cond x0 /\ forall x, Z.le x0 x -> P x.
Proof.
  intros P Ucond. rewrite ZP. rewrite ZP in Ucond.
  destruct Ucond as (ncond & Hcond).
  apply prop_ext. split.
  { intros [n0 H]. exists (Z.max ncond n0). splits.
    - apply Hcond. lia.
    - intros. apply H. lia. }
  { intros (n0 & lo_le_n0 & H). eauto. }
Qed.

Arguments ZP_ultimately [cond] [P] _.

Definition Zshift (x0 : Z) : Z -> Z :=
  fun x => (x0 + x)%Z.

Lemma Zshift_inv (x0 : Z) :
  forall x, Zshift (- x0) (Zshift x0 x) = x.
Proof.
  unfold Zshift. intros. omega.
Qed.

Lemma Zshift_limit (x0 : Z) :
  limit Z_filterType Z_filterType (Zshift x0).
Proof.
  intros. unfold limit, finer. introv H. rewrite limitP.
  rewrite ZP in H. destruct H as [x1 H1].
  rewrite ZP. exists (x1 - x0)%Z. intros. apply H1.
  unfold Zshift. lia.
Qed.

Lemma ZshiftP (x0 : Z) :
  forall P,
  ultimately Z_filterType (fun x => P (Zshift x0 x)) =
  ultimately Z_filterType P.
Proof.
  intros. apply prop_ext.
  split; do 2 rewrite ZP; intros (x1 & H1); unfold Zshift in *.
  { exists (x1 + x0)%Z. intros.
    assert (HH: n = (x0 + (n - x0))%Z) by lia. rewrite HH.
    apply H1. lia. }
  { exists (x1 - x0)%Z. intros. apply H1. lia. }
Qed.

(* ---------------------------------------------------------------------------- *)

(* The product of two filters. *)

(* The members of the product filter are all subsets [P] which contain a product
   [P1] * [P2], where [P1] and [P2] are members of the left-hand and right-hand
   filters, respectively. *)

(* This is a symmetric notion of product. It is *not* the same as writing
   [ultimately A1 (fun a1 => ultimately A2 (fun a2 => P (a1, a2)))], which is
   dissymmetric.

   The symmetric product implies the dissymetric ones, but the converse is
   false. For example, if P (x, y) = (x <= y), then
   [ultimately (fun x => ultimately (fun y => P (x, y)))] is true, but not
   [ultimately P].
*)

Section FilterProduct.

Variable A1 A2 : filterType.

Definition product : Filter.filter (A1 * A2) :=
  fun P =>
    exists P1 P2,
    ultimately A1 P1 /\ ultimately A2 P2 /\
    forall a1 a2, P1 a1 -> P2 a2 -> P (a1, a2).

Definition product_filterMixin : Filter.mixin_of (A1 * A2).
Proof.
  eapply Filter.Mixin with product.
  { do 2 (eexists (fun _ => True)).
    repeat split; apply filter_universe. }
  { intros P (P1 & P2 & H1 & H2 & ?).
    forwards [ a1 H1' ] : filter_member_nonempty H1.
    forwards [ a2 H2' ] : filter_member_nonempty H2.
    exists (a1, a2). eauto. }
  { intros P Q R.
    intros (P1 & P2 & uP1 & uP2 & ?).
    intros (Q1 & Q2 & uQ1 & uQ2 & ?).
    intros HH.
    exists (fun a1 => P1 a1 /\ Q1 a1).
    exists (fun a2 => P2 a2 /\ Q2 a2).
    repeat split; try (apply filter_conj; eauto).
    intuition eauto. }
Defined.

Definition product_filterType :=
  FilterType (A1 * A2) product_filterMixin.

End FilterProduct.

Arguments product : clear implicits.

Lemma productP :
  forall (A1 A2 : filterType) P,
  ultimately (product_filterType A1 A2) P =
  (exists P1 P2,
   ultimately A1 P1 /\
   ultimately A2 P2 /\
   (forall a1 a2, P1 a1 -> P2 a2 -> P (a1, a2))).
Proof. reflexivity. Qed.

Definition fswap (A1 A2 B : Type) (f: A1 * A2 -> B) : A2 * A1 -> B :=
  fun '(x, y) => f (y, x).

Lemma product_fswap :
  forall (A1 A2 : filterType) P,
  ultimately (product_filterType A1 A2) P <->
  ultimately (product_filterType A2 A1) (fswap P).
Proof.
  intros. do 2 rewrite productP.
  split; introv (P1 & P2 & UP1 & UP2 & HP); exists P2 P1; unfold fswap in *; splits~.
Qed.

Definition liftl (A1 A2 B : Type) (f: A1 -> B) : A1 * A2 -> B * A2 :=
  fun '(x, y) => (f x, y).

Definition liftr (A1 A2 B : Type) (f: A2 -> B) : A1 * A2 -> A1 * B :=
  fun '(x, y) => (x, f y).

Lemma limit_liftl :
  forall (A1 A2 B : filterType) f,
  limit A1 B f ->
  limit (product_filterType A1 A2) (product_filterType B A2) (liftl f).
Proof.
  unfold limit, finer. introv Lf UP. simpl in *.
  rewrite productP in UP. destruct UP as (P1 & P2 & UP1 & UP2 & HP).
  rewrite imageP. rewrite productP. unfold liftl.
  specializes Lf UP1. rewrite imageP in Lf.
  do 2 eexists. splits~.
  exact Lf. exact UP2.
  simpl. intros. eauto.
Qed.

Lemma limit_liftr :
  forall (A1 A2 B : filterType) f,
  limit A2 B f ->
  limit (product_filterType A1 A2) (product_filterType A1 B) (liftr f).
Proof.
  unfold limit, finer. introv Lf UP. simpl in *.
  rewrite productP in UP. destruct UP as (P1 & P2 & UP1 & UP2 & HP).
  rewrite imageP. rewrite productP. unfold liftr.
  specializes Lf UP2. rewrite imageP in Lf.
  do 2 eexists. splits~.
  exact UP1. exact Lf.
  simpl. intros. eauto.
Qed.

(* Symmetric product implies both dissymetric products. *)

Lemma product_dissym_l :
  forall (A1 A2 : filterType) P,
  ultimately (product_filterType A1 A2) P ->
  ultimately A1 (fun x => ultimately A2 (fun y => P (x, y))).
Proof.
  introv UP. rewrite productP in UP.
  destruct UP as (P1 & P2 & UP1 & UP2 & HP).
  revert UP1; filter_closed_under_intersection. introv P1a.
  revert UP2; filter_closed_under_intersection. introv P2a.
  apply HP; eauto.
Qed.

Lemma product_dissym_r :
  forall (A1 A2 : filterType) P,
  ultimately (product_filterType A1 A2) P ->
  ultimately A2 (fun y => ultimately A1 (fun x => P (x, y))).
Proof.
  introv UP.
  forwards UP': proj1 product_fswap UP.
  apply (product_dissym_l UP').
Qed.

(* Disprove some facts about [product] that may seem true. *)

(* Dissymetric products do not imply symmetric product.
   Symmetric product is strictly stronger than dissymetric products. *)
Goal
  (forall (A1 A2 : filterType) P,
   ultimately A1 (fun x => ultimately A2 (fun y => P (x, y))) ->
   ultimately A2 (fun y => ultimately A1 (fun x => P (x, y))) ->
   ultimately (product_filterType A1 A2) P) ->
  False.
Proof.
  intro H.
  specializes H nat_filterType nat_filterType
    (fun '(x, y) => x < y \/ y < x).
  simpl in H.
  specializes H ___.
  { rewrite natP. exists 0. intros.
    rewrite natP. exists (n+1). intros. lia. }
  { rewrite natP. exists 0. intros.
    rewrite natP. exists (n+1). intros. lia. }
  rewrite productP in H. destruct H as (P1 & P2 & UP1 & UP2 & HP).
  rewrite natP in UP1, UP2. destruct UP1 as (x0 & HP1). destruct UP2 as (y0 & HP2).

  destruct (Nat.le_gt_cases x0 y0).
  { specializes HP y0 y0 ___. lia. }
  { specializes HP x0 x0 ___. apply HP2. lia. lia. }
Qed.

(* Similarly, one cannot prove a property on a product filter by proving it
   component-by-component. *)
Goal
  (forall (A1 A2 : filterType) P Q,
   ultimately A1 (fun x =>
     ultimately A2 (fun y => P (x, y)) ->
     ultimately A2 (fun y => Q (x, y))) ->
   ultimately (product_filterType A1 A2) P ->
   ultimately (product_filterType A1 A2) Q) ->
  False.
Proof.
  intro H.
  specializes H Z_filterType Z_filterType
    (fun (_: Z * Z) => True)
    (fun '(x, y) => Z.le x y).
  simpl in H.
  specializes H ___.
  { rewrite ZP. exists 0%Z. intros.
    rewrite ZP. exists n. eauto. }
  { apply filter_universe. }
  rewrite productP in H. destruct H as (P1 & P2 & UP1 & UP2 & HP).
  rewrite ZP in UP1, UP2. destruct UP1 as (x0 & HP1). destruct UP2 as (y0 & HP2).

  destruct (Z.le_gt_cases x0 y0).
  { specializes HP (y0 + 1)%Z y0 ___.
    apply HP1. lia. apply HP2. lia.
    lia. }
  { specializes HP x0 y0 ___.
    apply HP1. lia. apply HP2. lia.
    lia. }
Qed.
