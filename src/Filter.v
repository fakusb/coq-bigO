Require Import Coq.Logic.Classical_Pred_Type.
Require Import Relations.
Require Import TLC.LibTactics.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List. (* for matching on boxers lists *)

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

Lemma filter_conj_alt :
  forall A P1 P2,
    ultimately A P1 ->
    ultimately A P2 ->
    ultimately A (fun x => P1 x /\ P2 x).
Proof. intros. apply filter_conj. tauto. Qed.

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
  forall P,
  ultimately (image_filterType A f) P =
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

(* The product of two filters. *)

(* The members of the product filter are all subsets [P] which contain a product
   [P1] * [P2], where [P1] and [P2] are members of the left-hand and right-hand
   filters, respectively. *)

(* This is a symmetric notion of product. It is *not* the same as writing
   [ultimately a1, [ultimately a2, P (a1, a2)]], which is dissymmetric. *)

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
