Require Import Coq.Logic.Classical_Pred_Type.
Require Import Relations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We could in principle perform this construction using [bool] instead of [Prop]
   as the codomain of predicates. However, [bool] does not support quantification
   over an infinite set, whereas [Prop] does. *)

Notation pred A := (A -> Prop) (only parsing).

(* ---------------------------------------------------------------------------- *)

Module Filter.

(* Technically, a filter is a nonempty set of nonempty subsets of A, which is
   closed under inclusion and (finite) intersection. *)

Definition filter A := pred (pred A).

(* Let us write [ultimately] for a filter.  A filter is a modality: if [P] is a
   predicate, then [ultimately P] is a proposition. In other words, a filter is
   a quantifier: if [P] is a predicate, then [ultimately (fun x => P x)] is a
   proposition. Intuitively, this proposition means that ``ultimately'' [P]
   holds. In other words, for every sufficiently ''large'' [x], [P] holds. *)

(* A filter is nonempty. In fact, it contains the universe. In other words,
   [ultimately x => True] is just [True]. Thus, the quantifier [ultimately]
   is weaker than a universal quantifier: [forall x, P x] implies
   [ultimately x, P x]. *)

Definition nonempty A (ultimately : filter A) :=
  ultimately (fun _ => True).

(* A filter does not have the empty set as a member. In other words, every
   member of the filter is nonempty. Thus, the quantifier [ultimately] is
   stronger than an existential quantifier: [ultimately x, P x] implies
   [exists x, P x]. *)

Definition members_nonempty A (ultimately : filter A) :=
  forall P, ultimately P -> exists a, P a.

(* A filter is closed by inclusion and by (finite) intersection. In other
   words, the quantifier [ultimately] is covariant and commutes with (finite)
   conjunction. The last condition means that [ultimately] is universal in
   nature, as opposed to existential. In particular, the universal quantifier
   can be viewed as a filter, but the existential quantifier cannot. *)

Definition closed_inclusion_intersection A (ultimately : filter A) :=
  forall P1 P2 P : pred A,
  ultimately P1 ->
  ultimately P2 ->
  (forall a, P1 a -> P2 a -> P a) ->
  ultimately P.

Record mixin_of (A : Type) := Mixin {
  ultimately : filter A;
  _ : nonempty ultimately;
  _ : members_nonempty ultimately;
  _ : closed_inclusion_intersection ultimately
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

Lemma product_nonempty : Filter.nonempty product.
Proof.
  do 2 (exists (fun _ => True)).
  repeat split; apply filter_universe.
Qed.

Lemma product_members_nonempty : Filter.members_nonempty product.
Proof.
  intros P (P1 & P2 & H1 & H2 & ?).
  pose proof (filter_member_nonempty H1) as [ a1 H1' ].
  pose proof (filter_member_nonempty H2) as [ a2 H2' ].
  exists (a1, a2). eauto.
Qed.

Lemma product_closed_inclusion_intersection :
  Filter.closed_inclusion_intersection product.
Proof.
  intros P Q R.
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
  intuition eauto.
Qed.

Definition product_filterMixin :=
  FilterMixin
    product_nonempty
    product_members_nonempty
    product_closed_inclusion_intersection.

Definition product_filterType := FilterType (A1 * A2) product_filterMixin.

End FilterProduct.

Arguments product : clear implicits.

(* ---------------------------------------------------------------------------- *)

Module OrderedFilter.

Record mixin_of (A : filterType) : Type := Mixin {
  le : relation A;
  _ : forall x : A, ultimately A (fun y => le x y)
}.

Section ClassDef.

Record class_of (A : Type) : Type := Class {
  base : Filter.class_of A;
  mixin : mixin_of (Filter.Pack base)
}.

Structure type := Pack { sort : Type; class : class_of sort }.

Definition filterType (cT : type) := @Filter.Pack (sort cT) (base (class cT)).
(* TEMPORARY (?) this definition looks natural, but does not match (at least
   obviously) the way similar ones are written in ssreflect *)

End ClassDef.

Module Exports.
Coercion base : class_of >-> Filter.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion filterType : type >-> Filter.type.
Notation orderedFilterType := type.
Notation OrderedFilterType T m := (@Pack T m).
Notation OrderedFilterMixin := Mixin.
End Exports.

End OrderedFilter.
Import OrderedFilter.Exports.

Definition orderedFilter_le T := OrderedFilter.le (OrderedFilter.class T).
Arguments orderedFilter_le : clear implicits.

Section OrderedFilterLaws.

Variable A : orderedFilterType.

Lemma orderedFilterP :
  forall x, ultimately A (fun y => orderedFilter_le A x y).
Proof.
  destruct A as [? [? M]]. destruct M. eauto.
Qed.

End OrderedFilterLaws.
