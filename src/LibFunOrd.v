(* This library defines some notions that involve functions and order,
   such as the property of being monotonic. *)

Set Implicit Arguments.
Require Import Coq.Classes.Morphisms.
Require Import TLC.LibTactics Omega.

(* -------------------------------------------------------------------------- *)

(* Definitions. *)

(* [within okA okB f] holds iff [f] maps [okA] into [okB]. *)

Definition within A B (okA : A -> Prop) (okB : B -> Prop) (f : A -> B) :=
  forall a,
  okA a ->
  okB (f a).

Definition preserves A (okA : A -> Prop) (f : A -> A) :=
  within okA okA f.

(* [monotonic leA leB f] holds iff [f] is monotonic with respect to
   the relations [leA] and [leB], i.e., [f] maps [leA] to [leB]. *)

Definition monotonic A B (leA : A -> A -> Prop) (leB : B -> B -> Prop) (f : A -> B) :=
  forall a1 a2,
  leA a1 a2 ->
  leB (f a1) (f a2).

(* [inverse_monotonic leA leB f] holds iff [f^-1] maps [leB] to [leA]. *)

Definition inverse_monotonic A B (leA : A -> A -> Prop) (leB : B -> B -> Prop) (f : A -> B) :=
  forall a1 a2,
  leB (f a1) (f a2) ->
  leA a1 a2.

(* [inflationary okA leA] holds iff [a] is less than [f a], with
   respect to the relation [leA], and for every [a] in [okA]. *)

Definition inflationary A (okA : A -> Prop) (leA : A -> A -> Prop) (f : A -> A) :=
  forall a,
  okA a ->
  leA a (f a).

(* If [leB] is a relation on [B], then [pointwise okA leB] is a relation
   on [A -> B]. *)

Definition pointwise A B (okA : A -> Prop) (leB : B -> B -> Prop) (f g : A -> B) :=
  forall a,
  okA a ->
  leB (f a) (g a).

(* [le_after a leA] is a relation on [A].

   It holds for elements [x] and [y] iff [leA x y] and [x] and [y] are after
   [a], i.e. [leA a x] and [leA a y].
*)

Definition le_after A (a : A) (leA : A -> A -> Prop) :=
  fun (x y : A) => leA a x /\ leA a y /\ leA x y.

(* -------------------------------------------------------------------------- *)

(* If [f] is monotonic, then rewriting in the argument of [f] is permitted. *)

(* Note: in order for [rewrite] to work properly, the lemmas that are able to
   prove [monotonic] assertions should be added to [typeclass_instances]. *)

(* TEMPORARY maybe this should be the *definition* of [monotonic] *)

Program Instance monotonic_Proper
  A B (leA : A -> A -> Prop) (leB : B -> B -> Prop) (f : A -> B) :
  monotonic leA leB f -> Proper (leA ++> leB) f.

(* -------------------------------------------------------------------------- *)

(* Letting [eauto] exploit [monotonic] and [inverse_monotonic]. *)

Lemma use_monotonic:
  forall B (leB : B -> B -> Prop) A (leA : A -> A -> Prop) (f : A -> B),
  monotonic leA leB f ->
  forall a1 a2,
  leA a1 a2 ->
  leB (f a1) (f a2).
Proof using.
  unfold monotonic. eauto.
Qed.

(* This variant is useful when the function has two arguments and one
   wishes to exploit monotonicity in the first argument. *)

Lemma use_monotonic_2:
  forall B (leB : B -> B -> Prop) A (leA : A -> A -> Prop) C (f : A -> C -> B) a1 a2 c,
  monotonic leA leB (fun a => f a c) ->
  leA a1 a2 ->
  leB (f a1 c) (f a2 c).
Proof using.
  unfold monotonic. eauto.
Qed.

Lemma use_inverse_monotonic:
  forall A (leA : A -> A -> Prop) B (leB : B -> B -> Prop) (f : A -> B),
  inverse_monotonic leA leB f ->
  forall a1 a2,
  leB (f a1) (f a2) ->
  leA a1 a2.
Proof using.
  unfold inverse_monotonic. eauto.
Qed.

(* It seems that these lemmas can be used as a hint only if we pick a
   specific instance of the ordering relation that appears in the
   conclusion. Furthermore, picking a specific instance of the
   ordering relation that appears in the premise can help apply
   [omega] to the premise. *)

Hint Resolve (@use_monotonic nat le nat le) (@use_monotonic nat lt nat lt)
: monotonic typeclass_instances.

Hint Resolve (@use_monotonic_2 nat le nat le) (@use_monotonic_2 nat lt nat lt)
: monotonic typeclass_instances.

Hint Resolve (@use_inverse_monotonic nat le nat le)
(@use_inverse_monotonic nat lt nat lt) : monotonic typeclass_instances.

(* -------------------------------------------------------------------------- *)

(* A little fact. If [f], viewed as a function of [A] into [B -> C], is
   monotonic, then its specialized version [fun a => f a b], which is a
   function of [A] to [C], is monotonic as well. And the converse holds. *)

Lemma monotonic_pointwise_specialize:
  forall A B C leA okB leC (f : A -> B -> C),
  monotonic leA (pointwise okB leC) f ->
  forall b, okB b -> monotonic leA leC (fun a => f a b).
Proof using.
  unfold monotonic, pointwise. auto.
Qed.

Lemma monotonic_pointwise_generalize:
  forall A B C leA (okB : B -> Prop) leC (f : A -> B -> C),
  (forall b, okB b -> monotonic leA leC (fun a => f a b)) ->
  monotonic leA (pointwise okB leC) f.
Proof using.
  unfold monotonic, pointwise. auto.
Qed.

(* -------------------------------------------------------------------------- *)

Require Import Coq.Arith.Arith.

(* The following tactics allow proving implications between inequalities
   by contraposition, while exploiting the fact that the negation of a
   strict inequality is a large inequality. *)

Ltac prove_le_le_by_contraposition :=
  match goal with h: ?a <= ?b |- ?x <= ?y =>
    (destruct (le_gt_dec x y); [ assumption | ]);
    assert (b < a); [ clear h | omega ]
  end.

Ltac prove_lt_lt_by_contraposition :=
  match goal with h: ?a < ?b |- ?x < ?y =>
    (destruct (le_gt_dec y x); [ false | omega ]);
    assert (b <= a); [ clear h | omega ]
  end.

(* If a function of type [nat -> nat] is strictly monotonic, then
   [f x1 <= f x2] implies [x1 <= x2]. The two assertions are in
   fact equivalent, since a strictly monotonic function is a
   fortiori a monotonic function. *)

Lemma monotonic_lt_lt_implies_inverse_monotonic_le_le:
  forall f : nat -> nat,
  monotonic lt lt f ->
  inverse_monotonic le le f.
Proof using.
  intros f ? x y ?. prove_le_le_by_contraposition. eauto.
Qed.

Lemma monotonic_lt_lt_implies_monotonic_le_le:
  forall f : nat -> nat,
  monotonic lt lt f ->
  monotonic le le f.
Proof using.
  introv h. intros x1 x2 ?.
  destruct (eq_nat_dec x1 x2).
    { assert (f x1 = f x2). congruence. omega. }
    { assert (f x1 < f x2). eapply h; omega. omega. }
Qed.

Hint Resolve monotonic_lt_lt_implies_inverse_monotonic_le_le
monotonic_lt_lt_implies_monotonic_le_le : monotonic typeclass_instances.

Goal
  forall f : nat -> nat,
  monotonic lt lt f ->
  forall x1 x2,
  f x1 <= f x2 <-> (* equivalence *)
  x1 <= x2.
Proof using.
  split; eauto with monotonic.
Qed.

(* If a function of type [nat -> nat] is monotonic, then
   [f x1 < f x2] implies [x1 < x2]. The converse is false. *)

Lemma monotonic_le_le_implies_inverse_monotonic_lt_lt:
  forall f : nat -> nat,
  monotonic le le f ->
  inverse_monotonic lt lt f.
Proof using.
  intros f ? x y ?. prove_lt_lt_by_contraposition. eauto.
Qed.

Hint Resolve monotonic_le_le_implies_inverse_monotonic_lt_lt :
monotonic typeclass_instances.
