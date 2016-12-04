Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import TLC.LibTactics.
Require Import LibNatExtra.
Require Import LibRewrite.

(* ---------------------------------------------------------------------------- *)

(* Type classes for two central properties of a binary operation: associativity,
   and the existence of a unit. *)

Class Unit {A : Type} (op : A -> A -> A) := {
  unit:
    A;
  left_unit:
    forall a,
    op unit a = a;
  right_unit:
    forall a,
    op a unit = a
}.

Class Commutative {A : Type} (op : A -> A -> A) := {
  commutativity:
    forall a1 a2,
    op a1 a2 = op a2 a1
}.

Class Associative {A : Type} (op : A -> A -> A) := {
  associativity:
    forall a1 a2 a3,
    op (op a1 a2) a3 = op a1 (op a2 a3)
}.

(* ---------------------------------------------------------------------------- *)

(* Instances for addition, multiplication, maximum. *)

Obligation Tactic := try solve [ intros; ring_simplify; omega ].
Program Instance unit_plus : Unit plus := { unit := 0 }.
Program Instance commutative_plus : Commutative plus.
Program Instance associative_plus : Associative plus.
Program Instance unit_mult : Unit mult := { unit := 1 }.
Program Instance commutative_mult : Commutative mult.
Program Instance associative_mult : Associative mult.
Obligation Tactic := try solve [ intros; repeat max_case; omega ].
Program Instance unit_max  : Unit max  := { unit := 0 }.
Program Instance commutative_max  : Commutative max.
Program Instance associative_max  : Associative max.

(* ---------------------------------------------------------------------------- *)

(* [big op xs] is the iterated application of [op] to the elements of
   the list [xs]. *)

Definition big {A : Type} (op : A -> A -> A) `{Unit A op} xs :=
  fold_right op unit xs.

(* This notation is inspired by Bertot et al.'s paper. *)

Notation "\big [ op ]_ ( r <- range ) f" :=
  (big op (map (fun r => f) range)) (at level 36).

(* ---------------------------------------------------------------------------- *)

(* [big] is covariant. *)

(* TEMPORARY (unused)

Obligation Tactic := unfold Proper, respectful.

Program Instance proper_big A op `{Unit A op} (R : relation A) `{Reflexive A R} :
  Proper (R ++> R ++> R) op -> Proper (Forall2 R ++> R) (big op).
Next Obligation.
  induction 3; simpl; eauto.
Qed.

(* [map] is covariant. *)

Program Instance proper_map A B (R : relation A) (S : relation B) :
  Proper ((R ++> S) ++> Forall2 R ++> Forall2 S) (@map A B).
Next Obligation.
  induction 2; simpl; eauto.
Qed.

*)

Lemma big_covariant:
  forall B op `{Unit B op} (R : relation B) `{Reflexive B R},
  Proper (R ++> R ++> R) op ->
  forall A (f g : A -> B) (xs : list A),
  (forall x, In x xs -> R (f x) (g x)) ->
  R (big op (map f xs)) (big op (map g xs)).
Proof using.
  introv ? hop. induction xs; simpl; intros.
  eauto.
  eapply hop. eauto. eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* [big op] plays well with lists. *)

Lemma big_nil:
  forall A op `{Unit A op},
  big op nil = unit.
Proof using.
  reflexivity.
Qed.

Lemma big_app:
  forall A op `{Unit A op} `{Associative A op} xs ys,
  big op (xs ++ ys) = op (big op xs) (big op ys).
Proof using.
  induction xs; simpl; intros.
  rewrite left_unit. reflexivity.
  rewrite IHxs. rewrite associativity. reflexivity.
Qed.

Lemma big_permutation:
  forall A op `{Unit A op, Commutative A op, Associative A op} xs ys,
  Permutation xs ys ->
  big op xs = big op ys.
Proof using.
  induction 3; simpl; try congruence.
  rewrite <- associativity. rewrite (@commutativity _ _ _ y x). rewrite associativity. congruence.
Qed.

Obligation Tactic := repeat intro; eauto using big_permutation.
Program Instance big_permutation_ A op `{Unit A op, Commutative A op, Associative A op} :
  Proper (@Permutation A ++> @eq A) (big op).

(* ---------------------------------------------------------------------------- *)

(* Distributivity of a product onto a big sum. *)

Class Distributive {A : Type} (mult plus : A -> A -> A) `{Unit A plus} := {
  distributivity:
    forall a b c,
    mult c (plus a b) = plus (mult c a) (mult c b);
  absorption:
    (* The unit of addition must be absorbant for multiplication. *)
    forall c, mult c unit = unit
}.

Obligation Tactic := intros; simpl; ring_simplify; omega.
Program Instance distributive_mult_plus : Distributive mult plus.
(* Program Instance distributive_plus_max  : Distributive plus max. (* fails, due to absorption *) *)

Lemma big_distributive:
  forall A mult plus `{Unit A plus, Associative A plus, Distributive A mult plus},
  forall c xs,
  mult c (big plus xs) = big plus (map (mult c) xs).
Proof using.
  induction xs; simpl; intros.
  (* Nil. *)
  rewrite absorption. reflexivity.
  (* Cons. *)
  rewrite distributivity. rewrite IHxs. reflexivity.
Qed.

Lemma big_map_distributive:
  forall A mult plus `{Unit A plus, Associative A plus, Distributive A mult plus},
  forall c B (f : B -> A) xs,
  mult c (big plus (map f xs)) = big plus (map (fun x => mult c (f x)) xs).
Proof using.
  intros. rewrite big_distributive by eauto with typeclass_instances.
  rewrite map_map. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Intervals. *)

(* [interval_ i len] is the semi-open interval [i, i + len). *)

Fixpoint interval_ i len :=
  match len with
  | 0 =>
      nil
  | S len =>
      i :: interval_ (i + 1) len
  end.

(* [interval i j] is the semi-open interval [i, j). *)

Definition interval i j :=
  interval_ i (j - i).

(* The length of [interval i j] is [j - i]. *)

Lemma length_interval_:
  forall len i,
  length (interval_ i len) = len.
Proof using.
  induction len; simpl; congruence.
Qed.

Lemma length_interval:
  forall i j,
  length (interval i j) = j - i.
Proof using.
  unfold interval. eauto using length_interval_.
Qed.

(* Basic properties. *)

Lemma interval_is_empty:
  forall i j,
  j <= i ->
  interval i j = nil.
Proof using.
  unfold interval. intros.
  replace (j - i) with 0 by omega.
  reflexivity.
Qed.

Lemma interval_is_nonempty:
  forall i j,
  i < j ->
  interval i j = i :: interval (i + 1) j.
Proof using.
  unfold interval. intros.
  replace (j - i) with (S (j - (i + 1))) by omega.
  reflexivity.
Qed.

Lemma in_interval_lo:
  forall x lo hi,
  In x (interval lo hi) ->
  lo <= x.
Proof using.
  assert (forall x len lo, In x (interval_ lo len) -> lo <= x).
    induction len; simpl; intros.
    false.
    match goal with h: _ \/ _ |- _ => destruct h end.
      omega.
      forwards: IHlen. eauto. omega.
  eauto.
Qed.

Lemma in_interval_hi:
  forall x lo hi,
  In x (interval lo hi) ->
  x < hi.
Proof using.
  assert (aux: forall x len lo, In x (interval_ lo len) -> x < lo + len /\ len > 0).
    induction len; simpl; intros.
    false.
    match goal with h: _ \/ _ |- _ => destruct h end.
      omega.
      forwards: IHlen. eauto. omega.
  intros. forwards: aux. eauto. omega.
Qed.

Lemma interval_app:
  forall i j k,
  i <= j ->
  j <= k ->
  interval i j ++ interval j k = interval i k.
Proof using.
  assert (reformulation:
    forall len1 i len2,
    interval_ i len1 ++ interval_ (i + len1) len2 = interval_ i (len1 + len2)
  ).
  induction len1; simpl; intros.
  (* Nil. *)
  f_equal. omega.
  (* Cons. *)
  rewrite <- IHlen1. do 3 f_equal. omega.
  (* Back to the original goal. *)
  unfold interval. intros. replace (k - i) with ((j - i) + (k - j)) by omega.
  rewrite <- reformulation. do 2 f_equal. omega.
Qed.

(* Test. *)

Goal \big[plus]_(i <- interval 0 10) i = 45.
Proof using.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The Cartesian product of two lists. *)

Fixpoint cartesian {A B : Type} (xs : list A) (ys : list B) : list (A * B) :=
  match xs with
  | nil =>
      nil
  | x :: xs =>
      map (fun y => (x, y)) ys ++ cartesian xs ys
  end.

(* Looking at [cartesian] from the other side. *)

Lemma cartesian_nil:
  forall {A B : Type} (xs : list A),
  cartesian xs (nil : list B) = nil.
Proof using.
  induction xs; simpl; eauto.
Qed.

Lemma cartesian_cons:
  forall {A B : Type} (xs : list A) y (ys : list B),
  Permutation
    (cartesian xs (y :: ys))
    (map (fun x => (x, y)) xs ++ cartesian xs ys).
Proof using.
  induction xs; simpl; intros.
  (* Nil. *)
  econstructor.
  (* Cons. *)
  econstructor.
  rewrite IHxs.
  do 2 rewrite app_assoc.
  eauto using Permutation_app, Permutation_app_comm.
Qed.

(* Up to a permutation of the list and up to swapping the pair components,
   [cartesian] is commutative. *)

Lemma cartesian_commutative:
  forall {A B C : Type} (f : A * B -> C) (g : B * A -> C),
  (forall x y, f (x, y) = g (y, x)) ->
  forall (xs : list A) (ys : list B),
  Permutation
    (map f (cartesian xs ys))
    (map g (cartesian ys xs)).
Proof using.
  introv h. induction xs as [| x xs ]; simpl; intros.
  (* Nil. *)
  rewrite cartesian_nil. econstructor.
  (* Cons. *)
  rewrite map_app.
  rewrite IHxs.
  rewrite map_map.
  erewrite map_ext by eapply h.
  rewrite <- map_map.
  rewrite <- map_app.
  rewrite <- cartesian_cons.
  eapply Permutation_refl.
Qed.

(* A sum of sums is equal to a single sum over the Cartesian product. *)

Lemma bigop_cartesian:
  forall A B C : Type,
  forall op `{Unit C op, Commutative C op, Associative C op},
  forall f : A * B -> C,
  forall xs ys,
  big op (map f (cartesian xs ys)) =
  big op (map (fun x => big op (map (fun y => f (x, y)) ys)) xs).
Proof using.
  induction xs; simpl; intros.
  (* Nil. *)
  reflexivity.
  (* Cons. *)
  rewrite map_app.
  rewrite map_map.
  rewrite big_app by assumption.
  rewrite IHxs.
  reflexivity.
Qed.

Goal
  forall A B C : Type,
  forall op `{Unit C op, Commutative C op, Associative C op},
  forall f : A * B -> C,
  forall xs ys,
  \big[op]_(xy <- cartesian xs ys) (f xy) =
  \big[op]_(x <- xs) \big[op]_(y <- ys) (f (x, y)).
Proof using.
  intros. eapply bigop_cartesian; eauto with typeclass_instances.
Qed.
