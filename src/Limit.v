Require Import TLC.LibTactics.
Require Import TLC.LibEqual.
Require Import TLC.LibLogic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Filter.
Require Import ZArith.
Require Import Psatz.
Local Open Scope Z_scope.

(* A notion of limit, or convergence, or divergence -- it all depends on which
   filters one uses. The assertion [limit f] states that any property [P] that
   is ultimately true of [y] is ultimately true of [f x]. If [f] is a function
   from [nat] to [nat], equipped with its standard filter, this means that [f x]
   tends to infinity as [x] tends to infinity. *)

(* [limit] could take two arguments of type [filter A] and [filter B]. Instead,
   we take two arguments of type [filterType]. *)

Section Limit.

Variables A B : filterType.

Definition limit f :=
  finer (ultimately (image_filterType A f)) (ultimately B).

Lemma limitP f :
  limit f =
  forall P, ultimately B P -> ultimately A (fun x => P (f x)).
Proof. reflexivity. Qed.

Lemma limit_eq f g :
  limit f ->
  (forall a, f a = g a) ->
  limit g.
Proof.
  rewrite !limitP. intros L E P UP.
  specializes L UP. revert L; filter_closed_under_intersection.
  introv H. rewrite~ E in H.
Qed.

Lemma limit_ultimately_eq f g :
  limit f ->
  ultimately A (fun a => f a = g a) ->
  limit g.
Proof.
  rewrite !limitP. intros L UE P UP.
  specializes L UP. revert L UE; filter_closed_under_intersection.
  introv (H & E). rewrite~ E in H.
Qed.

End Limit.
Arguments limit : clear implicits.

Lemma limit_id:
  forall A : filterType,
  limit A A (fun a : A => a).
Proof. intros. rewrite limitP. auto. Qed.

Hint Resolve limit_id : limit.

Lemma limit_comp :
  forall (A B C : filterType) (f : A -> B) (g : B -> C),
  limit A B f ->
  limit B C g ->
  limit A C (fun x => g (f x)).
Proof.
  introv LF LG. rewrite limitP in *.
  intros P UP.
  specializes LG UP. specializes LF LG. auto.
Qed.

Lemma limit_comp_eq :
  forall (A B C : filterType) (f : A -> B) (g : B -> C) (h : A -> C),
  limit A B f ->
  limit B C g ->
  (forall a, h a = g (f a)) ->
  limit A C h.
Proof.
  introv LF LG E.
  forwards E': func_ext_dep E.
  rewrite E'. applys~ limit_comp.
Qed.

Section LimitToZ.

Variable A : filterType.

Lemma limitPZ (f : A -> Z) :
  limit A Z_filterType f =
  (forall y, ultimately A (fun x => y <= f x)).
Proof.
  rewrite limitP.
  extens. split.
  - introv H. intro y. specializes H (ultimately_ge_Z y). auto.
  - introv H. intros P HP. rewrite ZP in HP. destruct HP as (n0 & Hn0).
    generalize (H n0). filter_closed_under_intersection. auto.
Qed.

Lemma limitPZ_ultimately (cond : Z -> Prop) (f : A -> Z) :
  ultimately Z_filterType cond ->
  limit A Z_filterType f =
  (forall y, cond y -> ultimately A (fun x => y <= f x)).
Proof.
  intro Hcond.
  rewrite limitP. extens. split.
  - introv H. intros y Cy. specializes H (ultimately_ge_Z y). auto.
  - introv H. intros P HP.
    rewrite~ (@ZP_ultimately cond) in HP. destruct HP as (n0 & Cn0 & Hn0).
    generalize (H n0 Cn0). filter_closed_under_intersection. auto.
Qed.

Lemma limitPZ_ge_0 (f : A -> Z) :
  limit A Z_filterType f =
  (forall y, 0 <= y -> ultimately A (fun x => y <= f x)).
Proof.
  rewrite~ (@limitPZ_ultimately (fun x => 0 <= x)).
  apply ultimately_ge_Z.
Qed.

Lemma limit_le f g :
  limit A Z_filterType f ->
  (forall a, f a <= g a) ->
  limit A Z_filterType g.
Proof.
  rewrite !limitPZ.
  intros L I y. generalize (L y); filter_closed_under_intersection.
  intros. specializes I a. lia.
Qed.

Lemma limit_ultimately_le f g :
  limit A Z_filterType f ->
  ultimately A (fun a => f a <= g a) ->
  limit A Z_filterType g.
Proof.
  rewrite !limitPZ.
  intros L UI y. generalize (L y) UI; filter_closed_under_intersection.
  intros. lia.
Qed.

Lemma limit_sum f g :
  limit A Z_filterType f ->
  limit A Z_filterType g ->
  limit A Z_filterType (fun x => (f x) + (g x)).
Proof.
  rewrite !limitPZ_ge_0.
  intros LF LG y Y.
  generalize (LF y Y) (LG y Y); filter_closed_under_intersection.
  intros. lia.
Qed.

Hint Resolve limit_sum : limit.

Lemma limit_sum_cst_l c f :
  limit A Z_filterType f ->
  limit A Z_filterType (fun x => c + (f x)).
Proof.
  rewrite !limitPZ.
  intros L y.
  generalize (L (y - c)); filter_closed_under_intersection.
  intros. lia.
Qed.

Hint Resolve limit_sum_cst_l : limit.

Lemma limit_sum_cst_r c f :
  limit A Z_filterType f ->
  limit A Z_filterType (fun x => (f x) + c).
Proof.
  rewrite !limitPZ.
  intros L y.
  generalize (L (y - c)); filter_closed_under_intersection.
  intros. lia.
Qed.

Hint Resolve limit_sum_cst_r : limit.

Lemma limit_mul f g :
  limit A Z_filterType f ->
  limit A Z_filterType g ->
  limit A Z_filterType (fun x => (f x) * (g x)).
Proof.
  rewrite !limitPZ_ge_0.
  intros LF LG y Y.
  generalize (LF y Y) (LG y Y); filter_closed_under_intersection.
  intros. assert (y * y <= f a * g a) by nia. nia.
Qed.

Hint Resolve limit_mul : limit.

Lemma limit_mul_cst_l c f :
  0 < c ->
  limit A Z_filterType f ->
  limit A Z_filterType (fun x => c * (f x)).
Proof.
  rewrite !limitPZ_ge_0.
  intros C L y Y.
  generalize (L y Y); filter_closed_under_intersection.
  intros; nia.
Qed.

Hint Resolve limit_mul_cst_l : limit.

Lemma limit_mul_cst_r c f :
  0 < c ->
  limit A Z_filterType f ->
  limit A Z_filterType (fun x => (f x) * c).
Proof.
  intros. eapply limit_eq. applys~ limit_mul_cst_l c. eassumption.
  intros; lia.
Qed.

Hint Resolve limit_mul_cst_r : limit.

Lemma limit_max f g :
  limit A Z_filterType f ->
  limit A Z_filterType g ->
  limit A Z_filterType (fun x => Z.max (f x) (g x)).
Proof.
  intros LF LG. rewrite limitPZ in *.
  intros y. generalize (LF y) (LG y); filter_closed_under_intersection.
  intros. lia.
Qed.

Hint Resolve limit_max : limit.

End LimitToZ.

Lemma limit_product :
  forall (A B C : filterType) (f : A -> B) (g : A -> C),
  limit A B f ->
  limit A C g ->
  limit A (product_filterType B C) (fun i => (f i, g i)).
Proof.
  introv Lf Lg. rewrite limitP in *.
  simpl. intros Pp UPp. rewrite productP in UPp.
  destruct UPp as (P1 & P2 & UP1 & UP2 & HPp).
  specializes Lf UP1. specializes Lg UP2.
  revert Lf Lg; filter_closed_under_intersection.
  intros. apply HPp; tauto.
Qed.

(******************************************************************************)

Lemma Zshift_limit (x0 : Z) :
  limit Z_filterType Z_filterType (Zshift x0).
Proof.
  intros. rewrite limitP. introv H.
  rewrite ZP in H. destruct H as [x1 H1].
  rewrite ZP. exists (x1 - x0)%Z. intros. apply H1.
  unfold Zshift. lia.
Qed.

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

(******************************************************************************)

Ltac limit_to_Z :=
  match goal with
    |- limit _ Z_filterType _ =>
    repeat first [
        apply limit_id
      | apply limit_sum_cst_l
      | apply limit_sum_cst_r
      | apply limit_sum
      | apply limit_mul_cst_l; [ auto with zarith | ]
      | apply limit_mul_cst_r; [ auto with zarith | ]
      | apply limit_mul
      | apply limit_max
    ]
  end.

Ltac limit :=
  repeat first [
      apply limit_id
    | limit_to_Z
    | apply limit_product
    | apply Zshift_limit
    | apply limit_liftl
    | apply limit_liftr
  ].

(* We could try to use [auto] with a custom database of lemmas. However, this
   does not seem to work, for strange reasons.

   See the test-cases below:
*)

(*
Goal limit Z_filterType Z_filterType (fun x => 3 * x).
  auto 59 with limit zarith. (* nothing *)

  apply limit_mul_cst_l.
  - auto with zarith.
  - apply limit_id.
Qed.

Goal limit Z_filterType Z_filterType (fun x => x + x).
  auto 59 with limit. (* nothing *)

  apply limit_sum. apply limit_id. apply limit_id.
Qed.

Lemma limit_sum_ f g :
  limit Z_filterType Z_filterType f ->
  limit Z_filterType Z_filterType g ->
  limit Z_filterType Z_filterType (fun x => (f x) + (g x)).
Proof.
Admitted.

Hint Resolve limit_sum_ : limit.

Goal limit Z_filterType Z_filterType (fun x => x + x).
  auto 59 with limit. (* works *)
Qed.
*)
