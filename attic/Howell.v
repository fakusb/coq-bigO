Require Import Coq.Logic.Classical_Pred_Type.
Require Import mathcomp.ssreflect.all_ssreflect.
Require Import mathcomp.algebra.all_algebra.
Require Import mathcomp.ssreflect.bigop.
Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Filter.
Require Import Dominated.

Definition filter_nat_base : filter nat :=
  fun P => exists n0, forall n, le n0 n -> P n.

Definition mixin_filter_nat : filterMixin filter_nat_base.
Proof.
  constructor; unfold filter_nat_base.
  - exists O. eauto.
  - intros ? [? ?]. eauto.
  - { intros P1 P2 P [n1 H1] [n2 H2] I. exists (max n1 n2).
      intros. apply I.
      - apply H1. apply Max.max_lub_l with n2. eauto.
      - apply H2. apply Max.max_lub_r with n1. eauto. }
Qed.

Definition filter_nat := FilterType mixin_filter_nat.
Definition filter_nat_nat := filter_product filter_nat filter_nat.

Definition dominated_forall := dominated filter_nat_nat.

Section Hat.

Variable B : numDomainType.

Definition hat_nat (f: nat -> B): nat -> B :=
  fun n => \big[Num.max/0]_(0 <= i < n+1) f i.

Definition hat_nat_nat (f: nat * nat -> B) : nat * nat -> B :=
  fun p =>
    let (n1, n2) := p in
    \big[Num.max/0]_(0 <= i < n1+1) \big[Num.max/0]_(0 <= j < n2+1) f (i, j).


SearchAbout Num.max.

Lemma hat_nat_ge : forall f, forall n, f n <= hat_nat f n.
Proof.
  intros. unfold hat_nat. rewrite big_nat_recr.
Admitted.

(* nondecr f -> hat f = f *)

End Hat.