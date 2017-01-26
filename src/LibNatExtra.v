Set Implicit Arguments.
Require Export Omega.
Require Export ArithRing.
Require Export Coq.Numbers.Natural.Peano.NPeano.
  (* [Nat] is a sub-module of [NPeano], which seems to contain many things.
     E.g. it defines [Nat.div], [Nat.pow], [Nat.log2].
     E.g. it defines [Nat.max], which is the same as [max].
     E.g. it has many properties of [max], see [Coq.Structures.GenericMinMax].
     Unfortunately [Nat.le] is NOT the same as [le], which is [Peano.le].
     For this reason, we do NOT import [Nat]. *)
  Notation log2 := Nat.log2.
Require Import TLC.LibTactics.
Require Import LibFunOrd.

(* ---------------------------------------------------------------------------- *)

(* A few simplification lemmas. *)

Lemma plus_lt_plus:
  forall a x y,
  x < y ->
  x + a < y + a.
Proof using.
  intros. omega.
Qed.

Lemma plus_le_plus:
  forall a x y,
  x <= y ->
  x + a <= y + a.
Proof using.
  intros. omega.
Qed.

(* ---------------------------------------------------------------------------- *)

(* [a <= b] is equivalent to [b = a + n] for some unknown [n]. *)

Lemma leq_to_eq_plus:
  forall a b,
  a <= b ->
  exists n,
  b = a + n.
Proof.
  intros. exists (b - a). omega.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Make [omega] a hint. *)

Hint Extern 1 => omega : omega.

(* ---------------------------------------------------------------------------- *)

(* This lemma allows simplifying a [max] expression, by cases. *)

Lemma max_case:
  forall m1 m2,
  m2 <= m1 /\ max m1 m2 = m1 \/
  m1 <= m2 /\ max m1 m2 = m2.
Proof using.
  intros. destruct (@le_gt_dec m1 m2); eauto using max_r, max_l with omega.
Qed.

(* This tactic looks for a [max] expression in the hypotheses or in the goal
   and applies the above lemma. *)

Ltac max_case_m_n_as m n h :=
  let i := fresh in
  destruct (max_case m n) as [ [ h i ] | [ h i ] ];
  rewrite i in *;
  clear i.

Ltac max_case_as h :=
  match goal with
  | |- context[max ?m ?n] =>
      max_case_m_n_as m n h
  | foo: context[max ?m ?n] |- _ =>
      max_case_m_n_as m n h
  end.

Ltac max_case :=
  let h := fresh in
  max_case_as h.

(* [max m1 m2] is an upper bound for [m1] and [m2]. This can be sufficient
   to reason about [max] without introducing a case split. *)

Lemma max_ub:
  forall m1 m2,
  m1 <= max m1 m2 /\ m2 <= max m1 m2.
Proof using.
  intros. eauto using Nat.le_max_l, Nat.le_max_r.
Qed.

Ltac max_ub_m_n_as m n h1 h2 :=
  destruct (max_ub m n) as [ h1 h2 ];
  generalize dependent (max m n);
  intros.

Ltac max_ub_as h1 h2 :=
  match goal with
  | |- context[max ?m ?n] =>
      max_ub_m_n_as m n h1 h2
  | foo: context[max ?m ?n] |- _ =>
      max_ub_m_n_as m n h1 h2
  end.

Ltac max_ub :=
  let h1 := fresh in
  let h2 := fresh in
  max_ub_as h1 h2.

(* ---------------------------------------------------------------------------- *)

(* Properties of multiplication. *)

Lemma mult_positive:
  forall m n,
  0 < m ->
  0 < n ->
  0 < m * n.
Proof using.
  intros.
  destruct (eq_nat_dec (m * n) 0).
  forwards [ ? | ? ]: mult_is_O. eauto. omega. omega.
  generalize dependent (m * n). intros. omega.
Qed.

Hint Resolve mult_positive : positive.

Lemma mult_magnifies_left:
  forall m n,
  0 < n ->
  m <= n * m.
Proof using.
  intros.
  destruct n; [ omega | simpl ].
  generalize (n * m); intro.
  omega.
Qed.

Lemma mult_magnifies_right:
  forall m n,
  0 < n ->
  m <= m * n.
Proof using.
  intros. rewrite mult_comm. eauto using mult_magnifies_left.
Qed.

Lemma mult_magnifies_right_strict:
  forall m n,
  0 < m ->
  1 < n ->
  m < m * n.
Proof using.
  intros.
  do 2 (destruct n; [ omega | ]).
  rewrite mult_comm. simpl.
  generalize (n * m). intros. omega.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Properties of division. *)

(* It is strange that the Coq standard library offers [divmod_spec],
   but lacks its corollary [div_spec]. *)

Lemma div_spec:
  forall n k,
  0 < k ->
  exists r,
  k * (n / k) + r = n /\ 0 <= r < k.
Proof using.
  intros. unfold Nat.div.
  destruct k; [ false; omega | simpl ].
  forwards: Nat.divmod_spec n k 0 k. eauto.
  destruct (Nat.divmod n k 0 k) as [ q r ]. unpack. simpl.
  exists (k - r). omega.
Qed.

(* Avoid undesired simplifications. *)
(* TEMPORARY [plus] should be opaque too? *)
Global Opaque mult Nat.div max.

(* A tactic to reason about [n/2] in terms of its specification. *)

Ltac div2 :=
  match goal with |- context[?n/2] =>
    let h := fresh in
    forwards h: div_spec n 2; [ omega |
      gen h; generalize (n/2); intros; unpack
    ]
  end.

(* [./2] is monotonic. *)

Lemma div2_monotonic:
  forall m n,
  m <= n ->
  m / 2 <= n / 2.
Proof using.
  intros. repeat div2. omega.
Qed.

Lemma div2_step:
  forall n,
  (n + 2) / 2 = n/2 + 1.
Proof using.
  intros. repeat div2. omega.
Qed.

Lemma div2_monotonic_strict:
  forall m n,
  m + 2 <= n ->
  m / 2 < n / 2.
Proof using.
  intros. cut (m/2 + 1 <= n/2). omega.
  rewrite <- div2_step.
  eauto using div2_monotonic.
Qed.

Lemma mult_div_2:
  forall n,
  2 * (n / 2) <= n.
Proof using.
  intros. div2. omega.
Qed.

Lemma div_mult_2:
  forall n,
  (2 * n) / 2 = n.
Proof using.
  intros. div2. omega.
Qed.

(* A collection of lemmas about division by two and ordering. *)

Lemma prove_div2_le:
  forall m n,
  m <= 2 * n + 1 -> (* tight *)
  m / 2 <= n.
Proof using.
  intros. div2. omega.
Qed.

Lemma use_div2_plus1_le:
  forall m n,
  (n + 1) / 2 <= m -> (* tight *)
  n <= 2 * m.
Proof using.
  intros m n. div2. omega.
Qed.

Lemma use_div2_le:
  forall m n,
  n / 2 <= m -> (* tight *)
  n <= 2 * m + 1.
Proof using.
  intros m n. div2. omega.
Qed.

Lemma prove_le_div2:
  forall m n,
  2 * m <= n -> (* tight *)
  m <= n / 2.
Proof using.
  intros. div2. omega.
Qed.

Lemma use_le_div2:
  forall m n,
  n <= m / 2 -> (* tight *)
  2 * n <= m.
Proof using.
  intros m n. div2. omega.
Qed.

Lemma prove_div2_lt:
  forall m n,
  m < 2 * n -> (* tight *)
  m / 2 < n.
Proof using.
  intros. div2. omega.
Qed.

Lemma use_div2_lt:
  forall m n,
  m / 2 < n -> (* tight *)
  m < 2 * n.
Proof using.
  intros m n. div2. omega.
Qed.

Lemma prove_lt_div2:
  forall m n,
  2 * m < n - 1 -> (* tight *)
  m < n / 2.
Proof using.
  intros. div2. omega.
Qed.

Lemma prove_lt_div2_zero:
  forall n,
  1 < n -> (* tight *)
  0 < n / 2.
Proof using.
  intros. div2. omega.
Qed.

Lemma use_lt_div2:
  forall m n,
  m < (n + 1) / 2 -> (* tight *)
  2 * m < n.
Proof using.
  intros m n. div2. omega.
Qed.

Hint Resolve prove_lt_div2_zero : positive.

Hint Resolve prove_div2_le use_div2_plus1_le use_div2_le prove_le_div2
use_le_div2 prove_div2_lt use_div2_lt prove_lt_div2 use_lt_div2 :
div2.

Goal
  forall n,
  n <= 2 * (n / 2) + 1.
Proof using.
  eauto with div2.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The [pow] function. *)

Lemma power_positive:
  forall k n,
  0 < n ->
  0 < n^k.
Proof using.
  induction k; simpl; intros.
  omega.
  eauto using mult_positive.
Qed.

Hint Resolve power_positive : positive.

Lemma power_plus:
  forall k1 k2 n,
  n^(k1 + k2) = n^k1 * n^k2.
Proof using.
  induction k1; simpl; intros.
  omega.
  rewrite IHk1. ring.
Qed.

Lemma power_of_zero:
  forall k,
  0 < k ->
  0^k = 0.
Proof using.
  induction k; simpl; intros; omega.
Qed.

Lemma power_monotonic_in_k:
  (* We must assume [n > 0], because [0^0] is 1, yet [0^1] is 0. *)
  forall n,
  0 < n ->
  monotonic le le (fun k => n^k).
Proof using.
  intros. intros k1 k2 ?.
  assert (f: k2 = k1 + (k2 - k1)). omega.
  rewrite f. rewrite power_plus.
  eapply mult_magnifies_right.
  eapply power_positive.
  assumption.
Qed.

Lemma power_strictly_monotonic_in_k:
  forall n,
  1 < n ->
  monotonic lt lt (fun k => n^k).
Proof using.
  intros. intros k1 k2 ?.
  assert (f: k2 = k1 + S (k2 - k1 - 1)). omega.
  rewrite f. rewrite power_plus.
  eapply mult_magnifies_right_strict.
    { eauto with positive omega. }
    { simpl.
      eapply lt_le_trans with (m := n). omega.
      eapply mult_magnifies_right.
      eauto with positive omega. }
Qed.

Lemma power_strictly_monotonic_in_n:
  forall k,
  0 < k ->
  monotonic lt lt (fun n => n^k).
Proof using.
  (* We first prove that this holds when [n1] is nonzero,
     and reformulate the hypothesis [k > 0] so that it is
     amenable to induction. *)
  assert (f:
    forall k n1 n2,
    0 < n1 < n2 ->
    n1^(S k) < n2^(S k)
  ).
  { induction k; simpl; intros.
    omega.
    eapply lt_le_trans; [ eapply mult_lt_compat_r | eapply mult_le_compat_l ]. (* wow *)
      omega.
      eapply power_positive with (k := S k). omega.
      forwards: IHk. eauto. simpl in *. omega. }
  (* There remains to treat separately the case where [n1] is 0. *)
  intros. intros n1 n2 ?.
  destruct (le_gt_dec n1 0).
    { assert (n1 = 0). omega. subst.
      rewrite power_of_zero by assumption.
      eapply power_positive. omega. }
    { destruct k; [ omega | ].
      eapply f. omega. } (* ouf *)
Qed.

Hint Resolve power_monotonic_in_k power_strictly_monotonic_in_k
power_strictly_monotonic_in_n : monotonic typeclass_instances.

Lemma power_monotonic_in_n:
  forall k,
  monotonic le le (fun n => n^k).
Proof using.
  intros.
  destruct (eq_nat_dec k 0).
  { subst. simpl. repeat intro. omega. }
  { eauto with monotonic omega. }
Qed.

Hint Resolve power_monotonic_in_n : monotonic typeclass_instances.

(* TEMPORARY maybe explicitly use [inverse_monotonic] in lemmas below *)

Lemma power_inverse_monotonic_in_k:
  forall n,
  1 < n ->
  forall k1 k2,
  n^k1 <= n^k2 ->
  k1 <= k2.
Proof using.
  intros.
  eapply monotonic_lt_lt_implies_inverse_monotonic_le_le with (f := fun k => n^k);
  eauto using power_strictly_monotonic_in_k.
Qed.

Lemma power_strictly_inverse_monotonic_in_k:
  forall n k1 k2,
  0 < n ->
  n^k1 < n^k2 ->
  k1 < k2.
Proof using.
  intros.
  eapply monotonic_le_le_implies_inverse_monotonic_lt_lt with (f := fun k => n^k);
  eauto using power_monotonic_in_k.
Qed.

Lemma power_strictly_inverse_monotonic_in_k_variant:
  forall n k1 k2,
  0 < n ->
  n^k1 < n^(1 + k2) ->
  k1 <= k2.
Proof using.
  intros. cut (k1 < 1 + k2). { omega. }
  eauto using power_strictly_inverse_monotonic_in_k.
Qed.

Lemma power_strictly_inverse_monotonic_in_k_frame:
  forall n k1 k2,
  1 < n ->
  n^k2 <= n^k1 < n^(1 + k2) ->
  k1 = k2.
Proof using.
  intros.
  assert (k2 <= k1).
    { eapply power_inverse_monotonic_in_k with (n := n); eauto with omega. }
  assert (k1 < 1 + k2).
    { eapply power_strictly_inverse_monotonic_in_k with (n := n); eauto with omega. }
  omega.
Qed.

Lemma power_inverse_monotonic_in_n:
  forall k,
  0 < k ->
  forall n1 n2,
  n1^k <= n2^k ->
  n1 <= n2.
Proof using.
  intros.
  eapply monotonic_lt_lt_implies_inverse_monotonic_le_le with (f := fun n => n^k);
  eauto using power_strictly_monotonic_in_n.
Qed.

(* A lower bound on [2^n]. *)

Lemma n_lt_power:
  forall n,
  n < 2^n.
Proof using.
  induction n; simpl; omega.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Base 2 logarithm. *)

(* The Coq standard library gives us the following:
     Lemma log2_spec : forall n, 0<n ->
       2^(log2 n) <= n < 2^(S (log2 n)).
*)

Ltac log2_spec :=
  match goal with |- context[log2 ?n] =>
    let h := fresh in
    forwards h: Nat.log2_spec n; [ eauto with positive omega |
      gen h; generalize (log2 n); intros; unpack
    ]
  end.

(* The above specification is functional, i.e., it defines [log2 n] in a
   unique manner. *)

Lemma log2_uniqueness_half:
  forall n k1 k2,
  2^k1 <= n < 2^(1 + k1) ->
  2^k2 <= n < 2^(1 + k2) ->
  k1 <= k2.
Proof using.
  simpl. intros. unpack.
  eapply power_strictly_inverse_monotonic_in_k_variant with (n := 2). omega.
  eauto using le_lt_trans.
Qed.

Lemma log2_uniqueness:
  forall n k1 k2,
  2^k1 <= n < 2^(1 + k1) ->
  2^k2 <= n < 2^(1 + k2) ->
  k1 = k2.
Proof using.
  intros.
  forwards: log2_uniqueness_half n k1 k2; eauto.
  forwards: log2_uniqueness_half n k2 k1; eauto.
  omega.
Qed.

(* When applied to a power of two, [log2] yields the exponent. *)

Lemma log2_pow:
  forall k,
  log2 (2^k) = k.
Proof using.
  intros k. log2_spec.
  symmetry. eapply power_strictly_inverse_monotonic_in_k_frame with (n := 2). omega.
  eauto.
Qed.

(* This is just a repetition of one half of [log2_spec]. *)

Lemma pow_log2:
  forall n,
  0 < n ->
  2 ^ (log2 n) <= n.
Proof using.
  intros. eapply Nat.log2_spec. eauto.
Qed.

Lemma pow_succ_log2:
  forall n,
  n < 2^(1 + log2 n).
Proof using.
  intros.
  destruct (eq_nat_dec n 0).
  { subst. simpl. omega. }
  { eapply Nat.log2_spec. omega. }
Qed.

(* The inductive step of many arguments that involve divide-and-conquer. *)

Lemma log2_step:
  forall n,
  2 <= n ->
  1 + log2 (n/2) = log2 n.
Proof using.
  intros. repeat log2_spec.
  eapply log2_uniqueness; [ | eauto ].
  simpl. eauto with div2.
Qed.

(* [log2] is monotonic. *)

Lemma log2_monotonic:
  monotonic le le log2.
Proof using.
  intros m n ?.
  (* A special case for [m = 0]. *)
  destruct (eq_nat_dec m 0).
  { subst. unfold log2. simpl. omega. }
  (* Case [m > 0]. *)
  do 2 log2_spec.
  eapply power_strictly_inverse_monotonic_in_k_variant with (n := 2); simpl; omega.
Qed.

Hint Resolve log2_monotonic : monotonic typeclass_instances.

(* A collection of lemmas involving [log2] and ordering. *)

Lemma prove_le_log2:
  forall k n,
  2^k <= n ->
  k <= log2 n.
Proof using.
  intros.
  forwards: log2_monotonic. eauto.
  rewrite log2_pow in *.
  assumption.
Qed.

Lemma prove_log2_le:
  forall k n,
  n <= 2^k ->
  log2 n <= k.
Proof using.
  intros.
  forwards: log2_monotonic. eauto.
  rewrite log2_pow in *.
  assumption.
Qed.

Lemma prove_log2_lt:
  forall k n,
  0 < n ->
  n < 2^k ->
  log2 n < k.
Proof using.
  intros.
  eapply monotonic_le_le_implies_inverse_monotonic_lt_lt with (f := fun n => 2^n).
    { eauto with monotonic. }
  eauto using le_lt_trans, pow_log2.
Qed.

Hint Resolve prove_le_log2 prove_log2_le prove_log2_lt : log2.

(* An upper bound on [log2 n]. *)

Lemma log2_lt_n:
  forall n,
  0 < n ->
  log2 n < n.
Proof using.
  eauto using prove_log2_lt, n_lt_power.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The existence of the function [log2] means that the sequence [n], [n/2],
   [n/4], etc. tends towards zero. We can exploit this by giving the following
   induction principle. *)

Lemma div2_induction:
  forall (P : nat -> Prop),
  P 0 ->
  (forall n, P (n/2) -> P n) ->
  forall n, P n.
Proof using.
  introv hbase hstep.
  assert (f: forall k n, log2 n < k -> P n).
  { induction k; intros.
    false. omega.
    (* Special cases for [n = 0] and [n = 1]. *)
    destruct (eq_nat_dec n 0); [ subst n | ]. { eauto. }
    destruct (eq_nat_dec n 1); [ subst n | ]. { eauto. }
    (* In the general case, [2 <= n], we use [log2_step]. *)
    eapply hstep. eapply IHk.
    cut (1 + log2 (n / 2) <= k). { omega. }
    rewrite log2_step by omega.
    omega.
  }
  intros. eapply f with (k := log2 n + 1). omega.
Qed.

(* The following variant of the above induction principle allows
   establishing a property [P] that mentions both [log2 n] and [n]. *)

Lemma log2_induction:
  forall (P : nat -> nat -> Prop),
  P 0 0 ->
  P 0 1 ->
  (forall k n, 2 <= n -> P k (n/2) -> P (1+k) n) ->
  forall n, P (log2 n) n.
Proof using.
  introv h00 h01 hkn.
  (* Maybe one could give a direct proof; anyway, we choose to give
     a proof based on the previous induction principle. *)
  assert (forall n, 1 <= n -> P (log2 n) n).
  { eapply (@div2_induction (fun n => 1 <= n -> P (log2 n) n)).
    (* The base case cannot arise. *)
    { intro. false. omega. }
    (* Step. *)
    { intros n IH ?.
      (* Special case for [n = 1]. *)
      destruct (eq_nat_dec n 1); [ subst n; exact h01 | ].
      (* In the general case, [2 <= n], we use [log2_step]. *)
      assert (2 <= n). { omega. }
      rewrite <- log2_step by assumption.
      eauto with div2. }
  }
  intro n.
  (* Special case for [n = 0]. *)
  destruct (eq_nat_dec n 0); [ subst n; exact h00 | ].
  (* General case. *)
  eauto with omega.
Qed.
