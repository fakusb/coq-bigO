Set Implicit Arguments.
Require Import TLC.LibTactics.
Require Import TLC.LibInt.
Require Import ZArith.
Open Scope Z_scope.
Require Import Psatz.

Hint Resolve Z.le_max_l : zarith.
Hint Resolve Z.le_max_r : zarith.

Lemma Zmax_rub : forall a b c,
  c <= a ->
  c <= b ->
  c <= Z.max a b.
Proof. intros. lia. Qed.

Hint Resolve Zmax_rub : zarith.

Lemma Zquot_mul_2 : forall x,
  0 <= x ->
  x - 1 <= 2 * (x ÷ 2) <= x.
Proof.
  intros x Hx. rewrite <-Zquot2_quot. set (half := Z.quot2 x).
  destruct (Zeven_odd_dec x) as [H|H].
  - rewrite (Zeven_quot2 x); subst half; auto with zarith.
  - rewrite (Zodd_quot2 x); subst half; auto with zarith.
Qed.

(************************************************************)
(* * Pow function *)

Lemma pow_ge_1 : forall k n,
  0 < k ->
  0 <= n ->
  1 <= k ^ n.
Proof.
  intros a b A B.
  rewrite <-(Z.pow_0_r a).
  apply Z.pow_le_mono_r; auto.
Qed.

Hint Resolve pow_ge_1 : zarith.

Lemma pow2_ge_1 : forall n,
  0 <= n ->
  1 <= 2 ^ n.
Proof using.
  auto with zarith.
Qed.

Hint Resolve pow2_ge_1 : zarith.

Lemma pow_succ : forall k n,
  0 < k ->
  0 <= n ->
  k ^ (n + 1) = k * k ^ n.
Proof using.
  intros.
  math_rewrite (n+1 = Z.succ n).
  rewrite Z.pow_succ_r; auto.
Qed.

Lemma pow2_succ : forall n,
  0 <= n ->
  2 ^ (n+1) = 2 * 2^n.
Proof using.
  intros.
  rewrite pow_succ; auto with zarith.
Qed.

(* A tactic that helps dealing with goals containing "b^m" for multiple m *)
Require Import TLC.LibList.

Ltac subst_eq_boxer_list l rewrite_tac :=
  match l with
  | nil => idtac
  | (@boxer _ ?p) :: ?Hs =>
    match p with
      (?tm, ?Htm) =>
      rewrite_tac Htm; clear Htm; clear tm;
      subst_eq_boxer_list Hs rewrite_tac
    end
  end.

(* Develop occurences of (b ^ m) in H into (b ^ (m - min_e) * b ^ min_e).
   (and try to simplify/compute b^(m - min_e)).
 *)
Ltac rew_pow_develop b m min_e H :=
  let m_eq_plusminus := fresh in
  assert (m = min_e + (m - min_e)) as m_eq_plusminus
      by (rewrite Zplus_minus; reflexivity);
  rewrite m_eq_plusminus in H; clear m_eq_plusminus;
  rewrite (Z.pow_add_r b min_e (m - min_e)) in H; [
    rewrite Z.mul_comm in H;
    let tm' := fresh "tm'" in
    let H' := fresh "H'" in
    remember (b ^ (m - min_e)) as tm' eqn:H' in H;
    let e := fresh "e" in
    evar (e: int);
    let Heqe := fresh in
    assert (e = m - min_e) as Heqe
        by (ring_simplify; subst e; reflexivity);
    rewrite <-Heqe in H'; clear Heqe; unfold e in H'; ring_simplify in H';
    rewrite H' in H; clear H'; clear tm'; clear e;
    try rewrite Z.mul_1_l in H
  | ring_simplify; auto with zarith ..].

Ltac rew_pow_aux_goal b min_e normalized_acc :=
  match goal with
  | |- context [ b ^ ?m ] =>
    let tm := fresh "tm" in
    let Heqtm := fresh "Heqtm" in
    remember (b ^ m) as tm eqn:Heqtm in |- *;
    rew_pow_develop b m min_e Heqtm; [
      rew_pow_aux_goal b min_e ((boxer (tm, Heqtm)) :: normalized_acc)
    | ..]
  | _ => subst_eq_boxer_list normalized_acc ltac:(fun E => rewrite E)
  end.

Ltac rew_pow_aux_in b min_e H normalized_acc :=
  match type of H with
  | context [ b ^ ?m ] =>
    let tm := fresh "tm" in
    let Heqtm := fresh "Heqtm" in
    remember (b ^ m) as tm eqn:Heqtm in H;
    rew_pow_develop b m min_e Heqtm; [
      rew_pow_aux_in b min_e H ((boxer (tm, Heqtm)) :: normalized_acc)
    | ..]
  | _ => subst_eq_boxer_list normalized_acc ltac:(fun E => rewrite E in H)
  end.

Tactic Notation "rew_pow" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer).
Tactic Notation "rew_pow" "~" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer); auto_tilde.
Tactic Notation "rew_pow" "*" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer); auto_star.
Tactic Notation "rew_pow" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer).
Tactic Notation "rew_pow" "~" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer); auto_tilde.
Tactic Notation "rew_pow" "*" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer); auto_star.

(* Test *)
Axiom P : int -> Prop.
Goal forall n, P (1 + 2 ^ (n + 3) + 2 ^ n + 2 ^ (n+1)).
Proof.
  intros.
  skip_asserts H: (3 = 2 ^ (n+3)). rew_pow 2 n in H.
  rew_pow 2 n.
Admitted.

(* ---------------------------------------------------------------------------- *)

(* Base 2 logarithm. *)

Lemma Zlog2_step : forall x,
  2 <= x ->
  1 + Z.log2 (x÷2) = Z.log2 x.
Proof.
  admit. (* TODO: prove from the log2_step in LibNatExtra? *)
Qed.
