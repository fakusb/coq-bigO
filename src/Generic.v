Require Import Coq.Lists.List.
Import List.ListNotations.

Fixpoint Rarrow (domain : list Type) (range : Type) : Type :=
  match domain with
    | nil => range
    | d :: ds => Rarrow ds (d -> range)
end.

Fixpoint Rtuple (domain : list Type) : Type :=
  match domain with
  | nil => unit
  | d :: nil => d
  | d :: ds => prod (Rtuple ds) d
  end.

Fixpoint Const {A : Type} (domain : list Type) (c : A) : Rarrow domain A :=
  match domain with
  | nil => c
  | d :: ds => Const ds (fun _ => c)
  end.

Lemma Const_eqn_1 : forall A (c : A),
  Const [] c = c.
Proof. intros. reflexivity. Qed.

Lemma Const_eqn_2 : forall A d ds (c : A),
  Const (d :: ds) c = Const ds (fun _ => c).
Proof. intros. reflexivity. Qed.

Hint Rewrite Const_eqn_1 : Const.
Hint Rewrite Const_eqn_2 : Const.
Opaque Const.

Fixpoint Fun' {domain : list Type} {range : Type} {struct domain}
         : (Rtuple domain -> range) -> (Rtuple domain) -> range
  :=
  match domain with
  | nil => fun body t => body tt
  | d :: ds =>
     let f := @Fun' ds range in
     match ds return
        ((Rtuple ds -> range) -> Rtuple ds -> range) ->
        ((Rtuple (d :: ds) -> range) -> Rtuple (d :: ds) -> range)
     with
     | [] => fun _ body t => body t
     | _ =>
         fun f body t =>
         let '(t', x) := t in f (fun p' => body (p', x)) t'
     end f
  end.

Lemma Fun'_eqn_1 : forall range body,
  @Fun' [] range body = (fun _ => body tt).
Proof. intros. reflexivity. Qed.

Lemma Fun'_eqn_2 : forall d range body,
  @Fun' [d] range body = body.
Proof. intros. reflexivity. Qed.

Lemma Fun'_eqn_3 : forall d d' ds range body,
  @Fun' (d :: d' :: ds) range body =
  (fun '(t', x) => @Fun' (d' :: ds) range (fun p' => body (p', x)) t').
Proof. intros. reflexivity. Qed.

Hint Rewrite Fun'_eqn_1 : Fun'.
Hint Rewrite Fun'_eqn_2 : Fun'.
Hint Rewrite Fun'_eqn_3 : Fun'.
Opaque Fun'.

Fixpoint App {domain : list Type} {range : Type} {struct domain}
         : (Rarrow domain range) -> Rtuple domain -> range
  :=
  match domain with
  | nil => fun f x => f
  | d :: ds =>
    let Apprec := @App ds (d -> range) in
    match ds return
      ((Rarrow ds (d -> range)) -> Rtuple ds -> d -> range) ->
      (Rarrow (d :: ds) range) -> Rtuple (d :: ds) -> range
    with
    | [] => fun _ f x => f x
    | _ => fun Apprec f t => Apprec f (fst t) (snd t)
    end Apprec
  end.

Lemma App_eqn_1 : forall range f x,
  @App [] range f x = f.
Proof. intros. reflexivity. Qed.

Lemma App_eqn_2 : forall d range f x,
  @App [d] range f x = f x.
Proof. intros. reflexivity. Qed.

Lemma App_eqn_3 : forall d d' ds range f x,
  @App (d :: d' :: ds) range f x = @App (d' :: ds) (d -> range) f (fst x) (snd x).
Proof. intros. reflexivity. Qed.

Hint Rewrite App_eqn_1 : App.
Hint Rewrite App_eqn_2 : App.
Hint Rewrite App_eqn_3 : App.
Opaque App.

Lemma Fun'_simpl : forall domain range body t,
  @Fun' domain range body t = body t.
Proof.
  intro. induction domain; intros; autorewrite with Fun'.
  - destruct t. reflexivity.
  - destruct domain; autorewrite with Fun'.
    + reflexivity.
    + destruct t. apply IHdomain.
Qed.

Hint Rewrite Fun'_simpl : generic.

Lemma App_Const_simpl :
  forall domain range c x,
  @App domain range (Const domain c) x = c.
Proof.
  intro. induction domain; intros; autorewrite with App.
  - reflexivity.
  - destruct domain; autorewrite with App.
    + reflexivity.
    + destruct x. simpl. rewrite Const_eqn_2.
      rewrite IHdomain. reflexivity.
Qed.

Hint Rewrite App_Const_simpl : generic.

Definition Const' (domain : list Type) {range : Type}
           (cst : range) : Rtuple domain -> range :=
  Fun' (App (Const domain cst)).

Hint Unfold Const' : generic.

Definition Uncurry {domain : list Type} {range : Type}
           (f : Rarrow domain range) : Rtuple domain -> range :=
  Fun' (App f).

Hint Unfold Uncurry : generic.

(******************************************************************************)
(* Rewriting with [generic] *)

Create HintDb nary_prepare.

(* XXX: workaround because [rewrite_strat] does not support [rewrite_strat ...
   in *]. (See https://github.com/coq/coq/issues/6107) *)
Ltac rew_generic :=
  repeat (
      autounfold with generic;
      rewrite_strat (
          try (hints nary_prepare);
          bottomup (hints generic)
        )
    ).

Ltac rew_generic_in H :=
  repeat (
      autounfold with generic in H;
      rewrite_strat (
          try (hints nary_prepare);
          bottomup (hints generic)
        ) in H
    ).

Ltac rew_generic_in_all :=
  match goal with
  | H : _ |- _ => rew_generic_in H; revert H; rew_generic_in_all
  | _ => intros; rew_generic
  end.

(* Try to prove a goal stated using the combinators above from a lemma [L] that
   is equivalent but does not use the combinators. *)
Ltac prove_nary L :=
  intros; rew_generic_in_all; eapply L; eauto.
