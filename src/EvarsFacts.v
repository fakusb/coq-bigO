(******************************************************************************)
(* pose_facts facts                                                           *)
(* prove_later facts                                                          *)
(* close_facts                                                                *)
(* pose_facts_evars facts a b...                                              *)
(******************************************************************************)

Definition close_facts P1 P2 :=
  P2 -> P1.

Lemma pose_facts_lemma :
  forall facts facts_closed P, (facts -> P) -> close_facts facts facts_closed -> facts_closed -> P.
Proof. unfold close_facts. tauto. Qed.

Ltac pose_facts facts :=
  eapply pose_facts_lemma; [ intro facts | .. ].

Ltac closed_facts_ty T :=
  lazymatch T with
  | and ?x ?y =>
    lazymatch y with
    | and _ _ =>
      let y' := closed_facts_ty y in
      constr:(and x y')
    | _ => constr:(x)
    end
  end.

Ltac close_facts_aux tm ty :=
  lazymatch ty with
  | and ?x ?y =>
    split; [apply (@proj1 x y tm) | close_facts_aux (@proj2 x y tm) y]
  | ?x => split; [apply tm | exact I]
  end.

Ltac close_facts :=
  unfold close_facts;
  let facts_closed := fresh "facts_closed" in
  intro facts_closed;
  match goal with
  | |- ?facts =>
    let facts_closed_T := closed_facts_ty facts in
    close_facts_aux facts_closed facts_closed_T
  end.

Ltac nested_and_proj2 p :=
  lazymatch p with
  | and _ ?y => nested_and_proj2 y
  | ?x => x
  end.

Ltac add_fact P facts :=
  let T := type of facts in
  let TE := nested_and_proj2 T in
  let TE' := fresh in
  evar (TE' : Prop);
  unify TE (and P TE');
  subst TE'.

Ltac prove_later_aux tm ty :=
  let ty' := (eval simpl in ty) in
  lazymatch ty' with
  | ?x /\ ?y => prove_later_aux (@proj2 x y tm) y
  | _ => eapply (proj1 tm)
  end.

Ltac prove_later facts :=
  let T := type of facts in
  prove_later_aux facts T.

Goal True.
  pose_facts facts.

  assert (H1 : 1 + 1 = 2) by (prove_later facts).
  assert (H2 : 1 + 2 = 3) by (prove_later facts).
  assert (H3 : 1 + 3 = 4) by (prove_later facts).

  tauto.
  close_facts.

  repeat split; reflexivity.
Qed.

Ltac prove_pose_evars :=
  repeat (
      match goal with
      | |- forall (_ : Type), _ =>
        intro
      end
    );
  intros facts facts_closed P H1 H2 H;
  repeat (let x := fresh "x" in destruct H as (x & H));
  unfold close_facts in *;
  eauto.

Lemma pose_facts_evars_1 : forall
    (A : Type)
    (facts : A -> Prop)
    (facts_closed : A -> Prop)
    (P : Type),
  (forall a, facts a -> P) ->
  (forall a, close_facts (facts a) (facts_closed a)) ->
  {a | facts_closed a} ->
  P.
Proof. prove_pose_evars. Qed.

Lemma pose_facts_evars_2 : forall
    (A B : Type)
    (facts : A -> B -> Prop)
    (facts_closed : A -> B -> Prop)
    (P: Type),
  (forall a b, facts a b -> P) ->
  (forall a b, close_facts (facts a b) (facts_closed a b)) ->
  (sigT (fun a => { b | facts_closed a b })) ->
  P.
Proof. prove_pose_evars. Qed.

Lemma pose_facts_evars_3 : forall
    (A B C : Type)
    (facts : A -> B -> C -> Prop)
    (facts_closed : A -> B -> C -> Prop)
    (P: Type),
  (forall a b c, facts a b c -> P) ->
  (forall a b c, close_facts (facts a b c) (facts_closed a b c)) ->
  (sigT (fun a => sigT (fun b => { c | facts_closed a b c }))) ->
  P.
Proof. prove_pose_evars. Qed.

Lemma pose_facts_evars_4 : forall
    (A B C D : Type)
    (facts : A -> B -> C -> D -> Prop)
    (facts_closed : A -> B -> C -> D -> Prop)
    (P: Type),
  (forall a b c d, facts a b c d -> P) ->
  (forall a b c d, close_facts (facts a b c d) (facts_closed a b c d)) ->
  (sigT (fun a => sigT (fun b => sigT (fun c => { d | facts_closed a b c d })))) ->
  P.
Proof. prove_pose_evars. Qed.

Lemma pose_facts_evars_5 : forall
    (A B C D E : Type)
    (facts : A -> B -> C -> D -> E -> Prop)
    (facts_closed : A -> B -> C -> D -> E -> Prop)
    (P: Type),
  (forall a b c d e, facts a b c d e -> P) ->
  (forall a b c d e, close_facts (facts a b c d e) (facts_closed a b c d e)) ->
  (sigT (fun a => sigT (fun b => sigT (fun c => sigT (fun d => { e | facts_closed a b c d e }))))) ->
  P.
Proof. prove_pose_evars. Qed.

Ltac pose_facts_evars_core facts lemma intros_tac :=
  eapply lemma;
  [ intros_tac tt; intro facts | | ].

Tactic Notation "pose_facts_evars" ident(facts) ident(a) :=
  pose_facts_evars_core facts pose_facts_evars_1 ltac:(fun tt => intros a).

Tactic Notation "pose_facts_evars" ident(facts) ident(a) ident(b) :=
  pose_facts_evars_core facts pose_facts_evars_2 ltac:(fun tt => intros a b).

Tactic Notation "pose_facts_evars" ident(facts) ident(a) ident(b) ident(c) :=
  pose_facts_evars_core facts pose_facts_evars_3 ltac:(fun tt => intros a b c).

Tactic Notation "pose_facts_evars" ident(facts) ident(a) ident(b) ident(c) ident(d) :=
  pose_facts_evars_core facts pose_facts_evars_4 ltac:(fun tt => intros a b c d).

Tactic Notation "pose_facts_evars" ident(facts) ident(a) ident(b) ident(c) ident(d) ident(e) :=
  pose_facts_evars_core facts pose_facts_evars_5 ltac:(fun tt => intros a b c d e).
