(******************************************************************************)
(* pose_facts facts                                                           *)
(* prove_later facts                                                          *)
(* close_facts                                                                *)
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

Ltac apply_last_fact_aux tm ty :=
  lazymatch ty with
  | and ?x ?y =>
    lazymatch y with
    | and _ _ => apply_last_fact_aux (@proj2 x y tm) y
    | _ =>
      apply (@proj1 x y tm)
    end
  end.

Ltac apply_last_fact facts :=
  let T := type of facts in
  apply_last_fact_aux facts T.

Ltac prove_later facts :=
  match goal with
    |- ?P => add_fact P facts
  end;
  simpl in facts;
  apply_last_fact facts.

Goal True.
  pose_facts facts.

  assert (H1 : 1 + 1 = 2) by (prove_later facts).
  assert (H2 : 1 + 2 = 3) by (prove_later facts).
  assert (H3 : 1 + 3 = 4) by (prove_later facts).

  tauto.
  close_facts.

  repeat split; reflexivity.
Qed.
