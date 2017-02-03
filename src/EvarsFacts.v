Require Import LibEvars.

Ltac pose_facts facts :=
  let facts_t := fresh "facts_t" in
  evar (facts_t : Type);
  evar (facts : facts_t);
  subst facts_t.

Ltac nested_prod_fst p :=
  match p with
  | prod ?x _ => nested_prod_fst x
  | ?x => x
  end.

Ltac nested_pair_fst p :=
  match p with
  | pair ?x _ => nested_pair_fst x
  | ?x => x
  end.

Ltac nested_pair_snd p :=
  match p with
    pair ?x ?y =>
    match x with
    | pair _ _ => nested_pair_snd x
    | _ => y
    end
  end.

Ltac add_fact_to_type P facts :=
  let T := get_body_type facts in
  let TE := nested_prod_fst T in
  let TE' := fresh in
  evar (TE' : Type);
  unify TE (prod TE' P);
  subst TE'.

Ltac add_fact P facts :=
  add_fact_to_type P facts;
  let new_fact := fresh in
  evar (new_fact : P);
  let T := get_body_type facts in
  let TE' := nested_prod_fst T in
  let FE' := fresh in
  evar (FE' : TE');
  let F := get_body facts in
  let FE := nested_pair_fst F in
  unify FE (pair FE' new_fact);
  subst new_fact FE'.

Ltac get_last_fact facts :=
  let F := get_body facts in
  nested_pair_snd F.

Ltac prove_later_using facts :=
  match goal with
    |- ?P => add_fact P facts
  end;
  let fact_P := get_last_fact facts in
  apply fact_P.

Ltac close_facts_type facts :=
  let T := get_body_type facts in
  let TE := nested_prod_fst T in
  unify TE True.

Ltac close_facts facts :=
  close_facts_type facts;
  let F := get_body facts in
  let FE := nested_pair_fst F in
  unify FE I.

Ltac prove_facts_tuple F :=
  match F with
  | @pair _ _ ?x ?y =>
    (try (is_evar y; prove_evar y)); [| prove_facts_tuple x]
  | _ =>
    idtac
  end.

Ltac generalize_proved_facts_tuple F :=
  match F with
  | pair ?x ?y =>
    generalize_proved_facts_tuple x;
    generalize y
  | _ =>
    idtac
  end.

Ltac generalize_proved_facts facts :=
  let F := get_body facts in
  generalize_proved_facts_tuple F.

Ltac prove_facts facts :=
  close_facts facts;
  let F := get_body facts in
  prove_facts_tuple F;
  [ .. | generalize_proved_facts facts; clear facts ].

Goal True.
  pose_facts facts.
  add_fact (1 + 1 = 2) facts.
  add_fact (1 + 2 = 3) facts.

  prove_facts facts.
  - reflexivity.
  - reflexivity.
  - intros H1 H2. tauto.
Qed.
