Require Import LibEvars.

Ltac is_def_to_evar id :=
  is_var id;
  let X := get_body id in
  is_evar X.

Ltac is_not_def_to_evar id :=
  tryif is_def_to_evar id then
    fail
  else
    idtac.

Ltac is_def id :=
  is_var id;
  let X := get_body id in
  idtac.

Ltac pose_facts facts :=
  let facts_t := fresh "facts_t" in
  evar (facts_t : Type);
  evar (facts : facts_t);
  subst facts_t.

Ltac nested_prod_fst p :=
  lazymatch p with
  | prod ?x _ => nested_prod_fst x
  | ?x => x
  end.

Ltac nested_pair_fst p :=
  lazymatch p with
  | pair ?x _ => nested_pair_fst x
  | ?x => x
  end.

Ltac nested_pair_snd p :=
  match p with
    pair ?x ?y =>
    lazymatch x with
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

Ltac add_fact fact_name P facts :=
  add_fact_to_type P facts;
  evar (fact_name : P);
  let T := get_body_type facts in
  let TE' := nested_prod_fst T in
  let FE' := fresh in
  evar (FE' : TE');
  let F := get_body facts in
  let FE := nested_pair_fst F in
  unify FE (pair FE' fact_name);
  subst FE'; fold fact_name in facts.

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
  lazymatch F with
  | pair ?x ?y =>
    tryif is_def_to_evar y then
      prove_evar_in y; prove_facts_tuple x
    else
      prove_facts_tuple x
  | _ =>
    idtac
  end.

Ltac clearbody_proved_facts_tuple F :=
  lazymatch F with
  | pair ?x ?y =>
    clearbody y;
    clearbody_proved_facts_tuple x
  | _ =>
    idtac
  end.

Ltac clearbody_proved_facts facts :=
  let F := get_body facts in
  clearbody_proved_facts_tuple F.

Ltac prove_facts facts :=
  close_facts facts;
  let F := get_body facts in
  prove_facts_tuple F;
  [ .. | clearbody_proved_facts facts; clear facts ].

Ltac trim_facts_tuple F :=
  constr:(ltac:(
    lazymatch F with
    | pair ?x ?y =>
      tryif (is_var y; is_not_def_to_evar y) then
        let F' := trim_facts_tuple x in
        exact F'
      else
        let x' := trim_facts_tuple x in
        exact (pair x' y)
    | ?x =>
      exact x
    end
  )).

Ltac remove_fact_tuple fact F :=
  constr:(ltac:(
    lazymatch F with
    | pair ?x fact =>
      exact x
    | pair ?x ?y =>
      let F' := remove_fact_tuple fact x in
      exact (pair F' y)
    | ?x =>
      exact x
    end
  )).

Ltac clear_non_evar_defs F :=
  match F with
  | pair ?y ?z =>
    tryif (is_def z; is_not_def_to_evar z) then
      clear z; clear_non_evar_defs y
    else
      clear_non_evar_defs y
  | _ =>
    idtac
  end.

Ltac trim_facts facts :=
  let F := get_body facts in
  clear facts;
  let F' := trim_facts_tuple F in
  clear_non_evar_defs F;
  pose (facts := F').

Ltac clear_fact fact facts :=
  let F := get_body facts in
  clear facts;
  let F' := remove_fact_tuple fact F in
  clear fact;
  pose (facts := F').

Ltac other_facts fact F :=
  constr:(ltac:(
    lazymatch F with
    | pair ?x fact =>
      let F' := other_facts fact x in
      exact F'
    | pair ?x ?y =>
      let F' := other_facts fact x in
      exact (pair F' y)
    | ?x =>
      exact x
    end
  )).

Ltac prove_fact_lemma fact OF :=
  constr:(ltac:(
    lazymatch OF with
    | pair ?x ?y =>
      let L := prove_fact_lemma fact x in
      let Y := type of y in
      exact (Y -> L)
    | _ =>
      let T := type of fact in
      exact T
    end
  )).

Ltac prove_fact_lemma_instantiate fact L OF :=
  constr:(ltac:(
    lazymatch OF with
    | pair ?x ?y =>
      let L' := prove_fact_lemma_instantiate fact (L y) x in
      exact L'
    | _ =>
      exact L
    end
  )).

Ltac prove_fact fact facts :=
  is_def_to_evar fact;
  prove_evar_in fact;
  [| clear_fact fact facts].

Ltac nested_pair_add_fst t :=
  constr:(ltac:(
    lazymatch t with
    | pair ?x ?y =>
      let x' := nested_pair_add_fst x in
      exact (pair x' y)
    | ?x =>
      exact (pair I x)
    end
  )).

Ltac prove_fact_using_OF OF fact facts :=
  let L := prove_fact_lemma fact OF in
  let Lfact := fresh "fact_lemma" in
  add_fact Lfact L facts;
  let L' := prove_fact_lemma_instantiate fact Lfact OF in
  let E := get_body fact in
  unify E L';
  clear_fact fact facts;
  prove_fact Lfact facts.

Ltac prove_fact_using aux_facts fact facts :=
  let OF := nested_pair_add_fst aux_facts in
  prove_fact_using_OF OF fact facts.

Ltac prove_fact_using_facts fact facts :=
  let F := get_body facts in
  let OF := other_facts fact F in
  prove_fact_using_OF OF fact facts.

Goal True.
  pose_facts facts.

  add_fact H1 (1 + 1 = 2) facts.
  add_fact H2 (1 + 2 = 3) facts.

  assert (1 + 1 = 2 /\ 1 + 2 = 3).
  { split. apply H1. apply H2. }

  prove_facts facts.
  - reflexivity.
  - reflexivity.
  - tauto.
Qed.

Definition P (i : nat) := True.

Goal True.
  pose_facts facts.

  add_fact H1 (P 0) facts.
  add_fact H2 (P 1) facts.
  add_fact H1H2 (P 0 -> P 1) facts.

  prove_fact_using (H1, H1H2) H2 facts.
  (* prove_fact_using_facts H2 facts. *)
  (* is there a way of having H1 and H1H2 already [intro]'d with the right names? *)
  tauto.

  prove_facts facts.
  unfold P; tauto.
  unfold P; tauto.
  tauto.
Qed.