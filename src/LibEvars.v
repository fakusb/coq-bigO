Ltac get_body id :=
  let id' := constr:(id) in
  let body := (eval unfold id in id') in
  body.

Ltac get_body_type id :=
  let B := get_body id in
  let T := type of B in
  T.

Ltac get_evar_in id :=
  constr:(ltac:(
    let body := get_body id in
    match body with
      context [?E] => is_evar E; exact E
    end
  )).

Ltac prove_evar_in id :=
  unshelve instantiate (1 := _) in (Value of id).

Ltac prove_evar E :=
  let x := fresh in
  pose (x := E);
  prove_evar_in x;
  [| clear x].

Require Import TLC.LibTactics.

Ltac admit_evar id :=
  let T := type of id in
  let E := get_body id in
  unify E (False_ind T LibTactics.skip_axiom).
