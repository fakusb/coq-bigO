Set Implicit Arguments.
Require Import TLC.LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
(* We re-use the methodology of Procrastination, and thus some of the definition
   and tactics *)
Require Export Procrastination.Procrastination.
(* Load the BigO library. *)
Require Import Dominated.
Require Import DominatedNary.
Require Import FilterNary.
Require Import LibFunOrd.
Require Import UltimatelyGreater.
Require Import LibZExtra.
Require Import TLC.LibIntTactics.
Require Import Generic.

(********************************************************************)

(* TODO: prove & move *)

Lemma monotonic_cumul_Z : forall (f : Z -> Z) (lo : Z),
  (forall x, lo <= x -> 0 <= f x) ->
  monotonic Z.le Z.le (fun n => cumul lo n f).
Proof. admit. Qed.

Hint Resolve monotonic_cumul_Z : monotonic.

(********************************************************************)

Record specO
       (A : filterType) (le : A -> A -> Prop)
       (spec : (A -> Z) -> Prop)
       (bound : A -> Z) :=
  SpecO {
      cost : A -> Z;
      spec : spec cost;
      cost_nonneg : forall x, 0 <= cost x;
      cost_monotonic : monotonic le Z.le cost;
      cost_dominated : dominated A cost bound
    }.

(********************************************************************)

(** Properties of the cost function in a specO, as separate lemmas. *)

Lemma monotonic_specO_cost :
  forall A le spec bound (S : @specO A le spec bound),
  monotonic le Z.le (cost S).
Proof.
  intros. apply cost_monotonic.
Qed.

Hint Extern 1 (monotonic _ _ (fun _ => cost ?S _)) =>
  match type of S with
  | @specO _ ?leS _ _ =>
     apply Monotonic.monotonic_comp with (leB := leS)
  end : monotonic.

Hint Extern 1 (monotonic _ _ (cost ?S)) =>
  match type of S with
  | @specO ?AS _ _ _ =>
    apply monotonic_specO_cost with (A := AS)
  end : monotonic.

Lemma monotonic_specO_nonneg :
  forall A le spec bound (S : @specO A le spec bound) x,
  0 <= cost S x.
Proof.
  intros. apply cost_nonneg.
Qed.

Hint Resolve monotonic_specO_nonneg : zarith.

(** *)

Inductive pack_provide_specO (A:Type) (V:A) : Prop :=
  | provide_specO : pack_provide_specO V.

(** *)

(********************************************************************)

(* Contravariant specs (wrt the cost function).

   If the spec can be proved contravariant, then the [cost_nonneg] field of
   [specO] can be proved automatically. *)

Definition spec_is_contravariant {A} (spec : (A -> Z) -> Prop) :=
  forall (cost1 cost2 : A -> Z),
  (forall x, cost1 x <= cost2 x) ->
  (spec cost1 -> spec cost2).

(* Tactic that tries to prove that a CFML spec is contravariant.

   It is generally the case for the specs with credits we consider, where the
   cost functions is used once and only in the precondition.

   More precisely, this tactic works with specifications of the form:
   [fun cost -> forall ...., app _ (\$cost (..) \* _) _] or
   [fun cost -> forall ...., app _ (\$cost (..)) _]
*)

Lemma spec_is_contravariant_lemma1 :
  forall A (cost cost' : int) (F: ~~A) Q,
  F (\$ cost') Q ->
  (cost' <= cost) ->
  is_local F ->
  F (\$ cost) Q.
Proof.
  introv HH Hcost L. xapply HH. hsimpl_credits. hsimpl. math.
Qed.

Lemma spec_is_contravariant_lemma2 :
  forall A (cost cost' : int) (F: ~~A) H Q,
  F (\$ cost' \* H) Q ->
  (cost' <= cost) ->
  is_local F ->
  F (\$ cost \* H) Q.
Proof.
  introv HH Hcost L. xapply HH. hsimpl_credits. hsimpl. math.
Qed.

Ltac spec_is_contravariant :=
  match goal with
  | |- spec_is_contravariant _ =>
    let cost1 := fresh "cost" in
    let cost2 := fresh "cost" in
    let Hcosts := fresh "Hcosts" in
    let spec_cost1 := fresh "spec_cost1" in
    intros cost1 cost2 Hcosts spec_cost1;
    intros;
    (first [
        eapply spec_is_contravariant_lemma1; [ | | xlocal]
      | eapply spec_is_contravariant_lemma2; [ | | xlocal]
      ]);
    [ apply spec_cost1; auto
    | apply Hcosts ]
  end.

(********************************************************************)
Definition cleanup_cost
           {A : filterType} (le : A -> A -> Prop)
           (cost : A -> Z)
           (bound : A -> Z) (spec : (A -> Z) -> Prop)
  :=
  sigT (fun cost_clean_eq =>
  sigT (fun cost_clean =>
    monotonic le Z.le cost_clean_eq *
    dominated A cost_clean bound *
    (spec_is_contravariant spec + (forall x, 0 <= cost_clean_eq x)) *
    dominated A cost_clean_eq cost_clean *
    (forall x, cost x = cost_clean_eq x)))%type.

Lemma cleanup_cost_alt :
  forall (A: filterType) le cost bound spec,
  @cleanup_cost A le cost bound spec ->
  monotonic le Z.le cost *
  dominated A cost bound *
  (spec cost -> specO A le spec bound).
Proof.
  intros ? ? cost.
  introv (cost_clean_eq & cost_clean & H).
  repeat (destruct H as (H & ?)).
  assert (monotonic le Z.le cost).
  { eapply Monotonic.monotonic_eq; eauto. }
  assert (dominated A cost bound).
  { eapply dominated_eq_l. eapply dominated_transitive; eauto. auto. }

  repeat split; auto; []. intro S.
  match goal with H : _ + _ |- _ => destruct H as [contra | N] end.
  { eapply SpecO with (fun x => Z.max 0 (cost x)).
    - eapply contra with cost; auto with zarith.
    - auto with zarith.
    - Monotonic.monotonic.
    - dominated. (* FIXME *) admit. }
  { eapply SpecO with cost; auto.
    intros. match goal with H : _ |- _ => rewrite H end. auto. }
Qed.

(* TODO: implement using setoid-rewrite? *)
Ltac dominated_cleanup_cost :=
  first [
      apply dominated_sum;
      [ | | dominated_cleanup_cost | dominated_cleanup_cost];
      simpl;
      solve [ ultimately_greater_trysolve ]
    | apply dominated_max;
      [ | | dominated_cleanup_cost | dominated_cleanup_cost];
      simpl;
      solve [ ultimately_greater_trysolve ]
    | apply dominated_big_sum;
      [ | | dominated_cleanup_cost ];
      simpl;
      solve [ ultimately_greater_trysolve ]
    | apply cost_dominated; dominated_cleanup_cost
    | eapply dominated_comp;
      [ apply cost_dominated | limit ]
    | apply dominated_reflexive
    ].

(* workaround because ring_simplify apparently sometimes chokes on
   evars. *)
Ltac hide_evars_then cont :=
  match goal with
    |- context [ ?X ] =>
    is_evar X;
    let hide_X := fresh in
    set (hide_X := X);
    hide_evars_then cont;
    subst hide_X
  | _ =>
    cont tt
  end.

Ltac simple_cleanup_cost :=
  simpl; hide_evars_then ltac:(fun _ => ring_simplify).

Ltac simple_cleanup_cost_eq :=
  simpl; simple_cleanup_cost.

(* TODO: make it more robust *)
Ltac intro_destructs :=
  let x := fresh "x" in
  intro x; repeat (destruct x as [x ?]).

(********************************************************************)

(* body is expected to be a uconstr *)
Ltac intro_cost_expr_1 A cost_name body :=
  simple refine (let cost_name := (fun (x:A) => body) : A -> Z in _); [ shelve .. | ].

(* body is expected to be a uconstr *)
Ltac intro_cost_expr_2 A cost_name body :=
  (* Ugly hack. See https://github.com/coq/coq/issues/6643 *)
  (* Was:
     refine (let cost_name := (fun '(x, y) => body) : A -> Z in _).
   *)
  let pat := fresh "pat" in
  match goal with |- ?G =>
    simple refine (let cost_name := (fun pat => let '(x,y) := pat in body) : A -> Z in _);
    try clear pat;
    [ shelve .. | ]
  end.

(* body is expected to be a uconstr *)
Ltac intro_cost_expr A cost_name body :=
  let A_sort := constr:(Filter.sort A) in
  let A_sort' := (eval compute in A_sort) in
  (* TODO: handle more arities *)
  lazymatch A_sort' with
  | (_ * _)%type => intro_cost_expr_2 A cost_name body
  | _ => intro_cost_expr_1 A cost_name body
  end.

Ltac eexists_cost_expr A :=
  let cost_name := fresh in
  intro_cost_expr A cost_name uconstr:(_);
  exists cost_name;
  subst cost_name.

(********************************************************************)
Definition close_cost (P : Type) := P.
Definition hide_spec {A} (spec : (A -> Z) -> Prop) := spec.
(********************************************************************)

Ltac try_prove_nonnegative :=
  first [
      solve [ left; unfold hide_spec; spec_is_contravariant ]
    | right
    ].

Ltac cleanup_cost :=
  match goal with |- @cleanup_cost ?A _ ?cost _ _ =>
    unfold cleanup_cost; do 2 (eexists_cost_expr A);
    try subst cost;
    split; [| intro_destructs;
              simple_cleanup_cost_eq;
              reflexivity ];
    split; [| eapply dominated_eq_r;
              [ dominated_cleanup_cost |];
              intro_destructs;
              simple_cleanup_cost;
              reflexivity ];
    split; [ split | try_prove_nonnegative ]
  end.

(********************************************************************)

Lemma specO_prove :
  forall (A : filterType) (le : A -> A -> Prop)
         (cost : A -> Z)
         (bound : A -> Z)
         (spec : (A -> Z) -> Prop),
    spec cost ->
    (spec_is_contravariant spec + (forall x, 0 <= cost x)) ->
    monotonic le Z.le cost ->
    dominated A cost bound ->
    specO A le spec bound.
Proof.
  introv S N M D.
  destruct N as [spec_contra | N].
  { pose (cost' := fun x => Z.max 0 (cost0 x)).
    apply SpecO with (cost := cost'); subst cost'.
    - eapply spec_contra with cost0; auto. math_lia.
    - math_lia.
    - Monotonic.monotonic.
    - dominated.  (* FIXME *) admit. }
  { apply SpecO with (cost := cost0); auto. }
Qed.

Lemma specO_refine_straight_line :
  forall (A : filterType) (le : A -> A -> Prop)
         (cost bound : A -> Z)
         (spec : (A -> Z) -> Prop),
    spec cost ->
    cleanup_cost le cost bound (hide_spec spec) ->
    specO A le spec bound.
Proof.
  introv H1 H2.
  forwards [[? ?] H]: cleanup_cost_alt H2.
  unfold hide_spec in *. apply~ H.
Qed.

Lemma specO_refine_recursive :
  forall (A : filterType) (le : A -> A -> Prop)
         (bound : A -> Z)
         (spec : (A -> Z) -> Prop)
         P P',
    (forall cost,
       monotonic le Z.le cost ->
       dominated A cost bound ->
       Marker.group (P cost) ->
       spec cost) ->
    close_cost
      ((forall cost, P' cost -> P cost) *
       sigT (fun cost =>
         P' cost *
         cleanup_cost le cost bound (hide_spec spec)))%type ->
    specO A le spec bound.
Proof.
  introv H1 H2.
  unfold close_cost in H2.
  destruct H2 as (? & cost & ? & c).
  forwards [[? ?] H]: cleanup_cost_alt c.
  unfold hide_spec, Marker.group in *. apply~ H.
Qed.

Ltac close_cost :=
  unfold close_cost;
  split; [ solve [ introv_rec; hnf; cleanup_conj_goal_core ] |];
  hnf.

Ltac xspecO_explicit_cost cost_expr :=
  match goal with |- specO ?A _ _ _ =>
    apply (@specO_prove A _ (cost_expr : A -> Z) _ _);
    [ | try_prove_nonnegative | .. ]
  end.

Ltac xspecO_refine_recursive :=
  eapply specO_refine_recursive.

(** Straight-line case *)

Ltac xspecO_refine_straight_line cost_name :=
  match goal with
    |- specO ?A ?le _ _ =>
    intro_cost_expr A cost_name uconstr:(_);
    eapply (@specO_refine_straight_line A le cost_name);
    [ unfold cost_name | ]
  end.

Tactic Notation "xspecO" uconstr(cost_expr) :=
  xspecO_explicit_cost cost_expr.

Tactic Notation "xspecO_refine" "straight_line" ident(cost_name) :=
  xspecO_refine_straight_line cost_name.

Tactic Notation "xspecO_refine" "straight_line" :=
  let costf := fresh "costf" in
  xspecO_refine_straight_line costf.

Tactic Notation "xspecO_refine" "recursive" :=
  xspecO_refine_recursive.

Notation "'close'  'cost'" := (close_cost _) (at level 0).
Tactic Notation "close" "cost" := close_cost.

Notation "'(...)'" := (hide_spec _) (at level 0).

(* Notations for common [specO]s *)

Notation "'specZ' [ X '\in_O' f ] E" :=
  (specO Z_filterType Z.le (fun X => E) f)
    (X ident, f at level 90, E at level 0,
     format "'[v' 'specZ'  [ X  '\in_O'  f ]  '/'  E ']'", at level 60).

(* Custom CF rules and tactics ************************************************)

(** *)

(* Ugly hack. See https://github.com/coq/coq/issues/6643 *)
Ltac refine_credits_preprocess_eta :=
  match goal with
    |- PRE (\$ (?c _) \* _) POST _ CODE _ =>
    is_evar c;
    let x := fresh in
    pose (x := c);
    unshelve instantiate (1 := _) in (Value of x);
    [ refine (fun _ => _); shelve | hnf ]
  end.

(* Must be called before any tactic that refines the credits evar found in the
   precondition. *)
Ltac refine_credits_preprocess :=
  try refine_credits_preprocess_eta.

(** *)

(* Custom xspec to fetch specO specifications *)

(* FIXME: copy-pasted from CFML *)
Ltac xspec_core_base f :=
  first [ xspec_for_record f
        | xspec_in_hyps_core f
        (* FUTURE: | xspec_in database_spec_credits f *)
        | xspec_in_core database_spec f
        | xspec_app_in_hyps f
        | fail 1 "xspec cannot find specification" ].

Ltac spec_of_specO :=
  match goal with
  | |- pack_provide_specO ?S -> _ =>
    intros _; generalize (spec S)
  end.

Ltac xspec_core f ::=
  xspec_core_base f; try spec_of_specO.

(** *)

Lemma refine_cost_setup_intro_emp :
  forall A (F: ~~A) cost Q,
  F (\$ cost \* \[]) Q ->
  F (\$ cost) Q.
Proof.
  introv H. rewrite star_neutral_r in H. auto.
Qed.

(* TODO: Improve is_evar handling *)
Ltac is_refine_cost_goal :=
  match goal with
    |- _ (\$ ?c) _ => is_evar c; apply refine_cost_setup_intro_emp
  | |- _ (\$ (?c _)) _ => is_evar c; apply refine_cost_setup_intro_emp
  | |- _ (\$ ?c \* _) _ => is_evar c; idtac
  | |- _ (\$ (?c _) \* _) _ => is_evar c; idtac
  end;
  refine_credits_preprocess.

(* weaken

   Applies to a goal with some credit cost, and turns it into a goal where the
   number of credits is an evar (so that the _refine tactics can apply).
   Produces a side-condition requiring that the evar cost is less than the
   original cost.

   Is also useful if the original number of credits _is_ an evar, but with a
   context that doesn't allow directly instanting it. Calling this tactic
   introduces a new evar in the local context, plus a subgoal where the user can
   explain how to instantiate the evar with the restricted context.
*)
Lemma weaken_credits :
  forall A (cost_weakened cost : int) (F: ~~A) H Q,
  F (\$ cost_weakened \* H) Q ->
  (cost_weakened <= cost) ->
  is_local F ->
  F (\$ cost \* H) Q.
Proof.
  introv HH Hcost L.
  xapply HH.
  { hsimpl_credits. }
  { hsimpl. math. }
Qed.

Ltac weaken :=
  match goal with
    |- _ (\$ _) _ => apply refine_cost_setup_intro_emp
  | |- _ (\$ _ \* _) _ => idtac
  end;
  eapply weaken_credits;
  [ | | xlocal ].

(* cutO *)

Lemma cutO_refine :
  forall (A : filterType) le B (bound : A -> Z) (F: ~~B) H Q (a: A),
  forall S : specO A le (fun cost => forall a, F (\$ cost a \* H) Q) bound,
  F (\$ (cost S) a \* H) Q.
Proof.
  introv. destruct S. simpl. auto.
Qed.

(* hpull & hclean *********************)

Ltac is_credits H :=
  match H with
  | \$ _ => idtac
  | _ => fail 1
  end.

Ltac bring_credits_to_head H :=
  match H with
  | context [?A \* \$ ?x \* _] =>
    tryif is_credits A then fail
    else rewrite (star_comm_assoc A (\$ x))
  | context [?A \* \$ ?x] =>
    tryif is_credits A then fail
    else rewrite (star_comm A (\$ x))
  end.

Ltac bring_credits_to_head_of_pre tt :=
  repeat on_formula_pre bring_credits_to_head.

Goal forall H1 H2 H3 H' p n m,
    \$ p \* \$ n \* \$ m \* H1 \* H2 \* H3 ==> H' ->
    \$ p \* H1 \* H2 \* \$ n \* H3 \* \$ m ==> H'.
Proof.
  intros. dup.
  (* detailed *)
  on_formula_pre bring_credits_to_head.
  on_formula_pre bring_credits_to_head.
  on_formula_pre bring_credits_to_head.
  on_formula_pre bring_credits_to_head.
  on_formula_pre bring_credits_to_head.
  assumption.
  (* short *)
  bring_credits_to_head_of_pre tt.
  assumption. (* demo *)
Qed.

Ltac hpull_main tt ::=
  hpull_setup tt;
  (repeat (hpull_step tt));
  bring_credits_to_head_of_pre tt;
  hpull_cleanup tt.

Ltac hclean_main tt ::=
  hclean_setup tt;
  (repeat (hclean_step tt));
  bring_credits_to_head_of_pre tt;
  hclean_cleanup tt.

(* hsimpl *****************************)

Lemma inst_credits_cost :
  forall (credits : int) H H' H'',
  H ==> H' \* H'' ->
  \$ credits \* H ==> H' \* \$ credits \* H''.
Proof.
  introv HH.
  xchange HH. hsimpl_credits.
Qed.

Ltac inst_credits_cost cont :=
  (first [ eapply inst_credits_cost
         | fail 100 "Evar instantiation failed" ]);
  cont tt.

Lemma intro_zero_credits_right : forall H H' H'',
  H ==> H' \* \$ 0 \* H'' ->
  H ==> H' \* H''.
Proof.
  introv.
  rewrite credits_zero_eq. rewrite star_neutral_l.
  auto.
Qed.

Lemma hsimpl_starify_left : forall H H' H'',
  H ==> \[] \* H' \* H'' ->
  H ==> H' \* H''.
Proof.
  introv. rewrite star_neutral_l. auto.
Qed.

Lemma hsimpl_assoc_right_1 : forall H H1 H2 H3,
  H ==> H1 \* H2 \* H3 ->
  H ==> (H1 \* H2) \* H3.
Proof. admit. (* ok *) Qed.

Lemma hsimpl_assoc_right_2 : forall H H1 H2 H3,
  H ==> H2 \* H1 \* H3 ->
  H ==> (H1 \* H2) \* H3.
Proof. admit. Qed.

Lemma hsimpl_assoc_right_3 : forall H H1 H2 H3 H4,
  H ==> H1 \* H2 \* H3 \* H4 ->
  H ==> (H1 \* H2 \* H3) \* H4.
Proof. admit. Qed.

Ltac hsimpl_inst_credits_cost_setup tt :=
  match goal with
  | |- \$ ?cost ==> _ => is_evar cost; apply hsimpl_start_1
  | |- \$ ?cost \* _ ==> _ => is_evar cost
  (* | |- \$ (?cost _) ==> _ => is_evar cost; apply hsimpl_start_1 *)
  (* | |- \$ (?cost _) \* _ ==> _ => is_evar cost *)
  (* these cases should not be necessary, because of refine_credits_preprocess? *)
  end;
  match goal with
  | |- _ ==> _ \* \$ _ => apply hsimpl_starify
  | |- _ ==> \$ _ \* _ => apply hsimpl_starify_left
  | |- _ ==> _ \* \$ _ \* _ => idtac
  (* FIXME? *)
  | |- _ ==> (_ \* \$ _) \* _ => apply hsimpl_assoc_right_1
  | |- _ ==> (\$ _ \* _) \* _ => apply hsimpl_assoc_right_2
  | |- _ ==> (_ \* \$ _ \* _) \* _ => apply hsimpl_assoc_right_3
  (* *)
  | |- _ ==> _ \* _ => apply intro_zero_credits_right
  end.

Ltac hsimpl_inst_credits_cost cont :=
  tryif hsimpl_inst_credits_cost_setup tt then
    inst_credits_cost cont
  else
    cont tt.

Ltac hsimpl_setup process_credits ::=
  prepare_goal_hpull_himpl tt;
  try (check_arg_true process_credits; credits_join_left_repeat tt);
  hsimpl_left_empty tt;
  hsimpl_inst_credits_cost ltac:(fun _ => apply hsimpl_start).

(* xcf ******************************************)

(* This is to ensure that credits are put at the head of the precondition. *)

Ltac xcf_post tt ::=
  cbv beta;
  remove_head_unit tt;
  hclean.

(* xpay *****************************************)

Lemma xpay_refine :
  forall A (cost : Z)
         (F: hprop -> (A -> hprop) -> Prop) H Q,
  is_local F ->
  F (\$ cost \* H) Q ->
  (Pay_ ;; F) (\$ (1 + cost) \* H) Q.
Proof.
  introv L HH.
  xpay_start tt.
  { unfold pay_one. hsimpl_credits. }
  xapply HH. hsimpl_credits. hsimpl. math.
Qed.

Ltac xpay_core tt ::=
  tryif is_refine_cost_goal then
    (eapply xpay_refine; [ xlocal | ])
  else
    (xpay_start tt; [ unfold pay_one; hsimpl | ]).

(* xret *******************************)

Lemma xret_refine : forall A (x : A) H (Q : A -> hprop),
  local (fun H' Q' => H' ==> Q' x) H Q ->
  local (fun H' Q' => H' ==> Q' x) (\$ 0 \* H) Q.
Proof.
  introv HH.
  rewrite credits_zero_eq. rewrite star_neutral_l.
  assumption.
Qed.

Ltac xret_apply_lemma tt ::=
  (tryif is_refine_cost_goal then apply xret_refine else idtac);
  first [ apply xret_lemma_unify
        | apply xret_lemma ].

Ltac xret_no_gc_core tt ::=
  (tryif is_refine_cost_goal then apply xret_refine else idtac);
  first [ apply xret_lemma_unify
        | eapply xret_no_gc_lemma ].

(* xseq *******************************)

Lemma xseq_refine :
  forall (A : Type) cost1 cost2 F1 F2 H (Q : A -> hprop),
  is_local F1 ->
  is_local F2 ->
  (exists Q',
    F1 (\$ cost1 \* H) Q' /\
    F2 (\$ cost2 \* Q' tt) Q) ->
  (F1 ;; F2) (\$ (cost1 + cost2) \* H) Q.
Proof.
  introv L1 L2 (Q' & H1 & H2).
  xseq_pre tt. apply local_erase. eexists. split.
  { xapply H1. credits_split. hsimpl. }
  { xapply H2. hsimpl. hsimpl. }
Qed.

Ltac xseq_core cont0 cont1 ::=
  (tryif is_refine_cost_goal then
     eapply xseq_refine; [ xlocal | xlocal | ]
   else
     apply local_erase);
  cont0 tt;
  split; [ | cont1 tt ];
  xtag_pre_post.

(* xlet *****************************************)

Lemma xlet_refine :
  forall
    (A B : Type) cost1 cost2
    (F1 : hprop -> (A -> hprop) -> Prop)
    (F2 : A -> hprop -> (B -> hprop) -> Prop)
    (H : hprop) (Q : B -> hprop),
  is_local F1 ->
  (forall x, is_local (F2 x)) ->
  (exists (Q' : A -> hprop),
    F1 (\$ cost1 \* H) Q' /\
    (forall r, F2 r (\$ cost2 \* Q' r) Q)) ->
  cf_let F1 F2 (\$ (cost1 + cost2) \* H) Q.
Proof.
  introv L1 L2 (Q' & H1 & H2).
  unfold cf_let.
  eexists. split.
  { xapply H1. credits_split. hsimpl. }
  { intro r. specializes L2 r. xapply H2; hsimpl. }
Qed.

Ltac xlet_core cont0 cont1 cont2 ::=
  apply local_erase;
  match goal with |- cf_let ?F1 (fun x => _) ?H ?Q =>
    tryif is_refine_cost_goal then (
      eapply xlet_refine;
      [ xlocal | intro; xlocal | ]
    ) else idtac;
    cont0 tt;
    split; [ | cont1 x; cont2 tt ];
    xtag_pre_post
  end.

(* xif ********************************)

Lemma xif_refine : forall (A: Type) cost1 cost2 cond (F1 F2: ~~A) H Q,
  is_local F1 ->
  is_local F2 ->
  ((cond = true -> F1 (\$ cost1 \* H) Q) /\
   (cond = false -> F2 (\$ cost2 \* H) Q)) ->
  (If_ cond Then F1 Else F2) (\$ (Z.max cost1 cost2) \* H) Q.
Proof.
  introv L1 L2 (H1 & H2).
  apply local_erase.
  split; intro; [xapply~ H1 | xapply~ H2]; hsimpl_credits;
  math_lia.
Qed.

Ltac xif_base cont1 cont2 ::=
  xpull_check_not_needed tt;
  xif_check_post_instantiated tt;
  let cont tt :=
    tryif is_refine_cost_goal then (
      eapply xif_refine;
      [ xlocal | xlocal | ]
    ) else (
      xuntag tag_if;
      apply local_erase
    );
    split; [ cont1 tt | cont2 tt ];
    xtag_pre_post
  in
  match cfml_get_tag tt with
  | tag_if => cont tt
  | tag_let => xlet; [ cont tt | instantiate ]
  end.

(* xif_guard: prototype *)

Lemma xif_guard_refine : forall (A: Type) cost1 cost2 (cond cond': bool) (F1 F2: ~~A) H Q,
  (cond = cond') ->
  is_local F1 ->
  is_local F2 ->
  ((cond = true -> F1 (\$ cost1 \* H) Q) /\
   (cond = false -> F2 (\$ cost2 \* H) Q)) ->
  (If_ cond Then F1 Else F2) (\$ (If cond' then cost1 else cost2) \* H) Q.
Proof.
  introv costE L1 L2 (H1 & H2).
  apply local_erase. rewrite costE.
  split; intro C; rewrite C; cases_if; [xapply~ H1 | xapply~ H2].
Qed.

Ltac xif_guard_base cont :=
  is_refine_cost_goal;
  eapply xif_guard_refine;
  [ try reflexivity | xlocal | xlocal | ];
  split; cont tt; xtag_pre_post.

Ltac xif_guard_core H :=
  xif_guard_base ltac:(fun _ => intro H; xif_post H).

Tactic Notation "xif_guard" "as" ident(H) :=
  xif_guard_core H.
Tactic Notation "xif_guard" :=
  let H := fresh "C" in xif_guard as C.

(* xguard ***************************************)

Lemma xguard_refine :
  forall A (cost : int) (F: ~~A) (G: Prop) H Q,
  G ->
  F (\$ cost \* H) Q ->
  F (\$ (If G then cost else 0) \* H) Q.
Proof.
  introv HG HH. cases_if. trivial.
Qed.

Ltac xguard G :=
  is_refine_cost_goal;
  eapply xguard_refine;
  [ eexact G | ].

(* xfor *****************************************)

(* TODO: prove using xfor_inv_case_lemma_refine instead of directly *)
Lemma xfor_inv_lemma_pred_refine :
  forall
    (I : int -> hprop)
    (cost_body : int -> int)
    (a : int) (b : int) (F : int-> ~~unit) H H',
  (a <= b) ->
  (forall i, a <= i < b -> F i (\$ (cost_body i) \* I i) (# I(i+1))) ->
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (For i = a To (b - 1) Do F i Done_)
    (\$ (cumul a b cost_body) \* H)
    (# I b \* H').
Proof.
Admitted. (* TODO *)


Lemma xfor_inv_case_lemma_refine : forall (I:int->hprop),
   forall (cost : int) (cost_body : int -> int),
   forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
   ((a <= b) -> exists H',
          (H ==> I a \* H')
       /\ (forall i, is_local (F i))
       /\ (forall i, a <= i <= b -> F i (\$ (cost_body i) \* I i) (# I(i+1)))
       /\ (cost = cumul a b cost_body)
       /\ (I (b+1) \* H' ==> Q tt \* \GC)) ->
   ((a > b) ->
          (cost = 0)
       /\ (H ==> Q tt \* \GC)) ->
   (For i = a To b Do F i Done_) (\$ cost \* H) Q.
Proof.
Admitted. (* TODO *)

Lemma xfor_inv_lemma_refine : forall (I:int->hprop),
  forall (cost_body : int -> int),
  forall (a:int) (b:int) (F:int->~~unit) H H',
  (a <= b+1) ->
  (forall i, a <= i <= b -> F i (\$ (cost_body i) \* I i) (# I(i+1))) ->
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (For i = a To b Do F i Done_)
    (\$ (cumul a (b + 1) cost_body) \* H)
    (# I (b+1) \* H').
Proof using.
Admitted. (* TODO *)

Lemma xfor_inv_void_lemma_refine :
  forall (a:int) (b:int) (F:int->~~unit) H (cost : int),
  (a > b) ->
  (For i = a To b Do F i Done_) (\$ 0 \* H) (# H).
Proof using.
Admitted. (* TODO *)

Ltac xfor_inv_core I ::=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
    tryif is_refine_cost_goal then (
      first [ eapply (@xfor_inv_lemma_pred_refine I)
            | eapply (@xfor_inv_lemma_refine I) ];
      [ | xtag_pre_post | | intro; xlocal ]
   ) else (
     first [ apply (@xfor_inv_lemma_pred I)
           | apply (@xfor_inv_lemma I) ];
     [ | | xtag_pre_post ]
   )).

Ltac xfor_inv_void_core tt ::=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
    tryif is_refine_cost_goal then
      eapply (@xfor_inv_void_lemma_refine)
    else
      apply (@xfor_inv_void_lemma)).

(* TODO: xfor_inv_case *)