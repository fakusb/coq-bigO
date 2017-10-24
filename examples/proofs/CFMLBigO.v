Set Implicit Arguments.
Require Import TLC.LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFML.CFLibCredits.
(* Load the BigO library. *)
Require Import Dominated.
Require Import LibFunOrd.
Require Import UltimatelyGreater.
Require Import LibZExtra.

(********************************************************************)

Definition max0 (x : Z) : Z :=
  match x with
  | Z0 => Z0
  | Zpos p => Zpos p
  | Zneg _ => Z0
  end.
  (* Z.max 0 x. *)

Lemma max0_max_0 : forall x, max0 x = Z.max 0 x.
Proof.
  intro x. destruct x.
  - reflexivity.
  - simpl. auto with zarith.
  - simpl. auto with zarith.
Qed.

Lemma max0_max_0' : forall x, max0 x = Z.max x 0.
Proof.
  intro x. destruct x.
  - reflexivity.
  - simpl. auto with zarith.
  - simpl. auto with zarith.
Qed.

Lemma max0_pos : forall x, 0 <= max0 x.
Proof. intros. rewrite max0_max_0. math_lia. Qed.

Hint Resolve max0_pos : zarith.

Lemma max0_eq : forall x, 0 <= x -> max0 x = x.
Proof. intros. rewrite max0_max_0. math_lia. Qed.

Lemma max0_add_eq : forall x y,
    0 <= x ->
    0 <= y ->
    max0 (x + y) = max0 x + max0 y.
Proof. intros. rewrite !max0_max_0. math_lia. Qed.

Lemma max0_add_le : forall x y,
  max0 (x + y) <= max0 x + max0 y.
Proof. intros. rewrite !max0_max_0. math_lia. Qed.

Lemma max0_max : forall x y,
  max0 (Z.max x y) = Z.max (max0 x) (max0 y).
Proof. intros. rewrite !max0_max_0. math_lia. Qed.

Lemma max0_max0 : forall x, max0 (max0 x) = max0 x.
Proof. intros. rewrite !max0_max_0. math_lia. Qed.

Lemma max0_max0_add : forall x y, max0 (max0 x + max0 y) = max0 x + max0 y.
Proof.
  intros x y.
  rewrite max0_add_eq; try apply max0_pos.
  rewrite !max0_max0. reflexivity.
Qed.

Lemma max0_ge_nonpos :
  forall x y, x <= 0 -> x <= max0 y.
Proof.
  intros x y.
  rewrite !max0_max_0. math_lia.
Qed.

Hint Resolve max0_ge_nonpos : zarith.

Lemma max0_ge :
  forall x y, x <= y -> x <= max0 y.
Proof.
  intros. rewrite !max0_max_0. math_lia.
Qed.

Hint Resolve max0_ge : zarith.

Lemma monotonic_max0 : monotonic Z.le Z.le max0.
Proof.
  intros x1 x2 H. rewrite !max0_max_0. math_lia.
Qed.

Lemma monotonic_max0_comp : forall A leA (f : A -> Z),
  monotonic leA Z.le f ->
  monotonic leA Z.le (fun x => max0 (f x)).
Proof.
  introv M. intros x1 x2 H.
  forwards: M x1 x2 H.
  rewrite !max0_max_0. math_lia.
Qed.

Hint Resolve monotonic_max0 : monotonic.
Hint Resolve monotonic_max0_comp : monotonic.

Lemma ultimately_ge_max0 :
  forall k f,
  ultimately Z_filterType (fun x => k <= f x) ->
  ultimately Z_filterType (fun x => k <= max0 (f x)).
Proof.
  introv. filter_closed_under_intersection.
  auto with zarith.
Qed.

Hint Resolve ultimately_ge_max0 : ultimately_greater.

Lemma dominated_max0 : forall A f g,
    dominated A f g ->
    dominated A (fun x => max0 (f x)) g.
Proof.
  introv (c & U). exists c.
  revert U; filter_closed_under_intersection.
  intros.
  assert (I: Z.abs (max0 (f a)) <= Z.abs (f a)). {
    rewrite max0_max_0. math_lia.
  }
  rewrite I. assumption.
Qed.

Hint Resolve dominated_max0 : dominated.

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

(** *)

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

Definition cleanup_cost (A : filterType) (cost cost_clean_eq cost_clean : A -> Z) :=
  (forall (x : A), cost x = cost_clean_eq x) /\
  dominated A cost_clean_eq cost_clean.

Lemma specO_refine_prove :
  forall (A : filterType) (le : A -> A -> Prop)
         (cost cost_clean_eq cost_clean bound : A -> Z)
         (spec : (A -> Z) -> Prop),
    spec cost ->
    cleanup_cost A cost cost_clean_eq cost_clean ->
    (forall x, 0 <= cost x) ->
    monotonic le Z.le cost_clean_eq ->
    dominated A cost_clean bound ->
    specO A le spec bound.
Proof.
  intros ? le cost cost_clean_eq cost_clean bound.
  introv S D1 N M D2.
  econstructor; eauto.
  - apply Monotonic.monotonic_eq with cost_clean_eq; auto.
    intro. rewrite~ (proj1 D1).
  - apply dominated_eq_l with cost_clean_eq.
    rewrite~ (proj2 D1). intro. rewrite~ (proj1 D1).
Qed.

(* body is expected to be a uconstr *)
Ltac intro_cost_expr_1 A cost_name body :=
  refine (let cost_name := (fun (x:A) => body) : A -> Z in _).

(* body is expected to be a uconstr *)
Ltac intro_cost_expr_2 A cost_name body :=
  refine (let cost_name := (fun '(x, y) => body) : A -> Z in _).

(* body is expected to be a uconstr *)
Ltac intro_cost_expr A cost_name body :=
  let A_sort := constr:(Filter.sort A) in
  let A_sort' := (eval compute in A_sort) in
  (* TODO: handle more arities *)
  match A_sort' with
  | (_ * _)%type => intro_cost_expr_2 A cost_name body
  | _ => intro_cost_expr_1 A cost_name body
  end.

(* TODO: make it more robust *)
Ltac intro_destructs :=
  let x := fresh "x" in
  intro x; repeat (destruct x as [x ?]).

Ltac prove_refined_nonneg :=
  intro_destructs; simpl; apply max0_pos.

Ltac xspecO_refine_base cost_name :=
  match goal with
    |- specO ?A ?le _ _ =>
    let cost_clean_eq := fresh "cost_clean_eq" in
    let cost_clean := fresh "cost_clean" in
    intro_cost_expr A cost_name uconstr:(max0 _);
    intro_cost_expr A cost_clean uconstr:(_);
    intro_cost_expr A cost_clean_eq uconstr:(_);
    eapply (@specO_refine_prove A le cost_name cost_clean_eq cost_clean);
    subst cost_clean cost_clean_eq;
    [ unfold cost_name | | prove_refined_nonneg
      | subst cost_name | subst cost_name ]
  end.

Tactic Notation "xspecO" ident(cost_name) :=
  xspecO_refine_base cost_name.

Tactic Notation "xspecO" :=
  let cost_name := fresh "costf" in
  xspecO_refine_base cost_name.

Tactic Notation "xspecO_cost" uconstr(cost_fun) :=
  match goal with
  | |- specO ?A _ _ _ =>
    apply (@SpecO A _ _ _ cost_fun)
  end.

(* This allows us to prove that the provided [cost] is non-negative only on the
   provided [domain].

  TODO: What if we also wanted to prove monicity/dominated only on [domain]?
*)
Lemma xspecO_cost_on_domain :
  forall (A: filterType) le
         (domain : A -> Prop)
         (spec: (A -> int) -> Prop)
         bound cost,
  (forall cost_max_0,
      (forall x, domain x -> cost_max_0 x = cost x) ->
      spec cost_max_0) ->
  (forall (x:A), domain x -> 0 <= cost x) ->
  monotonic le Z.le cost ->
  dominated A cost bound ->
  specO A le spec bound.
Proof.
  intros ? ? ? ? ? costf S Pos Mon Dom.
  pose (cost_max_0 := fun (n:A) => Z.max 0 (costf n)).

  apply SpecO with (cost := cost_max_0); subst cost_max_0; simpl.
  - apply S. intros x D. specialize (Pos _ D). math_lia.
  - intros x. math_lia.
  - Monotonic.monotonic.
  - apply dominated_max_distr.
    exists 0. apply filter_universe_alt. intros. rewrite Z.abs_0. math_lia. auto. (* xx *)
Qed.

Ltac rewrite_cost_domain :=
  let cost' := fresh "cost'" in
  let E := fresh "E" in
  pose ltac_mark;
  intros cost' E;
  repeat intro;
  (rewrite E; [| solve [auto]]);
  clear E cost';
  gen_until_mark.

Tactic Notation "xspecO_cost" uconstr(cost_fun) "on" uconstr(domain) :=
  match goal with
  | |- specO ?A _ _ _ =>
    apply (@xspecO_cost_on_domain A _ domain _ _ cost_fun)
  end;
  try rewrite_cost_domain.

Ltac dominated_cleanup_cost :=
  first [
      apply dominated_max0; dominated_cleanup_cost
    | apply dominated_sum;
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

Ltac clean_max0_math :=
  try cases_if; auto with zarith.

(* Simple tactic to eliminate occurences of [max0 x] when x is proved
   nonnegative by [clean_max0_math].

   We explicitely match the occurencies we want to rewrite before effectively
   rewriting, otherwise rewrite messes with the evars that may appear in the
   goal...
*)
Ltac clean_max0 :=
  repeat match goal with
  | |- context[ Z.max 0 ?x ] =>
    rewrite <-(@max0_max_0 x); rewrite (@max0_eq x) by clean_max0_math
  | |- context[ Z.max ?x 0 ] =>
    rewrite <-(@max0_max_0' x); rewrite (@max0_eq x) by clean_max0_math
  | |- context[ max0 ?x ] => rewrite (@max0_eq x) by clean_max0_math
  end.

Ltac simple_cleanup_cost :=
  simpl; hide_evars_then ltac:(fun _ => ring_simplify).

Ltac simple_cleanup_cost_eq :=
  simpl; clean_max0; simple_cleanup_cost.

Ltac unfold_cost_lhs :=
  match goal with
  | |- ?cost ?x = ?rhs => unfold cost
  end.

Ltac cleanup_cost :=
  unfold cleanup_cost;
  split; [
    intro_destructs; unfold_cost_lhs;
    simple_cleanup_cost_eq;
    reflexivity
  | eapply dominated_eq_r;
    [ dominated_cleanup_cost |];
    intro_destructs;
    simple_cleanup_cost;
    reflexivity
  ].

(* Notations for common [specO]s *)

Notation "'specZ' [ X '\in_O' f ] E" :=
  (specO Z_filterType Z.le (fun X => E) f)
    (X ident, f at level 90, E at level 0,
     format "'[v' 'specZ'  [ X  '\in_O'  f ]  '/'  E ']'", at level 60).

(* Custom CF rules and tactics ************************************************)

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

Ltac is_refine_cost_goal :=
  match goal with
    |- _ (\$ max0 _) _ => apply refine_cost_setup_intro_emp
  | |- _ (\$ max0 _ \* _) _ => idtac
  end.

(* refine_credits

   Applies to a goal with some credit cost, and turns it into a goal where the
number of credits is an evar (so that the _refine tactics can apply). Produces a
side-condition requiring that the evar cost is less than the original cost.
*)

Lemma refine_credits :
  forall A (cost_refined cost : int) (F: ~~A) H Q,
  F (\$ max0 cost_refined \* H) Q ->
  (max0 cost_refined <= cost) ->
  is_local F ->
  F (\$ cost \* H) Q.
Proof.
  introv HH Hcost L.
  xapply HH.
  { hsimpl_credits. math. forwards: max0_pos cost_refined. math. }
  { hsimpl. }
Qed.

Ltac refine_credits :=
  match goal with
    |- _ (\$ _) _ => apply refine_cost_setup_intro_emp
  | |- _ (\$ _ \* _) _ => idtac
  end;
  eapply refine_credits;
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
  | \$_nat _ => idtac
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
  | context [?A \* \$_nat ?x \* _] =>
    tryif is_credits A then fail
    else rewrite (star_comm_assoc A (\$_nat x))
  | context [?A \* \$_nat ?x] =>
    tryif is_credits A then fail
    else rewrite (star_comm A (\$_nat x))
  end.

Ltac bring_credits_to_head_of_pre tt :=
  repeat on_formula_pre bring_credits_to_head.

Goal forall H1 H2 H3 H' p n m,
    \$ p \* \$ n \* \$_nat m \* H1 \* H2 \* H3 ==> H' ->
    \$ p \* H1 \* H2 \* \$ n \* H3 \* \$_nat m ==> H'.
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
  (0 <= credits) ->
  H ==> H' \* H'' ->
  \$ max0 credits \* H ==> H' \* \$ credits \* H''.
Proof.
  introv P HH.
  rewrite max0_eq; auto.
  xchange HH. hsimpl_credits.
Qed.

Lemma cancel_credits_cost :
  forall (cost credits : int) H H' H'',
  (credits <= cost) ->
  (0 <= credits) ->
  \$ (cost - credits) \* H ==> H' \* H'' ->
  \$ max0 cost \* H ==> H' \* \$ credits \* H''.
Proof.
  intros cost_ credits. intros ? ? ? I N H.
  rewrite max0_eq; [| math].
  applys~ hsimpl_cancel_credits_int_1.
Qed.

Ltac inst_credits_cost cont :=
  first [ eapply inst_credits_cost; [ auto with zarith | cont tt ]
        | eapply cancel_credits_cost; [ | auto with zarith | cont tt ]
        ].

Lemma intro_zero_credits_right : forall H H' H'',
  H ==> H' \* \$ 0 \* H'' ->
  H ==> H' \* H''.
Proof.
  introv.
  rewrite credits_int_zero_eq. rewrite star_neutral_l.
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

(* \$_nat ? *)
Ltac hsimpl_inst_credits_cost_setup tt :=
  match goal with
  | |- \$ max0 ?cost ==> _ => is_evar cost; apply hsimpl_start_1
  | |- \$ max0 ?cost \* _ ==> _ => is_evar cost
  | |- \$ max0 (?cost _) ==> _ => is_evar cost; apply hsimpl_start_1
  | |- \$ max0 (?cost _) \* _ ==> _ => is_evar cost
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
  forall A (cost cost' : Z)
         (F: hprop -> (A -> hprop) -> Prop) H Q,
  (cost = 1 + max0 cost') ->
  is_local F ->
  F (\$ max0 cost' \* H) Q ->
  (Pay_ ;; F) (\$ max0 cost \* H) Q.
Proof.
  introv E L HH. rewrite E.
  xpay_start tt.
  { unfold pay_one.
    rewrite max0_eq; [| forwards: max0_pos cost'; math_lia ].
    credits_split.
    hsimpl_credits. math. forwards~: max0_pos cost'. }
  xapply HH. hsimpl_credits. hsimpl.
Qed.

Ltac xpay_core tt ::=
  tryif is_refine_cost_goal then
    (eapply xpay_refine; [ reflexivity | xlocal | ])
  else
    (xpay_start tt; [ unfold pay_one; hsimpl | ]).

(* xret *******************************)

Lemma xret_refine : forall cost A (x : A) H (Q : A -> hprop),
  (cost = 0) ->
  local (fun H' Q' => H' ==> Q' x) H Q ->
  local (fun H' Q' => H' ==> Q' x) (\$ max0 cost \* H) Q.
Proof.
  introv E HH.
  rewrite E. rewrite max0_eq; [| math]. rewrite credits_int_zero_eq. rewrite star_neutral_l.
  assumption.
Qed.

Ltac xret_inst_credits_zero :=
  apply xret_refine; [ reflexivity | ].

Ltac xret_apply_lemma tt ::=
  (tryif is_refine_cost_goal then xret_inst_credits_zero else idtac);
  first [ apply xret_lemma_unify
        | apply xret_lemma ].

Ltac xret_no_gc_core tt ::=
  (tryif is_refine_cost_goal then xret_inst_credits_zero else idtac);
  first [ apply xret_lemma_unify
        | eapply xret_no_gc_lemma ].

(* xseq *******************************)

Lemma xseq_refine :
  forall (A : Type) cost cost1 cost2 F1 F2 H (Q : A -> hprop),
  (cost = max0 cost1 + max0 cost2) ->
  is_local F1 ->
  is_local F2 ->
  (exists Q',
    F1 (\$ max0 cost1 \* H) Q' /\
    F2 (\$ max0 cost2 \* Q' tt) Q) ->
  (F1 ;; F2) (\$ max0 cost \* H) Q.
Proof.
  introv E L1 L2 (Q' & H1 & H2).
  rewrite E.
  xseq_pre tt. apply local_erase. eexists. split.
  { xapply H1. rewrite max0_add_eq; try apply max0_pos. repeat rewrite max0_max0.
    forwards: max0_pos cost1. forwards: max0_pos cost2.
    credits_split. hsimpl. math. math. }
  { xapply H2. hsimpl. hsimpl. }
Qed.

Ltac xseq_core cont0 cont1 ::=
  (tryif is_refine_cost_goal then
     eapply xseq_refine; [ reflexivity | xlocal | xlocal | ]
   else
     apply local_erase);
  cont0 tt;
  split; [ | cont1 tt ];
  xtag_pre_post.

(* xlet *****************************************)

Lemma xlet_refine :
  forall
    (A B : Type) cost cost1 cost2
    (F1 : hprop -> (A -> hprop) -> Prop)
    (F2 : A -> hprop -> (B -> hprop) -> Prop)
    (H : hprop) (Q : B -> hprop),
  (cost = max0 cost1 + max0 cost2) ->
  is_local F1 ->
  (forall x, is_local (F2 x)) ->
  (exists (Q' : A -> hprop),
    F1 (\$ max0 cost1 \* H) Q' /\
    (forall r, F2 r (\$ max0 cost2 \* Q' r) Q)) ->
  cf_let F1 F2 (\$ max0 cost \* H) Q.
Proof.
  introv E L1 L2 (Q' & H1 & H2).
  rewrite E.
  unfold cf_let.
  eexists. split.
  { xapply H1. rewrite max0_add_eq; try apply max0_pos. repeat rewrite max0_max0.
    forwards: max0_pos cost1. forwards: max0_pos cost2.
    credits_split. hsimpl. math. math. }
  { intro r. specializes L2 r. xapply H2; hsimpl. }
Qed.

Ltac xlet_core cont0 cont1 cont2 ::=
  apply local_erase;
  match goal with |- cf_let ?F1 (fun x => _) ?H ?Q =>
    tryif is_refine_cost_goal then (
      eapply xlet_refine;
      [ reflexivity | xlocal | intro; xlocal | ]
    ) else idtac;
    cont0 tt;
    split; [ | cont1 x; cont2 tt ];
    xtag_pre_post
  end.

(* xif ********************************)

Lemma xif_refine : forall (A: Type) cost cost1 cost2 cond (F1 F2: ~~A) H Q,
  (cost = Z.max (max0 cost1) (max0 cost2)) ->
  is_local F1 ->
  is_local F2 ->
  ((cond = true -> F1 (\$ max0 cost1 \* H) Q) /\
   (cond = false -> F2 (\$ max0 cost2 \* H) Q)) ->
  (If_ cond Then F1 Else F2) (\$ max0 cost \* H) Q.
Proof.
  introv costE L1 L2 (H1 & H2).
  apply local_erase. rewrite costE.
  forwards: max0_pos cost1. forwards: max0_pos cost2.
  split; intro; [xapply~ H1 | xapply~ H2];
  hsimpl_credits; try math; rewrite max0_max; rewrite !max0_max0;
  math_lia.
Qed.

Ltac xif_base cont1 cont2 ::=
  xpull_check_not_needed tt;
  xif_check_post_instantiated tt;
  let cont tt :=
    tryif is_refine_cost_goal then (
      eapply xif_refine;
      [ reflexivity | xlocal | xlocal | ]
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

Lemma xif_guard_refine : forall (A: Type) cost cost1 cost2 (cond cond': bool) (F1 F2: ~~A) H Q,
  (cond = cond') ->
  (cost = If cond' then cost1 else cost2) ->
  is_local F1 ->
  is_local F2 ->
  ((cond = true -> F1 (\$ max0 cost1 \* H) Q) /\
   (cond = false -> F2 (\$ max0 cost2 \* H) Q)) ->
  (If_ cond Then F1 Else F2) (\$ max0 cost \* H) Q.
Proof.
  introv condEq costE L1 L2 (H1 & H2).
  apply local_erase. rewrite <-condEq in costE. rewrite costE.
  forwards: max0_pos cost1. forwards: max0_pos cost2.
  split; intro C; rewrite C; cases_if; [xapply~ H1 | xapply~ H2];
  hsimpl_credits; try math; rewrite !max0_max0; math.
Qed.

Ltac xif_guard_base cont :=
  is_refine_cost_goal;
  eapply xif_guard_refine;
  [ try reflexivity | reflexivity | xlocal | xlocal | ];
  split; cont tt; xtag_pre_post.

Ltac xif_guard_core H :=
  xif_guard_base ltac:(fun _ => intro H; xif_post H).

Tactic Notation "xif_guard" "as" ident(H) :=
  xif_guard_core H.
Tactic Notation "xif_guard" :=
  let H := fresh "C" in xif_guard as C.

(* xguard ***************************************)

Lemma xguard_refine :
  forall A (cost cost' : int) (F: ~~A) (G: Prop) H Q,
  G ->
  (cost = If G then cost' else 0) ->
  F (\$ max0 cost' \* H) Q ->
  F (\$ max0 cost \* H) Q.
Proof.
  introv HG E HH. rewrite E. cases_if. trivial.
Qed.

Ltac xguard G :=
  is_refine_cost_goal;
  eapply xguard_refine;
  [ eexact G | reflexivity | ].

(* xfor *****************************************)

(* TODO: prove using xfor_inv_case_lemma_refine instead of directly *)
Lemma xfor_inv_lemma_pred_refine :
  forall
    (I : int -> hprop) (cost : int)
    (cost_body : int -> int)
    (a : int) (b : int) (F : int-> ~~unit) H H',
  (a <= b) ->
  (forall i, a <= i < b -> F i (\$ max0 (cost_body i) \* I i) (# I(i+1))) ->
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (cumul a b (fun i => max0 (cost_body i)) <= cost) ->
  (For i = a To (b - 1) Do F i Done_) (\$ max0 cost \* H) (# I b \* H').
Proof.
  introv a_le_b HI HH Flocal Icost.
  assert (cost_nonneg : 0 <= cost0). {
    rewrite cumulP in Icost. rewrite big_nonneg_Z. apply Icost.
    intros. simpl. apply max0_pos.
  }
  applys xfor_inv_case_lemma
    (fun (i: int) => \$ cumul i b (fun i => max0 (cost_body i)) \* I i);
  intros C.
  { eexists. splits~.
    - hchange HH. hsimpl.
      rewrite~ max0_eq. hsimpl_credits. math. admit. (* ok *)
    - intros i Hi.
      (* xframe (\$cumul f (i + 1) n). auto. *) (* ?? *)
      xframe_but (\$max0 (cost_body i) \* I i). auto.
      assert (forall f, cumul i b f = f i + cumul (i + 1) b f) as cumul_lemma by admit.
      rewrite cumul_lemma; clear cumul_lemma.
      credits_split. hsimpl. admit. (* ok *)
      admit. (* ok *)
      applys HI. math.
      xsimpl_credits.
    - math_rewrite ((b - 1) + 1 = b). hsimpl. }
  { xchange HH. math_rewrite (a = b). xsimpl. }
Qed.

Lemma xfor_inv_case_lemma_refine : forall (I:int->hprop),
   forall (cost : int) (cost_body : int -> int),
   forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
   ((a <= b) -> exists H',
          (H ==> I a \* H')
       /\ (forall i, is_local (F i))
       /\ (forall i, a <= i <= b -> F i (\$ max0 (cost_body i) \* I i) (# I(i+1)))
       /\ (cumul a b (fun i => max0 (cost_body i)) <= cost)
       /\ (I (b+1) \* H' ==> Q tt \* \GC)) ->
   ((a > b) ->
          (0 <= cost)
       /\ (H ==> Q tt \* \GC)) ->
   (For i = a To b Do F i Done_) (\$ max0 cost \* H) Q.
Proof.
  introv Ha_le_b Ha_gt_b.
  assert (cost_nonneg : 0 <= cost0). {
    destruct (Z.le_gt_cases a b) as [a_le_b | a_gt_b].
    - specializes~ Ha_le_b ___. destruct Ha_le_b as (? & H').
      rewrite cumulP in H'. rewrite big_nonneg_Z. apply H'.
      intros. simpl. apply max0_pos.
    - specializes~ Ha_gt_b ___. math.
  }
  applys xfor_inv_case_lemma
    (fun (i:int) => \$ cumul i b (fun i => max0 (cost_body i)) \* I i).
  - intro a_le_b. specializes~ Ha_le_b.
    destruct Ha_le_b as (H' & H1 & Hl & H2 & Hcumul & H3).
    eexists. splits.
    + hchange H1. hsimpl.
      rewrite~ max0_eq. hsimpl_credits. math. admit. (* ok *)
    + intros i Hi.
      xframe_but (\$ max0 (cost_body i) \* I i). auto.
      assert (forall f, cumul i b f = f i + cumul (i + 1) b f) as cumul_lemma by admit.
      rewrite cumul_lemma; clear cumul_lemma.
      credits_split. hsimpl. admit. (* ok *)
      admit. (* ok *)
      applys H2. math. xsimpl_credits.
    + xchange H3. admit. (* todo *)
  - intro a_gt_b. specializes~ Ha_gt_b. math. destruct Ha_gt_b as (? & HH).
    (* todo *) admit.
Qed.

Lemma xfor_inv_lemma_refine : forall (I:int->hprop),
  forall (cost : int) (cost_body : int -> int),
  forall (a:int) (b:int) (F:int->~~unit) H H',
  (a <= b+1) ->
  (forall i, a <= i <= b -> F i (\$ max0 (cost_body i) \* I i) (# I(i+1))) ->
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (cumul a (b + 1) (fun i => max0 (cost_body i)) <= cost) ->
  (For i = a To b Do F i Done_) (\$ max0 cost \* H) (# I (b+1) \* H').
Proof using.
  introv ML MI MH Mloc HI. applys xfor_inv_case_lemma_refine I; intros C.
  { exists H'. splits~. admit. (* ok *) hsimpl. }
  { splits. admit. (* ok *) xchange MH. math_rewrite (a = b + 1). xsimpl. }
Qed.

Lemma xfor_inv_void_lemma_refine :
  forall (a:int) (b:int) (F:int->~~unit) H (cost : int),
  (a > b) ->
  (0 <= cost) ->
  (For i = a To b Do F i Done_) (\$ max0 cost \* H) (# H).
Proof using.
  introv ML MC.
  applys xfor_inv_case_lemma_refine (fun (i:int) => \[]); intros C.
  { false. }
  { splits~. xsimpl. }
  Unshelve. exact (fun _ => 0).
Qed.

Ltac xfor_inv_core I ::=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
    tryif is_refine_cost_goal then (
      first [ eapply (@xfor_inv_lemma_pred_refine I)
            | eapply (@xfor_inv_lemma_refine I) ];
      [ | xtag_pre_post | | intro; xlocal | (* try reflexivity *) ]
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