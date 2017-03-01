Set Implicit Arguments.
Require Import LibTactics.
(* Load the CFML library, with time credits. *)
Require Import CFLibCredits.
Require Pervasives_ml.
Require Array_ml.
Require Import Pervasives_proof.
Require Import Array_proof.
(* Load the BigO library. *)
Require Import Dominated.
Require Import BigEnough.
Require Import LibEvars.
Require Import EvarsFacts.
(* Load the examples CF definitions. *)
Require Import Max_subsequence_sum_ml.
Require Import Simple_ml.

(* xxx *)
Lemma simpl_zero_credits : forall n, n = 0 -> \$ n ==> \[].
Proof. intros. subst. rewrite <-credits_int_zero_eq. hsimpl. Qed.

(* TODO: cas où f ne dépend pas de i *)
Lemma xfor_inv_lemma_pred_credits : forall (I:int->hprop) (f: int -> int),
  forall (a:int) (n:int) (F:int->~~unit) H H',
  (a <= n) ->
  (forall i, a <= i < n -> F i (\$ f i \* I i) (# I(i+1))) ->
  (H ==> \$ cumul f a n \* I a \* H') ->
  (forall i, is_local (F i)) ->
  (forall i, a <= i -> 0 <= f i) ->
  (For i = a To (n - 1) Do F i Done_) H (# I n \* H').
Proof.
  introv a_le_n HI HH Flocal Hf.
  applys xfor_inv_case_lemma (fun (i: int) => \$ cumul f i n \* I i); intros C.
  { exists H'. splits~.
    - hchange HH. hsimpl.
    - intros i Hi.
      (* xframe (\$cumul f (i + 1) n). auto. *) (* ?? *)
      xframe_but (\$f i \* I i). auto.
      assert (cumul f i n = f i + cumul f (i + 1) n) as cumul_lemma by admit.
      rewrite cumul_lemma; clear cumul_lemma.
      xsimpl_credits. admit. (* cumul f nonneg *) specializes Hf i ___.
      applys HI. math.
      xsimpl_credits. math. admit. (* cumul f nonneg. *)
      apply simpl_zero_credits. math.
    - hsimpl. math_rewrite ((n - 1) + 1 = n). hsimpl. }
  { xchange HH. math_rewrite (a = n). xsimpl. }
Qed.

Lemma xfor_inv_lemma_credits : forall (I:int->hprop) (f: int -> int),
  forall (a:int) (b:int) (F:int->~~unit) H H',
  (a <= b+1) ->
  (forall i, a <= i <= b -> F i (\$ f i \* I i) (# I(i+1))) ->
  (H ==> \$ cumul f a (b+1) \* I a \* H') ->
  (forall i, is_local (F i)) ->
  (forall i, a <= i -> 0 <= f i) ->
  (For i = a To b Do F i Done_) H (# I (b+1) \* H').
Proof.
  introv a_le_b HI HH Flocal Hf.
  math_rewrite (b = (b + 1) - 1).
  math_rewrite (((b + 1) - 1) + 1 = b + 1).
  applys~ xfor_inv_lemma_pred_credits.
  intros. apply HI. math.
Qed.

Ltac xfor_inv_credits_core I f :=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
     first [ apply (@xfor_inv_lemma_pred_credits I f)
           | apply (@xfor_inv_lemma_credits I f) ];
     [ | xtag_pre_post | | intros; xlocal | ..]).

Tactic Notation "xfor_inv_credits" constr(I) constr(f) :=
  xfor_inv_credits_core I f.

Ltac tlc_big :=
  autorewrite with rew_maths rew_int_comp rew_nat_comp;
  big.

Lemma tick_spec :
  app tick [tt]
    PRE (\$1)
    POST (fun (tt:unit) => \[]).
Proof. xcf. xpay. xret. hsimpl. Qed.

Hint Extern 1 (RegisterSpec tick) => Provide tick_spec.

Lemma cumul_pos :
  forall f i j,
  (forall x, 0 <= f x) ->
  0 <= cumul f i j.
Proof. admit. Qed.

Lemma dominated_sum' (A: filterType) f g h :
  dominated A f h ->
  dominated A g h ->
  dominated A (fun x => (f x) + (g x)) h.
Proof. admit. Qed.

Definition appO
  (f: func) (xs: list dynamic)
  (A: filterType) (costO : A -> Z) (cost_x : A)
  {B} (H: hprop) (Q : B -> hprop)
  :=
  exists (cost : A -> Z),
   app f xs
     PRE (\$ cost cost_x \* H)
     POST Q /\
   dominated A cost costO.

(* TODO : fix the parenthesis around the notation *)
Notation "'appO' f xs A costO cost_x" :=
  (@appO f (xs)%dynlist A costO cost_x _)
  (at level 80,
   f at level 0, xs at level 0,
   A at level 0, costO at level 0, cost_x at level 0) : charac.

(* TODO Notation:

   appO f xs
     COST A costO cost_x
     PRE H
     POST Q
*)

Lemma tick3_spec :
  appO tick3 [tt]
    unit_filterType (fun tt => 1) tt
    \[]
    (fun (tt:unit) => \[]).
Proof.
  exists_big_fun cost unit int; try split; swap 2 3.
  xcf.
  xpay. { xsimpl_credits. apply le_implies_ge. tlc_big. math. }
  xapp. { xsimpl_credits. cut (le (1 + 1) (cost tt)). math. tlc_big. math. }
  xapp. { xsimpl_credits. cut (le (1 + (1 + 1)) (cost tt)). math. tlc_big. math. }
  xapp. { xsimpl_credits. cut (le (1 + (1 + (1 + 1))) (cost tt)). math. tlc_big. math. }
  close.
  simpl in cost. subst cost.
  repeat (apply dominated_max_distr; [apply dominated_cst; math |]).
  apply dominated_cst; math.
Qed.

Lemma loop1_spec :
  exists (cost: int -> int),
  forall (n: int),
  0 <= n ->
  app loop1 [n]
    PRE (\$ cost n)
    POST (fun (tt:unit) => \[]) /\
  dominated Z_filterType cost (fun (n:Z) => n).
Proof.
  exists_big_fun cost int int; try split; swap 2 3.
  xcf.
  xpay. { xsimpl_credits. apply le_implies_ge. tlc_big. math. }
  pose_big_fun f int int.
  xfor_inv_credits (fun (i: int) => \[]) f.
  - math.
  - intros i Hi. xapp. xsimpl_credits. apply le_implies_ge. tlc_big. math.
    xapp. xsimpl_credits. cut (2 <= f i); [math|]. tlc_big. math.
  - xsimpl_credits.
    apply le_implies_ge. cut (cumul f 0 n + 1 <= cost n); [math|]. tlc_big.
    apply le_implies_ge. apply cumul_pos. intro. tlc_big.
  - intros. tlc_big.
  - xsimpl_credits.
  - close.
  - close.
  - simpl in cost. subst cost.
    apply dominated_max_distr. admit.
    apply dominated_max_distr; [|admit].
    apply dominated_sum'; [|admit].
    rewrite dominated_big_sum_bound.
    { simpl. admit. }
    { apply filter_universe_alt. intros _. math_lia. }
    { admit. }
Qed.

(* Disable a workaround by [logics] in TLC. The workaround uses the goal as a
   stack, and for that purpose [generalize]s then [intro]s assumptions of the
   goal.

   This has an unwanted side-effect: it strengthens the goal if it contained
   evars that could depend on assumptions of the context: after a [generalize;
   intro], those evars cannot depend anymore on the assumptions that got
   generalized.
*)
Ltac rew_isTrue ::= autorewrite with rew_isTrue.

Ltac exists_cost cost A :=
  let cost_rest := fresh "body" in
  evar (cost_rest : A -> Z);
  pose (cost := fun e => cost_rest e);
  subst cost_rest;
  exists cost;
  unfold cost.

Ltac add_credits n cost :=
  match type of cost with
    ?T =>
    let E := get_evar_in cost in
    let cost_rest' := fresh in
    evar (cost_rest' : T);
    let E' := get_body cost_rest' in
    unify E (fun e => n + E' e);
    simpl in cost; clear cost_rest'
  end.

Goal exists (cost : int -> int), cost 3 = 1.
  exists_cost cost int.
  add_credits 1 cost. simpl in *.
  prove_evar_in cost. exact (fun (x: int) => 0).
  simpl. math.
Qed.

Lemma Hcost_add_credits (A: Type) (n: int) (cost_rest : A -> int) :
  0 <= n ->
  (forall x, 0 <= cost_rest x) ->
  (forall x, 0 <= n + cost_rest x).
Proof.
  intros npos H x. specializes H x. math.
Qed.

Ltac prove_Hcost_with Hcost' cost Hcost :=
  match type of Hcost with
    forall x, 0 <= ?n + _ =>
    let side := fresh in
    evar (side : 0 <= n);
    let H := get_body Hcost in
    let H' := get_body Hcost' in
    let E := get_evar_in cost in
    let cost_rest := fresh in
    (* weird, but seems to be needed. inlining cost_rest with E in unify below
       doesn't work... *)
    pose (cost_rest := E);
    unify
      H
      (Hcost_add_credits cost_rest side H');
    subst cost_rest;
    prove_evar_in side; [| clear Hcost; clear side]
  end.

(* Set Printing Existential Instances. *)

Lemma tick3_spec_2 :
  appO tick3 [tt]
    unit_filterType (fun tt => 1) tt
    \[]
    (fun (tt:unit) => \[]).
Proof.
  exists_cost cost unit. split.
  let E := get_evar_in cost in evar (Hcost : forall x, 0 <= E x).

  xcf.

  add_credits 1 cost. simpl in *.
  let E := get_evar_in cost in evar (Hcost' : forall x, 0 <= E x).
  prove_Hcost_with Hcost' cost Hcost. math. rename Hcost' into Hcost.
  xpay. credits_split. hsimpl_credits. math. apply le_implies_ge. apply Hcost.

  add_credits 1 cost. simpl in *.
  let E := get_evar_in cost in evar (Hcost' : forall x, 0 <= E x).
  prove_Hcost_with Hcost' cost Hcost. math. rename Hcost' into Hcost.
  xapp. credits_split. hsimpl. math. apply le_implies_ge. apply Hcost.

  add_credits 1 cost. simpl in *.
  let E := get_evar_in cost in evar (Hcost' : forall x, 0 <= E x).
  prove_Hcost_with Hcost' cost Hcost. math. rename Hcost' into Hcost.
  xapp. credits_split. hsimpl. math. apply le_implies_ge. apply Hcost.

  add_credits 1 cost. simpl in *.
  let E := get_evar_in cost in evar (Hcost' : forall x, 0 <= E x).
  prove_Hcost_with Hcost' cost Hcost. math. rename Hcost' into Hcost.
  xapp. credits_split. hsimpl. math. apply le_implies_ge. apply Hcost.

  (* close cost. *)
  let E := get_evar_in cost in unify E (fun (_:unit) => 0).
  simpl in *.
  apply dominated_cst. math.

  Unshelve. (* prove Hcost *)
  math.
Qed.

Lemma hsimpl_cancel_credits_int_alt :
  forall A m (n rest : A -> int) x HT HA,
  (forall x, n x = m + rest x) ->
  0 <= m ->
  0 <= rest x ->
  \$(rest x) \* HT ==> HA ->
  \$(n x) \* HT ==> HA \* \$ m.
Proof.
  introv E m_nonneg rest_nonneg H.
  hsimpl_credits.
  { rewrite E. math. }
  { math. }
  { rewrite E. hchange H.
    { hsimpl_credits. math. math. }
    { hsimpl_credits. apply simpl_zero_credits. math. }
  }
Qed.

Ltac hsimpl_cancel_credits_int_alt facts :=
  hsimpl_setup tt; hsimpl_step tt; eapply hsimpl_cancel_credits_int_alt;
  [ reflexivity
  |
  | match goal with
      |- _ <= _ ?x => generalize x; prove_later_as_fact facts
    end
  | hsimpl
  ].

(*
Ltac Hcost_bookkeeping Hcost facts :=
  let Hcost' := fresh in
  name_latest_fact Hcost' facts;
  prove_fact_using Hcost' Hcost facts; [ intros H x; specializes H x; omega |];
  trim_facts facts; rename Hcost' into Hcost.

Lemma tick3_spec_3 :
  appO tick3 [tt]
    unit_filterType (fun tt => 1) tt
    \[]
    (fun (tt:unit) => \[]).
Proof.
  exists_cost cost unit. split.
  pose_facts facts; cut True.
  let E := get_evar_in cost in add_fact Hcost (forall x, 0 <= E x) facts.

  xcf.

  xpay.
  hsimpl_cancel_credits_int_alt facts. math.
  Hcost_bookkeeping Hcost facts.

  xapp.
  hsimpl_cancel_credits_int_alt facts. math.
  Hcost_bookkeeping Hcost facts.

  xapp.
  hsimpl_cancel_credits_int_alt facts. math.
  Hcost_bookkeeping Hcost facts.

  xapp.
  hsimpl_cancel_credits_int_alt facts. math.

  (* arg *)
  (* trim_facts facts. *) (* ???? *)
  close_facts facts. trim_facts facts.
  let E := get_evar_in cost in unify E (fun (_:unit) => 0). simpl in *.
  (* .... *) exact I.

  simpl in *. apply dominated_cst. math.

  Unshelve. math. math.
Qed.
 *)

Record cost_fun A := make_cost_fun {
  cost :> A -> Z ;
  cost_nonneg : forall x, 0 <= cost x
}.

Arguments make_cost_fun [A].

(*
Lemma costP A (f : cost_fun A) :
  cost f = fun (x : A) => f x.
Proof. reflexivity. Qed.
*)

(* Hint Rewrite costP : rew_cost. *)

Global Instance cost_fun_inhab A : Inhab (cost_fun A).
Proof using.
  applys prove_Inhab.
  applys make_cost_fun (fun (_ : A) => 0). intros _.
  omega.
Qed.

Definition myif A (cond : Prop) (a b : A) :=
  if (classicT cond) then a else b.

(*
Program Definition cost_cst A (c : Z) :=
  If (0 <= c) then make_cost_fun (fun (_ : A) => c) _ else arbitrary.
*)

Opaque myif.

Program Definition cost_cst A (c : Z) :=
  myif (0 <= c) (make_cost_fun (fun (_ : A) => c) _) arbitrary.
Next Obligation.
  admit.
Defined.

Program Definition cost_one A :=
  make_cost_fun (fun (_ : A) => 1) _.

Arguments cost_one : clear implicits.

Program Definition cost_add A (f g : cost_fun A) :=
  make_cost_fun (fun (x : A) => f x + g x) _.
Next Obligation.
  intros A f g x. simpl.
  forwards: cost_nonneg f x.
  forwards: cost_nonneg g x.
  math.
Defined.

Program Definition cost_max A (f g : cost_fun A) :=
  make_cost_fun (fun (x : A) => Z.max (f x) (g x)) _.
Next Obligation.
  intros A f g x. simpl.
  forwards: cost_nonneg f x.
  forwards: cost_nonneg g x.
  math_lia.
Defined.

Lemma cost_cstP :
  forall A (c : Z) (x : A),
  0 <= c ->
  cost_cst A c x = c.
Proof.
  introv N.
  unfold cost_cst. (* todo notation *)
  Transparent myif. unfold myif.
  destruct (classicT (0 <= c)). simpl. auto. false. auto.
Qed.

Hint Rewrite cost_cstP : rew_cost.

Lemma cost_oneP :
  forall A (x : A),
  cost_one A x = 1.
Proof. reflexivity. Qed.

Hint Rewrite cost_oneP : rew_cost.

Lemma cost_cst_one :
  forall A x,
  cost_cst A 1 x = cost_one A x.
Proof. intros. rewrite cost_cstP. rewrite cost_oneP. math. math. Qed.

Lemma cost_addP :
  forall A (f g : cost_fun A) x,
  cost_add f g x = f x + g x.
Proof. reflexivity. Qed.

Hint Rewrite cost_addP : rew_cost.

Tactic Notation "rew_cost" :=
  autorewrite with rew_cost.
Tactic Notation "rew_cost" "~" :=
  rew_cost; auto_tilde.
Tactic Notation "rew_cost" "in" hyp(H) :=
  autorewrite with rew_cost in H.
Tactic Notation "rew_cost" "~" "in" hyp(H) :=
  rew_cost in H; auto_tilde.
Tactic Notation "rew_cost" "in" "*" :=
  autorewrite with rew_cost in *.
Tactic Notation "rew_cost" "~" "in" "*" :=
  rew_cost in *; auto_tilde.

Definition appO_
  (f: func) (xs: list dynamic)
  (A: filterType) (costO : A -> Z) (x : A)
  {B} (H: hprop) (Q : B -> hprop)
  :=
  exists (cost : cost_fun A),
   app f xs
     PRE (\$ cost x \* H)
     POST Q /\
   dominated A cost costO.

(* TODO : fix the parenthesis around the notation *)
Notation "'appO_' f xs A costO x" :=
  (@appO_ f (xs)%dynlist A costO x _)
  (at level 80,
   f at level 0, xs at level 0,
   A at level 0, costO at level 0, x at level 0) : charac.

Lemma xpay_refine :
  forall A B (cost cost' : cost_fun A) (x: A)
         (F: hprop -> (B -> hprop) -> Prop) H Q,
  (cost = cost_add (cost_one A) cost') ->
  is_local F ->
  F (\$ cost' x \* H) Q ->
  (Pay_ ;; F) (\$ cost x \* H) Q.
Proof.
  introv E L HH. rewrite E. rew_cost.
  xpay_start tt.
  { unfold pay_one. credits_split. hsimpl. math.
    forwards: cost_nonneg cost' x. math. }
  xapply HH. hsimpl. hsimpl.
Qed.

(* tmp *)
Ltac xpay_core tt ::=
  eapply xpay_refine; [ reflexivity | xlocal | ].

Lemma xseq_refine :
  forall (A B : Type) cost cost1 cost2 (x : A) F1 F2 H (Q : B -> hprop),
  (cost = cost_add cost1 cost2) ->
  is_local F1 ->
  is_local F2 ->
  (exists Q',
    F1 (\$ cost1 x \* H) Q' /\
    F2 (\$ cost2 x \* Q' tt) Q) ->
  (F1 ;; F2) (\$ cost x \* H) Q.
Proof.
  introv E L1 L2 (Q' & H1 & H2).
  rewrite E. rew_cost.
  xseq_pre tt. apply local_erase. eexists. split.
  { xapply H1. credits_split. hsimpl.
    forwards~: cost_nonneg cost1 x.
    forwards~: cost_nonneg cost2 x. }
  { xapply H2. hsimpl. hsimpl. }
Qed.

(* tmp *)
Ltac xseq_noarg_core tt ::=
  eapply xseq_refine; [ reflexivity | xlocal | xlocal | eexists; split ].

Ltac dominated_rew_cost :=
  eapply dominated_eq_l; [ | intros; rew_cost; reflexivity ]; simpl.

(*
Lemma group_credits_lemma : forall H1 H2 H3,
    H1 \* H2 \* H3 = (H2 \* H1) \* H3.
Proof. intros. rewrite (star_comm H2 H1). rew_heap. auto. Qed.

Ltac group_credits_step H :=
  match H with
  | ?H1 \* ?H2 \* ?H3 =>
    tryif is_credits H2 then
      tryif is_credits H3 then
        fail
      else
        rewrite (group_credits_lemma H1 H2 H3)
    else fail
  end.

Ltac group_credits_in_pre tt :=
  repeat on_formula_pre group_credits_step.

Ltac group_credits_in_post tt :=
  repeat on_formula_post group_credits_step.

Goal forall H H' n m p,
    (\$ p \* \$ m \* \$ n) \* H ==> H' ->
    \$ n \* \$ m \* \$ p \* H ==> H'.
Proof.
  intros. dup.
  (* detailed *)
  on_formula_pre group_credits_step.
  on_formula_pre group_credits_step.
  assumption.
  (* short *)
  group_credits_in_pre tt.
  assumption.
Qed.

Goal forall H' n m p,
    \$ n \* \$ m \* \$ p ==> H'.
Proof.
  intros.
  group_credits_in_pre tt.
Admitted. (* demo *)

Goal forall H H' n,
    \$ n \* H ==> H'.
Proof.
  intros.
  group_credits_in_pre tt.
Admitted. (* demo *)
*)

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

Lemma inst_credits_cost : forall A (cost : cost_fun A) x credits H H' H'',
    (cost = cost_cst A credits) ->
    0 <= credits ->
    H ==> H' \* H'' ->
    \$ cost x \* H ==> H' \* \$ credits \* H''.
Proof.
  introv E P HH.
  rewrite E.
  rewrite cost_cstP.
  xchange HH. hsimpl.
  auto.
Qed.

Lemma inst_credits_cost_1 : forall A (cost : cost_fun A) x H H' H'',
    (cost = cost_one A) ->
    H ==> H' \* H'' ->
    \$ cost x \* H ==> H' \* \$ 1 \* H''.
Proof.
  introv E HH.
  rewrite E. rewrite <-cost_cst_one.
  applys~ inst_credits_cost.
  math.
Qed.

Ltac inst_credits_cost :=
  first [
      (apply inst_credits_cost_1; [ reflexivity | ])
    | (apply inst_credits_cost; [ reflexivity | try math | ])
  ].

Ltac is_cost_evar f :=
  match f with cost ?body => is_evar body end.

(* \$_nat ? *)
Ltac hsimpl_inst_credits_cost_setup tt :=
  match goal with
  | |- \$ ?f _ ==> _ => is_cost_evar f; apply hsimpl_start_1
  | |- \$ ?f _ \* _ ==> _ => is_cost_evar f
  end;
  match goal with
  | |- _ ==> _ \* \$ _ => apply hsimpl_starify
  | |- _ ==> _ \* \$ _ \* _ => idtac
  end.

Ltac hsimpl_inst_credits_cost tt :=
  tryif hsimpl_inst_credits_cost_setup tt then
    inst_credits_cost
  else
    idtac.

Ltac hsimpl_setup process_credits ::=
  prepare_goal_hpull_himpl tt;
  try (check_arg_true process_credits; credits_join_left_repeat tt);
  hsimpl_left_empty tt;
  hsimpl_inst_credits_cost tt;
  apply hsimpl_start.

Lemma tick3_spec_4 :
  appO_ tick3 [tt]
    unit_filterType (fun tt => 1) tt
    \[]
    (fun (tt:unit) => \[]).
Proof.
  eexists. split.
  xcf.
  xpay.
  xseq.
  xapp. hsimpl.
  xapp. hsimpl.
  xapp. hsimpl.

  dominated_rew_cost.
  apply dominated_cst. math.
Qed.

Lemma loop1_spec_2 :
  exists (cost: Z -> Z),
  (forall (n: Z),
   0 <= n ->
   app loop1 [n]
     PRE (\$ cost n)
     POST (fun (tt:unit) => \[])) /\
  (forall x, 0 <= cost x) /\
  dominated Z_filterType cost (fun (n:Z) => n).
Proof. admit. Admitted.

Lemma xlet_refine :
  forall
    (A B : Type) cost cost1 cost2
    (F1 : hprop -> (A -> hprop) -> Prop)
    (F2 : A -> hprop -> (B -> hprop) -> Prop)
    (H : hprop) (Q : B -> hprop),
  (cost = cost1 + cost2)%nat ->
  is_local F1 ->
  (forall x, is_local (F2 x)) ->
  (exists (Q' : A -> hprop),
    F1 (\$ Z.of_nat cost1 \* H) Q' /\
    (forall r, F2 r (\$ Z.of_nat cost2 \* Q' r) Q)) ->
  (Let r := F1 in F2 r) (\$ Z.of_nat cost \* H) Q.
Proof.
  introv E L1 L2 (Q' & H1 & H2).
  rewrite E.
  unfold cf_let. xuntag tag_let. apply local_erase.
  eexists. split.
  { xapply H1. rewrite Nat2Z.inj_add. credits_split. hsimpl. math. math. }
  { intro r. specializes L2 r. xapply H2; hsimpl. }
Qed.

Ltac xlet_pre tt ::=
  xpull_check_not_needed tt.

Ltac xlet_core cont0 cont1 cont2 ::=
  match goal with |- (tag tag_let (local (cf_let ?F1 (fun x => _)))) ?H ?Q =>
    eapply xlet_refine;
    [ reflexivity | xlocal | intro; xlocal | ];
    cont0 tt;
    split; [ | cont1 x; cont2 tt ];
    xtag_pre_post
  end.

Lemma xpay_refine_nat :
  forall A (cost cost' : nat)
         (F: hprop -> (A -> hprop) -> Prop) H Q,
  (cost = 1 + cost')%nat ->
  is_local F ->
  F (\$ Z.of_nat cost' \* H) Q ->
  (Pay_ ;; F) (\$ Z.of_nat cost \* H) Q.
Proof.
  introv E L HH. rewrite E. rew_cost.
  xpay_start tt.
  { unfold pay_one. credits_split.
    hsimpl_credits. math. math. }
  xapply HH. hsimpl_credits. math. math.
  hsimpl.
Qed.

(* tmp *)
Ltac xpay_core tt ::=
  eapply xpay_refine_nat; [ reflexivity | xlocal | ].

Lemma xseq_refine_nat :
  forall (A : Type) cost cost1 cost2 F1 F2 H (Q : A -> hprop),
  (cost = cost1 + cost2)%nat ->
  is_local F1 ->
  is_local F2 ->
  (exists Q',
    F1 (\$ Z.of_nat cost1 \* H) Q' /\
    F2 (\$ Z.of_nat cost2 \* Q' tt) Q) ->
  (F1 ;; F2) (\$ Z.of_nat cost \* H) Q.
Proof.
  introv E L1 L2 (Q' & H1 & H2).
  rewrite E. rew_cost.
  xseq_pre tt. apply local_erase. eexists. split.
  { xapply H1. rewrite Nat2Z.inj_add. credits_split. hsimpl. math. math. }
  { xapply H2. hsimpl. hsimpl. }
Qed.

(* tmp *)
Ltac xseq_noarg_core tt ::=
  eapply xseq_refine_nat; [ reflexivity | xlocal | xlocal | eexists; split ].


Lemma xret_refine_nat : forall cost A (x : A) H (Q : A -> hprop),
  (cost = 0)%nat ->
  local (fun H' Q' => H' ==> Q' x) H Q ->
  local (fun H' Q' => H' ==> Q' x) (\$ Z.of_nat cost \* H) Q.
Proof.
  introv E HH.
  rewrite E. simpl. rewrite credits_int_zero_eq. rewrite star_neutral_l.
  assumption.
Qed.

Ltac xret_inst_credits_zero :=
  apply xret_refine_nat; [ reflexivity | ].

Ltac xret_pre cont1 cont2 ::=
  xpull_check_not_needed tt;
  match cfml_get_tag tt with
  | tag_ret => xret_inst_credits_zero; cont1 tt
  | tag_let => xlet; [ xret_inst_credits_zero; cont1 tt | instantiate; cont2 tt ]
  end.

Lemma spec_cost_is_constant :
  forall A (F : ~~A) B (x : B) (costf: B -> Z) (cost : nat) H (Q : A -> hprop),
    (PRE \$ Z.of_nat cost \* H
     POST Q
     CODE F) ->
    (Z.of_nat cost = costf x) ->
    (PRE \$costf x \* H
     POST Q
     CODE F).
Proof.
  introv HF E. rewrite <-E. apply HF.
Qed.


Definition to_nat' : forall (x : Z), 0 <= x -> nat.
Proof.
  intros x Px.
  exact (Z.to_nat x).
Defined.

Arguments to_nat' : clear implicits.

Lemma Z2Nat_id' : forall (x : int) Px, Z.of_nat (to_nat' x Px) = x.
Proof.
  intros x Px.
  unfold to_nat'.
  apply Z2Nat.id.
  exact Px.
Qed.

(* todo: notation for to_nat' in order to hide the proof term *)

Lemma let1_spec :
  exists (cost : Z -> Z),
  (forall n,
   0 <= n ->
   app let1 [n]
     PRE (\$ cost n \* \[])
     POST (fun (tt:unit) => \[])) /\
  (forall x, 0 <= cost x) /\
  dominated Z_filterType cost (fun (n:Z) => n).
Proof.
  destruct loop1_spec_2 as (loop1_cost & L & LP & LD).
  eexists. splits. intros n N.

  eapply spec_cost_is_constant.

  xcf.
  xpay.

  xlet.
  { xseq. xapp. instantiate (2 := 1%nat). instantiate (1 := \[]). admit.
    xret. }

  xpull. intro Hm.

  xapp. math.

  hsimpl_credits.
  { assert (LL: forall a b, b = a -> ge a b). admit. apply LL. clear LL.
    subst m.

    Lemma inst_nat :
      forall (a : Z) (n : nat) (Pa : 0 <= a),
        (n = to_nat' a Pa) ->
        (a = Z.of_nat n).
    Proof. introv E. rewrite E. rewrite Z2Nat_id'; auto. Qed.

    unshelve eapply inst_nat. apply LP. reflexivity.
  }
  { (* ... *) specializes LP m. math. }

  match goal with
    |- _ = ?rhs =>
    let hide_cost := fresh in
    set (hide_cost := rhs);
    repeat rewrite Nat2Z.inj_add;
    repeat rewrite Z2Nat_id';
    simpl;
    ring_simplify;
    subst hide_cost
  end.

  reflexivity.

  { intros x. simpl. specializes LP (x + 1). math. }
  { apply dominated_sum_distr.
    { apply dominated_transitive with loop1_cost.
      - admit.
      - apply LD. }
    admit. }
Qed.

(*
  assert (LL: forall y (cost : Z -> Z), cost n = loop1_cost y -> forall H: (forall n, 0 <= cost n), \$ make_cost_fun cost H n ==> \GC \* \$ loop1_cost y).
  { introv E. intro H. simpl. rewrite E. hsimpl. }
  unshelve apply LL; [ shelve | ..]; swap 1 2.
  rewrite Hy.
*)


(*
  assert (LL: forall (x y : int) cost cost' H, \$ cost' (x, y) ==> H -> cost x = cost' (x, y) -> \$ cost x ==> H).
  { introv H1 H2. auto. rewrite H2. auto. }
  eapply LL with (y := y).

  rewrite Hy.
*)


(*
Parameter N_ : Type.
Parameter ω : N_.
Parameter inj : N -> N_.
Parameter le_ : N_ -> N_ -> Prop.

Goal
  forall (P : N_ -> Prop),
    (forall x : N_, (forall n : N, le_ (inj n) x) -> P x) ->
    (exists (n0 : N_), forall (n : N_), le_ n0 n -> P n).
intro P.

intros H.
exists ω.
intros ω' Hω'.
apply H.
intros n.
(* ok *) admit.
Qed.
*)


Lemma xfor_inv_lemma_pred_credits' : forall A (I:int->hprop) (cost : cost_fun A) (cost' : cost_fun (Z * A)),
  forall (x: A) (a:int) (b:int) (F:int->~~unit) H H',
  (a <= b) ->
  (forall i, a <= i < b -> F i (\$ cost' (i, x) \* I i) (# I(i+1))) ->
  (cost x = cumul (fun i => cost' (i, x)) a b) ->
  (H ==> I a \* H') ->
  (forall i, is_local (F i)) ->
  (For i = a To (b - 1) Do F i Done_) (\$ cost x \* H) (# I b \* H').
Proof.
  introv a_le_b HI Hcost HH Flocal.
  applys xfor_inv_case_lemma (fun (i: int) => \$ cumul (fun i => cost' (i, x)) i b \* I i); intros C.
  { exists H'. splits~.
    - hchange HH. rewrite Hcost. hsimpl.
    - intros i Hi.
      (* xframe (\$cumul f (i + 1) n). auto. *) (* ?? *)
      xframe_but (\$cost' (i, x) \* I i). auto.
      assert (forall f, cumul f i b = f i + cumul f (i + 1) b) as cumul_lemma by admit.
      rewrite cumul_lemma; clear cumul_lemma.
      credits_split. hsimpl. forwards~: cost_nonneg cost' (i, x).
      admit. (* cumul cost' >= 0 *)
      applys HI. math.
      xsimpl_credits.
    - math_rewrite ((b - 1) + 1 = b). hsimpl. }
  { xchange HH. math_rewrite (a = b). xsimpl. }
Qed.

Lemma loop1_spec_1 :
  forall (n: int),
  0 <= n ->
  appO_ loop1 [n]
    Z_filterType (fun n => n) n
    \[]
    (fun (tt:unit) => \[]).
Proof.
  intros n Hn.
  eexists. split.
  xcf.
  xpay.
  xfor_pre_ensure_evar_post ltac:(fun _ => eapply (xfor_inv_lemma_pred_credits' (fun _ => \[]))).
  - auto.
  - intros i Hi.
    xseq. xapp. hsimpl. xapp. hsimpl.
  - simpl. admit.
  - hsimpl.
  - intros. xlocal.
  - hsimpl.
  - dominated_rew_cost. admit.
    Unshelve. admit.
Admitted.



(*
  xpay => xpay+hsimpl si$1 visible   OR  xpay_add_credits_1  OR  xpay_avec_soustraction
        xapp
                 $(cost_rest)
           consume $m
         $(cost_rest) ==> $m + $?r

      $cost_rest \* H ==> H1 \* H2

    add_credits m cost_rest
       $(m + cost_rest') ==> $m + $?r

    forall cost_rest',
    (forall x, cost_rest x = m + cost_rest' x) ->
    $cost_rest x ==> $m + $cost_rest'
*)

(*
Lemma loop1_spec_bis :
  forall (n: int),
  0 <= n ->
  exists (cost: int -> int),
  app loop1 [n]
    PRE (\$ cost n)
    POST (fun (tt:unit) => \[]) /\
  dominated Z_filterType cost (fun (n:Z) => n).
Proof.
  intros.
  (* pose_big P Prop. cut P. intro HP. *)
  pose_ t. cut t. intro Ht.

  exists_big_fun cost int int; try split; swap 2 3.
  xcf.
  xpay. { xsimpl_credits. apply le_implies_ge. tlc_big. math. }

  match goal with |- ?e ?H ?Q =>
    add_witness_to t { cost' : int -> int |
                       e (\$ cost' n) Q /\
                       dominated Z_filterType cost' (fun (n:int) => n) /\
                       (forall x, 0 <= cost' x) }
  end.

  pose (cost' := proj1_sig (fst Ht)).
  pose (S := proj1 (proj2_sig (fst Ht))).
  pose (D := proj1 (proj2 (proj2_sig (fst Ht)))).
  pose (Pos := proj2 (proj2 (proj2_sig (fst Ht)))).

  xapply S. xsimpl_credits.
  { match goal with |- ge (?a - 1)%I ?b => cut (b + 1 <= a) end. admit. big. }
  { apply le_implies_ge. apply Pos. }
  hsimpl.
  close.

  simpl in cost.
  close_ t. subst t. destruct Ht as [? ?]. destruct s as (cost' & S & D & Pos).
  simpl in cost.
  subst cost.
  apply dominated_max_distr. admit.
  apply dominated_max_distr; [| admit].
  apply dominated_sum_distr. apply D. admit.

  subst t. split; [| apply tt]. exists_big_fun cost' Z Z. splits.


  exists_big_fun cost' int int; repeat split; swap 2 4.

  pose_big_fun f int int.
  xfor_inv_credits (fun (i: int) => \[]) f.
  - math.
  - intros i Hi. xapp. xsimpl_credits. apply le_implies_ge. tlc_big. math.
    xapp. xsimpl_credits. cut (2 <= f i); [math|]. tlc_big. math.
  - xsimpl_credits.
    apply le_implies_ge. tlc_big.
    apply le_implies_ge. apply cumul_pos. intro. tlc_big.
  - intros. tlc_big.
  - xsimpl_credits.
  - close.
  - close.
  - simpl in cost'; subst cost'. simpl. intros. math_lia.
  - simpl in cost'. subst cost'.
    apply dominated_max; [|admit].
    rewrite dominated_big_sum_bound.
    { simpl. admit. }
    { apply filter_universe_alt. intros _. math_lia. }
    { admit. }

  - forwards Hcost'': indefinite_description Hcost'. clear Hcost'.
    forwards (S & D & P): proj2_sig Hcost''.
    xapply S; [| hsimpl].
    xsimpl_credits.
    match goal with |- (?a - 1)%I >= ?b => cut (b + 1 <= a) end.
    { generalize (proj1_sig Hcost''). math. }


    autorewrite with rew_maths rew_int_comp rew_nat_comp.

    specializes P n. math.

  - close.
  - Check indefinite_description.



Qed.
*)

(*
Lemma maxsum_iter_spec :
  forall (a: array int) (l: list int),
  exists (cost: int -> int),
  app maxsum_iter [a]
    PRE (a ~> Array l \* \$ (cost (length l)))
    POST (fun (i:int) => \[]).
Proof.
  exists_big_fun cost int int.
  xcf.
  xpay. { xsimpl_credits. cut (1 <= cost (length l)); [math|].
          autorewrite with rew_maths rew_int_comp. (* hmm *)
          big. math. }
  xapp. xapp as a_len. intros Hlen.
  xfor_inv_credits (fun (i: int) => Hexists (mx: int), a ~> Array l \* m ~~> mx).
  { math. }
  { intros i Hi. xpull. intros mx. xapps.
    xfor_inv_credits (fun (j: int) => Hexists (mx: int), a ~> Array l \* m ~~> mx).
    { math. }
    { intros j Hj. xpull. clear mx. intros mx. xapps.
      xfor_inv_credits (fun (k: int) => Hexists (mx sumx: int),
                          a ~> Array l \* m ~~> mx \* sum ~~> sumx).
      { math. }
      { intros k Hk. xpull. clear mx. intros mx sumx.
        xapp. { rewrite index_bounds. math. }
        intro. xapp. intros; subst.
        xapp. }
      { xsimpl_credits. apply le_implies_ge.
        autorewrite with rew_maths rew_int_comp. big.
        assert (lemma: forall f, (forall x, 0 <= f x) -> cumul f i j >= 0) by admit.
        apply lemma. intro. autorewrite with rew_maths rew_int_comp. big. }
      { intros. xlocal. }
      { intros. simpl. autorewrite with rew_maths rew_int_comp. big. }
      { clear mx. intros mx sumx.
        xapp. intros; subst.
        xapp. intros; subst.
        xapp. } }
    xsimpl_credits.
    { apply le_implies_ge.
      autorewrite with rew_maths rew_int_comp. big. }
    { assert (lemma: forall f i j, (forall x, 0 <= f x) -> cumul f i j >= 0) by admit.
      apply lemma. intro.
      autorewrite with rew_maths rew_int_comp. big. }
    { intros. xlocal. }
    { intros.
      autorewrite with rew_maths rew_int_comp. big. }
    simpl.
    xsimpl_credits. }
  xsimpl_credits.




  { intros i Hi. xpull. intros mx. xapps.
    xfor_inv (fun (j: int) => Hexists (mx: int), a ~> Array l \* m ~~> mx).
    { math. } { hsimpl. }
    { intros j Hj. xpull. clear mx. intro mx. xapps.
      xfor_inv (fun (k: int) => Hexists (mx sumx: int),
                  a ~> Array l \* m ~~> mx \* sum ~~> sumx).
      { math. } { hsimpl. }
      { intros k Hk. xpull. clear mx. intros mx sumx.
        xapp. { rewrite index_bounds. math. }
        intro. xapp. intros; subst.
        xapp. }
      { clear mx. intros mx sumx.
        xapp. intros; subst.
        xapp. intros; subst.
        xapp. } }
    hsimpl. }
  { intros mx. xapp. }
Qed.
*)

(*
Lemma maxsum_iter_spec :
  forall (a: array int) (l: list int),
  exists (cost: int -> int),
  app maxsum_iter [a]
    PRE (a ~> Array l \* \$ (cost (length l)))
    POST (fun (i:int) => \[]).
Proof.
  exists_big_fun cost int int.
  xcf.
  xpay. { xsimpl_credits. cut (1 <= cost (length l)); [math|].
          autorewrite with rew_maths rew_int_comp. (* hmm *)
          big. math. }
  xapp. xapp as a_len. intros Hlen.
  xfor_inv_credits (fun (i: int) => Hexists (mx: int), a ~> Array l \* m ~~> mx).
  { math. } { xsimpl_credits. }
  { intros i Hi. xpull. intros mx. xapps.
    xfor_inv (fun (j: int) => Hexists (mx: int), a ~> Array l \* m ~~> mx).
    { math. } { hsimpl. }
    { intros j Hj. xpull. clear mx. intro mx. xapps.
      xfor_inv (fun (k: int) => Hexists (mx sumx: int),
                  a ~> Array l \* m ~~> mx \* sum ~~> sumx).
      { math. } { hsimpl. }
      { intros k Hk. xpull. clear mx. intros mx sumx.
        xapp. { rewrite index_bounds. math. }
        intro. xapp. intros; subst.
        xapp. }
      { clear mx. intros mx sumx.
        xapp. intros; subst.
        xapp. intros; subst.
        xapp. } }
    hsimpl. }
  { intros mx. xapp. }
Qed.
*)