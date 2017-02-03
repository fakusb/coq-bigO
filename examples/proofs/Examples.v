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

(* + cas où f ne dépend pas de i *)
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
  forall (n: int),
  0 <= n ->
  exists (cost: int -> int),
  app loop1 [n]
    PRE (\$ cost n)
    POST (fun (tt:unit) => \[]) /\
  dominated Z_filterType cost (fun (n:Z) => n).
Proof.
  intros.
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

Lemma tick3_spec_3 :
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
  xpay. credits_split. hsimpl. math. apply le_implies_ge. apply Hcost.

(*
  xapp. {
    add_credits 1 cost. simpl.

    let E := get_evar_in cost in evar (Hcost' : forall x, 0 <= E x).
    credits_split.
    { hsimpl_credits. }
    { math. }
    { apply le_implies_ge. apply Hcost'. }
  }

  Unshelve.
*)

  evar (foo_t : Type).
  evar (foo : foo_t).

  xapp. {
    hsimpl_setup tt. hsimpl_step tt. eapply hsimpl_cancel_credits_int_alt.
    reflexivity. math. simpl in *.

    let E := get_evar_in cost in evar (Hcost' : forall x, 0 <= E x).

    let H' := get_body Hcost' in
    let T := type of H' in
    unify foo_t T.

    let H' := get_body Hcost' in
    unify H' foo.

    apply Hcost'. hsimpl_credits.
  }

  subst foo_t. simpl in *.
  prove_Hcost_with foo cost Hcost. math.
  rename foo into Hcost.

  admit_evar Hcost.
  admit. admit.
  Unshelve. exact (fun (_:unit) => 0).
Qed.

(*
  let P := cfml_get_precondition tt in
  match P with context [\$ ?X _] => pose X end. *)
(* hsimpl_cancel_credits_int
  n >= m
  m>= 0
  $(n -m ) * HT => HA
  $n * HT ==> HA * $m

  0 <= m  ->
  0 <= rest x ->
  (forall x, n x = m + rest x) ->
  $(n x) * HT ==> HA * $m
*)

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