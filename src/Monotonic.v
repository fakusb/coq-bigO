Require Import ZArith.
Require Import Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import TLC.LibTactics.
Require Import TLC.LibOrder.
Require Import LibFunOrd.
Require Import Filter.

(* todo: move *)
Lemma preorder_of_PreOrder A (R : A -> A -> Prop) :
  PreOrder R ->
  preorder R.
Proof.
  intros (HR & HT). constructor.
  - apply HR.
  - intros y x z H1 H2. apply HT with (y := y); assumption.
Qed.

Section General_facts.
Context {A} (leA : A -> A -> Prop) {OA : preorder leA}.
Context {B} (leB : B -> B -> Prop) {OB : preorder leB}.
Context {C} (leC : C -> C -> Prop) {OC : preorder leC}.

Lemma monotonic_id :
  monotonic leA leA (fun (x: A) => x).
Proof. intros a1 a2. auto. Qed.

Lemma monotonic_comp : forall (f : B -> C) (g : A -> B),
  monotonic leB leC f ->
  monotonic leA leB g ->
  monotonic leA leC (fun x => f (g x)).
Proof. introv Hf Hg. intros a1 a2 ?. auto. Qed.

Lemma monotonic_cst : forall b,
  monotonic leA leB (fun (_ : A) => b).
Proof. intros b a1 a2 ?. applys OB. Qed.

Lemma monotonic_after_of_monotonic : forall (f : A -> B),
  monotonic leA leB f ->
  (forall (a : A), monotonic (le_after a leA) leB f).
Proof.
  intros f fmon a.
  intros a1 a2 H. apply fmon. apply H.
Qed.

Lemma monotonic_of_monotonic_after : forall (f : A -> B),
  (forall a, monotonic (le_after a leA) leB f) ->
  monotonic leA leB f.
Proof.
  intros f fmon.
  intros a1 a2 H. eapply fmon.
  splits; try (apply preorder_refl; typeclass); assumption.
Qed.

Lemma monotonic_after_weaken : forall (f : A -> B) (a1 a2 : A),
  leA a1 a2 ->
  monotonic (le_after a1 leA) leB f ->
  monotonic (le_after a2 leA) leB f.
Proof.
  intros f a1 a2 H fmon.
  intros x y Hxy. apply fmon.
  splits; try apply Hxy;
  eapply (preorder_trans a2); first [apply H | apply Hxy].
  Unshelve. typeclass. typeclass.
Qed.

End General_facts.

Lemma ultimately_monotonic_of_monotonic :
  forall (A : filterType) B
         (leA : A -> A -> Prop) (leB : B -> B -> Prop)
         (f : A -> B),
  monotonic leA leB f ->
  ultimately A (fun a => monotonic (le_after a leA) leB f).
Proof.
  introv fmon. applys filter_universe_alt.
  eapply monotonic_after_of_monotonic. apply fmon.
Qed.

Section Z_facts.
Local Open Scope Z.

Context {A} (leA: A -> A -> Prop) {OA: preorder leA}.

Lemma monotonic_sum : forall (f g : A -> Z),
  monotonic leA Z.le f ->
  monotonic leA Z.le g ->
  monotonic leA Z.le (fun x => f x + g x).
Proof.
  introv Hf Hg. intros a1 a2 ?.
  forwards~: Hf a1 a2. forwards~: Hg a1 a2. lia.
Qed.

Lemma monotonic_max : forall (f g : A -> Z),
  monotonic leA Z.le f ->
  monotonic leA Z.le g ->
  monotonic leA Z.le (fun x => Z.max (f x) (g x)).
Proof.
  introv Hf Hg. intros a1 a2 ?.
  forwards~: Hf a1 a2. forwards~: Hg a1 a2. lia.
Qed.

Lemma monotonic_mul : forall (f g : A -> Z),
  (forall x, 0 <= f x) ->
  (forall x, 0 <= g x) ->
  monotonic leA Z.le f ->
  monotonic leA Z.le g ->
  monotonic leA Z.le (fun x => f x * g x).
Proof.
  introv Pf Pg Hf Hg. intros a1 a2 ?.
  forwards~: Pf a1. forwards~: Pf a2. forwards~: Pg a1. forwards~: Pg a2.
  forwards~: Hf a1 a2. forwards~: Hg a1 a2. nia.
Qed.

Lemma monotonic_mul_cst_l : forall (f : A -> Z) (c : Z),
  0 <= c ->
  monotonic leA Z.le f ->
  monotonic leA Z.le (fun x => c * f x).
Proof.
  introv cpos Hf. intros a1 a2 H.
  forwards~: Hf a1 a2. nia.
Qed.

Lemma monotonic_mul_cst_r : forall (f : A -> Z) (c : Z),
  0 <= c ->
  monotonic leA Z.le f ->
  monotonic leA Z.le (fun x => f x * c).
Proof.
  introv cpos Hf.
  intros a1 a2 H. forwards~: Hf a1 a2. nia.
Qed.

Lemma monotonic_log2 : monotonic Z.le Z.le Z.log2.
Proof.
  intros a1 a2 H. apply~ Z.log2_le_mono.
Qed.

Lemma monotonic_pow_l : forall e,
  monotonic (le_after 0 Z.le) Z.le (fun b => b ^ e).
Proof.
  intros e a1 a2 H. apply~ Z.pow_le_mono_l. splits; apply H.
Qed.

Lemma monotonic_pow_r : forall b,
  0 < b ->
  monotonic Z.le Z.le (Z.pow b).
Proof.
  intros b a1 a2 H. apply~ Z.pow_le_mono_r.
Qed.

End Z_facts.

Section Ultimately_Z_facts.
Local Open Scope Z.

Lemma ultimately_monotonic_mul :
  forall (A : filterType) (leA : A -> A -> Prop)
         {OA: preorder leA}
         (f g : A -> Z),
  ultimately A (fun x => 0 <= f x) ->
  ultimately A (fun x => 0 <= g x) ->
  ultimately A (fun a => monotonic (le_after a leA) Z.le f) ->
  ultimately A (fun a => monotonic (le_after a leA) Z.le g) ->
  ultimately A (fun a => monotonic (le_after a leA) Z.le (fun x => f x * g x)).
Proof.
  introv OA. introv. filter_closed_under_intersection.
  introv (Pf & Pg & Hf & Hg). intros a1 a2 (a_le_a1 & a_le_a2 & a1_le_a2).
  forwards~: Hf a a1; forwards~: Hg a a1;
  forwards~: Hf a1 a2; forwards~: Hg a1 a2;
  try (splits; first [apply OA | assumption]).
  nia.
Qed.

End Ultimately_Z_facts.

(******************************************************************************)
(* Add lemmas to a [monotonic] hint base. *)

Hint Resolve monotonic_cst : monotonic.
Hint Resolve monotonic_id : monotonic.
Hint Resolve monotonic_sum : monotonic.
Hint Extern 1 (monotonic _ _ (fun _ => Z.sub _ ?y)) =>
  apply monotonic_sum : monotonic.
Hint Extern 1 (monotonic _ _ (Z.sub ?y)) =>
  apply monotonic_sum : monotonic.
Hint Resolve monotonic_max : monotonic.
Hint Resolve monotonic_mul : monotonic.
Hint Resolve monotonic_mul_cst_l : monotonic.
Hint Resolve monotonic_mul_cst_r : monotonic.
Hint Resolve monotonic_log2 : monotonic.
Hint Resolve monotonic_pow_l : monotonic.
Hint Resolve monotonic_pow_r : monotonic.
Hint Extern 1 (monotonic _ _ (fun _ => Z.log2 _)) =>
  apply monotonic_comp with (leB := Z.le);
  [ apply monotonic_log2 | ] : monotonic.
Hint Extern 2 (monotonic _ _ (fun _ => Z.pow ?b _)) =>
  apply monotonic_comp with (leB := Z.le);
  [ apply monotonic_pow_r | ].
Hint Extern 2 (monotonic _ _ (Z.pow ?b)) =>
  apply monotonic_comp with (leB := Z.le);
  [ apply monotonic_pow_r | ].
(* todo: Z.pow _ ?e *)

Hint Extern 1 (monotonic _ _ (fun _ => ?f _)) =>
  match goal with
  | H: monotonic ?le _ f |- _ =>
    apply monotonic_comp with (leB := le); [ apply H | ]
  end : monotonic.

Hint Extern 0 (preorder _) =>
  first [ typeclass
        | apply preorder_of_PreOrder; typeclass ]
  : monotonic.

Hint Extern 100 => try (intros; omega) : monotonic.

Hint Extern 999 (monotonic _ _ _) => shelve : monotonic_fallback.
Hint Extern 999 (preorder _) => shelve : monotonic_fallback.

(******************************************************************************)

(* TODO: make the search depth customisable *)

Ltac monotonic :=
  unshelve (auto 20 with zarith typeclass_instances monotonic monotonic_fallback).

Ltac monotonic_trysolve :=
  auto 20 with zarith typeclass_instances monotonic.

(* TODO: extend monotonic_Z to handle monotonic (le_after ..) .., and ultimately
   (fun a => monotonic (le_after a ..) ..) *)

(* Ltac monotonic_Z_auto_step := *)
(*   match goal with *)
(*   | |- @monotonic _ _ _ _ _ => *)
(*     let a := fresh "a" in *)
(*     apply monotonic_of_monotonic_after; [ *)
(*         eauto; typeclass *)
(*       | intro a; *)
(*         monotonic_after_Z_auto; *)
(*         try apply monotonic_after_of_monotonic ] *)
(*   | |- @monotonic_after _ _ _ _ _ _ => *)
(*     eapply monotonic_after_of_monotonic; eauto *)
(*   | |- context [ @monotonic_after _ _ _ _ _ ] => *)
(*     eapply ultimately_monotonic_of_monotonic; *)
(*     eauto; try typeclass *)
(*   end. *)
