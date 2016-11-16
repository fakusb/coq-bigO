Require Import Coq.Logic.Classical_Pred_Type.
Require Import Relations. (* reflexive, transitive *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Product.

Variable A : Type.
Variable B : Type.

Variable leA : relation A.
Variable leB : relation B.

Definition product (p1 p2 : A * B) :=
  let (a1, b1) := p1 in
  let (a2, b2) := p2 in
  leA a1 a2 /\ leB b1 b2.

Lemma product_reflexive :
  reflexive A leA -> reflexive B leB ->
  reflexive (A * B) product.
Proof.
  intros reA reB [ x y ].
  simpl. split. apply reA. apply reB.
Qed.

Lemma product_transitive :
  transitive A leA -> transitive B leB ->
  transitive (A * B) product.
Proof.
  intros trA trB [ x1 y1 ] [ x2 y2 ] [ x3 y3 ] [ ? ? ] [ ? ? ].
  simpl. split. eapply trA; eauto. eapply trB; eauto.
Qed.

Lemma product_preorder :
  preorder A leA -> preorder B leB ->
  preorder (A * B) product.
Proof.
  intros [ ? ? ] [ ? ? ].
  constructor.
  - apply product_reflexive; eauto.
  - apply product_transitive; eauto.
Qed.

End Product.
