Require Import Coq.Logic.Classical_Pred_Type.
Require Import Relations. (* reflexive, transitive *)
Require Import RelationsExtra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module MeetSemiLattice.

Definition axiom A (le : relation A) (meet : A -> A -> A) :=
  forall x y : A, le x (meet x y) /\ le y (meet x y).

Record mixin_of (A : Type) := Mixin {
  inhab : A;
  le : relation A;
  meet : A -> A -> A;
  _ : preorder A le;
  _ : axiom le meet;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.
  Record type : Type := Pack { sort : Type; class : class_of sort }.
End ClassDef.

Module Exports.
  Coercion sort : type >-> Sortclass.
  Notation meetSemiLatticeType := type.
  Notation MeetSemiLatticeMixin := Mixin.
  Notation MeetSemiLatticeType T m := (@Pack T m).
End Exports.

End MeetSemiLattice.
Export MeetSemiLattice.Exports.

Definition inhab T := MeetSemiLattice.inhab (MeetSemiLattice.class T).
Definition le T := MeetSemiLattice.le (MeetSemiLattice.class T).
Definition meet T := MeetSemiLattice.meet (MeetSemiLattice.class T).
Arguments inhab : clear implicits.
Arguments le : clear implicits.
Arguments meet : clear implicits.

(* ---------------------------------------------------------------------------- *)

Section Laws.

Variable A : meetSemiLatticeType.

Lemma meetSemiLattice_preorder :
  preorder A (le A).
Proof. destruct A as [? M]. destruct M. eauto. Qed.

Lemma meetSemiLatticeP :
  forall x y, le A x (meet A x y) /\ le A y (meet A x y).
Proof. destruct A as [? M]. destruct M. eauto. Qed.

End Laws.

(* ---------------------------------------------------------------------------- *)

Section ProductMeetSemiLattice.

Variable A : meetSemiLatticeType.
Variable B : meetSemiLatticeType.

Definition product_meet (p1 : A * B) (p2 : A * B) :=
  let (a1, b1) := p1 in
  let (a2, b2) := p2 in
  (meet A a1 a2, meet B b1 b2).

Lemma product_meetP :
  forall x y,
    product (le A) (le B) x (product_meet x y) /\
    product (le A) (le B) y (product_meet x y).
Proof.
  intros [x1 y1] [x2 y2]. unfold product. simpl.
  repeat split; apply meetSemiLatticeP.
Qed.

Definition product_meetSemiLatticeMixin :=
  MeetSemiLatticeMixin
    (inhab A, inhab B)
    (product_preorder (meetSemiLattice_preorder A) (meetSemiLattice_preorder B))
    product_meetP.

Definition product_meetSemiLatticeType :=
  MeetSemiLatticeType (A * B) product_meetSemiLatticeMixin.

End ProductMeetSemiLattice.
