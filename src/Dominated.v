Require Import Coq.Logic.Classical_Pred_Type.
Require Import ZArith.
Local Open Scope Z_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Filter.

(* ---------------------------------------------------------------------------- *)

(* If we have a filter on [A] and a norm on [B], then we can define a domination
   relation between functions of type [A -> B]. *)

(* [dominated f g] holds if and only if, for some constant [c], [f x] is
   ultimately bounded (in norm) by [c * g x]. We explicitly require [c] to
   be nonnegative, because this seems more convenient.
*)

Section Domination.

Variable A : filterType.

Definition dominated (f g : A -> Z) :=
  exists c, (0 <= c) /\ ultimately A (fun x => Z.abs (f x) <= c * Z.abs (g x)).

(* This notion is analogous to [is_domin] in Coquelicot. *)

End Domination.

Arguments dominated : clear implicits.
