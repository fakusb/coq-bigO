Set Implicit Arguments.
Require Import CFML.CFLib.
Require Import TLC.LibListZ.
Require CFML.Stdlib.Sys_ml.
Require CFML.Stdlib.Array_ml.

(* -------------------------------------------------------------------------- *)

(* Conventions. *)

Implicit Types t : loc.         (* array *)
Implicit Types i ofs len : int. (* index *)

(* -------------------------------------------------------------------------- *)

(* An ad hoc notation for array accesses in OCaml code. For display only. *)

Notation "'App'' t `[ i ]" := (App Array_ml.get t i;)
  (at level 69, t at level 0, no associativity,
   format "'App''  t `[ i ]") : charac.

Notation "'App'' t `[ i ] `<- x" := (App Array_ml.set t i x;)
  (at level 69, t at level 0, no associativity,
   format "'App''  t `[ i ]  `<-  x") : charac.

(* -------------------------------------------------------------------------- *)

(* The model of an imperative array is a sequence, represented as a list. *)

Parameter Array : forall A, list A -> loc -> hprop.
  (* TODO: realize this definition as an iterated star of
     the ownership of single cells, each of which being
     described using heap_is_single. *)

(* -------------------------------------------------------------------------- *)

(* The length of an array is at most [Sys.max_array_length]. This could be
   useful someday if we need to prove that certain integer calculations
   cannot overflow. *)

Parameter bounded_length:
  forall A t (xs : list A),
  t ~> Array xs ==>
  t ~> Array xs \* \[ length xs <= Sys_ml.max_array_length ].

(* -------------------------------------------------------------------------- *)

(* [Array.of_list]. *)

Parameter of_list_spec :
  curried 2%nat Array_ml.of_list /\
  forall A (xs:list A),
  app Array_ml.of_list [xs]
    PRE  (\$ 1)
    POST (fun t => t ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.of_list) => Provide of_list_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.length]. *)

Parameter length_spec :
  curried 1%nat Array_ml.length /\
  forall A (xs:list A) t,
  app Array_ml.length [t]
    PRE (\$ 1 \* t ~> Array xs)
    POST (fun n => t ~> Array xs \* \[n = length xs]).

Hint Extern 1 (RegisterSpec Array_ml.length) => Provide length_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.get]. *)

Parameter get_spec :
  curried 2%nat Array_ml.get /\
  forall A `{Inhab A} (xs:list A) t i,
  index xs i ->
  app Array_ml.get [t i]
    PRE (\$ 1 \* t ~> Array xs)
    POST (fun x => t ~> Array xs \* \[x = xs[i] ]).

Hint Extern 1 (RegisterSpec Array_ml.get) => Provide get_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.set]. *)

Parameter set_spec :
  curried 2%nat Array_ml.set /\
  forall A (xs:list A) t i x,
  index xs i ->
  app Array_ml.set [t i x]
    PRE  (\$ 1 \* t ~> Array xs)
    POST (# t ~> Array (xs[i:=x])).

Hint Extern 1 (RegisterSpec Array_ml.set) => Provide set_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.make]. *)

(* In practice, the parameter [n] of [Array.make] must not exceed the constant
   [Sys.max_array_length]. In the specification, we ignore this aspect, as it
   would pollute the client quite severely, without a clear benefit. If someday
   we decide to make this precondition explicit, then we should guarantee that
   [Sys.max_array_length] is at least [2^22 - 1], as this will help prove that
   it is safe to allocate arrays of known small size. *)

Parameter make_spec :
  curried 2%nat Array_ml.make /\
  forall A n (x:A),
  0 <= n ->
  app Array_ml.make [n x]
    PRE  (\$ (n+1))
    POST (fun t => Hexists xs, t ~> Array xs \* \[xs = make n x]).

Hint Extern 1 (RegisterSpec Array_ml.make) => Provide make_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.init]. *)

(* TEMPORARY clean up: *)

Local Hint Resolve index_length_unfold int_index_prove. (* for array indexing *)

Lemma aaa: forall n, n <= n.
Proof. math. Qed.
Lemma aab: forall n, 0 <= n -> n <> 0 -> 0 < n.
Proof. math. Qed.
Lemma aac: forall i, 1 <= i -> 0 <= i.
Proof. math. Qed.

Local Hint Resolve aaa aab aac.

Lemma singleton_prefix_make:
  forall n A (x : A),
  0 < n ->
  prefix (x :: nil) (make n x).
Proof.
  intros.
  exists (make (n - 1) x).
  rewrite app_cons_one.
  apply* cons_make.
Qed.

Lemma prefix_snoc_write:
  forall A i n x (xs zs : list A),
  prefix xs zs ->
  i = length xs ->
  n = length zs ->
  i < n ->
  prefix (xs & x) zs[i := x].
Proof.
  introv [ ys Hp ] Hxs Hzs ?.
  (* [ys] cannot be empty. *)
  destruct ys as [| y ys ].
  { false. rewrite app_nil_r in Hp. subst xs. math. }
  (* The witness is the tail of [ys], now also named [ys]. *)
  exists ys. subst zs. rewrite* update_app_right_here.
Qed.

Lemma prefix_identity:
  forall A n (xs zs : list A),
  prefix xs zs ->
  n = length xs ->
  n = length zs ->
  xs = zs.
Proof.
  introv [ ys ? ] Hxs Hzs. subst zs. rewrite length_app in Hzs.
  assert (ys = nil). { eapply length_zero_inv. math. }
  subst ys. rewrite app_nil_r. reflexivity.
Qed.

Lemma init_spec :
  forall A (F : list A -> hprop) (n : int) (f : func),
  0 <= n ->
  (forall (i : int) (xs : list A),
      index n i ->
      i = length xs ->
      app f [i] (F xs) (fun x => F (xs & x))) ->
  app Array_ml.init [n f]
      (\$ (n+1) \* F nil)
      (fun t =>
         Hexists xs, t ~> Array xs \* \[n = length xs] \* F xs).
Proof.
Admitted.

Hint Extern 1 (RegisterSpec Array_ml.init) => Provide init_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.copy]. *)

Parameter copy_spec:
  curried 1%nat Array_ml.copy /\
  forall A (xs:list A) t,
  app Array_ml.copy [t]
    INV (\$ (length xs + 1) \* t ~> Array xs)
    POST (fun t' => t' ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.copy) => Provide copy_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.fill]. *)

(*
Parameter fill_spec :
  curried 4%nat Array_ml.fill /\
  forall A `{Inhab A} (xs:list A) t ofs len x,
  0 <= ofs ->
  ofs <= length xs ->
  0 <= len ->
  ofs + len <= length xs ->
  app Array_ml.fill [t ofs len x]
    PRE  (t ~> Array xs)
    POST (# Hexists xs', t ~> Array xs' \*
      \[ length xs' = length xs ] \*
      \[ forall i, ofs <= i < ofs + len -> xs'[i] = x ] \*
      \[ forall i, (i < ofs \/ ofs + len <= i) -> xs'[i] = xs[i] ]
    ).

Hint Extern 1 (RegisterSpec Array_ml.fill) => Provide fill_spec.
*)

(* TEMPORARY todo: define [LibListZ.fill] at the logical level *)

(* -------------------------------------------------------------------------- *)

(* [Array.iter]. *)

(*
Parameter iter_spec :
  curried 2%nat Array_ml.iter /\
  forall A (I : list A -> hprop),
  forall xs f t,
  (
    forall ys x,
    prefix (ys & x) xs ->
    app f [x]
      PRE    (I  ys)
      POST (# I (ys & x))
  ) ->
  app Array_ml.iter [f t]
    PRE  (  t ~> Array xs \* I nil)
    POST (# t ~> Array xs \* I xs ).

Hint Extern 1 (RegisterSpec Array_ml.iter) => Provide iter_spec.
*)

(* TEMPORARY iter: give a stronger spec with "read" access to array *)
(* TEMPORARY give a generic spec to iter-like functions *)

(* -------------------------------------------------------------------------- *)

(* [Array.sub]. *)

(*
Parameter sub_spec :
  curried 3%nat Array_ml.sub /\
  forall A `{Inhab A} (xs:list A) t ofs len,
  0 <= ofs ->
  0 <= len ->
  ofs + len <= length xs ->
  app Array_ml.sub [t ofs len]
    INV (t ~> Array xs)
    POST (fun t' => Hexists xs',
             t' ~> Array xs'
          \* \[length xs' = len]
          \* \[forall i, ofs <= i < len -> xs'[i] = xs[i]]).

Hint Extern 1 (RegisterSpec Array_ml.sub) => Provide sub_spec.
*)

(* TEMPORARY todo: define [LibListZ.sub] at the logical level *)

(* TODO: spec of arrays with credits *)
