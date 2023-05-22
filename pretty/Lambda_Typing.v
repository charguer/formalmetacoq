(************************************************************
* Lambda-calculus,                                          *
* Simple typing                                             *
*************************************************************)

Set Implicit Arguments.
Require Import Lambda_Syntax.
From TLC Require Import LibLN LibInt.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

Notation "x ~~ a" := (single x a)
  (at level 27, left associativity) : env_scope.

(************************************************************)
(* ** Grammar of simple types *)

CoInductive typ :=
  | typ_int : typ
  | typ_arrow : typ -> typ -> typ.


(************************************************************)
(* ** Typing judgment *)

Inductive typing : env typ -> trm -> typ -> Prop :=
  | typing_int : forall E k,
      ok E ->
      typing E (val_int k) typ_int
  | typing_clo : forall E x T1 T2 t1,
      ok E ->
      typing (empty & x ~~ T1) t1 T2 ->
      typing E (val_clo x t1) (typ_arrow T1 T2)
  | typing_var : forall E x T,
      ok E ->
      binds x T E ->
      typing E (trm_var x) T
  | typing_abs : forall x E U T t1,
      typing (E & x ~~ U) t1 T ->
      typing E (trm_abs x t1) (typ_arrow U T)
  | typing_app : forall T1 T2 E t1 t2,
      typing E t1 (typ_arrow T1 T2) ->
      typing E t2 T1 ->
      typing E (trm_app t1 t2) T2.
