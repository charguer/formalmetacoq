(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Small-step semantics                                      *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_Syntax.
From TLC Require Import LibRelation.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Reduction contexts *)

(** Grammar of contexts *)

Inductive ctx :=
  | ctx_hole : ctx
  | ctx_app_1 : ctx -> trm -> ctx
  | ctx_app_2 : val -> ctx -> ctx
  | ctx_case : ctx -> trm -> trm -> ctx
  | ctx_inj : bool -> ctx -> ctx
  | ctx_try : ctx -> trm -> ctx
  | ctx_raise : ctx -> ctx.

Implicit Types c : ctx.

(** Application of contexts *)

Fixpoint ctx_apply c t :=
  let r c' := ctx_apply c' t in
  match c with
  | ctx_hole => t
  | ctx_app_1 c' t2 => trm_app (r c') t2
  | ctx_app_2 v1 c' => trm_app v1 (r c')
  | ctx_inj b c' => trm_inj b (r c')
  | ctx_case c' t1 t2 => trm_case (r c') t1 t2
  | ctx_try c' t2 => trm_try (r c') t2
  | ctx_raise c' => trm_raise (r c')
  end.

Coercion ctx_apply : ctx >-> Funclass.

(** Contexts that do not contain [try] construct *)

Fixpoint ctx_notry c :=
  let r := ctx_notry in
  match c with
  | ctx_hole => True
  | ctx_app_1 c' t2 => r c'
  | ctx_app_2 v1 c' => r c'
  | ctx_inj b c' => r c'
  | ctx_case c' t1 t2 => r c'
  | ctx_try c' t2 => False
  | ctx_raise c' => r c'
  end.


(************************************************************)
(* ** Semantics *)

(** Reduction *)

Inductive step : binary trm :=
  | step_ctx : forall c t1 t2,
      step t1 t2 ->
      step (c t1) (c t2)
  | step_exn : forall c v,
      ctx_notry c ->
      step (c (trm_raise v)) (trm_raise v)
  | step_abs : forall x t,
      step (trm_abs x t) (val_abs x t)
  | step_beta : forall x t3 v2,
      step (trm_app (val_abs x t3) v2) (subst x v2 t3)
  | step_try_val : forall v1 t2,
      step (trm_try v1 t2) v1
  | step_try_exn : forall v t2,
      step (trm_try (trm_raise v) t2) (trm_app t2 v)
  | step_inj : forall b v1,
      step (trm_inj b v1) (val_inj b v1)
  | sred_case_true : forall t1 t2 t3 v1,
      step (trm_case (val_inj true v1) t2 t3) (trm_app t2 v1)
  | sred_case_false : forall t1 t2 t3 v1,
      step (trm_case (val_inj false v1) t2 t3) (trm_app t3 v1).

(** Complete evaluation *)

Definition sredstar t t' := (rtclosure step) t t'.

Definition sredplus t t' := (tclosure step) t t'.

Definition sredval t v := sredstar t v.

Definition sdiverge t := (infclosure step) t.

Notation "'stepstar'" := (rtclosure step).
Notation "'stepplus'" := (tclosure step).

