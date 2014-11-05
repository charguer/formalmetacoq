(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Big-step semantics                                        *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_Syntax.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

Inductive beh :=
  | beh_ret : val -> beh
  | beh_exn : val -> beh.
  
Coercion beh_ret : val >-> beh.

(** Reduction *)

Inductive bigred : trm -> beh -> Prop :=
  | bigred_val : forall v,
      bigred v v
  | bigred_abs : forall x t,
      bigred (trm_abs x t) (val_abs x t)
  | bigred_app : forall t1 t2 x t3 v2 o,
      bigred t1 (val_abs x t3) ->
      bigred t2 v2 ->
      bigred (subst x v2 t3) o ->
      bigred (trm_app t1 t2) o
  | bigred_app_exn_1 : forall t1 t2 v,
      bigred t1 (beh_exn v) ->
      bigred (trm_app t1 t2) (beh_exn v)
  | bigred_app_exn_2 : forall t1 t2 v1 v,
      bigred t1 v1 ->
      bigred t2 (beh_exn v) ->
      bigred (trm_app t1 t2) (beh_exn v)
  | bigred_try : forall t1 t2 v1,
      bigred t1 v1 ->
      bigred (trm_try t1 t2) v1
  | bigred_try_1 : forall t1 t2 o2 v,
      bigred t1 (beh_exn v)->
      bigred (trm_app t2 v) o2 ->
      bigred (trm_try t1 t2) o2
  | bigred_raise : forall t1 v1,
      bigred t1 v1 ->
      bigred (trm_raise t1) (beh_exn v1)
  | bigred_raise_exn_1 : forall t1 v,
      bigred t1 (beh_exn v) ->
      bigred (trm_raise t1) (beh_exn v)
  | bigred_inj : forall b t1 v1,
      bigred t1 v1 ->
      bigred (trm_inj b t1) (val_inj b v1)
  | bigred_inj_1 : forall b t1 v,
      bigred t1 (beh_exn v) ->
      bigred (trm_inj b t1) (beh_exn v)
  | bigred_case_true : forall t1 t2 t3 v1 o,
      bigred t1 (val_inj true v1) ->
      bigred (trm_app t2 v1) o -> 
      bigred (trm_case t1 t2 t3) o
  | bigred_case_false : forall t1 t2 t3 v1 o,
      bigred t1 (val_inj false v1) ->
      bigred (trm_app t3 v1) o -> 
      bigred (trm_case t1 t2 t3) o
  | bigred_case_1 : forall t1 t2 t3 v,
      bigred t1 (beh_exn v) ->
      bigred (trm_case t1 t2 t3) (beh_exn v).

(** Divergence *)

CoInductive bigdiv : trm -> Prop :=
  | bigdiv_app_1 : forall t1 t2,
      bigdiv t1 ->
      bigdiv (trm_app t1 t2) 
  | bigdiv_app_2 : forall t1 v1 t2,
      bigred t1 v1 ->
      bigdiv t2 ->
      bigdiv (trm_app t1 t2) 
  | bigdiv_app_3 : forall t1 t2 x t3 v2,
      bigred t1 (val_abs x t3) ->
      bigred t2 v2 ->
      bigdiv (subst x v2 t3) ->
      bigdiv (trm_app t1 t2) 
  | bigdiv_try_1 : forall t1 t2,
      bigdiv t1 ->
      bigdiv (trm_try t1 t2) 
  | bigdiv_try_2 : forall t1 t2 v,
      bigred t1 (beh_exn v) ->
      bigdiv (trm_app t2 v) ->
      bigdiv (trm_try t1 t2)
  | bigdiv_raise_1 : forall t1,
      bigdiv t1 ->
      bigdiv (trm_raise t1)
  | bigdiv_inj_1 : forall b t1,
      bigdiv t1 ->
      bigdiv (trm_inj b t1)
  | bigdiv_case_1 : forall t1 t2 t3,
      bigdiv t1 ->
      bigdiv (trm_case t1 t2 t3) 
  | bigdiv_case_true : forall t1 t2 t3 v1,
      bigred t1 (val_inj true v1) ->
      bigdiv (trm_app t2 v1) -> 
      bigdiv (trm_case t1 t2 t3)
  | bigdiv_case_false : forall t1 t2 t3 v1,
      bigred t1 (val_inj false v1) ->
      bigdiv (trm_app t3 v1) -> 
      bigdiv (trm_case t1 t2 t3).



