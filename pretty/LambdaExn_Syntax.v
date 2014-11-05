(************************************************************
* Lambda-calculus with exceptions,                          *
* Syntax                                                    *
*************************************************************)

Set Implicit Arguments.
Require Export Common.

(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Syntax *)

(** Grammar of values and terms *)

Inductive val : Type :=
  | val_int : int -> val
  | val_clo : var -> trm -> val
  | val_err : val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_abs : var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_try : trm -> trm -> trm
  | trm_raise : trm -> trm
  | trm_rand : trm.

Coercion trm_val : val >-> trm.

(** Substitution *)

Fixpoint subst (x:var) (v:val) (t:trm) : trm :=
  let s := subst x v in
  match t with
  | trm_val v => t
  | trm_var y => If x = y then trm_val v else t
  | trm_abs y t3 => trm_abs y (If x = y then t3 else s t3)
  | trm_app t1 t2 => trm_app (s t1) (s t2)  
  | trm_try t1 t2 => trm_try (s t1) (s t2) 
  | trm_raise t1 => trm_raise (s t1)
  | trm_rand => t 
  end.


(************************************************************)
(* ** Definition shared by the semantics *)

(** If [ParamDeterministic], then [rand] always reduces to zero,
    otherwise it non-deterministically reduces to any number *)

Parameter ParamDeterministic : Prop.

(** Assuming a deterministic semantics *)

Module AssumeDeterministic.
Parameter Deterministic : ParamDeterministic = True.
End AssumeDeterministic.


(** Grammar of behaviors without errors *)

Module BehaviorsWithoutErrors.

Inductive beh :=
  | beh_ret : val -> beh
  | beh_exn : val -> beh.
  
Coercion beh_ret : val >-> beh.

End BehaviorsWithoutErrors.


(** Grammar of behaviors, including errors *)

Module BehaviorsWithErrors.

Inductive beh :=
  | beh_ret : val -> beh
  | beh_exn : val -> beh
  | beh_err : beh.
  
Coercion beh_ret : val >-> beh.

End BehaviorsWithErrors.

