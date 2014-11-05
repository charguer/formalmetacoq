(************************************************************
* Lambda-calculus,                                          *
* Syntax                                                    *
*************************************************************)

Set Implicit Arguments.
Require Export Common.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Syntax of the language *)

Inductive val : Type :=
  | val_int : int -> val
  | val_clo : var -> trm -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_abs : var -> trm -> trm
  | trm_app : trm -> trm -> trm.

Coercion trm_val : val >-> trm.


(************************************************************)
(* ** Definition of substitution *)

Fixpoint subst (x:var) (v:val) (t:trm) : trm :=
  let s := subst x v in
  match t with
  | trm_val v => t
  | trm_var y => If x = y then trm_val v else t
  | trm_abs y t3 => trm_abs y (If x = y then t3 else s t3)
  | trm_app t1 t2 => trm_app (s t1) (s t2)  
  end.

