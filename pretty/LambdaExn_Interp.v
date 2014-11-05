(************************************************************
* Lambda-calculus with exceptions                           *
* Definition of an interpreter                              *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExn_Syntax.
Import AssumeDeterministic.
Import BehaviorsWithErrors.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : beh.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Results *)

(** Grammar of results of the interpreter *)

Inductive res :=
  | res_return : beh -> res
  | res_bottom : res.

Coercion res_return : beh >-> res.
Implicit Types r : res.


(************************************************************)
(* ** Monadic operators *)

(** Bind-style operators *)

Definition if_success (r:res) (k:val->res) : res :=
  match r with
  | res_return (beh_ret v) => k v
  | _ => r
  end.

Definition if_fault (r:res) (k:val->res) : res :=
  match r with
  | res_return (beh_exn v) => k v
  | _ => r
  end.

Definition if_isclo (v:val) (k:var->trm->res) : res :=
  match v with
  | val_clo x t => k x t
  | _ => beh_err
  end.


(************************************************************)
(* ** Interpreter *)

(** Definition of the interpreter *)

Fixpoint run (n:nat) (t:trm) : res :=
  match n with 
  | O => res_bottom
  | S m => 
    match t with
    | trm_val v => v
    | trm_abs x t1 => val_clo x t1
    | trm_var x => beh_err
    | trm_app t1 t2 => 
       if_success (run m t1) (fun v1 =>
         if_success (run m t2) (fun v2 =>
            if_isclo v1 (fun x t3 =>
              run m (subst x v2 t3))))
    | trm_try t1 t2 =>
       if_fault (run m t1) (fun v => run m (trm_app t2 v))
    | trm_raise t1 => 
       if_success (run m t1) (fun v1 => beh_exn v1)
    | trm_rand => val_int 0
    end
  end.


