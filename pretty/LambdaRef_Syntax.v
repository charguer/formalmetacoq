(************************************************************
* Lambda-calculus with references                           *
* Syntax                                                    *
*************************************************************)

Set Implicit Arguments.
Require Export Common LibHeap.
Notation "x ~~ a" := (single x a)
  (at level 27, left associativity) : env_scope.


(************************************************************)
(* * Definition of the language *)

(** Representation of locations *)

Definition loc := nat.

(** Grammar of values and terms *)

Inductive val : Type :=
  | val_int : int -> val
  | val_clo : env val -> var -> trm -> val
  | val_loc : loc -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_abs : var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_new : trm -> trm
  | trm_get : trm -> trm
  | trm_set : trm -> trm -> trm.

Coercion trm_val : val >-> trm.

(** Contexts (executable) *)

Definition ctx := env val.

(** Memory store (executable) *)

Definition mem := Heap.heap loc val.

