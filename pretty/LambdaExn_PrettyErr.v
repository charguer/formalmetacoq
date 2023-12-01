(************************************************************
* Lambda-calculus with exceptions,                          *
* Pretty-big-step semantics                                 *
*************************************************************)

Set Implicit Arguments.
Require Export Common.

(************************************************************)
(* ** Syntax *)

Inductive trm : Type :=
  | trm_var : var -> trm
  | trm_abs : var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_try : trm -> var -> trm -> trm
  | trm_raise : trm -> trm.

(** Grammar of values and terms *)

Inductive val : Type :=
  | val_int : int -> val
  | val_clo : env val -> var -> trm -> val
  | val_err : val.

Definition stack := env val.

Inductive beh :=
  | beh_ret : val -> beh
  | beh_exn : val -> beh
  | beh_err : beh.

Coercion beh_ret : val >-> beh.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : beh.

(*==========================================================*)
(* * Definitions *)

Notation "x ~~ a" := (single x a)
  (at level 27, left associativity) : env_scope.


(************************************************************)
(* ** Semantics *)

Implicit Types s : stack.

(** Grammar of outcomes, isomorphic to:
      Inductive out :=
        | out_ret : val -> out
        | out_exn : val -> out
        | out_div : out.
    *)

Inductive out :=
  | out_beh : beh -> out
  | out_div : out.

Coercion out_beh : beh >-> out.
Implicit Types o : out.
Notation "'out_exn' v" := (out_beh (beh_exn v)) (at level 60).
Notation "'out_err'" := (out_beh (beh_err)) (at level 0).

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext
  | ext_try_1 : out -> var -> trm -> ext
  | ext_raise_1 : out -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

(** Abort behavior *)

Inductive abort : out -> Prop :=
  | abort_exn : forall v, abort (out_exn v)
  | abort_div : abort out_div
  | abort_err : abort out_err.

(** "One rule applies" judgment *)

Inductive one : stack -> ext -> Prop :=
  | one_var : forall s x v,
      binds x v s ->
      one s (trm_var x)
  | one_abs : forall s x t,
      one s (trm_abs x t)
  | one_app : forall s t1 t2,
      one s (trm_app t1 t2)
  | one_app_1_abort : forall s o1 t2,
      abort o1 ->
      one s (ext_app_1 o1 t2)
  | one_app_1 : forall s v1 t2,
      one s (ext_app_1 v1 t2)
  | one_app_2_abort : forall s v1 o2,
      abort o2 ->
      one s (ext_app_2 v1 o2)
  | one_app_2 : forall s' s x t3 v2,
      one s' (ext_app_2 (val_clo s x t3) v2)
  | one_try : forall s t1 x t2,
      one s (trm_try t1 x t2)
  | one_try_1_val : forall s v1 x t2,
      one s (ext_try_1 v1 x t2)
  | one_try_1_exn : forall s x t2 v,
      one s (ext_try_1 (out_exn v) x t2)
  | one_try_1_div : forall s x t2,
      one s (ext_try_1 out_div x t2)
  | one_raise : forall s t1,
      one s (trm_raise t1)
  | one_raise_1_abort : forall s o1,
      abort o1 ->
      one s (ext_raise_1 o1)
  | one_raise_1 : forall s v,
      one s (ext_raise_1 v).

(** Evaluation judgment *)

Inductive red : stack -> ext -> out -> Prop :=
  | red_var : forall s x v,
      binds x v s ->
      red s (trm_var x) v
  | red_abs : forall s x t,
      red s (trm_abs x t) (val_clo s x t)
  | red_app : forall s t1 t2 o1 o,
      red s t1 o1 ->
      red s (ext_app_1 o1 t2) o ->
      red s (trm_app t1 t2) o
  | red_app_1_abort : forall s o1 t2,
      abort o1 ->
      red s (ext_app_1 o1 t2) o1
  | red_app_1 : forall s v1 t2 o o2,
      red s t2 o2 ->
      red s (ext_app_2 v1 o2) o ->
      red s (ext_app_1 v1 t2) o
  | red_app_2_abort : forall s v1 o2,
      abort o2 ->
      red s (ext_app_2 v1 o2) o2
  | red_app_2 : forall (s s':stack) x t3 v2 o,
      red (s' & x ~~ v2) t3 o ->
      red s (ext_app_2 (val_clo s' x t3) v2) o
  | red_try : forall s t1 x t2 o1 o,
      red s t1 o1 ->
      red s (ext_try_1 o1 x t2) o ->
      red s (trm_try t1 x t2) o
  | red_try_1_val : forall s v1 x t2,
      red s (ext_try_1 v1 x t2) v1
  | red_try_1_exn : forall s t2 o v x,
      red (s & x ~~ v) t2 o ->
      red s (ext_try_1 (out_exn v) x t2) o
  | red_try_1_div : forall s x t2,
      red s (ext_try_1 out_div x t2) out_div
  | red_raise : forall s t1 o1 o,
      red s t1 o1 ->
      red s (ext_raise_1 o1) o ->
      red s (trm_raise t1) o
  | red_raise_1_abort : forall s o1,
      abort o1 ->
      red s (ext_raise_1 o1) o1
  | red_raise_1 : forall s v,
      red s (ext_raise_1 v) (out_exn v)
  | red_err : forall s e,
      ~ one s e ->
      red s e out_err.

(** Coevaluation judgment:
    copy-paste of the above definition,
    simply replacing [red] with [cored] *)

Inductive cored : stack -> ext -> out -> Prop :=
  | cored_var : forall s x v,
      binds x v s ->
      cored s (trm_var x) v
  | cored_abs : forall s x t,
      cored s (trm_abs x t) (val_clo s x t)
  | cored_app : forall s t1 t2 o1 o,
      cored s t1 o1 ->
      cored s (ext_app_1 o1 t2) o ->
      cored s (trm_app t1 t2) o
  | cored_app_1_abort : forall s o1 t2,
      abort o1 ->
      cored s (ext_app_1 o1 t2) o1
  | cored_app_1 : forall s v1 t2 o o2,
      cored s t2 o2 ->
      cored s (ext_app_2 v1 o2) o ->
      cored s (ext_app_1 v1 t2) o
  | cored_app_2_abort : forall s v1 o2,
      abort o2 ->
      cored s (ext_app_2 v1 o2) o2
  | cored_app_2 : forall (s s':stack) x t3 v2 o,
      cored (s' & x ~~ v2) t3 o ->
      cored s (ext_app_2 (val_clo s' x t3) v2) o
  | cored_try : forall s t1 x t2 o1 o,
      cored s t1 o1 ->
      cored s (ext_try_1 o1 x t2) o ->
      cored s (trm_try t1 x t2) o
  | cored_try_1_val : forall s v1 x t2,
      cored s (ext_try_1 v1 x t2) v1
  | cored_try_1_exn : forall s t2 o v x,
      cored (s & x ~~ v) t2 o ->
      cored s (ext_try_1 (out_exn v) x t2) o
  | cored_try_1_div : forall s x t2,
      cored s (ext_try_1 out_div x t2) out_div
  | cored_raise : forall s t1 o1 o,
      cored s t1 o1 ->
      cored s (ext_raise_1 o1) o ->
      cored s (trm_raise t1) o
  | cored_raise_1_abort : forall s o1,
      abort o1 ->
      cored s (ext_raise_1 o1) o1
  | cored_raise_1 : forall s v,
      cored s (ext_raise_1 v) (out_exn v)
  | cored_err : forall s e,
      ~ one s e ->
      cored s e out_err.
