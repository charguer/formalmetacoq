(************************************************************
* Lambda-calculus with exceptions,                          *
* Pretty-big-step semantics                                 *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExn_Syntax.
Export BehaviorsWithErrors.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : beh.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Grammar of outcomes, isomorphic to:
      Inductive out :=
        | out_ret : val -> out
        | out_exn : val -> out
        | out_div : out.  
    *)

Inductive out :=
  | out_beh : beh -> out
  | out_div : out
  | out_err.

Coercion out_beh : beh >-> out.
Implicit Types o : out.
Notation "'out_exn' v" := (out_beh (beh_exn v)) (at level 60).

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext
  | ext_try_1 : out -> trm -> ext
  | ext_raise_1 : out -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

(** Abort behavior *)

Inductive abort : out -> Prop :=
  | abort_exn : forall v, abort (out_exn v)
  | abort_div : abort out_div
  | abort_err : abort out_err.


(** "One rule applies" judgment *)

Inductive one : ext -> Prop :=
  | one_val : forall v,
      one v 
  | one_abs : forall x t,
      one (trm_abs x t) 
  | one_app : forall t1 t2,
      one (trm_app t1 t2) 
  | one_app_1_abort : forall o1 t2,
      abort o1 ->
      one (ext_app_1 o1 t2)
  | one_app_1 : forall v1 t2,
      one (ext_app_1 v1 t2) 
  | one_app_2_abort : forall v1 o2,
      abort o2 ->
      one (ext_app_2 v1 o2) 
  | one_app_2 : forall x t3 v2,
      one (ext_app_2 (val_clo x t3) v2)
  | one_try : forall t1 t2,
      one (trm_try t1 t2)
  | one_try_1_val : forall v1 t2,
      one (ext_try_1 v1 t2) 
  | one_try_1_exn : forall t2 v,
      one (ext_try_1 (out_exn v) t2)
  | one_try_1_div : forall t2,
      one (ext_try_1 out_div t2)
  | one_raise : forall t1,
      one (trm_raise t1)
  | one_raise_1_abort : forall o1,
      abort o1 ->
      one (ext_raise_1 o1) 
  | one_raise_1 : forall v,
      one (ext_raise_1 v).

(** Evaluation judgment *)

Inductive red : ext -> out -> Prop :=
  | red_val : forall v,
      red v v
  | red_abs : forall x t,
      red (trm_abs x t) (val_clo x t)
  | red_app : forall t1 t2 o1 o,
      red t1 o1 ->
      red (ext_app_1 o1 t2) o ->
      red (trm_app t1 t2) o
  | red_app_1_abort : forall o1 t2,
      abort o1 ->
      red (ext_app_1 o1 t2) o1
  | red_app_1 : forall v1 t2 o o2,
      red t2 o2 ->
      red (ext_app_2 v1 o2) o ->
      red (ext_app_1 v1 t2) o
  | red_app_2_abort : forall v1 o2,
      abort o2 ->
      red (ext_app_2 v1 o2) o2
  | red_app_2 : forall x t3 v2 o,
      red (subst x v2 t3) o ->
      red (ext_app_2 (val_clo x t3) v2) o
  | red_try : forall t1 t2 o1 o,
      red t1 o1 ->
      red (ext_try_1 o1 t2) o ->
      red (trm_try t1 t2) o
  | red_try_1_val : forall v1 t2,
      red (ext_try_1 v1 t2) v1
  | red_try_1_exn : forall t2 o v,
      red (trm_app t2 v) o ->
      red (ext_try_1 (out_exn v) t2) o
  | red_try_1_div : forall t2,
      red (ext_try_1 out_div t2) out_div
  | red_raise : forall t1 o1 o,
      red t1 o1 ->
      red (ext_raise_1 o1) o ->
      red (trm_raise t1) o
  | red_raise_1_abort : forall o1,
      abort o1 ->
      red (ext_raise_1 o1) o1
  | red_raise_1 : forall v,
      red (ext_raise_1 v) (out_exn v)
  | red_err : forall e,
      ~ one e ->
      red e out_err.


(** Coevaluation judgment:
    copy-paste of the above definition, 
    simply replacing [red] with [cored] *)

CoInductive cored : ext -> out -> Prop :=
  | cored_val : forall v,
      cored v v
  | cored_abs : forall x t,
      cored (trm_abs x t) (val_clo x t)
  | cored_app : forall t1 t2 o1 o,
      cored t1 o1 ->
      cored (ext_app_1 o1 t2) o ->
      cored (trm_app t1 t2) o
  | cored_app_1_abort : forall o1 t2,
      abort o1 ->
      cored (ext_app_1 o1 t2) o1
  | cored_app_1 : forall v1 t2 o o2,
      cored t2 o2 ->
      cored (ext_app_2 v1 o2) o ->
      cored (ext_app_1 v1 t2) o
  | cored_app_2_abort : forall v1 o2,
      abort o2 ->
      cored (ext_app_2 v1 o2) o2
  | cored_app_2 : forall x t3 v2 o,
      cored (subst x v2 t3) o ->
      cored (ext_app_2 (val_clo x t3) v2) o
  | cored_try : forall t1 t2 o1 o,
      cored t1 o1 ->
      cored (ext_try_1 o1 t2) o ->
      cored (trm_try t1 t2) o
  | cored_try_1_val : forall v1 t2,
      cored (ext_try_1 v1 t2) v1
  | cored_try_1_exn : forall t2 o v,
      cored (trm_app t2 v) o ->
      cored (ext_try_1 (out_exn v) t2) o
  | cored_try_1_div : forall t2,
      cored (ext_try_1 out_div t2) out_div
  | cored_raise : forall t1 o1 o,
      cored t1 o1 ->
      cored (ext_raise_1 o1) o ->
      cored (trm_raise t1) o
  | cored_raise_1_abort : forall o1,
      abort o1 ->
      cored (ext_raise_1 o1) o1
  | cored_raise_1 : forall v,
      cored (ext_raise_1 v) (out_exn v)
  | cored_err : forall e,
      ~ one e ->
      cored e out_err.


(** Definition of divergence *)

Definition diverge e := cored e out_div.

(*==========================================================*)
(* * Typing *)

Notation "x ~~ a" := (single x a)
  (at level 27, left associativity) : env_scope.

(************************************************************)
(* ** Grammar of simple types *)

CoInductive typ :=
  | typ_int : typ
  | typ_arrow : typ -> typ -> typ.


(************************************************************)
(* ** Typing judgment *)

Inductive valtyping :  trm -> typ -> Prop :=
  | valtyping_int : forall k,
      valtyping (val_int k) typ_int
  | valtyping_clo : forall E x T1 T2 t1,
      valtyping (empty & x ~~ T1) t1 T2 ->
      valtyping (val_clo x t1) (typ_arrow T1 T2).

Inductive typing : env typ -> trm -> typ -> Prop :=

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


(*==========================================================*)
(* * Proofs *)


