(************************************************************
* Lambda-calculus,                                          *
* Pretty-big-step semantics with error rule                 *
*************************************************************)

Set Implicit Arguments.
Require Export Lambda_PrettyErr LibInt.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Grammar of outcomes, with an explicit error behavior *)

Inductive beh :=
  | beh_ret : val -> beh
  | beh_err : beh.

Coercion beh_ret : val >-> beh.
Implicit Types b : beh.

Inductive out :=
  | out_ter : nat -> beh -> out
  | out_div : out.

Implicit Types o : out.

(** Partial order on the outcomes *)

Implicit Types n : nat.

Inductive faster : binary out :=
  | faster_ter : forall n n' r r',
      n < n' ->
      faster (out_ter n r) (out_ter n' r')
  | faster_div : forall o,
      faster o out_div.

Inductive before : binary out :=
  | before_ter : forall n n' r,
      n < n' ->
      before (out_ter n r) (out_ter n' r)
  | before_div : 
      before out_div out_div.

Definition faster_before o1 o2 o :=
  before o2 o /\ faster o1 o.

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

(** "One rule applies" judgment *)

Inductive one : ext -> Prop :=
  | one_val : forall v,
      one v 
  | one_abs : forall x t,
      one (trm_abs x t) 
  | one_app : forall t1 t2,
      one (trm_app t1 t2) 
  | one_app_1_abort : forall t2,
      one (ext_app_1 out_div t2)
  | one_app_1 : forall n v1 t2,
      one (ext_app_1 (out_ter n v1) t2) 
  | one_app_2_abort : forall v1,
      one (ext_app_2 v1 out_div) 
  | one_app_2 : forall n x t3 v2,
      one (ext_app_2 (val_clo x t3) (out_ter n v2)).

(** Combined evaluation *)

CoInductive cred : ext -> out -> Prop :=
  | cred_val : forall n v,
      cred v (out_ter n v)
  | cred_abs : forall n x t,
      cred (trm_abs x t) (out_ter n (val_clo x t))
  | cred_app : forall o t1 t2 o1 o2,
      cred t1 o1 -> 
      cred (ext_app_1 o1 t2) o2 -> 
      faster_before o1 o2 o ->
      cred (trm_app t1 t2) o
  | cred_app_1_abort : forall t2,
      cred (ext_app_1 out_div t2) out_div
  | cred_app_1 : forall o n v1 t2 o2 o3,
      cred t2 o2 -> 
      cred (ext_app_2 v1 o2) o3 -> 
      faster_before o2 o3 o ->
      cred (ext_app_1 (out_ter n v1) t2) o
  | cred_app_2_abort : forall v1,
      cred (ext_app_2 v1 out_div) out_div
  | cred_app_2 : forall o n x t3 v2 o3,
      cred (subst x v2 t3) o3 -> 
      before o3 o ->
      cred (ext_app_2 (val_clo x t3) (out_ter n v2)) o
  | cred_err : forall n e,
      ~ one e ->
      cred e (out_ter n beh_err).

(** Main semantics judgments *)

Definition credval e v := exists n, cred e (out_ter n v).

Definition cdiverge e := cred e out_div.

Definition cstuck e := exists n, cred e (out_ter n beh_err).

