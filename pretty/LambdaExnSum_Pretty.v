(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Pretty-big-step semantics                                 *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_Syntax.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Output of an evaluation *)

Inductive out :=
  | out_ret : val -> out
  | out_exn : val -> out
  | out_div : out.

Implicit Types o : out.

Coercion out_ret : val >-> out.

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext
  | ext_inj_1 : bool -> out -> ext
  | ext_case_1 : out -> trm -> trm -> ext
  | ext_try_1 : out -> trm -> ext
  | ext_raise_1 : out -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

(** Non-regular behaviors *)

Inductive abort : out -> Prop :=
  | abort_exn : forall v,
     abort (out_exn v)
  | abort_div :
     abort out_div.

(** Evaluation *)

Inductive red : ext -> out -> Prop :=
  | red_val : forall v,
      red v v
  | red_abs : forall x t,
      red (trm_abs x t) (val_abs x t)
  | red_app : forall o1 o2 t1 t2,
      red t1 o1 ->
      red (ext_app_1 o1 t2) o2 ->
      red (trm_app t1 t2) o2
  | red_app_1_abort : forall o1 t2,
      abort o1 ->
      red (ext_app_1 o1 t2) o1
  | red_app_1 : forall o2 o3 v1 t2,
      red t2 o2 ->
      red (ext_app_2 v1 o2) o3 ->
      red (ext_app_1 v1 t2) o3
  | red_app_2_abort : forall o2 v1,
      abort o2 ->
      red (ext_app_2 v1 o2) o2
  | red_app_2 : forall o3 x t3 v2,
      red (subst x v2 t3) o3 ->
      red (ext_app_2 (val_abs x t3) v2) o3
  | red_inj : forall o1 o2 b t1,
      red t1 o1 ->
      red (ext_inj_1 b o1) o2 ->
      red (trm_inj b t1) o2
  | red_inj_1_abort : forall o1 b,
      abort o1 ->
      red (ext_inj_1 b o1) o1
  | red_inj_1 : forall b v1,
      red (ext_inj_1 b v1) (val_inj b v1)
  | red_case : forall o1 o2 t1 t2 t3,
      red t1 o1 ->
      red (ext_case_1 o1 t2 t3) o2 ->
      red (trm_case t1 t2 t3) o2
  | red_case_1_abort : forall o1 t2 t3,
      abort o1 ->
      red (ext_case_1 o1 t2 t3) o1
  | red_case_1_true : forall o1 v1 t2 t3,
      red (trm_app t2 v1) o1 ->
      red (ext_case_1 (val_inj true v1) t2 t3) o1
  | red_case_1_false : forall o1 v1 t2 t3,
      red (trm_app t3 v1) o1 ->
      red (ext_case_1 (val_inj false v1) t2 t3) o1
  | red_try : forall o1 o2 t1 t2,
      red t1 o1 ->
      red (ext_try_1 o1 t2) o2 ->
      red (trm_try t1 t2) o2
  | red_try_1_val : forall v1 t2,
      red (ext_try_1 v1 t2) v1
  | red_try_1_exn : forall o1 v t2,
      red (trm_app t2 v) o1 ->
      red (ext_try_1 (out_exn v) t2) o1
  | red_try_1_div : forall t2,
      red (ext_try_1 out_div t2) out_div
  | red_raise : forall o1 o2 t1,
      red t1 o1 ->
      red (ext_raise_1 o1) o2 ->
      red (trm_raise t1) o2
  | red_raise_1_abort : forall o1,
      abort o1 ->
      red (ext_raise_1 o1) o1
  | red_raise_1 : forall v1,
      red (ext_raise_1 v1) (out_exn v1).

(** CoEvaluation -- same as above, but coinductively *)

CoInductive cored : ext -> out -> Prop :=
  | cored_val : forall v,
      cored v v
  | cored_abs : forall x t,
      cored (trm_abs x t) (val_abs x t)
  | cored_app : forall o1 o2 t1 t2,
      cored t1 o1 ->
      cored (ext_app_1 o1 t2) o2 ->
      cored (trm_app t1 t2) o2
  | cored_app_1_abort : forall o1 t2,
      abort o1 ->
      cored (ext_app_1 o1 t2) o1
  | cored_app_1 : forall o2 o3 v1 t2,
      cored t2 o2 ->
      cored (ext_app_2 v1 o2) o3 ->
      cored (ext_app_1 v1 t2) o3
  | cored_app_2_abort : forall o2 v1,
      abort o2 ->
      cored (ext_app_2 v1 o2) o2
  | cored_app_2 : forall o3 x t3 v2,
      cored (subst x v2 t3) o3 ->
      cored (ext_app_2 (val_abs x t3) v2) o3
  | cored_inj : forall o1 o2 b t1,
      cored t1 o1 ->
      cored (ext_inj_1 b o1) o2 ->
      cored (trm_inj b t1) o2
  | cored_inj_1_abort : forall o1 b,
      abort o1 ->
      cored (ext_inj_1 b o1) o1
  | cored_inj_1 : forall b v1,
      cored (ext_inj_1 b v1) (val_inj b v1)
  | cored_case : forall o1 o2 t1 t2 t3,
      cored t1 o1 ->
      cored (ext_case_1 o1 t2 t3) o2 ->
      cored (trm_case t1 t2 t3) o2
  | cored_case_1_abort : forall o1 t2 t3,
      abort o1 ->
      cored (ext_case_1 o1 t2 t3) o1
  | cored_case_1_true : forall o1 v1 t2 t3,
      cored (trm_app t2 v1) o1 ->
      cored (ext_case_1 (val_inj true v1) t2 t3) o1
  | cored_case_1_false : forall o1 v1 t2 t3,
      cored (trm_app t3 v1) o1 ->
      cored (ext_case_1 (val_inj false v1) t2 t3) o1
  | cored_try : forall o1 o2 t1 t2,
      cored t1 o1 ->
      cored (ext_try_1 o1 t2) o2 ->
      cored (trm_try t1 t2) o2
  | cored_try_1_val : forall v1 t2,
      cored (ext_try_1 v1 t2) v1
  | cored_try_1_exn : forall o1 v t2,
      cored (trm_app t2 v) o1 ->
      cored (ext_try_1 (out_exn v) t2) o1
  | cored_try_1_div : forall t2,
      cored (ext_try_1 out_div t2) out_div
  | cored_raise : forall o1 o2 t1,
      cored t1 o1 ->
      cored (ext_raise_1 o1) o2 ->
      cored (trm_raise t1) o2
  | cored_raise_1_abort : forall o1,
      abort o1 ->
      cored (ext_raise_1 o1) o1
  | cored_raise_1 : forall v1,
      cored (ext_raise_1 v1) (out_exn v1).

Definition diverge e := cored e out_div.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Properties *)

Axiom cored_to_diverge_or_red : forall e o,
  cored e o -> diverge e \/ red e o.

Axiom red_trm_not_div : forall t,
  red (ext_trm t) out_div -> False.

Section L.
#[local]
Hint Constructors cored.
Theorem red_cored : forall e o,
  red e o -> cored e o.
Proof. introv H. induction* H. Qed.
End L.

(* TODO: equivalence with pretty *)