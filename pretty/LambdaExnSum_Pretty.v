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



(************************************************************)
(* ** Equivalence with small-step semantics *)

Require Import LambdaExnSum_Small.
Implicit Types c : ctx.

Hint Constructors step.

Hint Unfold sredval sredstar sredplus.
Hint Resolve rtclosure_once.

Hint Constructors rtclosure infclosure.

(** Addition reduction contexts *)

Definition isctx (f:trm->trm) :=
  forall t1 t2, step t1 t2 -> step (f t1) (f t2).

Lemma isctx_ctx : forall c, isctx c.
Proof. intros_all. applys* step_ctx. Qed.

Hint Resolve isctx_ctx.

(** Transitive reduction in contexts *)

Lemma stepstar_ctx : forall f t1 t2,
  isctx f ->
  stepstar t1 t2 ->
  stepstar (f t1) (f t2).
Proof. introv C R. induction* R. Qed.

(** Extended forms with divergence *)

Definition ext_not_diverge e :=
  let n o := o <> out_div in
  match e with
  | ext_trm _ => True
  | ext_app_1 o1 t2 => n o1
  | ext_app_2 v1 o2 => n o2
  | ext_inj_1 b o1 => n o1
  | ext_case_1 o1 t2 t3 => n o1
  | ext_try_1 o1 t2 => n o1
  | ext_raise_1 o1 => n o1
  end.

Hint Unfold ext_not_diverge.

Lemma red_not_div : forall e o,
  red e o -> ext_not_diverge e -> o <> out_div.
Proof. introv H. induction* H; auto_false. Qed.

Hint Resolve red_not_div.

(** Conversions of extended forms into terms *)

Instance trm_inhab : Inhab trm.
Proof. applys Inhab_of_val (trm_val (val_int 0)). Qed.

Definition trm_of_out o : trm :=
  match o with
  | out_ret v => v
  | out_exn v => trm_raise v
  | out_div => arbitrary
  end.

Definition trm_of_ext e : trm :=
  let r := trm_of_out in
  match e with
  | ext_trm t => t
  | ext_app_1 o1 t2 => trm_app (r o1) t2
  | ext_app_2 v1 o2 => trm_app v1 (r o2)
  | ext_inj_1 b o1 => trm_inj b (r o1)
  | ext_case_1 o1 t2 t3 => trm_case (r o1) t2 t3
  | ext_try_1 o1 t2 => trm_try (r o1) t2
  | ext_raise_1 o1 => trm_raise (r o1)
  end.

Hint Unfold ctx_notry.

(** Proof of equivalence *)

Section Equiv.

Tactic Notation "applys_simpl" constr(E) :=
  let M := fresh "TEMP" in
  lets M: E; simpl in M; applys M; clear M.

Tactic Notation "applys_simpl" "~" constr(E) :=
  applys_simpl E; auto_tilde.
Tactic Notation "applys_simpl" "*" constr(E) :=
  applys_simpl E; auto_star.

(** [sredval] to [red] *)

Lemma sredval_red : forall t v,
  sredval t v -> red t v.
Proof. skip. Qed.

(** [red] to [sredval] *)

Lemma red_sredstar : forall e o,
  red e o -> ext_not_diverge e -> sredstar (trm_of_ext e) (trm_of_out o).
Proof.
  introv R. induction R; introv N; simpls.
  auto.
  auto.
  applys rtclosure_trans; [ | applys* IHR2].
   applys* stepstar_ctx (ctx_app_1 ctx_hole t2).
  inverts H; tryfalse. simpl. applys rtclosure_once.
   applys~ step_exn (ctx_app_1 ctx_hole t2).
  applys rtclosure_trans; [ | applys* IHR2].
   applys* stepstar_ctx (ctx_app_2 v1 ctx_hole).
  inverts H; tryfalse. simpl. applys rtclosure_once.
   applys~ step_exn (ctx_app_2 v1 ctx_hole).
  applys rtclosure_trans; [ | applys* IHR].
   applys* rtclosure_once.
  applys rtclosure_trans; [ | applys* IHR2].
   applys* stepstar_ctx (ctx_inj b ctx_hole).
  inverts H; tryfalse. simpl. applys rtclosure_once.
   applys~ step_exn (ctx_inj b ctx_hole).
  auto.
  applys rtclosure_trans; [ | applys* IHR2].
   applys* stepstar_ctx (ctx_case ctx_hole t2 t3).
  inverts H; tryfalse. simpl. applys rtclosure_once.
   applys~ step_exn (ctx_case ctx_hole t2 t3).
  applys rtclosure_trans; [ | applys* IHR].
   applys rtclosure_once. simple*.
  applys rtclosure_trans; [ | applys* IHR].
   applys rtclosure_once. simple*.
  applys rtclosure_trans; [ | applys* IHR2].
   applys* stepstar_ctx (ctx_try ctx_hole t2).
  applys* rtclosure_once.
  applys rtclosure_trans; [ | applys* IHR].
   applys* rtclosure_once.
  false.
  applys rtclosure_trans; [ | applys* IHR2].
   applys* stepstar_ctx (ctx_raise ctx_hole).
  inverts H; tryfalse. simpl. applys rtclosure_once.
   applys~ step_exn (ctx_raise ctx_hole).
  auto.
Qed.

Lemma red_sredval : forall t v,
  red t v -> sredval t v.
Proof. introv R. applys~ red_sredstar R. Qed.

End Equiv.


(************************************************************)
(* ** Determinacy *)

Definition deterministic :=
  forall e o1 o2, red e o1 -> cored e o2 -> o1 = o2.

(** Proof that the language is deterministic *)

Ltac off :=
  try solve [ match goal with
    H: abort _ |- _ => tryfalse_invert H
  end | false ].

Lemma red_cored_deterministic :
  deterministic.
Proof.
  introv R C. gen o2. induction R; intros;
   inverts C; off; auto; try solve [ false; auto ].
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
Qed.

(** Proof that [red] and [diverge] are exclusive *)

Lemma red_not_diverge_ext :
  forall e o, red e o -> diverge e -> ext_not_diverge e -> False.
Proof.
  introv R1 R2 N. forwards M: red_cored_deterministic R1 R2.
  applys* red_not_div M.
Qed.

Lemma red_not_diverge_trm :
  forall t o, red t o -> diverge t -> False.
Proof. introv R1 R2. applys* red_not_diverge_ext. Qed.
