(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Small-step semantics                                      *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_Syntax LibRelation.

Implicit Types v : val.
Implicit Types t : trm.


(* TODO move *)

CoInductive infclosure A (R:binary A) : A -> Prop :=
  | infclosure_step : forall y x,
      R x y -> infclosure R y -> infclosure R x.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Reduction contexts *)

(** Grammar of contexts *)

Inductive ctx :=
  | ctx_hole : ctx
  | ctx_app_1 : ctx -> trm -> ctx
  | ctx_app_2 : val -> ctx -> ctx
  | ctx_case : ctx -> trm -> trm -> ctx
  | ctx_inj : bool -> ctx -> ctx
  | ctx_try : ctx -> trm -> ctx
  | ctx_raise : ctx -> ctx.

Implicit Types c : ctx.

(** Application of contexts *)

Fixpoint ctx_apply c t :=
  let r c' := ctx_apply c' t in
  match c with
  | ctx_hole => t
  | ctx_app_1 c' t2 => trm_app (r c') t2
  | ctx_app_2 v1 c' => trm_app v1 (r c')
  | ctx_inj b c' => trm_inj b (r c')
  | ctx_case c' t1 t2 => trm_case (r c') t1 t2
  | ctx_try c' t2 => trm_try (r c') t2
  | ctx_raise c' => trm_raise (r c') 
  end.

Coercion ctx_apply : ctx >-> Funclass.

(** Contexts that do not contain [try] construct *)

Fixpoint ctx_notry c :=
  let r := ctx_notry in 
  match c with
  | ctx_hole => True
  | ctx_app_1 c' t2 => r c'
  | ctx_app_2 v1 c' => r c'
  | ctx_inj b c' => r c'
  | ctx_case c' t1 t2 => r c'
  | ctx_try c' t2 => False
  | ctx_raise c' => r c'
  end.


(************************************************************)
(* ** Semantics *)

(** Reduction *)

Inductive step : binary trm :=
  | step_ctx : forall c t1 t2,
      step t1 t2 ->
      step (c t1) (c t2)
  | step_exn : forall c v, 
      ctx_notry c ->
      step (c (trm_raise v)) (trm_raise v)
  | step_abs : forall x t,
      step (trm_abs x t) (val_abs x t)
  | step_beta : forall x t3 v2,
      step (trm_app (val_abs x t3) v2) (subst x v2 t3)
  | step_try_val : forall v1 t2,
      step (trm_try v1 t2) v1
  | step_try_exn : forall v t2,
      step (trm_try (trm_raise v) t2) (trm_app t2 v)
  | step_inj : forall b v1,
      step (trm_inj b v1) (val_inj b v1)
  | sred_case_true : forall t1 t2 t3 v1,
      step (trm_case (val_inj true v1) t2 t3) (trm_app t2 v1)
  | sred_case_false : forall t1 t2 t3 v1,
      step (trm_case (val_inj false v1) t2 t3) (trm_app t3 v1).

(** Complete evaluation *)

Definition sredstar t t' := (rtclosure step) t t'.

Definition sredplus t t' := (tclosure step) t t'.

Definition sredval t v := sredstar t v.

Definition sdiverge t := (infclosure step) t.


(*==========================================================*)
(* * Proofs *)

Notation "'stepstar'" := (rtclosure step).
Notation "'stepplus'" := (tclosure step).

Hint Constructors step.
Hint Unfold sredval sredstar sredplus.
Hint Resolve rtclosure_once.

Hint Constructors rtclosure infclosure.


(************************************************************)
(* ** Derived reduction rules *)

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


(************************************************************)
(* ** Equivalence with pretty-big-step semantics *)

Require Export LambdaExnSum_Pretty.


(* todo: move *)

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
Admitted.

Hint Resolve red_not_div.

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


(* TODO

(** [sdiverge] to [diverge] *)

Lemma sdiverge_diverge : forall t,
  sdiverge t -> diverge t.
Proof.
  hint sredval_cored. unfold diverge. cofix IH.
  introv H. inverts H; try solve [constructors*].
Qed.

(** [diverge] to [sdiverge] *)

Lemma diverge_sdiverge : forall t,
  diverge t -> sdiverge t.
Proof.
  hint red_sredval. cofix IH. introv R. inverts R as.
  introv R1 R2. destruct~ (cored_to_diverge_or_red R1).
    apply* sdiverge_app_1.
    inverts R2 as.
      intros. apply~ sdiverge_app_1.
      introv R2 R3. destruct~ (cored_to_diverge_or_red R2).
        apply* sdiverge_app_2. 
        inverts R3 as.
          intros. apply* sdiverge_app_2.
          introv R3. apply* sdiverge_app_3.
Qed.
*)

End Equiv.


