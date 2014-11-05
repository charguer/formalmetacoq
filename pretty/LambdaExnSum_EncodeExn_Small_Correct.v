(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Encoding of exceptions into sums                          *
* Correctness using combined small-step semantics           *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_EncodeExn LambdaExnSum_Small.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Theorem statement *)

Definition correctness_step :=
  forall t t', step t t' -> 
  fresh (trm_vars not_used t) 3 L ->
  stepplus (tr_trm t) (tr_trm t').


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Derived reduction rules *)

Lemma stepplus_beta' : forall x t3 v2,
  stepplus (trm_app (val_abs x t3) v2) (subst x v2 t3).
Proof. intros. applys* tclosure_intro. Qed.

Tactic Notation "applys_simpl" constr(E) :=
  let M := fresh "TEMP" in 
  lets M: E; simpl in M; applys M; clear M.

Lemma stepplus_abs_beta : forall x t3 v2,
  stepplus (trm_app (trm_abs x t3) v2) (subst x v2 t3).
Proof.
  intros. applys tclosure_intro.
  applys_simpl (>> step_ctx (ctx_app_1 ctx_hole v2)).
  auto. auto.
Qed.


(************************************************************)
(* ** Freshness results *)

(* todo: ctx_vars *)

(** Reduction of terms does not introduce new variables *)

Lemma notin_step : forall t t' x,
  step t t' ->
  x \notin trm_vars not_used t ->
  x \notin trm_vars not_used t'.
Proof.
  introv R. induction R; introv F; simpls; auto.
  skip. (* todo : ctxvars *)
  skip. (* todo : ctxvars *)
  applys~ subst_notin. 
Qed. 

Lemma fresh_cred : forall t t' m xs,
  step t t' ->
  fresh (trm_vars not_used t) m xs ->
  fresh (trm_vars not_used t') m xs.
Proof.
  introv R Fr. applys* notin_to_fresh.
  intros. applys* notin_step.
Qed.


(************************************************************)
(* ** Correctness of auxiliary functions *)

(*
Fixpoint build_ctx_for t :=
  let r := build_ctx_for in
  let s t1 k :=
    match t1 with
    | trm_val v1 => ctx_hole
    | _ => k (r t1)
    end in
  match t with
  | trm_val v1 => ctx_hole
  | trm_var x => ctx_hole
  | trm_abs x t1 => ctx_hole
  | trm_app t1 t2 => 
    match t1 with
    | trm_val v1 => 
        match t2 with 
        | trm_val v2 => ctx_hole
        | _ => ctx_app_2 v1 (r t2)
        end
    | _ => ctx_app_1 (r t1) t2
    end 
  | trm_case t1 t2 t3 => s t1 (fun c => ctx_case c t2 t3)
  | trm_inj b t1 => s t1 (fun c => ctx_inj b c)
  | trm_try t1 t2 => s t1 (fun c => ctx_try c t2)
  | trm_raise t1 => s t1 (fun c => ctx_raise c)
  end.

Ltac build_ctx tt :=
  match goal with |- _ ?t _ => 
    let c := constr:(build_ctx_for t) in
    let c := (eval simpl in c) in 
    c
  end.
*)

Ltac build_ctx_for t :=
  let r t' := build_ctx_for t' in
  let s t1 k :=
    match t1 with
    | trm_val ?v1 => constr:(ctx_hole)
    | _ => let c := r t1 in k c
    end in
  match t with
  | trm_val ?v1 => constr:(ctx_hole)
  | trm_var ?x => constr:(ctx_hole)
  | trm_abs ?x ?t1 => constr:(ctx_hole)
  | trm_app ?t1 ?t2 => 
    match t1 with
    | trm_val ?v1 => 
        match t2 with 
        | trm_val ?v2 => constr:(ctx_hole)
        | _ => let c := r t2 in constr:(ctx_app_2 v1 c)
        end
    | _ => let c := r t1 in constr:(ctx_app_1 c t2)
    end 
  | trm_case ?t1 ?t2 ?t3 => s t1 ltac:(fun c => constr:(ctx_case c t2 t3))
  | trm_inj ?b ?t1 => s t1 ltac:(fun c => constr:(ctx_inj b c))
  | trm_try ?t1 ?t2 => s t1 ltac:(fun c => constr:(ctx_try c t2))
  | trm_raise ?t1 => s t1 ltac:(fun c => constr:(ctx_raise c))
  | _ => constr:(ctx_hole)
  end.

Ltac build_ctx tt :=
  match goal with |- _ ?t _ => build_ctx_for t end.


Ltac show_ctx :=
  let c := build_ctx tt in pose c.

Ltac do_step_ctx_core :=
  let c := build_ctx tt in
  let f := constr:(@step_ctx c) in
  let f := (eval simpl in f) in
  first [ applys_simpl f 
       | let M := fresh in lets M: f; simpl in M ].

Ltac do_step_ctx_high :=
  match goal with 
  | |- step _ _ => do_step_ctx_core
  | |- _ => applys rtclosure_step; [do_step_ctx_core|]
  end.

Tactic Notation "do_step_ctx" :=
  do_step_ctx_high.

Tactic Notation "do_step_ctx" "~" :=
  do_step_ctx_high; auto_tilde.
Tactic Notation "do_step_ctx" "*" :=
  do_step_ctx_high; auto_star.


Ltac simpl_substs := simpl; simpl_subst.



(** Verification of [tr_bind] *)

Lemma isctx_tr_bind : forall x k, 
  isctx (fun t => tr_bind t x k).
Proof.
  introv R. simpl. unfold tr_bind.
  do_step_ctx. auto.
Qed.

Lemma step_tr_bind_ret : forall v x k,
  stepstar (tr_bind (tr_ret v) x k) (subst x v k).
Proof.
  intros. unfold tr_bind, tr_ret. do 3 do_step_ctx~.
Qed.

Lemma step_tr_bind_exn : forall v x k,
  stepstar (tr_bind (tr_exn v) x k) (tr_exn v).
Proof.
  intros. unfold tr_bind, tr_exn. do 4 do_step_ctx~.
  simpl_substs. auto.
Qed.

(** Verification of [tr_cont] *)

Lemma step_tr_cont : forall t v,
  fresh (trm_vars not_used t) 3 L ->
  stepstar (trm_app (tr_cont t) v) (tr_bind t x3 (trm_app x3 v)).
Proof.
  introv F. unfold tr_cont. do 2 do_step_ctx~.
  rewrite~ subst_tr_bind.
  simpl_substs. auto. rewrite~ (@subst_id not_used).
Qed.

(** Preservation of reduction context by [tr_trm] 

Lemma isctx_tr_trm : isctx tr_trm.
Proof.
  introv R. simpl. destruct t1; simpl.
  unfold tr_ret.
  do_step_ctx. auto.
Qed.
*)

(** Transitive reduction in contexts *)

Lemma stepplus_ctx : forall f t1 t2,
  isctx f ->
  stepplus t1 t2 ->
  stepplus (f t1) (f t2).
Proof.
  introv C R. inverts R as R1 R2.
  constructors. applys* C. applys* stepstar_ctx.
Qed.


Hint Resolve isctx_tr_bind.


(************************************************************)
(* ** Correctness of translation *)

(** Terminating programs *)

Lemma tr_trm_correct_step : correctness_step.
Proof.
  unfolds. introv R. induction R; introv Fr; simpls.
  (* case ctx *)
Focus 1.
  induction c; simpls.
  auto. 
  applys~ stepplus_ctx (fun u => (tr_bind u x1 (tr_bind (tr_trm t) x2 (trm_app x1 x2)))).
  Print tr_ret. 
  Print tr_val. 
  applys~ stepplus_ctx (fun u => (tr_bind u x1 (tr_bind (tr_trm t) x2 (trm_app x1 x2)))).




  (* case abs *)
  applys* bigred_inj.
  (* case_app *)
  sets_eq v1: (val_abs x t3).
  applys* bigred_tr_bind_ret. rewrite~ subst_tr_bind.
  simpl. simpl_subst.
  rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ].
  applys* bigred_tr_bind_ret. simpl. simpl_subst.
  subst v1. applys bigred_abs_beta'. fold tr_trm.
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M1: fresh_bigred R1 Fr1. simpl in M1.
  asserts~ Fr2: (fresh (trm_vars not_used t2) 3 L).
  forwards M2: fresh_bigred R2 Fr2. simpl in M2.
  rewrite~ <- tr_val_subst. applys~ IH. applys~ fresh_subst.
  (* case_app_exn_1 *)
  applys* bigred_tr_bind_exn. 
  (* case_app_exn_2 *)
  applys* bigred_tr_bind_ret. rewrite~ subst_tr_bind.
  simpl. simpl_subst.
  rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ].
  applys* bigred_tr_bind_exn. 
  (* case_try *)
  applys bigred_case_true. applys IH (beh_ret v1). auto. auto.
  applys bigred_abs_beta. simpl. simpl_subst. auto.
  (* case_try_1 *)
  applys bigred_case_false. applys IH (beh_exn v). auto. auto.
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M: fresh_bigred R1 Fr1. simpl in M.
  applys bigred_tr_cont. skip. (* applys IH. makes Guarded loop ! *)
  auto. auto. auto.
  (* case_raise *)
  applys* bigred_tr_bind_ret. simpl_substs. auto.
  (* case_raise_exn_1 *)
  applys* bigred_tr_bind_exn. 
  (* case_inj *)
  applys* bigred_tr_bind_ret. simpl_substs. auto.
  (* case_inj_1 *)
  applys* bigred_tr_bind_exn. 
  (* case_true *)
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M: fresh_bigred R1 Fr1. simpl in M.
  applys* bigred_tr_bind_ret. sets_eq T: tr_cont.
  simpl. simpl_subst. subst. 
  do 2 rewrite~ subst_tr_cont.
  do 2 (rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ]).
  applys* bigred_case_true. 
  applys bigred_tr_cont R2. skip. (* applys IH. makes Guarded loop ! *)
  auto. auto.
  (* case_false *)
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M: fresh_bigred R1 Fr1. simpl in M.
  applys* bigred_tr_bind_ret. sets_eq T: tr_cont.
  simpl. simpl_subst. subst. 
  do 2 rewrite~ subst_tr_cont.
  do 2 (rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ]).
  applys* bigred_case_false. 
  applys bigred_tr_cont R2. skip. (* applys IH. makes Guarded loop ! *)
  auto. auto.
  (* case_1 *)
  applys* bigred_tr_bind_exn. 
Qed.
