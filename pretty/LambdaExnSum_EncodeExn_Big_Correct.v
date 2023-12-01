(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Encoding of exceptions into sums                          *
* Correctness using big-step semantics                      *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_Big LambdaExnSum_EncodeExn.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : beh.
Implicit Types o : beh.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Translation *)

Definition tr_beh (b:beh) :=
  match b with
    | beh_ret v => beh_ret (val_inj true (tr_val v))
    | beh_exn v => beh_ret (val_inj false (tr_val v))
  end.

(************************************************************)
(* ** Freshness *)

Definition beh_vars (f:vars_opt) (b:beh) :=
  match b with
  | beh_ret v => trm_vars f v
  | beh_exn v => trm_vars f v
  end.

(************************************************************)
(* ** Theorem *)

Definition correctness_bigred :=
  forall t b, bigred t b ->
  fresh (trm_vars not_used t) 3 L ->
  bigred (tr_trm t) (tr_beh b).

Definition correctness_bigdiv :=
  forall t, bigdiv t ->
  fresh (trm_vars not_used t) 3 L ->
  bigdiv (tr_trm t).


(*==========================================================*)
(* * Proofs *)

Hint Constructors bigred.

(* TODO: why simpl_subst and simpl_substs ?*)
Ltac simpl_substs := simpl; case_if; tryfalse.


(************************************************************)
(* ** Derived reduction rules *)

Lemma bigred_abs_beta : forall o x t3 v2,
   bigred (subst x v2 t3) o ->
   bigred (trm_app (trm_abs x t3) v2) o.
Proof. introv R. autos*. Defined.

Lemma bigred_abs_beta' : forall o x t3 v2,
   bigred (subst x v2 t3) o ->
   bigred (trm_app (val_abs x t3) v2) o.
Proof. introv R. autos*. Defined.

Lemma bigdiv_abs_beta : forall x t3 v2,
   bigdiv (subst x v2 t3) ->
   bigdiv (trm_app (trm_abs x t3) v2).
Proof. introv R. applys* bigdiv_app_3. Defined.

Lemma bigdiv_abs_beta' : forall x t3 v2,
   bigdiv (subst x v2 t3) ->
   bigdiv (trm_app (val_abs x t3) v2).
Proof. introv R. applys* bigdiv_app_3. Defined.


(************************************************************)
(* ** Freshness results *)

(** Reduction of terms does not introduce new variables *)

Lemma notin_bigred : forall x t b,
  bigred t b ->
  x \notin trm_vars not_used t ->
  x \notin beh_vars not_used b.
Proof.
  introv R. induction R; introv F; simpls; auto.
  forwards~: IHR1. applys~ IHR3. applys~ subst_notin.
Qed.

Lemma fresh_bigred : forall m xs t b,
  bigred t b ->
  fresh (trm_vars not_used t) m xs ->
  fresh (beh_vars not_used b) m xs.
Proof.
  introv R Fr. applys* notin_to_fresh.
  intros. applys* notin_bigred.
Qed.


(************************************************************)
(* ** Correctness of auxiliary functions *)

(** Verification of [tr_bind] *)

Lemma bigred_tr_bind_ret : forall o t1 v1 k x1,
  correctness_bigred ->
  bigred t1 v1 ->
  bigred (subst x1 (tr_val v1) k) o ->
  fresh (trm_vars not_used t1) 3 L ->
  bigred (tr_bind (tr_trm t1) x1 k) o.
Proof.
  introv C R1 R2 Fr.
  applys bigred_case_true.
  applys* C (beh_ret v1).
  applys* bigred_abs_beta.
Defined.

Lemma bigred_tr_bind_exn : forall t1 x k v,
  correctness_bigred ->
  bigred t1 (beh_exn v) ->
  fresh (trm_vars not_used t1) 3 L ->
  bigred (tr_bind (tr_trm t1) x k) (tr_beh (beh_exn v)).
Proof.
  introv C R Fr.
  applys bigred_case_false.
  applys* C (beh_exn v).
  applys bigred_abs_beta. simpl_substs. auto.
Defined.

Lemma bigdiv_tr_bind_1 : forall t1 x k,
  correctness_bigdiv ->
  bigdiv t1 ->
  fresh (trm_vars not_used t1) 3 L ->
  bigdiv (tr_bind (tr_trm t1) x k).
Proof.
  introv C R Fr.
  applys bigdiv_case_1. applys* C.
Defined.

Lemma bigdiv_tr_bind_ret : forall t1 v1 k x1,
  correctness_bigred ->
  correctness_bigdiv ->
  bigred t1 v1 ->
  bigdiv (subst x1 (tr_val v1) k) ->
  fresh (trm_vars not_used t1) 3 L ->
  bigdiv (tr_bind (tr_trm t1) x1 k).
Proof.
  introv C C' R1 R2 Fr.
  applys bigdiv_case_true. applys* C (beh_ret v1).
  applys* bigdiv_abs_beta.
Defined.

(** Verification of [tr_cont] *)

Lemma bigred_tr_cont : forall o t v,
  correctness_bigred ->
  bigred (trm_app t v) o ->
  fresh (trm_vars not_used t) 3 L ->
  fresh (val_vars not_used v) 3 L ->
  bigred (trm_app (tr_cont (tr_trm t)) (tr_val v)) (tr_beh o).
Proof.
  introv C R Frt Frv. applys bigred_abs_beta.
  rewrite~ subst_tr_bind. simpl. simpl_subst.
  forwards M: tr_trm_vars Frt.
  rewrite~ (@subst_id not_free). clear M.
  unfold tr_bind. inverts R as.
  introv R1 R2 R3. inverts R2. applys bigred_case_true.
    applys* C (val_abs x t3).
    applys bigred_abs_beta. simpl. simpl_subst.
     applys bigred_abs_beta'.
     forwards M: fresh_bigred R1 Frt. simpl in M.
     rewrite~ <- tr_val_subst.
     applys* (C _ _ R3). applys~ fresh_subst.
  introv R1. applys bigred_case_false.
    applys* (C _ _ R1).
    applys bigred_abs_beta. simpl. simpl_subst. auto.
  introv R1 R2. inverts R2.
Defined.

Lemma bigdiv_tr_cont : forall t v,
  correctness_bigred ->
  correctness_bigdiv ->
  bigdiv (trm_app t v) ->
  fresh (trm_vars not_used t) 3 L ->
  fresh (val_vars not_used v) 3 L ->
  bigdiv (trm_app (tr_cont (tr_trm t)) (tr_val v)).
Proof.
  introv C C' R Frt Frv. applys bigdiv_abs_beta.
  rewrite~ subst_tr_bind. simpl. simpl_subst.
  forwards M: tr_trm_vars Frt.
  rewrite~ (@subst_id not_free). clear M.
  unfold tr_bind. inverts R as.
  introv R1. applys bigdiv_case_1. applys* C'.
  introv R1 R2. inverts R2.
  introv R1 R2 R3. inverts R2. applys bigdiv_case_true.
    applys* (C _ _ R1).
    applys bigdiv_abs_beta. simpl. simpl_subst.
     applys~ bigdiv_abs_beta'.
     forwards M: fresh_bigred R1 Frt. simpl in M.
     rewrite~ <- tr_val_subst.
     applys* C'. applys~ fresh_subst.
Defined.



(************************************************************)
(* ** Correctness of translation *)

(** Terminating programs *)

Lemma tr_trm_correct_red : correctness_bigred.
Proof.
  unfolds. fix IH 3. introv R Fr. destruct R; simpls.
  (* case val *)
  applys* bigred_inj.
  (* case abs *)
  applys* bigred_inj.
  (* case_app *)
  sets_eq v1: (val_abs x t3).
  applys* bigred_tr_bind_ret. rewrite~ subst_tr_bind.
  simpl. simpl_subst.
  rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ].
  applys* bigred_tr_bind_ret. simpl. simpl_subst.
  try subst v1. applys bigred_abs_beta'. fold tr_trm.
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
  applys bigred_tr_cont. exact IH.
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
  applys bigred_tr_cont R2. exact IH.
  auto. auto.
  (* case_false *)
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M: fresh_bigred R1 Fr1. simpl in M.
  applys* bigred_tr_bind_ret. sets_eq T: tr_cont.
  simpl. simpl_subst. subst.
  do 2 rewrite~ subst_tr_cont.
  do 2 (rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ]).
  applys* bigred_case_false.
  applys bigred_tr_cont R2. exact IH.
  auto. auto.
  (* case_1 *)
  applys* bigred_tr_bind_exn.
Qed.

(** Diverging programs *)

Lemma tr_trm_correct_div : correctness_bigdiv.
Proof.
  cofixs IH. introv R Fr. lets K: tr_trm_correct_red.
  inverts R as; simpls.
  (* case app_1 *)
  introv R1. applys* bigdiv_tr_bind_1.
  (* case app_2 *)
  introv R1 R2. applys* bigdiv_tr_bind_ret.
  rewrite~ subst_tr_bind.
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M: fresh_bigred R1 Fr1. simpl in M.
  simpl. simpl_subst.
  rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ].
  applys* bigdiv_tr_bind_1.
  (* case app_3 *)
  introv R1 R2 R3. sets_eq v1: (val_abs x t3).
  applys* bigdiv_tr_bind_ret. rewrite~ subst_tr_bind.
  simpl. simpl_subst.
  rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ].
  applys* bigdiv_tr_bind_ret. simpl. simpl_subst.
  try subst v1. applys bigdiv_abs_beta'. fold tr_trm.
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M1: fresh_bigred R1 Fr1. simpl in M1.
  asserts~ Fr2: (fresh (trm_vars not_used t2) 3 L).
  forwards M2: fresh_bigred R2 Fr2. simpl in M2.
  rewrite~ <- tr_val_subst. applys~ IH. applys~ fresh_subst.
  (* case try_1 *)
  introv R1. applys* bigdiv_case_1.
  (* case try_2 *)
  introv R1 R2. applys bigdiv_case_false.
  applys* K (beh_exn v).
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M: fresh_bigred R1 Fr1. simpl in M.
  applys* bigdiv_tr_cont.
  (* case raise_1 *)
  introv R1. applys* bigdiv_tr_bind_1.
  (* case inj_1 *)
  introv R1. applys* bigdiv_tr_bind_1.
  (* case case_1 *)
  introv R1. applys* bigdiv_tr_bind_1.
  (* case case_true *)
  introv R1 R2.
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M: fresh_bigred R1 Fr1. simpl in M.
  applys* bigdiv_tr_bind_ret. sets_eq T: tr_cont.
  simpl. simpl_subst. subst.
  do 2 rewrite~ subst_tr_cont.
  do 2 (rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ]).
  applys* bigdiv_case_true.
  applys* bigdiv_tr_cont R2.
  (* case case_false *)
  introv R1 R2.
  asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
  forwards M: fresh_bigred R1 Fr1. simpl in M.
  applys* bigdiv_tr_bind_ret. sets_eq T: tr_cont.
  simpl. simpl_subst. subst.
  do 2 rewrite~ subst_tr_cont.
  do 2 (rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ]).
  applys* bigdiv_case_false.
  applys* bigdiv_tr_cont R2.
Qed.
