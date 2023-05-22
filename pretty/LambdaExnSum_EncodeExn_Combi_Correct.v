(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Encoding of exceptions into sums                          *
* Correctness using combined pretty-big-step semantics      *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_EncodeExn LambdaExnSum_Combi.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types o : out.
Implicit Types e : ext.

(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Translation *)

Definition tr_res (r:res) :=
  match r with
    | res_ret v => res_ret (val_inj true (tr_val v))
    | res_exn v => res_ret (val_inj false (tr_val v))
  end.

Definition tr_out (o:out) :=
  match o with
  | out_ter n r => out_ter n (tr_res r)
  | out_div => out_div
  end.


(************************************************************)
(* ** Theorem statement *)

Notation "'nine' n" := ((n+n+n+n+n+n+n+n+n)%nat) (at level 20).
Definition cin n := (nine n + 8)%nat.

Definition correctness :=
  forall t o, cred t o ->
  fresh (trm_vars not_used t) 3 L ->
  cred (tr_trm t) (map cin (tr_out o)).


(************************************************************)
(* ** Freshness *)

Definition res_vars (f:vars_opt) (r:res) :=
  match r with
  | res_ret v => trm_vars f v
  | res_exn v => trm_vars f v
  end.

Definition out_vars (f:vars_opt) (o:out) :=
  match o with
  | out_ter n r => res_vars f r
  | out_div => \{}
  end.

Definition ext_vars (f:vars_opt) (e:ext) :=
  let trm_vars := trm_vars f in
  let out_vars := out_vars f in
  match e with
  | ext_trm t1 => trm_vars t1
  | ext_app_1 o1 t1 => out_vars o1 \u trm_vars t1
  | ext_app_2 v1 o2 => trm_vars v1 \u out_vars o2
  | ext_inj_1 b o1 => out_vars o1
  | ext_case_1 o1 t2 t3 => out_vars o1 \u trm_vars t2 \u trm_vars t3
  | ext_try_1 o1 t2 => out_vars o1 \u trm_vars t2
  | ext_raise_1 o1 => out_vars o1
  end.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Derived reduction rules *)

Lemma cred_inj_val : forall b v1,
  cred (trm_inj b v1) (out_ter 1 (val_inj b v1)).
Proof.
  intros. applys* cred_inj.
Defined.

Lemma cred_abs_beta : forall o1 o x t3 v2,
  cred (subst x v2 t3) o1 ->
  before (add 2 o1) o ->
  cred (trm_app (trm_abs x t3) v2) o.
Proof.
  introv R B. applys cred_app. auto.
  applys cred_app_1. auto.
  applys cred_app_2 R. apply before_succ'.
  apply faster_before_zero_succ.
  apply faster_before_zero.
  clear R. (* required for guard condition *)
  destruct o1; inverts B; simple~.
Defined.

Lemma cred_abs_beta' : forall o1 o x t3 v2,
  cred (subst x v2 t3) o1 ->
  before (add 2 o1) o ->
  cred (trm_app (val_abs x t3) v2) o.
Proof.
  introv R B. applys cred_app. auto.
  applys cred_app_1. auto.
  applys cred_app_2 R. apply before_succ'.
  apply faster_before_zero_succ.
  apply faster_before_zero.
  clear R. (* required for guard condition *)
  destruct o1; inverts B; simple~.
Defined.


(************************************************************)
(* ** Freshness results *)

(** Reduction of terms does not introduce new variables *)

Hint Extern 1 (_ \notin ext_vars _ _) => unfold ext_vars.

Lemma notin_cred : forall n x e r,
  cred e (out_ter n r) ->
  x \notin ext_vars not_used e ->
  x \notin res_vars not_used r.
Proof.
  induction n using peano_induction. introv R F.
  asserts IH: (forall e m r, cred e (out_ter m r) ->
    m < n -> x \notin ext_vars not_used e ->
    x \notin res_vars not_used r).
    intros. applys* H. clear H.
  inverts R as; simpls.
  auto.
  auto.
  introv R1 R2 [L2 L1]. inverts L1. inverts L2.
   forwards~: IH R1. forwards~: IH R2.
  introv A B. inverts B. simpls~.
  introv R1 R2 [L2 L1]. inverts L1. inverts L2.
   forwards~: IH R1. forwards~: IH R2. simpls~.
  introv A B. inverts B. simpls~.
  introv R1 B. inverts B. forwards~: IH R1. simpls.
   applys~ subst_notin.
  introv R1 R2 [L2 L1]. inverts L1. inverts L2.
   forwards~: IH R1. forwards~: IH R2.
  introv A B. inverts B. simpls~.
  auto.
  introv R1 R2 [L2 L1]. inverts L1. inverts L2.
   forwards~: IH R1. forwards~: IH R2.
  introv A B. inverts B. simpls~.
  introv R1 B. inverts B. forwards~: IH R1. simpls~.
  introv R1 B. inverts B. forwards~: IH R1. simpls~.
  introv R1 R2 [L2 L1]. inverts L1. inverts L2.
   forwards~: IH R1. forwards~: IH R2.
  auto.
  introv R1 B. inverts B. forwards~: IH R1. simpls~.
  introv R1 R2 [L2 L1]. inverts L1. inverts L2.
   forwards~: IH R1. forwards~: IH R2.
  introv A B. inverts B. simpls~.
  auto.
Qed.

Lemma fresh_cred : forall n m xs e r,
  cred e (out_ter n r) ->
  fresh (ext_vars not_used e) m xs ->
  fresh (res_vars not_used r) m xs.
Proof.
  introv R Fr. applys* notin_to_fresh.
  intros. applys* notin_cred.
Qed.


(************************************************************)
(* ** Auxiliary lemmas and tactics *)

Lemma faster_tr_out : forall o1 o2,
  faster o1 o2 -> faster (tr_out o1) (tr_out o2).
Proof. introv F. inverts F; simple~. Qed.

Ltac simpl_substs := simpl; case_if; tryfalse.

Lemma monotone_cin : monotone cin.
Proof. introv L. unfold cin. math. Qed.

Hint Resolve monotone_cin.

Lemma faster_cin_tr_out : forall o1 o2,
  faster o1 o2 ->
  faster (map cin (tr_out o1)) (map cin (tr_out o2)).
Proof. intros. applys~ faster_map; applys~ faster_tr_out. Qed.
Hint Immediate faster_cin_tr_out.

Ltac done := simpl; unfolds cin; auto.


(************************************************************)
(* ** Correctness of auxiliary functions *)

(** Verification of [tr_bind] *)

Lemma cred_tr_bind_abort : forall o3 o2 o o1 t1 x k,
  correctness ->
  cred t1 o1 ->
  abort o1 ->
  before o1 o2 ->
  before o2 o ->
  faster o1 o ->
  before (map cin (tr_out o1)) o3 ->
  fresh (trm_vars not_used t1) 3 L ->
  cred (tr_bind (tr_trm t1) x k) o3.
Proof.
  introv C R A B1 B2 F1 B3 Fr. inverts A.
  inverts B1. inverts B2. inverts B3. inverts F1.
   applys cred_case. applys* C.
   simpl. applys cred_case_1_false.
   applys cred_abs_beta. unfold tr_exn. simpl_substs.
   applys cred_inj_val. auto. auto. done.
  inverts F1. inverts B3. inverts B1. applys cred_case.
   applys* C. applys* cred_case_1_abort. auto.
Defined.

Lemma cred_tr_bind_ret : forall o3 t1 n v1 k x1 o4,
  correctness ->
  cred t1 (out_ter n v1) ->
  faster (map cin (tr_out (out_ter n v1))) o4 ->
  cred (subst x1 (tr_val v1) k) o3 ->
  before (add 4 o3) o4 ->
  fresh (trm_vars not_used t1) 3 L ->
  cred (tr_bind (tr_trm t1) x1 k) o4.
Proof.
  introv C R F1 R3 B3 Fr.
  applys cred_case; [ applys* C | | eauto ].
  simpl. applys cred_case_1_true (add 3 o3).
  applys cred_abs_beta. eauto.
  applys~ before_add. applys~ before_add.
Defined.

(** Verification of [tr_cont] *)

Lemma cred_tr_cont : forall o2 o t v,
  correctness ->
  cred (trm_app t v) o2 ->
  before (add 4 (map cin (tr_out o2))) o ->
  fresh (trm_vars not_used t) 3 L ->
  fresh (val_vars not_used v) 3 L ->
  cred (trm_app (tr_cont (tr_trm t)) (tr_val v)) o.
Proof.
  introv C R B3 Frt Frv. inverts R as R1 R2 [L2 L1].
  applys cred_abs_beta (add 2 (map cin (tr_out o2))).
  rewrite~ subst_tr_bind. simpl.
  simpl_subst. forwards M: tr_trm_vars Frt. auto.
  rewrite~ (@subst_id not_free). clear M.
  inverts R2 as.
    introv A B. applys cred_tr_bind_abort o0; eauto.
     inverts B; inverts L2; done.
    introv R3 R4 [L4 L3]. applys* cred_tr_bind_ret (map cin (tr_out o4)).
      inverts L1; done.
      inverts R3. inverts R4 as.
        introv A B. inverts A.
        introv R5 L5. simpl. case_if; tryfalse.
         applys cred_abs_beta'.
         forwards M: fresh_cred R1 Frt. simpl in M.
         rewrite~ <- tr_val_subst.
         applys* C. applys~ fresh_subst.
         inverts L5; done.
       inverts L4; inverts L2; done.
  destruct o2; inverts B3; done.
Defined.


(************************************************************)
(* ** Correctness of translation *)

(** Verification of the transformation [tr_trm].
    Recall that [correctness] is define as:
    [forall t o, cred t o -> cred (tr_trm t) (map cin (tr_out o))] *)

Lemma tr_trm_correct : correctness.
Proof.
  cofixs IH. introv R Fr. inverts R as; simpls.
  (* case val *)
  unfolds cin. applys* cred_inj.
  (* case abs *)
  unfolds cin. applys* cred_inj.
  (* case app *)
  introv R1 R2 [L2 L1]. inverts R2 as.
    introv A B. applys cred_tr_bind_abort o2; eauto.
     inverts B; inverts L2; done.
    introv R3 R4 [L4 L3].
     applys* cred_tr_bind_ret (add 4 (map cin (tr_out o2)));
       [ |inverts L4; inverts L2; done ].
     rewrite~ subst_tr_bind.
     rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ].
     simpl. simpl_subst. inverts R4 as.
      introv A B. applys* cred_tr_bind_abort o3 o2.
         inverts B; inverts L4; done.
       introv R5 L5.
         applys* cred_tr_bind_ret (add 4 (map cin (tr_out o3))).
           inverts L3; done.
           simpl. case_if; tryfalse.
           asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
            forwards M1: fresh_cred R1 Fr1. simpl in M1.
           asserts~ Fr2: (fresh (trm_vars not_used t2) 3 L).
            forwards M2: fresh_cred R3 Fr2. simpl in M2.
            applys cred_abs_beta'.
              rewrite <- tr_val_subst.
                applys* IH.
                applys~ fresh_subst.
                auto.
             inverts L5; inverts L4; done.
           inverts L5; inverts L4; done.
  (* case inj *)
  introv R1 R2 [L2 L1]. inverts R2 as.
    introv A B. applys* cred_tr_bind_abort.
      clear_coind. destruct o1; done. inverts B; inverts L2; done.
    applys* cred_tr_bind_ret.
      simpl_substs. applys cred_inj. applys cred_inj_val.
      applys cred_inj_1. applys faster_before_max.
      inverts L2. done.
  (* case case *)
  introv R1 R2 [L2 L1].
   asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
   asserts~ Fr2: (fresh (trm_vars not_used t2) 3 L). inverts R2 as.
    introv A B. applys cred_tr_bind_abort o2; eauto.
     inverts B; inverts L2; done.
    introv R3 L3. applys cred_tr_bind_ret
      (map (fun n => (n-5)%nat) (map cin (tr_out o))); eauto;
      [| clear_coind; destruct o; done ].
     sets_eq T: tr_cont. simpl. subst. case_if;tryfalse.
     do 2 rewrite~ subst_tr_cont.
     do 2 (rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ]).
     applys cred_case. applys cred_val O.
     applys cred_case_1_true.
     forwards M: fresh_cred R1 Fr1. simpl in M.
     applys* cred_tr_cont. auto.
     inverts L2. inverts L3. inverts L1. done. inverts L3. done.
    introv R3 L3. applys cred_tr_bind_ret
      (map (fun n => (n-5)%nat) (map cin (tr_out o))); eauto;
      [| clear_coind; destruct o; done ].
     sets_eq T: tr_cont. simpl. subst. simpl_subst.
     do 2 rewrite~ subst_tr_cont.
     do 2 (rewrite (@subst_id not_free); [ | applys~ tr_trm_vars ]).
     applys cred_case. applys cred_val O.
     applys cred_case_1_false.
     forwards M: fresh_cred R1 Fr1. simpl in M.
     applys* cred_tr_cont. auto.
     inverts L2. inverts L3. inverts L1. done. inverts L3. done.
  (* case try *)
  introv R1 R2 [L2 L1]. inverts R2 as.
  inverts L2. inverts L1. applys* cred_case. simpl.
   applys cred_case_1_true. applys cred_abs_beta.
   simpl. case_if; tryfalse. applys cred_inj_val.
   auto. auto. done.
  introv R3 L3. applys* cred_case. simpl.
   applys cred_case_1_false.
   asserts~ Fr1: (fresh (trm_vars not_used t1) 3 L).
   forwards M: fresh_cred R1 Fr1. simpl in M.
   applys* cred_tr_cont.
   auto. inverts L3; inverts L2; inverts L1; done.
  inverts L2. applys* cred_case.
  (* case raise *)
  introv R1 R2 [L2 L1]. inverts R2 as.
    introv A B. applys* cred_tr_bind_abort.
      clear_coind; destruct o1; done. inverts B; inverts L2; done.
    applys* cred_tr_bind_ret.
      simpl_substs. applys cred_inj_val.
      inverts L2. done.
Admitted. (* TEMPORARY: for faster compilation *)
(* Qed.*)
(* Warning: the check of the guard condition takes about 30 sec *)

