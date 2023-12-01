(************************************************************
* Lambda-calculus with exceptions,                          *
* Combined pretty-big-step semantics                        *
*************************************************************)

Set Implicit Arguments.
Require Import LambdaExn_Pretty.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : beh.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Outcome of an evaluation *)

Inductive out :=
  | out_ter : nat -> beh -> out
  | out_div : out.

Implicit Types o : out.
Implicit Types n : nat.

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
  | abort_exn : forall v n, abort (out_ter n (beh_exn v))
  | abort_div : abort out_div.

(** Partial order on the outcomes *)

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

(** Reduction *)

CoInductive cred : ext -> out -> Prop :=
  | cred_val : forall n v,
      cred v (out_ter n v)
  | cred_abs : forall n x t,
      cred (trm_abs x t) (out_ter n (val_clo x t))
  | cred_app : forall o1 o2 o t1 t2,
      cred t1 o1 ->
      cred (ext_app_1 o1 t2) o2 ->
      faster_before o1 o2 o ->
      cred (trm_app t1 t2) o
  | cred_app_1_abort : forall o1 o t2,
      abort o1 ->
      before o1 o ->
      cred (ext_app_1 o1 t2) o
  | cred_app_1 : forall o2 o3 o n v1 t2,
      cred t2 o2 ->
      cred (ext_app_2 v1 o2) o3 ->
      faster_before o2 o3 o ->
      cred (ext_app_1 (out_ter n v1) t2) o
  | cred_app_2_abort : forall o2 v1 o,
      abort o2 ->
      before o2 o ->
      cred (ext_app_2 v1 o2) o
  | cred_app_2 : forall o3 o n x t3 v2,
      cred (subst x v2 t3) o3 ->
      before o3 o ->
      cred (ext_app_2 (val_clo x t3) (out_ter n v2)) o
  | cred_try : forall o1 o2 t1 t2 o,
      cred t1 o1 ->
      cred (ext_try_1 o1 t2) o2 ->
      faster_before o1 o2 o ->
      cred (trm_try t1 t2) o
  | cred_try_1_val : forall n n' v1 t2,
      cred (ext_try_1 (out_ter n v1) t2) (out_ter n' v1)
  | cred_try_1_exn : forall o1 n v1 t2 o,
      cred (trm_app t2 v1) o1 ->
      before o1 o ->
      cred (ext_try_1 (out_ter n (beh_exn v1)) t2) o
  | cred_try_1_div : forall t2,
      cred (ext_try_1 out_div t2) out_div
  | cred_raise : forall o1 o2 t1 o,
      cred t1 o1 ->
      cred (ext_raise_1 o1) o2 ->
      faster_before o1 o2 o ->
      cred (trm_raise t1) o
  | cred_raise_1_abort : forall o1 o,
      abort o1 ->
      before o1 o ->
      cred (ext_raise_1 o1) o
  | cred_raise_1 : forall n n' v1,
      cred (ext_raise_1 (out_ter n v1)) (out_ter n' (beh_exn v1))
  | cred_rand : forall n k,
      (ParamDeterministic -> k = 0) ->
      cred trm_rand (out_ter n (val_int k)).

Definition credbeh e b := exists n, cred e (out_ter n b).

Definition cdiverge e := cred e out_div.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Properties of the semantics *)

Hint Constructors abort cred faster before.
Hint Extern 1 (_ < _) => math.
Hint Extern 1 (_ <= _) => math.

(** Properties of partial order *)

Lemma faster_le_l : forall o n n' b,
  faster o (out_ter n b) -> n <= n' -> faster o (out_ter n' b).
Proof. introv O L. inverts* O. Qed.

Lemma before_le_l : forall o n n' b,
  before o (out_ter n b) -> n <= n' -> before o (out_ter n' b).
Proof. introv O L. inverts* O. Qed.

Lemma faster_before_le_l : forall o1 o2 n n' b,
  faster_before o1 o2 (out_ter n b) -> n <= n' ->
  faster_before o1 o2 (out_ter n' b).
Proof.
  hint faster_le_l, before_le_l.
  unfold faster_before. introv [O1 O2] L. split*.
Qed.

Hint Resolve faster_before_le_l.

(** Automation for the partial order *)

Lemma faster_succ : forall n b,
  faster (out_ter n b) (out_ter (S n) b).
Proof. intros. auto. Qed.

Lemma before_succ : forall n b,
  before (out_ter n b) (out_ter (S n) b).
Proof. intros. auto. Qed.

Hint Extern 1 (before _ _) => apply before_succ.
Hint Extern 1 (faster _ _) => apply faster_succ.
Hint Extern 3 (faster_before _ _ _) => split.

(** Other automation, not needed here *)

Section OtherAutomation.

Lemma faster_before_max : forall n1 n2 b1 b2,
  faster_before (out_ter n1 b1) (out_ter n2 b2)
                (out_ter (S (max n1 n2)) b2).
Proof.
  intros. forwards [[? ?]|[? ?]]: max_cases n1 n2; split~.
Qed.

Ltac max_resolve :=
  simpl; match goal with |- context [max ?n1 ?n2] =>
    let e := fresh "m" in
    destruct (max_cases n1 n2) as [[? ?]|[? ?]];
    set (e := max n1 n2) in *; clearbody e end.

Hint Resolve faster_before_max.
Hint Extern 1 (before _ _) => max_resolve; constructor.
Hint Extern 1 (faster_before _ _ _) => apply faster_before_max.
End OtherAutomation.


(************************************************************)
(* ** Determinacy *)

Section Det.

(** We assume that [trm_rand] always returns zero *)

Variables Det : ParamDeterministic.

(** Statement of [deterministic] *)

Inductive equiv : binary out :=
  | equiv_ter : forall n n' b,
      equiv (out_ter n b) (out_ter n' b)
  | equiv_div :
      equiv out_div out_div.

Definition deterministic := forall e o1 o2,
  cred e o1 -> cred e o2 -> equiv o1 o2.

(** Proof of deterministic *)

Inductive ext_equiv : binary ext :=
  | ext_equiv_trm : forall t,
      ext_equiv t t
  | ext_equiv_app_1 : forall o1 o2 t,
      equiv o1 o2 ->
      ext_equiv (ext_app_1 o1 t) (ext_app_1 o2 t)
  | ext_equiv_app_2 : forall o1 o2 v,
      equiv o1 o2 ->
      ext_equiv (ext_app_2 v o1) (ext_app_2 v o2)
  | ext_equiv_try_1 : forall o1 o2 t,
      equiv o1 o2 ->
      ext_equiv (ext_try_1 o1 t) (ext_try_1 o2 t)
  | ext_equiv_raise_1 : forall o1 o2,
      equiv o1 o2 ->
      ext_equiv (ext_raise_1 o1) (ext_raise_1 o2).

Hint Constructors equiv ext_equiv.

Lemma equiv_refl : refl equiv.
Proof. intros o. destruct~ o. Qed.

Hint Resolve equiv_refl.

Lemma ext_equiv_refl : refl ext_equiv.
Proof. intros e. destruct~ e. Qed.

Hint Resolve ext_equiv_refl.

Ltac inverts2 E :=
  let H := fresh "X" in inverts E as H; inverts H.

Lemma det_ter_any : forall n e e' b o,
  cred e (out_ter n b) -> cred e' o -> ext_equiv e e' ->
  exists n', o = out_ter n' b.
Proof.
  induction n using peano_induction.
  asserts IH: (forall e e' b o m,
    cred e (out_ter m b) -> cred e' o -> ext_equiv e e' ->
    m < n -> exists n', o = out_ter n' b).
    intros. applys* H. clear H.
  introv R S E. inverts R as.
  inverts E. inverts* S.
  inverts E. inverts* S.
  skip.
  introv A B. inverts B. inverts2 E. inverts A;
    inverts S as A' B'; inverts B'; eauto.
  skip.
  introv A B. inverts B. inverts2 E. inverts A;
    inverts S as A' B'; inverts B'; eauto.
  introv R1 L1. inverts L1. inverts2 E. inverts S as.
    introv A B. inverts A.
    introv S1 M1. forwards~ (n1'&N1): IH R1 S1. subst. inverts* M1.
  introv R1 R2 [L2 L1]. inverts E. inverts S as S1 S2 [M2 M1].
   inverts L1. inverts L2.
   forwards~ (n1'&N1): IH R1 S1. subst.
   forwards~ (n2'&N2): IH R2 S2. subst.
   inverts M2. eauto.
  inverts2 E. inverts* S.
  introv R1 L1. inverts L1. inverts2 E. inverts S as S1 M1.
   forwards~ (n1'&N1): IH R1 S1. subst. inverts* M1.
  introv R1 R2 [L2 L1]. inverts E. inverts S as S1 S2 [M2 M1].
   inverts L1. inverts L2.
   forwards~ (n1'&N1): IH R1 S1. subst.
   forwards~ (n2'&N2): IH R2 S2. subst.
   inverts M2. eauto.
  introv A B. inverts B. inverts2 E. inverts A;
    inverts S as A' B'; inverts B'; eauto.
  inverts2 E. inverts S as.
    introv A B. inverts A.
    eauto.
  introv D. inverts E. inverts S as D'. rewrite~ D. rewrite* D'.
Qed.

Lemma deterministic_prove : deterministic.
Proof.
  introv R1 R2. destruct o1; destruct o2.
  forwards~ (n3&M): det_ter_any R1 R2. inverts~ M.
  forwards~ (?&M): det_ter_any R1 R2. inverts~ M.
  forwards~ (?&M): det_ter_any R2 R1. inverts~ M.
  constructor.
Qed.

(** Bonus *)

Lemma det_ter_ter : forall e n1 n2 b1 b2,
  cred e (out_ter n1 b1) -> cred e (out_ter n2 b2) -> b1 = b2.
Proof.
  introv R1 R2. forwards~ (?&M): det_ter_any R1 R2. inverts~ M.
Qed.

Lemma det_ter_div : forall e n b,
  cred e (out_ter n b) -> cred e out_div -> False.
Proof.
  introv R1 R2. forwards~ M: det_ter_any R1 R2. inverts M. false.
Qed.

End Det.


(************************************************************)
(* ** Equivalence with big-step *)

Require Import LambdaExn_Big.
Hint Constructors bigred.

Definition cred_raise_1' n := cred_raise_1 n n.
Hint Resolve cred_raise_1'.

Lemma bigred_credbeh : forall t b,
  bigred t b -> credbeh t b.
Proof.
  unfold credbeh. introv H.
  forwards (n&M): bigred_bigredh (rm H).
  exists ((n+n+n+n)%nat).
  induction M; eauto; eauto 9.
Qed.

Lemma credbeh_bigred : forall t b,
  credbeh t b -> bigred t b.
Proof.
  introv (n&R). gen t b. induction n using peano_induction.
  asserts IH: (forall m t b, cred t (out_ter m b) -> m < n -> bigred t b).
    autos*. clear H.
  introv R. inverts R as; auto.
  introv R1 R2 [L2 L1]. inverts L2. inverts L1. inverts R2 as.
     introv A B. inverts A. inverts* B.
     introv R3 R4 [L4 L3]. inverts L3. inverts L4. inverts R4 as.
       introv A B. inverts A. inverts* B.
       introv R5 L5. inverts* L5.
  introv R1 R2 [L2 L1]. inverts L2. inverts L1. inverts R2 as.
    constructors*.
    introv R3 L3. inverts* L3.
  introv R1 R2 [L2 L1]. inverts L2. inverts L1. inverts R2 as.
    introv A B. inverts A. inverts* B.
    constructors*.
Qed.

Lemma bigdiv_cdiverge : forall t,
  bigdiv t -> cdiverge t.
Proof.
  introv R. unfold cdiverge. gen t. cofix IH.
  introv H. inverts H as.
  introv R1. constructors*.
  introv R1 R2. forwards (n1&M1): bigred_credbeh R1. constructors*.
  introv R1 R2 R3. forwards (n1&M1): bigred_credbeh R1.
    forwards (n2&M2): bigred_credbeh R2. constructors*.
  introv R1. constructors*.
  introv R1 R2. forwards (n1&M1): bigred_credbeh R1. constructors*.
  introv R1. constructors*.
Qed.

Lemma cdiverge_bigdiv : forall t,
  cdiverge t -> bigdiv t.
Proof.
  asserts M: (forall n t b, cred t (out_ter n b) -> bigred t b).
    introv R. apply* credbeh_bigred. exists* n.
  unfolds cdiverge. cofix IH.
  introv R. inverts R as R1 R2 [L2 L1].
  inverts L2. inverts R2 as.
    introv A B. inverts B. applys* bigdiv_app_1.
    introv R3 R4 [L4 L3]. inverts L4. inverts R4 as.
      introv A B. inverts B. apply* bigdiv_app_2.
      introv R5 L5. inverts L5. apply* bigdiv_app_3.
  inverts L2. inverts R2 as.
    introv R5 L5. inverts L5. apply* bigdiv_try_2.
  apply* bigdiv_try_1.
  inverts L2. inverts R2 as.
   introv A B. inverts B. apply* bigdiv_raise_1.
Qed.
