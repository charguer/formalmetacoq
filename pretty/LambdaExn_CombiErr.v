(************************************************************
* Lambda-calculus with exceptions                           *
* Combined pretty-big-step semantics with error rules       *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExn_Pretty.
Export BehaviorsWithErrors.

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

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext
  | ext_try_1 : out -> trm -> ext
  | ext_raise_1 : out -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

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

(** Non-regular behavior *)

Inductive abort : out -> Prop :=
  | abort_exn : forall n v, 
     abort (out_ter n (beh_exn v))
  | abort_err : forall n,
     abort (out_ter n beh_err)
  | abort_div : 
     abort out_div.

(** Characterisation of closures *)

Inductive isclo : val -> Prop :=
  | isclo_intro : forall x t3, isclo (val_clo x t3).

(** Semantics with a collection of error rules,
    and with [rand] always returning zero. *)

CoInductive cred : ext -> out -> Prop :=
  | cred_var : forall n x,
      cred (trm_var x) (out_ter n beh_err)
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
  | cred_app_2_err : forall v1 n n' v2,
      ~ isclo v1 ->
      cred (ext_app_2 v1 (out_ter n v2)) (out_ter n' beh_err)
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
  | cred_try_1_err : forall n n' t2,
      cred (ext_try_1 (out_ter n beh_err) t2) (out_ter n' beh_err)
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
  | cred_rand : forall n, 
      cred trm_rand (out_ter n (val_int O)).

(** Auxiliary *)

Definition credbeh e b := exists n, cred e (out_ter n b).

Definition cdiverge e := cred e out_div.

Definition terminates e := exists n b, cred e (out_ter n b).



(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Basic properties of the semantics *)

Hint Constructors abort cred faster before.
Hint Extern 1 (_ < _) => math.
Hint Extern 1 (_ <= _) => math.

(** Monotonicity *)

Section Monotonicity.

Lemma faster_le_l : forall o n n' b,
  faster o (out_ter n b) -> n <= n' -> faster o (out_ter n' b).
Proof. introv O L. inverts* O. Qed.

Lemma before_le_l : forall o n n' b,
  before o (out_ter n b) -> n <= n' -> before o (out_ter n' b).
Proof. introv O L. inverts* O. Qed.

Hint Resolve faster_le_l before_le_l.

Lemma faster_before_le_l : forall o1 o2 n n' b,
  faster_before o1 o2 (out_ter n b) -> n <= n' -> 
  faster_before o1 o2 (out_ter n' b).
Proof. unfold faster_before. introv [O1 O2] L. split*. Qed.

End Monotonicity.

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

Hint Resolve faster_before_le_l.

(** Additional automation *)

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


(************************************************************)
(* * Full coverage property *)

Section Full.

(** Note: could be automated better using more advanced tactics *)

Ltac esplits := 
  esplit;
  repeat (match goal with |- exists _, _ => esplit end).

Lemma not_terminates_cred_div : forall e,
  ~ terminates e -> cred e out_div.
Proof.
  cofix IH. introv N. destruct e.
  destruct t; try solve [ false N; exists O __; auto ].
  tests (n1&b1&R1) C: (terminates t1).  
    tests (n2&b2&R2) C': (terminates (ext_app_1 (out_ter n1 b1) t2)).
      false N. esplits. applys* cred_app.
      forwards: IH C'. applys* cred_app.
    applys* cred_app.
  tests (n1&b1&R1) C: (terminates t1).  
    tests (n2&b2&R2) C': (terminates (ext_try_1 (out_ter n1 b1) t2)).
      false N. esplits. applys* cred_try.
      forwards: IH C'. applys* cred_try.
    applys* cred_try.
  tests (n1&b1&R1) C: (terminates t).  
    tests (n2&b2&R2) C': (terminates (ext_raise_1 (out_ter n1 b1))).
      false N. esplits. applys* cred_raise.
      forwards: IH C'. applys* cred_raise.
     applys* cred_raise.
  destruct o.
    destruct b.
      tests (n1&b1&R1) C: (terminates t).  
        tests (n2&b2&R2) C': (terminates (ext_app_2 v (out_ter n1 b1))).
          false N. esplits. applys* cred_app_1.
          forwards: IH C'. applys* cred_app_1.
        applys* cred_app_1. 
      false N. esplits. applys~ cred_app_1_abort.
      false N. esplits. applys~ cred_app_1_abort.
      constructor~.
  destruct o.
    destruct b.
      tests C: (isclo v).
        inverts C as (?&?&?).
         tests (?&?&?) C': (terminates (subst x v0 t3)).
           false N. esplits. applys* cred_app_2.
           forwards: IH C'. applys* cred_app_2.
        false N. exists O __. applys~ cred_app_2_err.
      false N. esplits. applys~ cred_app_2_abort.
      false N. esplits. applys~ cred_app_2_abort.
    constructors~.
  destruct o.
    destruct b.
      false N. exists O __. applys~ cred_try_1_val.
      tests (?&?&?) C': (terminates (trm_app t v)).
        false N. esplits. applys* cred_try_1_exn.
        forwards: IH C'. applys* cred_try_1_exn.
      false N. exists O __. applys~ cred_try_1_err.
    constructors~.
  destruct o.
    destruct b.
      false N. exists O __. applys~ cred_raise_1.
      false N. esplits. applys~ cred_raise_1_abort.
      false N. esplits. applys~ cred_raise_1_abort.
    constructors~.
Qed.

Corollary cred_full : forall e, exists o, cred e o.
Proof.
  intros. tests_basic C: (exists n b, cred e (out_ter n b)).
  destruct C as (n&b&?). eauto.
  exists out_div. apply* not_terminates_cred_div.
Qed.

End Full.

