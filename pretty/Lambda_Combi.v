(************************************************************
* Lambda-calculus,                                          *
* Combined pretty-big-step semantics                        *
*************************************************************)

Set Implicit Arguments.
Require Import Lambda_Pretty.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Outcome of an evaluation *)

Inductive out :=
  | out_ter : nat -> val -> out
  | out_div : out.

Implicit Types o : out.
Implicit Types n : nat.

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

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

(** Optimization for automation:
    instead of writing two premises
    [faster o1 o -> before o2 o -> ..]
    we use a combined premise as follows. *)

Definition faster_before o1 o2 o :=
  before o2 o /\ faster o1 o.

(** Semantics *)

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
  | cred_app_1_div : forall t2,
      cred (ext_app_1 out_div t2) out_div
  | cred_app_1 : forall o n v1 t2 o2 o3,
      cred t2 o2 ->
      cred (ext_app_2 v1 o2) o3 ->
      faster_before o2 o3 o ->
      cred (ext_app_1 (out_ter n v1) t2) o
  | cred_app_2_div : forall v1,
      cred (ext_app_2 v1 out_div) out_div
  | cred_app_2 : forall o n x t3 v2 o3,
      cred (subst x v2 t3) o3 ->
      before o3 o ->
      cred (ext_app_2 (val_clo x t3) (out_ter n v2)) o.

Definition credval e v := exists n, cred e (out_ter n v).

Definition cdiverge e := cred e out_div.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Properties of combined big-step *)

Hint Constructors cred faster before.
Hint Extern 1 (_ < _) => math.
Hint Extern 1 (_ <> _) => congruence.

(** Monotonicity *)

Section Monotonicity.

Lemma faster_le_l : forall o n n' v,
  faster o (out_ter n v) -> n <= n' -> faster o (out_ter n' v).
Proof. introv O L. inverts* O. Qed.

Lemma before_le_l : forall o n n' v,
  before o (out_ter n v) -> n <= n' -> before o (out_ter n' v).
Proof. introv O L. inverts* O. Qed.

Hint Resolve faster_le_l before_le_l.

Lemma faster_before_le_l : forall o1 o2 n n' v,
  faster_before o1 o2 (out_ter n v) -> n <= n' ->
  faster_before o1 o2 (out_ter n' v).
Proof. unfold faster_before. introv [O1 O2] L. split*. Qed.

Hint Resolve faster_before_le_l.

Lemma cred_le : forall n n' e v,
  cred e (out_ter n v) -> n <= n' -> cred e (out_ter n' v).
Proof. cofix IH. introv R L. inverts R; constructors*. Qed.

End Monotonicity.

(** Automation for the partial order *)

Lemma faster_succ : forall n v,
  faster (out_ter n v) (out_ter (S n) v).
Proof. intros. auto. Qed.

Lemma before_succ : forall n v,
  before (out_ter n v) (out_ter (S n) v).
Proof. intros. auto. Qed.

Hint Extern 1 (before _ _) => apply before_succ.
Hint Extern 1 (faster _ _) => apply faster_succ.
Hint Extern 3 (faster_before _ _ _) => split.

(** Other automation not needed here *)

Section OtherAutomation.

Lemma faster_before_max : forall n1 n2 v1 v2,
  faster_before (out_ter n1 v1) (out_ter n2 v2)
                (out_ter (S (max n1 n2)) v2).
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
(* ** Equivalence with pretty-big-step *)

Require Lambda_Pretty.
Module Pretty := Lambda_Pretty.

Definition proj_out (o:out) :=
  match o with
  | out_ter n v => Pretty.out_ret v
  | out_div => Pretty.out_div
  end.

Definition proj_ext (e:ext) :=
  match e with
  | ext_trm t => Pretty.ext_trm t
  | ext_app_1 o t => Pretty.ext_app_1 (proj_out o) t
  | ext_app_2 v o => Pretty.ext_app_2 v (proj_out o)
  end.

(** Auxiliary lemma *)

Lemma before_proj_out : forall o1 o2,
  before o1 o2 -> proj_out o2 = proj_out o1.
Proof. introv R. inverts~ R. Qed.

(** Proof of equivalence *)

(** [red] to [cred] *)

Lemma red_credval : forall e v,
  red (proj_ext e) v -> credval e v.
Proof.
  unfold credval. introv H. lets (n&M): red_redh (rm H).
  exists n. inductions M; destruct e; tryfalse; inverts x; auto.
  inverts keep M2. constructors~.
  destruct o; inverts~ H0. inverts keep M2. constructors~.
  destruct o; inverts~ H1. constructors~.
Qed.

(** [cred] to [red] *)

Lemma credval_red : forall e v,
  credval e v -> red (proj_ext e) v.
Proof.
  introv (n&R). gen e v. induction n using peano_induction.
  asserts IH: (forall m e f v, cred e (out_ter m v) -> f = proj_ext e -> m < n -> red f v).
    intros. subst. autos*. clear H.
  introv R. inverts R as; simpls; auto.
  introv R1 R2 [L2 L1]. inverts L2. inverts L1. constructors*.
  introv R1 R2 [L2 L1]. inverts L2. inverts L1. constructors*.
  introv R1 L1. inverts L1. constructors*.
Qed.

(** [diverge] to [cdiverge] *)

Lemma cored_cred_or_diverge : forall t (o:Pretty.out),
  cored t o -> (exists o', proj_out o' = o /\ cred t o')
             \/ diverge t.
Proof.
  introv R. lets [M|M]: cored_to_diverge_or_red R.
  right*.
  left. destruct o.
    lets (n&N): (red_credval t M). exists~ (out_ter n v).
    false. applys~ red_not_div M.
Qed.

Lemma diverge_cdiverge : forall e,
  diverge (proj_ext e) -> cdiverge e.
Proof.
  unfold diverge, cdiverge. cofix IH.
  introv H. destruct e; simpls; inverts H as.
  introv R1 R2. lets [(o1'&E1&M1)|M1]: cored_cred_or_diverge R1; subst*.
  introv E. destruct o; tryfalse; auto.
  introv R1 R2 E. inverts E as E. destruct o; tryfalse. inverts E.
   lets [(o1'&E1&M1)|M1]: cored_cred_or_diverge R1; subst*.
  introv E. destruct o; tryfalse; auto.
  introv R1 E. inverts E as E. destruct o; tryfalse. inverts E. autos*.
Qed.

(** [cdiverge] to [diverge] *)

Lemma cred_cored : forall e o,
  cred e o -> cored (proj_ext e) (proj_out o).
Proof.
  cofix IH.
  assert (IH' : forall e o f, cred e o -> f = proj_ext e -> cored f (proj_out o)).
    intros. subst. auto. clear IH.
  introv R. inverts R as; simpl.
  auto.
  auto.
  introv R1 R2 [L2 L1]. rewrite* (before_proj_out L2).
  auto.
  introv R1 R2 [L2 L1]. rewrite* (before_proj_out L2).
  auto.
  introv R1 L1. rewrite* (before_proj_out L1).
Qed.

Lemma cdiverge_diverge : forall e,
  cdiverge e -> diverge (proj_ext e).
Proof. intros. applys~ (>> cred_cored out_div). Qed.



(************************************************************)
(* ** Equivalence with big-step *)

Require Import Lambda_Big.
Hint Constructors bigred.

(** [bigred] to [credval] *)

Lemma bigred_credval : forall t v,
  bigred t v -> credval t v.
Proof.
  unfold credval. introv H.
  forwards (n&M): bigred_bigredh (rm H).
  exists ((n+n+n+n)%nat).
  induction M; auto.
  eauto 9.
Qed.

(** [credval] to [bigred] *)

Lemma credval_bigred : forall t v,
  credval t v -> bigred t v.
Proof.
  introv (n&R). gen t v. induction n using peano_induction.
  asserts IH: (forall m t v, cred t (out_ter m v) -> m < n -> bigred t v).
    autos*. clear H.
  introv R. inverts R as; auto.
  introv R1 R2 [L2 L1]. inverts L2. inverts L1.
   inverts R2 as R3 R4 [L4 L3]. inverts L3. inverts L4.
   inverts R4 as R5 L5. inverts L5. constructors*.
Qed.

(** [bigdiv] to [cdiverge] *)

Lemma bigdiv_cdiverge : forall t,
  bigdiv t -> cdiverge t.
Proof.
  introv R. unfold cdiverge. gen t. cofix IH.
  introv H. inverts H as.
  introv R1. constructors*.
  introv R1 R2. forwards (n1&M1): bigred_credval R1. constructors*.
  introv R1 R2 R3. forwards (n1&M1): bigred_credval R1.
    forwards (n2&M2): bigred_credval R2. constructors*.
Qed.

(** [cdiverge] to [bigdiv] *)

Lemma cdiverge_bigdiv : forall t,
  cdiverge t -> bigdiv t.
Proof.
  asserts M: (forall n t v, cred t (out_ter n v) -> bigred t v).
    introv R. apply* credval_bigred. exists* n.
  unfolds cdiverge. cofix IH.
  introv R. inverts R as R1 R2 [L2 L1].
   inverts L2. inverts R2 as.
     apply* bigdiv_app_1.
     introv R3 R4 [L4 L3]. inverts L4. inverts R4 as.
       apply* bigdiv_app_2.
       introv R5 L5. inverts L5. apply* bigdiv_app_3.
Qed.



