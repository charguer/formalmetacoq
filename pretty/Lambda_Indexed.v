(************************************************************
* Lambda-calculus,                                          *
* Indexed pretty-big-step semantics                         *
*************************************************************)

Set Implicit Arguments.
Require Import Lambda_Syntax Lambda_Pretty.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types o : out.
Implicit Types e : ext.

(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Order on the indices, [Lo o n n'] is
    equivalent to [o = out_div \/ n < n']. *)

Definition Lo o (n n':nat) :=
  match o with
  | out_div => True
  | _ => n < n'
  end.

(** Semantics *)

CoInductive ired : nat -> ext -> out -> Prop :=
  | ired_val : forall n v,
      ired n v v
  | ired_abs : forall n x t,
      ired n (trm_abs x t) (val_clo x t)
  | ired_app : forall n2 n1 n t1 t2 o1 o,
      ired n1 t1 o1 -> Lo o n1 n ->
      ired n2 (ext_app_1 o1 t2) o -> Lo o n2 n ->
      ired n (trm_app t1 t2) o
  | ired_app_1_div : forall n t2,
      ired n (ext_app_1 out_div t2) out_div
  | ired_app_1 : forall n2 n1 n v1 t2 o o2,
      ired n1 t2 o2 -> Lo o n1 n ->
      ired n2 (ext_app_2 v1 o2) o -> Lo o n2 n ->
      ired n (ext_app_1 v1 t2) o
  | ired_app_2_div : forall n v1,
      ired n (ext_app_2 v1 out_div) out_div
  | ired_app_2 : forall n1 n x t3 v2 o,
      ired n1 (subst x v2 t3) o -> Lo o n1 n ->
      ired n (ext_app_2 (val_clo x t3) v2) o.

Definition iredval e v := exists n, ired n e v.

Definition idiverge e := exists n, ired n e out_div.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Monotonicity properties *)

Hint Constructors ired.
Hint Unfold Lo.
Hint Extern 1 (_ < _) => math.
Hint Extern 1 (_ <> _) => math.

Lemma lt_Lo : forall o n1 n2,
  n1 < n2 -> Lo o n1 n2.
Proof. unfolds Lo. destruct o. math. auto. Qed.

Lemma Lo_le : forall o n1 n2 n2',
  Lo o n1 n2 -> n2 <= n2' -> Lo o n1 n2'.
Proof. unfolds Lo. destruct o. math. auto. Qed.

Hint Resolve lt_Lo Lo_le.

Lemma ired_le : forall n n' e o,
  ired n e o -> n <= n' -> ired n' e o.
Proof.
  cofix IH. introv R L. inverts R; try solve [ constructors* ].
Qed.

Lemma ired_div_n : forall n n' e,
  ired n e out_div -> ired n' e out_div.
Proof.
  cofix IH. introv R. inverts R; try solve [ constructors* ].
Qed.


(************************************************************)
(* ** Equivalence with pretty-big-step *)

Require Import Lambda_Pretty.
Hint Constructors red.

(** [red] to [iredval] *)

Lemma red_ired : forall e o,
  red e o -> exists n, ired n e o.
Proof.
  unfold iredval. introv H.
  forwards (n&M): red_redh (rm H).
  exists ((n+n+n)%nat).
  induction M; auto.
  applys* ired_app ((n+n+n)%nat).
  applys* ired_app_1 ((n+n+n)%nat).
  applys* ired_app_2 ((n+n+n)%nat).
Qed.

Corollary red_iredval : forall e v,
  red e v -> iredval e v.
Proof. introv R. applys* red_ired. Qed.

(** [iredval] to [red] *)

Lemma iredval_red : forall e v,
  iredval e v -> red e v.
Proof.
  introv (n&R). gen e v. induction n using peano_induction.
  asserts IH: (forall m e v, ired m e v -> m < n -> red e v).
    autos*. clear H.
  introv R. inverts R as; auto.
  introv R1 L1 R2 L2. destruct o1; [ | inverts R2 ]. autos*.
  introv R1 L1 R2 L2. destruct o2; [ | inverts R2 ]. autos*.
  introv R1 L1. autos*.
Qed.

(** [diverge] to [idiverge] *)

Lemma cored_red_or_diverge : forall e o,
  cored e o -> (exists n, ired n e o) \/ diverge e.
Proof.
  introv R. lets [H|H]: cored_to_diverge_or_red R.
  right*.
  left. applys* red_ired.
Qed.

Section DivHints.
Definition ired_app_1_div_zero := ired_app_1_div 0.
Definition ired_app_2_div_zero := ired_app_2_div 0.
Hint Resolve ired_app_1_div_zero ired_app_2_div_zero.

Lemma diverge_idiverge : forall e,
  diverge e -> idiverge e.
Proof.
  unfold idiverge. introv R. exists O. gen e. cofix IH.
  introv R. inverts R as.
  introv R1 R2. lets [(n1&M1)|M1]: cored_red_or_diverge R1; constructors*.
  constructors*.
  introv R1 R2. lets [(n1&M1)|M1]: cored_red_or_diverge R1; constructors*.
  constructors*.
  introv R1. constructors*.
Qed.

End DivHints.

(** [idiverge] to [diverge] *)

Lemma ired_cored : forall n e o,
  ired n e o -> cored e o.
Proof. cofix IH. introv R. inverts R as; constructors*. Qed.

Corollary idiverge_diverge : forall e,
  idiverge e -> diverge e.
Proof. introv (n&R). applys* ired_cored. Qed.


(************************************************************)
(* ** Equivalence with big-step *)

Require Import Lambda_Big.
Hint Constructors bigred.

(** [bigred] to [iredval] *)

Lemma bigred_iredval : forall t v,
  bigred t v -> iredval t v.
Proof.
  unfold iredval. introv H.
  forwards (n&M): bigred_bigredh (rm H).
  exists ((n+n+n)%nat).
  induction M; auto.
  applys* ired_app ((S n+S n+n)%nat).
   applys* ired_app_1 ((S n+n+n)%nat).
Qed.

(** [iredval] to [bigred] *)

Lemma iredval_bigred : forall t v,
  iredval t v -> bigred t v.
Proof.
  introv (n&R). gen t v. induction n using peano_induction.
  asserts IH: (forall m t v, ired m t v -> m < n -> bigred t v).
    autos*. clear H.
  introv R. inverts R as; auto.
  introv R1 L1 R2 L2. inverts R2 as R3 L3 R4 L4.
   inverts R4 as R5 L5. unfolds Lo. constructors*.
Qed.

(** [bigdiv] to [idiverge] *)

Lemma ired_bigred : forall n t v,
  ired n t v -> bigred t v.
Proof. introv R. apply* iredval_bigred. exists* n. Qed.

Lemma bigdiv_idiverge : forall t,
  bigdiv t -> idiverge t.
Proof.
  introv R. exists O. gen t. cofix IH.
  introv H. inverts H as.
  introv R1. applys* ired_app O.
  introv R1 R2. forwards (n1&M1): bigred_iredval R1.
   applys ired_app O. eauto. eauto. applys* ired_app_1 O. auto.
  introv R1 R2 R3. forwards (n1&M1): bigred_iredval R1.
    forwards (n2&M2): bigred_iredval R2.
    applys ired_app O. eauto. eauto. applys* ired_app_1 O. auto.
Qed.

(** [idiverge] to [bigdiv] *)

Lemma idiverge_bigdiv : forall t,
  idiverge t -> bigdiv t.
Proof.
  hint ired_bigred.
  introv (n&R). gen n t. cofix IH.
  introv R. inverts R as R1 L1 R2 L2.
  inverts R2 as.
    apply* bigdiv_app_1.
    introv R3 L3 R4 L4. inverts R4 as.
      apply* bigdiv_app_2.
      introv R5 L5. apply* bigdiv_app_3.
Qed.



