(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Combined pretty-big-step semantics                        *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_Pretty.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Output of an evaluation *)

Inductive res :=
  | res_ret : val -> res
  | res_exn : val -> res.

Inductive out :=
  | out_ter : nat -> res -> out
  | out_div : out.

Coercion res_ret : val >-> res.
Implicit Types o : out.

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
  | abort_exn : forall n v,
     abort (out_ter n (res_exn v))
  | abort_div :
     abort out_div.

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

(** Semantics *)

CoInductive cred : ext -> out -> Prop :=
  | cred_val : forall n v,
      cred v (out_ter n v)
  | cred_abs : forall n x t,
      cred (trm_abs x t) (out_ter n (val_abs x t))
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
      cred (ext_app_2 (val_abs x t3) (out_ter n v2)) o
  | cred_inj : forall o1 o2 b t1 o,
      cred t1 o1 ->
      cred (ext_inj_1 b o1) o2 ->
      faster_before o1 o2 o ->
      cred (trm_inj b t1) o
  | cred_inj_1_abort : forall o1 b o,
      abort o1 ->
      before o1 o ->
      cred (ext_inj_1 b o1) o
  | cred_inj_1 : forall n b v1,
      cred (ext_inj_1 b (out_ter n v1)) (out_ter n (val_inj b v1))
  | cred_case : forall o1 o2 t1 t2 t3 o,
      cred t1 o1 ->
      cred (ext_case_1 o1 t2 t3) o2 ->
      faster_before o1 o2 o ->
      cred (trm_case t1 t2 t3) o
  | cred_case_1_abort : forall o1 t2 t3 o,
      abort o1 ->
      before o1 o ->
      cred (ext_case_1 o1 t2 t3) o
  | cred_case_1_true : forall o1 n v1 t2 t3 o,
      cred (trm_app t2 v1) o1 ->
      before o1 o ->
      cred (ext_case_1 (out_ter n (val_inj true v1)) t2 t3) o
  | cred_case_1_false : forall o1 n v1 t2 t3 o,
      cred (trm_app t3 v1) o1 ->
      before o1 o ->
      cred (ext_case_1 (out_ter n (val_inj false v1)) t2 t3) o
  | cred_try : forall o1 o2 t1 t2 o,
      cred t1 o1 ->
      cred (ext_try_1 o1 t2) o2 ->
      faster_before o1 o2 o ->
      cred (trm_try t1 t2) o
  | cred_try_1_val : forall n v1 t2,
      cred (ext_try_1 (out_ter n v1) t2) (out_ter n v1)
  | cred_try_1_exn : forall o1 n v1 t2 o,
      cred (trm_app t2 v1) o1 ->
      before o1 o ->
      cred (ext_try_1 (out_ter n (res_exn v1)) t2) o
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
  | cred_raise_1 : forall n v1,
      cred (ext_raise_1 (out_ter n v1)) (out_ter n (res_exn v1)).

Definition credval e r := exists n, cred e (out_ter n r).

Definition cdiverge e := cred e out_div.



(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Properties *)

Hint Constructors abort cred faster before.
Hint Extern 1 (_ < _) => abstracts math.
Hint Extern 1 (_ <= _) => abstracts math.

(** Update of indices *)

Definition map f o :=
  match o with
  | out_ter n v => out_ter (f n) v
  | out_div => out_div
  end.

Definition add d o := map (fun n => (n+d)%nat) o.

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

Lemma before_succ' : forall o,
  before o (map S o).
Proof. intros. destruct o; simple~. Qed.

Lemma before_add : forall n m o,
  n < m ->
  before (add n o) (add m o).
Proof. intros. destruct o; simple~. Qed.

Lemma before_pcred : forall n v,
  O < n ->
  before (out_ter (n-1) v) (out_ter n v).
Proof. auto. Qed.

Lemma faster_pcred : forall n v,
  O < n ->
  faster (out_ter (n-1) v) (out_ter n v).
Proof. auto. Qed.

Lemma before_map_le : forall (f g:nat->nat) o1 o2,
  before (map g o1) o2 -> (forall n, f n <= g n) ->
  before (map f o1) o2.
Proof.
  introv B L. destruct o1; inverts B; simple.
  specializes L n. constructor. math.
  auto.
Qed.

Definition monotone (f:nat->nat) :=
  forall n1 n2, n1 < n2 -> f n1 < f n2.

Lemma faster_map : forall f o1 o2,
  monotone f -> faster o1 o2 -> faster (map f o1) (map f o2).
Proof.
  introv M F. inverts F as.
  introv H. constructor. forwards~: M n n'.
  constructor.
Qed.

Hint Resolve before_pcred.
Hint Extern 1 (before _ _) => apply before_succ.
Hint Extern 1 (before _ _) => apply before_succ'.
Hint Extern 1 (faster _ _) => apply faster_succ.
Hint Extern 3 (faster_before _ _ _) => split.

Lemma faster_before_zero : forall o1 o2 v,
  before o1 o2 ->
  faster_before (out_ter O v) o1 o2.
Proof. intros. inverts H; simple*. Qed.

Lemma faster_before_zero_succ : forall o1 v,
  faster_before (out_ter O v) o1 (map S o1).
Proof. intros. apply~ faster_before_zero. Qed.

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
Hint Extern 1 (before _ _) => (abstracts max_resolve); constructor.
Hint Extern 1 (faster_before _ _ _) => apply faster_before_max.

