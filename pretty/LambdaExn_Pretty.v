(************************************************************
* Lambda-calculus with exceptions,                          *
* Pretty-big-step semantics                                 *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExn_Syntax.
Export BehaviorsWithoutErrors.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : beh.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Grammar of outcomes, isomorphic to:
      Inductive out :=
        | out_ret : val -> out
        | out_exn : val -> out
        | out_div : out.
*)

Inductive out :=
  | out_beh : beh -> out
  | out_div : out.

Coercion out_beh : beh >-> out.
Implicit Types o : out.
Notation "'out_exn' v" := (out_beh (beh_exn v)) (at level 60).

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
  | abort_exn : forall v, abort (out_exn v)
  | abort_div : abort out_div.

(** Evaluation judgment *)

Inductive red : ext -> out -> Prop :=
  | red_val : forall v,
      red v v
  | red_abs : forall x t,
      red (trm_abs x t) (val_clo x t)
  | red_app : forall t1 t2 o1 o,
      red t1 o1 ->
      red (ext_app_1 o1 t2) o ->
      red (trm_app t1 t2) o
  | red_app_1_abort : forall o1 t2,
      abort o1 ->
      red (ext_app_1 o1 t2) o1
  | red_app_1 : forall v1 t2 o o2,
      red t2 o2 ->
      red (ext_app_2 v1 o2) o ->
      red (ext_app_1 v1 t2) o
  | red_app_2_abort : forall v1 o2,
      abort o2 ->
      red (ext_app_2 v1 o2) o2
  | red_app_2 : forall x t3 v2 o,
      red (subst x v2 t3) o ->
      red (ext_app_2 (val_clo x t3) v2) o
  | red_try : forall t1 t2 o1 o,
      red t1 o1 ->
      red (ext_try_1 o1 t2) o ->
      red (trm_try t1 t2) o
  | red_try_1_val : forall v1 t2,
      red (ext_try_1 v1 t2) v1
  | red_try_1_exn : forall t2 o v,
      red (trm_app t2 v) o ->
      red (ext_try_1 (out_exn v) t2) o
  | red_try_1_div : forall t2,
      red (ext_try_1 out_div t2) out_div
  | red_raise : forall t1 o1 o,
      red t1 o1 ->
      red (ext_raise_1 o1) o ->
      red (trm_raise t1) o
  | red_raise_1_abort : forall o1,
      abort o1 ->
      red (ext_raise_1 o1) o1
  | red_raise_1 : forall v,
      red (ext_raise_1 v) (out_exn v)
  | red_rand : forall k,
      (ParamDeterministic -> k = 0) ->
      red trm_rand (val_int k).

(** Coevaluation judgment:
    copy-paste of the above definition,
    simply replacing [red] with [cored] *)

CoInductive cored : ext -> out -> Prop :=
  | cored_val : forall v,
      cored v v
  | cored_abs : forall x t,
      cored (trm_abs x t) (val_clo x t)
  | cored_app : forall t1 t2 o1 o,
      cored t1 o1 ->
      cored (ext_app_1 o1 t2) o ->
      cored (trm_app t1 t2) o
  | cored_app_1_abort : forall o1 t2,
      abort o1 ->
      cored (ext_app_1 o1 t2) o1
  | cored_app_1 : forall v1 t2 o o2,
      cored t2 o2 ->
      cored (ext_app_2 v1 o2) o ->
      cored (ext_app_1 v1 t2) o
  | cored_app_2_abort : forall v1 o2,
      abort o2 ->
      cored (ext_app_2 v1 o2) o2
  | cored_app_2 : forall x t3 v2 o,
      cored (subst x v2 t3) o ->
      cored (ext_app_2 (val_clo x t3) v2) o
  | cored_try : forall t1 t2 o1 o,
      cored t1 o1 ->
      cored (ext_try_1 o1 t2) o ->
      cored (trm_try t1 t2) o
  | cored_try_1_val : forall v1 t2,
      cored (ext_try_1 v1 t2) v1
  | cored_try_1_exn : forall t2 o v,
      cored (trm_app t2 v) o ->
      cored (ext_try_1 (out_exn v) t2) o
  | cored_try_1_div : forall t2,
      cored (ext_try_1 out_div t2) out_div
  | cored_raise : forall t1 o1 o,
      cored t1 o1 ->
      cored (ext_raise_1 o1) o ->
      cored (trm_raise t1) o
  | cored_raise_1_abort : forall o1,
      abort o1 ->
      cored (ext_raise_1 o1) o1
  | cored_raise_1 : forall v,
      cored (ext_raise_1 v) (out_exn v)
  | cored_rand : forall k,
      (ParamDeterministic -> k = 0) ->
      cored trm_rand (val_int k).

(** Definition of divergence *)

Definition diverge e := cored e out_div.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Basic properties of the semantics *)

Hint Constructors red cored abort.

(** Proof that [cored] contains [red] *)

Theorem red_cored : forall e o,
  red e o -> cored e o.
Proof. introv H. induction* H. Qed.

(** Proof that [red e out_div -> False] *)

Definition ext_not_diverge e :=
  let n o := o <> out_div in
  match e with
  | ext_trm _ => True
  | ext_app_1 o1 t2 => n o1
  | ext_app_2 v1 o2 => n o2
  | ext_try_1 o1 t2 => n o1
  | ext_raise_1 o1 => n o1
  end.

Hint Unfold ext_not_diverge.

Hint Extern 1 (_ <> _) => congruence.

Lemma red_not_div : forall e o,
  red e o -> ext_not_diverge e -> o <> out_div.
Proof. introv H. induction* H. Qed.

Lemma red_trm_not_div' : forall t o,
  red (ext_trm t) o -> o <> out_div.
Proof. introv H. apply* red_not_div. Qed.

Lemma red_trm_not_div : forall t,
  red (ext_trm t) out_div -> False.
Proof. introv M. applys* red_trm_not_div' M. Qed.

(** Proof that [cored] implies [red] or [diverge] *)

Ltac doi_base :=
  match goal with IH: forall _, _ |- _ =>
    eapply IH
  end;
  [ eauto | intros ?;
    match goal with N: ~ red _ _ |- _  => false N end ].

Ltac doi := doi_base; eauto.

Ltac testi H :=
  match type of H with cored ?e ?o => tests: (red e o) end.

Lemma cored_not_red_diverge : forall e o,
  cored e o -> ~ red e o -> diverge e.
Proof.
  unfold diverge. cofix IH. introv C R.
  inverts C; try solve [ false* R ].
  testi H.
    (*details:
    constructors.
     eassumption.
     eapply IH. eassumption. intros M. applys R. constructors. eassumption. eassumption.
    *)
    constructors*.
    (* details:
    constructors.
      applys IH. eassumption. eassumption.
      constructors. auto.
    *)
    constructors~. apply* IH.
  testi H.
    constructors*.
    constructors~. apply* IH.
  constructors*.
  testi H.
    destruct o1.
      constructors*.
      constructors*.
    constructors~. apply* IH.
  constructors. doi.
  testi H.
    constructors*.
    constructors~. apply* IH.
Qed.

Corollary cored_not_diverge_red : forall e o,
  cored e o -> ~ diverge e -> red e o.
Proof.
  introv C D. apply not_not_inv. intros R.
  apply D. applys* cored_not_red_diverge.
Qed.

Corollary cored_to_diverge_or_red : forall e o,
  cored e o -> diverge e \/ red e o.
Proof.
  introv C. apply or_classic_l. intros.
  applys* cored_not_red_diverge.
Qed.


(************************************************************)
(* ** Determinacy *)

(** Definition of [deterministic] *)

Definition deterministic :=
  forall e o1 o2, red e o1 -> cored e o2 -> o1 = o2.

(** Proof that the language is deterministic *)

Ltac off :=
  try solve [ match goal with
    H: abort _ |- _ => tryfalse_invert H
  end | false ].

Lemma red_cored_deterministic :
  ParamDeterministic -> deterministic.
Proof.
  introv Det R C. gen o2. induction R; intros;
   inverts C; off; auto; try solve [ false; auto ].
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite H, H0; auto.
Qed.

(** Corollary: [red] is deterministic *)

Corollary red_deterministic :
  ParamDeterministic ->
  forall e o1 o2, red e o1 -> red e o2 -> o1 = o2.
Proof.
  introv D R1 R2. hint red_cored.
  applys* red_cored_deterministic.
Qed.

(** Corollary: termination and divergence are exclusive
    for terms *)

Corollary red_not_diverge_trm :
  ParamDeterministic ->
  forall t o, red t o -> diverge t -> False.
Proof.
  introv D R1 R2. forwards M: red_cored_deterministic D R1 R2.
  applys* red_trm_not_div' M.
Qed.

(** Note that for extended terms, the above result holds only
    for those satisfying [ext_not_diverge] *)

Lemma red_not_diverge_ext :
  ParamDeterministic ->
  forall e o, red e o -> diverge e -> ext_not_diverge e -> False.
Proof.
  introv D R1 R2 N. forwards M: red_cored_deterministic D R1 R2.
  applys* red_not_div M.
Qed.


(************************************************************)
(* ** Induction principle on the height of a derivation *)

(** Ideally, would be automatically generated by Coq *)

Hint Constructors red cored.

(** Copy-paste of the definition of [red], plus a depth counter *)

Inductive redh : nat -> ext -> out -> Prop :=
  | redh_val : forall n v,
      redh (S n) v v
  | redh_abs : forall n x t,
      redh (S n) (trm_abs x t) (val_clo x t)
  | redh_app : forall n t1 t2 o1 o2,
      redh n t1 o1 ->
      redh n (ext_app_1 o1 t2) o2 ->
      redh (S n) (trm_app t1 t2) o2
  | redh_app_1_abort : forall n o1 t2,
      abort o1 ->
      redh (S n) (ext_app_1 o1 t2) o1
  | redh_app_1_clo : forall n v1 t2 o o2,
      redh n t2 o2 ->
      redh n (ext_app_2 v1 o2) o ->
      redh (S n) (ext_app_1 v1 t2) o
  | redh_app_2_abort : forall n v1 o2,
      abort o2 ->
      redh (S n) (ext_app_2 v1 o2) o2
  | redh_app_2_beta : forall n x t3 v2 o,
      redh n (subst x v2 t3) o ->
      redh (S n) (ext_app_2 (val_clo x t3) v2) o
  | redh_try : forall n t1 t2 o1 o,
      redh n t1 o1 ->
      redh n (ext_try_1 o1 t2) o ->
      redh (S n) (trm_try t1 t2) o
  | redh_try_1_val : forall n v1 t2,
      redh (S n) (ext_try_1 v1 t2) v1
  | redh_try_1_exn : forall n t2 o v,
      redh n (trm_app t2 v) o ->
      redh (S n) (ext_try_1 (out_exn v) t2) o
  | redh_try_1_div : forall n t2,
      redh (S n) (ext_try_1 out_div t2) out_div
  | redh_raise : forall n t1 o1 o,
      redh n t1 o1 ->
      redh n (ext_raise_1 o1) o ->
      redh (S n) (trm_raise t1) o
  | redh_raise_1_abort : forall n o1,
      abort o1 ->
      redh (S n) (ext_raise_1 o1) o1
  | redh_raise_1 : forall n v,
      redh (S n) (ext_raise_1 v) (out_exn v)
  | redh_rand : forall n k,
      (ParamDeterministic -> k = 0) ->
      redh (S n) trm_rand (val_int k).

Hint Constructors redh.
Hint Extern 1 (_ < _) => math.

Lemma redh_lt : forall n n' e o,
  redh n e o -> n < n' -> redh n' e o.
Proof.
  introv H. gen n'. induction H; introv L;
   (destruct n' as [|n']; [ false; math | autos* ]).
Qed.

Lemma red_redh : forall e o,
  red e o -> exists n, redh n e o.
Proof.
  hint redh_lt. introv H. induction H; try induct_height.
Qed.

Lemma redh_red : forall n e o,
  redh n e o -> red e o.
Proof. introv H. induction* H. Qed.


(************************************************************)
(* ** Equivalence with the traditional big-step semantics *)

Require Import LambdaExn_Big.
Hint Constructors bigred.

(** [bigred] to [red] *)

Lemma bigred_red : forall t b,
  bigred t b -> red t b.
Proof. introv H. induction H; simpls*. Qed.

(** [red] to [bigred] *)

Lemma red_bigred : forall t b,
  red t b -> bigred t b.
Proof.
  introv R. forwards (n&R'): red_redh (rm R).
  gen b t. induction n using peano_induction.
  asserts IH: (forall m t b, redh m t b -> m < n -> bigred t b).
    intros. apply* H.
  clear H. introv R. inverts R as; auto.
  introv R1 R2. inverts R2 as.
    introv O. inverts* O.
    introv R2 R3. inverts R3 as.
      introv O. inverts* O.
      autos*.
  introv R1 R2. inverts* R2.
  introv R1 R2. inverts R2 as.
    introv O. inverts* O.
    autos*.
Qed.

(** [bigdiv] to [diverge] *)

Lemma bigdiv_diverge : forall t,
  bigdiv t -> diverge t.
Proof.
  asserts M: (forall t b, bigred t b -> cored t b).
    intros. apply red_cored. apply~ bigred_red.
  unfold diverge. cofix IH. introv H.
  inverts H; try solve [constructors*].
Qed.

(** [diverge] to [bigdiv] *)

Lemma diverge_bigdiv : forall t,
  diverge t -> bigdiv t.
Proof.
  hint red_bigred.
  cofix IH. introv R. inverts R as.
  introv R1 R2. destruct~ (cored_to_diverge_or_red R1).
    apply* bigdiv_app_1.
    inverts R2 as.
      intros. apply~ bigdiv_app_1.
      introv R2 R3. destruct~ (cored_to_diverge_or_red R2).
        apply* bigdiv_app_2.
        inverts R3 as.
          intros. apply* bigdiv_app_2.
          introv R3. apply* bigdiv_app_3.
  introv R1 R2. destruct~ (cored_to_diverge_or_red R1).
    constructors*.
    inverts R2.
      apply* bigdiv_try_2.
      apply* bigdiv_try_1.
  introv R1 R2. destruct~ (cored_to_diverge_or_red R1).
    constructors*.
    inverts R2. constructors*.
Qed.


(*************************************************************)
(* ** Bonus: an inversion principle for divergence *)

CoInductive div : ext -> Prop :=
  | div_app_div : forall t1 t2,
      div t1 ->
      div (trm_app t1 t2)
  | div_app : forall t1 t2 o1,
      red t1 o1 ->
      div (ext_app_1 o1 t2) ->
      div (trm_app t1 t2)
  | div_app_1_abort : forall t2,
      div (ext_app_1 out_div t2)
  | div_app_1_div : forall v1 t2,
      div t2 ->
      div (ext_app_1 v1 t2)
  | div_app_1_clo : forall v1 t2 o o2,
      red t2 o2 ->
      div (ext_app_2 v1 o2) ->
      div (ext_app_1 v1 t2)
  | div_app_2_abort : forall v1,
      div (ext_app_2 v1 out_div)
  | div_app_2_beta : forall x t3 v2,
      div (subst x v2 t3)  ->
      div (ext_app_2 (val_clo x t3) v2)
  | div_try_div : forall t1 t2 o1 o,
      div t1 ->
      div (trm_try t1 t2)
  | div_try : forall t1 t2 o1 o,
      red t1 o1 ->
      div (ext_try_1 o1 t2) ->
      div (trm_try t1 t2)
  | div_try_1_exn : forall t2 v,
      div (trm_app t2 v) ->
      div (ext_try_1 (out_exn v) t2)
  | div_try_1_div : forall t2,
      div (ext_try_1 out_div t2)
  | div_raise_div : forall t1,
      div t1 ->
      div (trm_raise t1)
  | div_raise : forall t1 o1,
      red t1 o1 ->
      div (ext_raise_1 o1) ->
      div (trm_raise t1)
  | div_raise_1_div :
      div (ext_raise_1 out_div).

Lemma div_diverge : forall e,
  div e -> diverge e.
Proof.
  hint red_cored.
  unfold diverge. cofix IH. introv R.
  inverts R; try solve [constructors*].
Qed.

Lemma diverge_div : forall e,
  diverge e -> div e.
Proof.
  sets C: cored_to_diverge_or_red.
  unfold diverge. cofix IH. introv R. inverts R as.
  introv R1 R2. lets [?|?]: C R1.
    apply* div_app_div.
    apply* div_app.
  introv _. constructors.
  introv R1 R2. lets [?|?]: C R1.
    apply* div_app_1_div.
    apply* div_app_1_clo.
  introv _. constructors.
  introv R. constructors*.
  introv R1 R2. lets [?|?]: C R1.
    apply* div_try_div.
    apply* div_try.
  introv R. constructors*.
  constructors*.
  introv R1 R2. lets [?|?]: C R1.
    apply* div_raise_div.
    apply* div_raise.
  constructors*.
Qed.
