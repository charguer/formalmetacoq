(************************************************************
* Lambda-calculus,                                          *
* Pretty-big-step semantics                                 *
*************************************************************)

Set Implicit Arguments.
Require Export Lambda_Syntax.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Grammar of outcomes *)

Inductive out :=
  | out_ret : val -> out
  | out_div : out.

Coercion out_ret : val >-> out.
Implicit Types o : out.

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

(** Evaluation judgment *)

Inductive red : ext -> out -> Prop :=
  | red_val : forall v,
      red v v
  | red_abs : forall x t,
      red (trm_abs x t) (val_clo x t)
  | red_app : forall o1 t1 t2 o2,
      red t1 o1 ->
      red (ext_app_1 o1 t2) o2 ->
      red (trm_app t1 t2) o2
  | red_app_1_abort : forall t2,
      red (ext_app_1 out_div t2) out_div
  | red_app_1 : forall o2 v1 t2 o,
      red t2 o2 ->
      red (ext_app_2 v1 o2) o ->
      red (ext_app_1 v1 t2) o
  | red_app_2_abort : forall v1,
      red (ext_app_2 v1 out_div) out_div
  | red_app_2 : forall x t3 v2 o,
      red (subst x v2 t3) o ->
      red (ext_app_2 (val_clo x t3) v2) o.

(** Co-evaluation judgment: copy-paste of the above
    definition, where [red] is replaced with [cored]
    and where [Inductive] becomes [CoInductive]. *)

CoInductive cored : ext -> out -> Prop :=
  | cored_val : forall v,
      cored v v
  | cored_abs : forall x t,
      cored (trm_abs x t) (val_clo x t)
  | cored_app : forall o1 t1 t2 o2,
      cored t1 o1 ->
      cored (ext_app_1 o1 t2) o2 ->
      cored (trm_app t1 t2) o2
  | cored_app_1_abort : forall t2,
      cored (ext_app_1 out_div t2) out_div
  | cored_app_1 : forall o2 v1 t2 o,
      cored t2 o2 ->
      cored (ext_app_2 v1 o2) o ->
      cored (ext_app_1 v1 t2) o
  | cored_app_2_abort : forall v1,
      cored (ext_app_2 v1 out_div) out_div
  | cored_app_2 : forall x t3 v2 o,
      cored (subst x v2 t3) o ->
      cored (ext_app_2 (val_clo x t3) v2) o.

Definition diverge e := cored e out_div.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Basic properties of the semantics *)

Hint Constructors red cored.
Hint Extern 1 (_ <> _) => congruence.

(** Proof that [cored] contains [red] *)

Theorem red_cored : forall e o,
  red e o -> cored e o.
Proof. introv H. induction* H. Qed.

(** Proof that [red e out_div] is not derivable *)

Definition ext_not_diverge e :=
  let n o := o <> out_div in
  match e with
  | ext_trm _ => True
  | ext_app_1 o1 t2 => n o1
  | ext_app_2 v1 o2 => n o2
  end.

Hint Unfold ext_not_diverge.

Lemma red_not_div_ind : forall e o,
  red e o -> ext_not_diverge e -> o <> out_div.
Proof. introv H. induction* H. Qed.

Lemma red_not_div : forall t o,
  red (ext_trm t) o -> o <> out_div.
Proof. introv H. apply* red_not_div_ind. Qed.

(** Proof that [cored] implies [red] or [diverge] *)

Ltac testi H :=
  match type of H with cored ?e ?o => tests: (red e o) end.

Lemma cored_not_red_diverge : forall e o,
  cored e o -> ~ red e o -> diverge e.
Proof.
  unfold diverge. cofix IH. introv C R.
  inverts C; try solve [ false* R ]. 
  testi H.
    constructors*.
    constructors~. applys* IH.
  testi H.
    constructors*.
    constructors~. apply* IH.
  constructors. applys* IH.
Qed.

Corollary cored_to_diverge_or_red : forall e o,
  cored e o -> diverge e \/ red e o.
Proof.
  introv C. apply classic_left. intros.
  applys* cored_not_red_diverge.
Qed.


(************************************************************)
(* ** Determinacy *)

(** Definition of deterministic *)

Definition deterministic := 
  forall e o1 o2, red e o1 -> cored e o2 -> o1 = o2.

(** Proof that the language is deterministic *)

Lemma red_cored_deterministic : deterministic.
Proof.
  introv R C. gen o2. induction R; intros;
   inverts C; auto; try solve [ false; auto ].
  rewrite~ <- IHR2. erewrite* IHR1.
  rewrite~ <- IHR2. erewrite* IHR1.
Qed.

(** Corollary: [red] is deterministic *) 

Corollary red_deterministic : 
  forall e o1 o2, red e o1 -> red e o2 -> o1 = o2.
Proof.
  introv R1 R2. hint red_cored.
  applys* red_cored_deterministic.
Qed.

(** Corollary: termination and divergence are exclusive 
    for terms *) 

Corollary red_not_diverge_trm : 
  forall t o, red t o -> diverge t -> False.
Proof.
  introv R1 R2. forwards M: red_cored_deterministic R1 R2.
  applys* red_not_div M.
Qed.


(************************************************************)
(* ** Induction principle on the height of a derivation *)

(** Ideally, would be automatically generated by Coq *)

Section RedInd.

(** Copy-paste of the definition of [red], plus a depth counter *)

Inductive redh : nat -> ext -> out -> Prop :=
  | redh_val : forall n v,
      redh (S n) v v
  | redh_abs : forall n x t,
      redh (S n) (trm_abs x t) (val_clo x t)
  | redh_app : forall n o1 t1 t2 o2,
      redh n t1 o1 ->
      redh n (ext_app_1 o1 t2) o2 ->
      redh (S n) (trm_app t1 t2) o2
  | redh_app_1_abort : forall n t2,
      redh (S n) (ext_app_1 out_div t2) out_div
  | redh_app_1 : forall n o2 v1 t2 o,
      redh n t2 o2 ->
      redh n (ext_app_2 v1 o2) o ->
      redh (S n) (ext_app_1 v1 t2) o
  | redh_app_2_abort : forall n v1,
      redh (S n) (ext_app_2 v1 out_div) out_div
  | redh_app_2 : forall n x t3 v2 o,
      redh n (subst x v2 t3) o ->
      redh (S n) (ext_app_2 (val_clo x t3) v2) o.

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
 
End RedInd.


(************************************************************)
(* ** Equivalence between with big-step *)

Require Import Lambda_Big.
Hint Constructors bigred.
Hint Extern 1 (_ < _) => math.

(** [bigred] to [red] *)

Lemma bigred_red : forall t v,
  bigred t v -> red t v.
Proof. introv H. induction H; simpls*. Qed.

(** [red] to [bigred] *)

Lemma red_bigred : forall t v,
  red t v -> bigred t v.
Proof.
  introv R. forwards (n&R'): red_redh (rm R).
  gen v t. induction n using peano_induction.
  asserts IH: (forall m t v, redh m t v -> m < n -> bigred t v).
    intros. apply* H. clear H.
  introv R. inverts R as; autos*. 
  introv R1 R2. inverts R2 as R2 R3. inverts* R3.
Qed.
 
(** [bigdiv] to [diverge] *)

Lemma bigdiv_diverge : forall t,
  bigdiv t -> diverge t.
Proof. 
  asserts K: (forall t b, bigred t b -> cored t b).
   intros. apply red_cored. apply~ bigred_red. 
  unfold diverge. cofix IH.
  introv H. inverts H; try solve [constructors*].
Qed.

(** [diverge] to [bigdiv] *)

Lemma diverge_bigdiv : forall t,
  diverge t -> bigdiv t.
Proof.
  hint red_bigred. cofix IH. introv R. inverts R as.
  introv R1 R2. destruct~ (cored_to_diverge_or_red R1).
    apply* bigdiv_app_1.
    inverts R2 as.
      intros. apply~ bigdiv_app_1.
      introv R2 R3. destruct~ (cored_to_diverge_or_red R2).
        apply* bigdiv_app_2. 
        inverts R3 as.
          intros. apply* bigdiv_app_2.
          introv R3. apply* bigdiv_app_3.
Qed.



