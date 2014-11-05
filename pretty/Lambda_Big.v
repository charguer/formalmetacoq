(************************************************************
* Lambda-calculus,                                          *
* Big-step semantics                                        *
*************************************************************)

Set Implicit Arguments.
Require Export Lambda_Syntax.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

Inductive bigred : trm -> val -> Prop :=
  | bigred_val : forall v,
      bigred v v
  | bigred_abs : forall x t,
      bigred (trm_abs x t) (val_clo x t)
  | bigred_app : forall t1 t2 x t3 v2 v,
      bigred t1 (val_clo x t3) ->
      bigred t2 v2 ->
      bigred (subst x v2 t3) v ->
      bigred (trm_app t1 t2) v.

CoInductive bigdiv : trm -> Prop :=
  | bigdiv_app_1 : forall t1 t2,
      bigdiv t1 ->
      bigdiv (trm_app t1 t2) 
  | bigdiv_app_2 : forall t1 v1 t2,
      bigred t1 v1 ->
      bigdiv t2 ->
      bigdiv (trm_app t1 t2) 
  | bigdiv_app_3 : forall t1 t2 x t3 v2,
      bigred t1 (val_clo x t3) ->
      bigred t2 v2 ->
      bigdiv (subst x v2 t3) ->
      bigdiv (trm_app t1 t2) .


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Induction principle on the height of a derivation *)

(** Ideally, would be automatically generated by Coq *)

Section BigredInd.

Inductive bigredh : nat -> trm -> val -> Prop :=
  | bigredh_val : forall n v,
      bigredh (S n) v v
  | bigredh_abs : forall n x t,
      bigredh (S n) (trm_abs x t) (val_clo x t)
  | bigredh_app : forall n t1 t2 x t3 v2 v,
      bigredh n t1 (val_clo x t3) ->
      bigredh n t2 v2 ->
      bigredh n (subst x v2 t3) v ->
      bigredh (S n) (trm_app t1 t2) v.

Hint Constructors bigred bigredh.
Hint Extern 1 (_ < _) => math.

Lemma bigredh_lt : forall n n' t v,
  bigredh n t v -> n < n' -> bigredh n' t v.
Proof.
  introv H. gen n'. induction H; introv L; 
   (destruct n' as [|n']; [ false; math | auto* ]).
Qed.

Lemma bigred_bigredh : forall t v,
  bigred t v -> exists n, bigredh n t v.
Proof. hint bigredh_lt. introv H. induction H; try induct_height. Qed.

End BigredInd.





