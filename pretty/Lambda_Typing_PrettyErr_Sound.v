(************************************************************
* Lambda-calculus,                                          *
* Type soundness proof                                      *
* using pretty-big-step semantics with error rules          *
*************************************************************)

Set Implicit Arguments.
Require Import Lambda_PrettyErr Lambda_Typing.
From TLC Require Import LibLN LibInt.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Proof of type soundness *)

(** Hints *)

Hint Constructors one typing.
Hint Extern 1 (_ < _) => math.
Hint Extern 1 (~ one _ -> exists _, _) =>
  let H := fresh in intros H; false H.

(** Regularity lemma *)

Lemma typing_ok : forall E t T,
  typing E t T -> ok E.
Proof. introv H. induction* H. Qed.

(** Weakening for values *)

Lemma typing_val_weaken : forall E v T,
  typing empty v T -> ok E -> typing E v T.
Proof. introv H. inverts* H. Qed.

(** Substitution lemma *)

Lemma typing_subst : forall E x T U t v,
  typing empty v U ->
  typing (empty & single x U & E) t T ->
  typing E (subst x v t) T.
Proof.
  introv Tv Tt. inductions Tt; simpl.
  constructors*.
  constructors*.
  cases_if.
    binds_cases H0.
      false* binds_empty_inv.
      subst. applys* typing_val_weaken.
      lets (?&?): (ok_middle_inv H).
       false~ (binds_fresh_inv B0).
    binds_cases H0.
      false* binds_empty_inv.
      constructors~.
  cases_if.
    false. lets N: typing_ok Tt.
     rewrite <- concat_assoc in N.
     lets (?&M): (ok_middle_inv N).
     simpl_dom. notin_false.
    forwards*: IHTt. rewrite* concat_assoc.
  constructors*.
Qed.

(************************************************************)
(* ** Typing judgment for extended terms *)

Definition trmtyping t T :=
  typing empty t T.

Inductive outtyping : out -> typ -> Prop :=
  | outtyping_ter : forall v T,
      trmtyping v T ->
      outtyping (out_ret v) T
  | outtyping_div : forall T,
      outtyping out_div T.

Inductive exttyping : ext -> typ -> Prop :=
  | extyping_trm : forall t T,
      trmtyping t T ->
      exttyping t T
  | exttyping_app_1 : forall T1 T2 o1 t2,
      outtyping o1 (typ_arrow T1 T2) ->
      trmtyping t2 T1 ->
      exttyping (ext_app_1 o1 t2) T2
  | exttyping_app_2 : forall T1 T2 v1 o2,
      trmtyping v1 (typ_arrow T1 T2) ->
      outtyping o2 T1 ->
      exttyping (ext_app_2 v1 o2) T2.


(************************************************************)
(* ** Soundness *)

Hint Constructors outtyping exttyping.
Hint Unfold trmtyping.

(*
Lemma red_not_div : forall t o,
  red (ext_trm t) o -> o <> out_div.
Admitted.
Hint Resolve red_not_div.
*)

Lemma abort_outyping : forall o T T',
  abort o -> outtyping o T -> outtyping o T'.
Proof.
  introv A M. inverts M; inverts A. auto.
Qed.

Lemma soundness_ind : forall e o T,
  red e o -> exttyping e T -> outtyping o T.
Proof.
  introv R. gen T. induction R; introv M.
  inverts M as M. auto.
  inverts M as M. inverts* M.
  inverts M as M. inverts* M.
  inverts M as M1 M2. forwards*: abort_outyping H.
  inverts M as M1 M2. inverts* M1.
  inverts M as  M1 M2. forwards*: abort_outyping H.
  inverts M as M1 M2. inverts M2. inverts* M1.
   applys IHR. constructors. apply_empty* typing_subst.
  false (rm H). inverts M as.
    introv M. inverts M.
      eauto.
      eauto.
      false* binds_empty_inv.
      eauto.
      eauto.
    introv M1 M2. inverts* M1.
    introv M1 M2. inverts M1. inverts* M2.
Qed.

(** Soundness theorem:
    Well-typed terms don't end up in an error *)

Lemma soundness : forall t T,
  typing empty t T -> ~ red t out_err.
Proof. introv M R. forwards* K: soundness_ind R. inverts K. Qed.


