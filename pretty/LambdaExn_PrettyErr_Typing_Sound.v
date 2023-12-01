(************************************************************
* Lambda-calculus with exceptions,                          *
* Pretty-big-step semantics                                 *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExn_PrettyErr.


(*==========================================================*)
(* * Typing *)

(************************************************************)
(* ** Grammar of simple types *)

CoInductive typ :=
  | typ_int : typ
  | typ_arrow : typ -> typ -> typ.


(************************************************************)
(* ** Typing judgment *)

Inductive trmtyping : env typ -> trm -> typ -> Prop :=
  | trmtyping_var : forall E x T,
      binds x T E ->
      trmtyping E (trm_var x) T
  | trmtyping_abs : forall x E U T t1,
      trmtyping (E & x ~~ U) t1 T ->
      trmtyping E (trm_abs x t1) (typ_arrow U T)
  | trmtyping_app : forall T1 T2 E t1 t2,
      trmtyping E t1 (typ_arrow T1 T2) ->
      trmtyping E t2 T1 ->
      trmtyping E (trm_app t1 t2) T2
  | trmtyping_raise : forall E t1 T,
      trmtyping E t1 typ_int ->
      trmtyping E (trm_raise t1) T
  | trmtyping_try : forall E t1 x t2 T,
      trmtyping E t1 T ->
      trmtyping (E & x~~typ_int) t2 T ->
      trmtyping E (trm_try t1 x t2) T.


Inductive valtyping : val -> typ -> Prop :=
  | valtyping_int : forall k,
      valtyping (val_int k) typ_int
  | valtyping_clo : forall E s x T1 T2 t1,
      stacktyping E s ->
      trmtyping (E & x ~~ T1) t1 T2 ->
      valtyping (val_clo s x t1) (typ_arrow T1 T2)

with stacktyping : env typ -> stack -> Prop :=
  | stacktyping_intro : forall E s,
     (forall x T, binds x T E ->
        exists v, binds x v s /\ valtyping v T) ->
     stacktyping E s.

(* Alternative definition:
  | stacktyping_empty :
     stacktyping empty
  | stacktyping_push : forall s x v T,
     stacktyping s ->
     valtyping v T ->
     stacktyping (s & x ~~ v).
*)

Inductive outtyping : out -> typ -> Prop :=
  | outtyping_ter : forall v T,
      valtyping v T ->
      outtyping (out_beh v) T
  | outtyping_exn : forall v T,
      valtyping v typ_int ->
      outtyping (out_exn v) T
  | outtyping_div : forall T,
      outtyping out_div T.

Inductive exttyping : env typ -> ext -> typ -> Prop :=
  | extyping_trm : forall E t T,
      trmtyping E t T ->
      exttyping E t T
  | exttyping_app_1 : forall E T1 T2 o1 t2,
      outtyping o1 (typ_arrow T1 T2) ->
      trmtyping E t2 T1 ->
      exttyping E (ext_app_1 o1 t2) T2
  | exttyping_app_2 : forall E T1 T2 v1 o2,
      valtyping v1 (typ_arrow T1 T2) ->
      outtyping o2 T1 ->
      exttyping E (ext_app_2 v1 o2) T2
  | extyping_raise_1 : forall E T o1,
      outtyping o1 typ_int ->
      exttyping E (ext_raise_1 o1) T
  | extyping_try_1 : forall E T o1 x t2,
      outtyping o1 T ->
      trmtyping (E & x ~~ typ_int) t2 T ->
      exttyping E (ext_try_1 o1 x t2) T.


(*==========================================================*)
(* * Proofs *)

Lemma stacktyping_push : forall E s x v T,
  stacktyping E s ->
  valtyping v T ->
  stacktyping (E & x ~~ T) (s & x ~~ v).
Proof.
  introv M H. inverts M as M.
  constructors. introv B. binds_cases B.
  forwards* (v'&?&?): M.
  subst*.
Qed.

Lemma stacktyping_binds : forall E x s v T,
  stacktyping E s -> binds x v s -> binds x T E ->
  valtyping v T.
Proof.
  introv M Bv BT. inverts M as M.
  forwards* (v'&Bv'&?): M. unfolds binds.
  asserts: (v = v'). congruence. subst*.
Qed.

Lemma stacktyping_elim_1 : forall E x s T,
  stacktyping E s -> binds x T E -> exists v, binds x v s.
Proof.
  introv M B. inverts M as M. forwards* (?&?&?): M.
Qed.

Hint Resolve stacktyping_push stacktyping_binds.


(************************************************************)
(* ** Soundness *)

Hint Constructors one abort outtyping exttyping valtyping.

Lemma abort_outyping : forall o T T',
  abort o -> outtyping o T -> outtyping o T'.
Proof.
  introv A M. inverts M; inverts A; auto.
Qed.

Lemma soundness_ind : forall E s e o T,
  red s e o ->
  stacktyping E s ->
  exttyping E e T ->
  outtyping o T.
Proof.
  introv R. gen E T. induction R; introv S M.
  inverts M as M. inverts* M.
  inverts M as M. inverts* M.
  inverts M as M. inverts* M.
  inverts M as M1 M2. forwards*: abort_outyping H.
  inverts M as M. inverts* M.
  inverts M as M1 M2. forwards*: abort_outyping H.
  inverts M as M1 M2. inverts M2. inverts* M1.
  inverts M as M. inverts* M.
  inverts M as M. inverts* M.
  inverts M as M. inverts* M.
  inverts M as M. inverts* M.
  inverts M as M. inverts* M.
  inverts M as M1 M2. forwards*: abort_outyping H.
  inverts M as M. inverts* M.
  false (rm H). inverts M as.
    introv M. inverts* M. forwards* (?&?): stacktyping_elim_1.
    introv M1 M2. inverts* M1.
    introv M1 M2. inverts M1. inverts* M2.
    introv M1. inverts* M1.
    introv M1 M2. inverts* M1.
Qed.
