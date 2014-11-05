(***************************************************************************
* Simply Typed Lambda Calculus: Typing is Decidabl                         *
* Brian Aydemir & Arthur Charguéraud & Stephanie Weirich, July 2007        *
***************************************************************************)

(** IN NON CONSTRUCTIVE LOGIC THIS IS NOT RELEVANT *)

Set Implicit Arguments.
Require Import Decidable Metatheory
  STLC_Dec_Definitions 
  STLC_Dec_Infrastructure
  STLC_Dec_Soundness.

(*
Library Coq.Logic.Decidable defines:
  Definition decidable (P:Prop) := P \/ ~ P.
*)

(** Equality on types is decidable *)

Lemma eq_typ_dec : forall (T T' : typ), 
  sumbool (T = T') (T <> T').
Proof.
  unfold decidable. decide equality. lets: eq_var_dec. jauto.
Qed.

(** Existence of a binding in the environment is decidable *)

Lemma binds_typ_dec : forall x (T : typ) E, 
  decidable (binds x T E).
Proof.
  intros. apply binds_dec. apply eq_typ_dec.
Qed.

(** Renaming lemma for the typing relation *)

Lemma typing_rename : forall x y E t T U,
  x \notin (fv t \u dom E) -> 
  y \notin (fv t \u dom E) ->
  (E & x ~ U) |= (t ^ x) ~: T ->
  (E & y ~ U) |= (t ^ y) ~: T.
Proof.
  introv Frx Fry Typ.
  asserts* K (ok (E & x ~ U)). inversions K.
  destruct (x == y). subst*.
  rewrite~ (@subst_intro x).
  apply_empty* typing_subst.
  poses P (@typing_weaken (x ~ U) E (y ~ U)). 
   simpls. apply* P; env_fix.
  apply* ok_push.
  apply* typing_var.
Qed.

(** Typing is decidable *)

Lemma typing_dec' : forall t E T, term t -> ok E -> 
  decidable (E |= t ~: T).
Proof.
  introv Wf Ok. gen T E.
  induction Wf; intros.
  (* case var *)
  destruct (@binds_typ_dec x T E).
    left. apply* typing_var.
    right. intros K. inversions* K.
  (* case abs *)
  destruct T. right. intros K. inversions K.
    pick_fresh x.
    forward~ (H0 x) as H1. clear H0.
    forward~ (H1 T2 (E & x ~ T1)) as [Typ1 | NTyp1 ]. clear H1.
      left. apply_fresh* typing_abs as y. apply* (@typing_rename x). 
      right. intros Typ1. inversions Typ1. apply NTyp1.
        (* picking y now *)
        pick_fresh y. forward~ (H4 y) as K.
        (* last, apply renaming *) 
        apply* (@typing_rename y).
  (* case app *)
  forward~ (IHWf1 (typ_arrow T T0) E) as [Typ1 | NTyp1]. clear IHWf1.
    forward~ (IHWf2 T E) as [Typ2 | NTyp2]. clear IHWf2.
      left. apply* typing_app.
      right. intros K. inversions* K. 
    right. intros K. inversions* K. 
Qed.


