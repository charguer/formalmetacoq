(***************************************************************************
* Safety for STLC with References - Proof in Omni-Small-Step               *
* Arthur Chargueraud, Dec 2023                                             *
***************************************************************************)

(** The proof technique is explained in the Omni-Semantics paper (TOPLAS'23).
     http://www.chargueraud.org/research/2022/omnisemantics/omnisemantics.pdf *)

Set Implicit Arguments.
From TLC Require Import LibLN.
Require Import Fsub_Definitions Fsub_Infrastructure Fsub_Soundness.


(* ********************************************************************** *)
(** * Definition of Omni-Small-Step Semantics *)

(** The omni-small-step judgment [omnismall c P], where [P] is a postcondition,
    asserts that [c] is not stuck and that in one step it reaches a configuration
    that satisfies [P]. *)

CoInductive omnismall : trm -> (trm->Prop) -> Prop :=
  | omnismall_app_1 : forall e1 e2 P1 P,
      omnismall e1 P1 ->
      (forall e1', P1 e1' -> P (trm_app e1' e2)) ->
      omnismall (trm_app e1 e2) P
  | omnismall_app_2 : forall e1 e2 P1 P,
      value e1 ->
      omnismall e2 P1 ->
      (forall e2', P1 e2' -> P (trm_app e1 e2')) ->
      omnismall (trm_app e1 e2) P
  | omnismall_tapp : forall e1 V P1 P,
      omnismall e1 P1 ->
      (forall e1', P1 e1' -> P (trm_tapp e1' V)) ->
      omnismall (trm_tapp e1 V) P
  | omnismall_abs : forall V e1 v2 P,
      term (trm_abs V e1) ->
      value v2 ->
      P (open_ee e1 v2) ->
      omnismall (trm_app (trm_abs V e1) v2) P
  | omnismall_tabs : forall V1 V2 e1 P,
      term (trm_tabs V1 e1) ->
      type V2 ->
      P (open_te e1 V2) ->
      omnismall (trm_tapp (trm_tabs V1 e1) V2) P.

Hint Constructors omnismall.

(** [omnismall e P] is covariant in the postcondition [P]. *)

Lemma omnismall_conseq : forall e P1 P2,
  (forall e', P1 e' -> P2 e') ->
  omnismall e P1 ->
  omnismall e P2.
Proof using. introv HW Typ. inverts* Typ. Qed.


(* ********************************************************************** *)
(** * Hint to workaround a limitation of [eauto] *)

(** Custom hint: the application of a constructor for reducing under
    a context, such as [omnismall_app_1], leaves in the second subgoal
    an hypothesis of the form [(fun e' => P1_body) e1')]. Unfortunately,
    [eauto] does not simplify these beta-redexes. Hence we need a hint. *)

 Hint Extern 1 (typing ?E ?e ?T) =>
  match goal with H: (fun _ => _) _ |- _ => hnf in H end.


(* ********************************************************************** *)
(** * Soundness proof *)

(** Well typed terms are either values or can take a step,
    and for any step they can take they reach another term
    that admits the same type. *)

Lemma omnismall_soundness_result : forall e T,
  typing empty e T->
  value e \/ omnismall e (fun e' => typing empty e' T).
Proof using. (* 22 lines *)
  introv Typ. gen_eq E: (@empty bind). lets Typ': Typ.
  induction Typ; intros; subst.
  (* case: var *)
  { false* binds_empty_inv. }
  (* case: abs *)
  { left*. }
  (* case: app *)
  { right. forwards* [Val1|HR1]: IHTyp1.
    { lets (S&e3&->): (canonical_form_abs Val1 Typ1).
      lets (P1&S2&L&P2): typing_inv_abs Typ1 T1 T2. { apply* sub_reflexivity. }
      forwards* [Val2|HR2]: IHTyp2.
      { applys* omnismall_abs. pick_fresh X.
        forwards~ (K1&K2): (P2 X). rewrite* (@subst_ee_intro X).
        applys_eq (>> typing_through_subst_ee S (empty:env) (empty:env));
          try rewrite concat_empty_r; auto.
        { applys* typing_sub K1. apply_empty* sub_weakening. } } } }
  (* case: tabs *)
  { left*. }
  (* case: tapp *)
  { right. forwards* [Val1|HR1]: IHTyp.
    { lets (S&e3&->): (canonical_form_tabs Val1 Typ).
      lets (P1&S2&L&P2): typing_inv_tabs Typ T1 T2. { apply* sub_reflexivity. }
      applys* omnismall_tabs. pick_fresh X. forwards~ (K1&K2): (P2 X).
      rewrite* (@subst_te_intro X). rewrite* (@subst_tt_intro X).
      applys_eq (>> typing_through_subst_te T1 (empty:env) (empty:env));
       try rewrite map_empty; try rewrite concat_empty_r; eauto. } }
  (* case: sub *)
  { forwards* [Val1|Rede]: IHTyp. { right. applys* omnismall_conseq Rede. } }
Qed.

