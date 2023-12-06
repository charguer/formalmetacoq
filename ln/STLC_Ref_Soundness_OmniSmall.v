(***************************************************************************
* Safety for STLC with References - Proof in Omni-Small-Step               *
* Arthur Chargueraud, Dec 2023                                             *
***************************************************************************)

(** The proof is explained in the Omni-Semantics paper (TOPLAS'23).
     http://www.chargueraud.org/research/2022/omnisemantics/omnisemantics.pdf *)

Set Implicit Arguments.
Require Import STLC_Ref_Soundness_Common.


(* ********************************************************************** *)
(** * Definition of Omni-Small-Step Semantics *)

(** The omni-small-step judgment [omnismall c P], where [P] is a postcondition,
    asserts that [c] is not stuck and that in one step it reaches a configuration
    that satisfies [P]. *)

CoInductive omnismall : conf -> (conf->Prop) -> Prop :=
  | omnismall_beta : forall mu t1 t2 P,
      sto_ok mu ->
      term (trm_abs t1) ->
      value t2 ->
      P (t1 ^^ t2, mu) ->
      omnismall (trm_app (trm_abs t1) t2, mu) P
  | omnismall_ref : forall mu t1 P,
      sto_ok mu ->
      value t1 ->
      (forall l, l # mu -> P (trm_loc l, (mu & l ~ t1))) ->
      omnismall (trm_ref t1, mu) P
  | omnismall_get : forall mu l t P,
      sto_ok mu ->
      binds l t mu ->
      P (t, mu) ->
      omnismall (trm_get (trm_loc l), mu) P
  | omnismall_set : forall mu l t2 P,
      sto_ok mu ->
      value t2 ->
      P (trm_unit, mu & l ~ t2) ->
      omnismall (trm_set (trm_loc l) t2, mu) P
  | omnismall_rand : forall mu n P,
      (forall m, 0 <= m < max n 1 -> P ((trm_int m), mu)) ->
      omnismall (trm_rand (trm_int n), mu) P

  | omnismall_app_1 : forall mu t1 t2 P1 P,
      omnismall (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> P (trm_app t1' t2, mu')) ->
      omnismall (trm_app t1 t2, mu) P
  | omnismall_app_2 : forall mu t1 t2 P1 P,
      value t1 ->
      omnismall (t2, mu) P1 ->
      (forall t2' mu', P1 (t2',mu') -> P (trm_app t1 t2', mu')) ->
      omnismall (trm_app t1 t2, mu) P
  | omnismall_ref_1 : forall mu t1 P1 P,
      omnismall (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> P (trm_ref t1', mu')) ->
      omnismall (trm_ref t1, mu) P
  | omnismall_get_1 : forall mu t1 P1 P,
      omnismall (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> P (trm_get t1', mu')) ->
      omnismall (trm_get t1, mu) P
  | omnismall_set_1 : forall mu t1 t2 P1 P,
      omnismall (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> P (trm_set t1' t2, mu')) ->
      omnismall (trm_set t1 t2, mu) P
  | omnismall_set_2 : forall mu t1 t2 P1 P,
      value t1 ->
      omnismall (t2, mu) P1 ->
      (forall t2' mu', P1 (t2',mu') -> P (trm_set t1 t2', mu')) ->
      omnismall (trm_set t1 t2, mu) P
  | omnismall_rand_1 : forall mu t1 P1 P,
      omnismall (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> P (trm_rand t1', mu')) ->
      omnismall (trm_rand t1, mu) P.

(** The definition above may be considered as the reference semantics,
    in replacement of the standard small-step judgment [c --> c'].
    The folder '/omni' of this repository contains a proof of the
    following equivalence between small-step and omni-small-step. *)

Parameter omnismall_equiv_red : forall c P,
  omnismall c P <->
    (   (exists c', c --> c')
     /\ (forall c', c --> c' -> P c')).


(* ********************************************************************** *)
(** * Postconditions for Types *)

(** Configurations associated with a given type and store typing *)

Definition post (Y:phi) (T:typ) : conf->Prop :=
  fun '(t,mu) =>
    exists Y', extends Y Y'
             /\ Y' |== mu
             /\ empty ! Y' |= t ~: T.

(** Postcondition holds of a well-typed state *)

Lemma post_current : forall Y mu t T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  post Y T (t,mu).
Proof using.
  introv HS HT. exists Y. splits*.
Qed.

Hint Resolve post_current.


(* ********************************************************************** *)
(** * Statement of Omni-Small-Step Soundness *)

(** The goal is to prove omnismall-soundness: well typed configurations
    are either made of a value or can take a step towards a configuration
    that satisfies the same type, for an extended store typing. *)

Definition omnismall_soundness := forall mu t Y T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  value t \/ omnismall (t,mu) (post Y T).


(* ********************************************************************** *)
(** * Soundness proof *)

Hint Constructors typing.

Ltac sound_ctx E := (* tactic for context evaluation rules *)
  let Y' := fresh "Y'" in
  applys* E; try (introv (Y'&?&?&?); exists* Y').

Lemma omnismall_soundness_result :
  omnismall_soundness.
Proof using. (* 34 lines *)
  introv HS HT. gen_eq E: (@empty typ). gen mu.
  induction HT; intros; subst; try solve [left* ].
  { false* binds_empty_inv. }
  { left*. constructors.
    { applys term_abs L. intros x Hx. forwards*: H x. } }
  { right. forwards* [Val1|HR1]: IHHT1.
    { forwards* [Val2|HR2]: IHHT2.
      { inversions HT1; inversions Val1. applys* omnismall_beta.
        { applys* post_current.
          pick_fresh x. rewrite* (@subst_intro x).
          apply_empty* typing_subst. } }
      { sound_ctx omnismall_app_2. } }
    { sound_ctx omnismall_app_1. } }
  { right. forwards* [Val1|HR1]: IHHT.
    { applys* omnismall_ref. intros l Hl. exists (Y & l ~ T).
      lets: (proj32 HS) Hl. splits*. { applys* sto_typing_push. } }
    { sound_ctx omnismall_ref_1. } }
  { right. forwards* [Val1|HR1]: IHHT.
    { inverts HT; inverts Val1. destruct~ ((proj33 HS) l0 T) as (t&Valt&Hast&Typt).
      applys* omnismall_get. }
    { sound_ctx omnismall_get_1. } }
  { right. forwards* [Val1|HR1]: IHHT1.
    { forwards* [Val2|HR2]: IHHT2.
      { inverts HT1; inverts Val1. destruct~ ((proj33 HS) l0 T) as (t&Valt&Hast&Typt).
        applys* omnismall_set. exists Y.
        destruct HS as (StoOk&Dom&Map). splits*.
        { splits*. intros l T' HB. tests: (l = l0).
          { exists t2. rewrites* (>> binds_functional T' T HB). }
          { destruct (Map _ _ HB) as (t'&Has&Typ). exists* t'. } } }
      { sound_ctx omnismall_set_2. } }
    { sound_ctx omnismall_set_1. } }
  { right. forwards* [Val1|HR1]: IHHT.
    { inverts HT; inverts Val1. applys* omnismall_rand. }
    { sound_ctx omnismall_rand_1. } }
Qed.


(* ********************************************************************** *)
(** * Generic result: type soundness follows from omnismall-soudness *)

(** We next give a generic proof that [omnismall_soundness_induction]
    entails type soundness, as defined in file [STLC_Ref_Definitions]:
    starting from a well-typed configuration, all accessible
    configurations are either final or reducible. *)

Lemma soundness_of_omnismall_soundness :
  omnismall_soundness ->
  soundness.
Proof using.
  introv Sou. intros (t,mu) (Y&T&HT&HY). introv HR.
  gen_eq c: (t,mu). gen t mu Y T. induction HR; intros; subst.
  { intros. forwards [HV|M]: Sou HY HT.
    { left*. }
    { right. rewrite* omnismall_equiv_red in M. } }
  { lets [HV|M]: Sou HY HT.
    { inverts HV; inverts H. }
    { rewrite omnismall_equiv_red in M. destruct M as (M1&M2).
      specializes M2 H. destruct c2 as (t2,mu2).
      destruct M2 as (Y'&EY'&HY'&HT'). applys* IHHR HT'. } }
Qed.
