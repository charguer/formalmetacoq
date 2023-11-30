(***************************************************************************
* Safety for STLC with References - Proof in Omni-Big-Step                 *
* Arthur Chargueraud, Dec 2023                                             *
***************************************************************************)

(** The proof is explained in the Omni-Semantics paper (TOPLAS'23).
     http://www.chargueraud.org/research/2022/omnisemantics/omnisemantics.pdf *)

Set Implicit Arguments.
Set Implicit Arguments.
From TLC Require Import LibLN LibNat.
Require Import STLC_Ref_Definitions STLC_Ref_Infrastructure.



Hint Constructors typing.

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F Y t T,
   (E & G) ! Y |= t ~: T ->
   ok (E & F & G) ->
   (E & F & G) ! Y |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F E Y t T z u U,
  (E & z ~ U & F) ! Y |= t ~: T ->
  E ! Y |= u ~: U ->
  (E & F) ! Y |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; introv Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
Qed.

(** Typing is preserved by an extension of store typing. *)

Lemma typing_stability : forall Y E Y' t T,
  E ! Y |= t ~: T ->
  extends Y Y' ->
  E ! Y' |= t ~: T.
Proof.
  introv Typ Ext. induction* Typ.
Qed.

Hint Resolve typing_stability.

(** Store typing preserved by allocation of a well-typed term. *)

Lemma sto_typing_push : forall Y mu l t T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  l # mu -> l # Y ->
  (Y & l ~ T) |== (mu & l ~ t).
Proof.
  unfold sto_typing. introv [StoOk [Dom Ext]]. splits 3.
    auto.
    intros l0 Fr. simpl_dom. lets: (Dom l0).
      asserts* Fr2: (l <> l0). asserts* Fr3: (l0 # Y). auto.
    intros l' T' Has. binds_cases Has.
      destruct (Ext _ _ B) as [t' [Hast' Typt']].
       exists* t'.
      subst. exists* t.
Qed.



(** Omni-Small-Step semantics [omnismall c Y]. *)

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


Hint Constructors omnismall typing.

(** Postcondition associated with a type *)

Definition post (Y:phi) (T:typ) : conf->Prop :=
  fun '(t,mu) =>
    exists Y', extends Y Y'
             /\ Y' |== mu
             /\ empty ! Y' |= t ~: T.

Lemma post_current : forall Y mu t T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  post Y T (t,mu).
Proof using.
  introv HS HT. exists Y. splits*.
Qed.

Hint Resolve post_current.

(** Soundness proof *)

Definition omnismall_soundness :=
  forall mu t Y T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  value t \/ omnismall (t,mu) (post Y T).

Ltac sound_ctx E :=
  let Y' := fresh "Y'" in
  applys* E; try (introv (Y'&?&?&?); exists* Y').

Lemma omnismall_soundness_induction :
  omnismall_soundness.
Proof using.
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
    { inverts HT; inverts Val1. destruct~ ((proj33 HS) l0 T) as [t [Hast Typt]].
      applys* omnismall_get. }
    { sound_ctx omnismall_get_1. } }
  { right. forwards* [Val1|HR1]: IHHT1.
    { forwards* [Val2|HR2]: IHHT2.
      { inverts HT1; inverts Val1. destruct~ ((proj33 HS) l0 T) as [t [Hast Typt]].
        applys* omnismall_set. exists Y.
        destruct HS as [StoOk [Dom Map]]. splits*.
        { splits*. intros l T' HB. tests: (l = l0).
          { exists t2. rewrites* (>> binds_functional T' T HB). }
          { destruct (Map _ _ HB) as [t' [Has Typ]]. exists* t'. } } }
      { sound_ctx omnismall_set_2. } }
    { sound_ctx omnismall_set_1. } }
  { right. forwards* [Val1|HR1]: IHHT.
    { inverts HT; inverts Val1. applys* omnismall_rand. }
    { sound_ctx omnismall_rand_1. } }
Qed.

(** We next give a generic proof that [omnismall_soundness_induction]
    entails [type soundness], under the assumption that the omni-small-step
    judgment admits the expected postretation w.r.t. the standard
    small-step judgment. *)

Parameter omnismall_characterization : forall c P,
  omnismall c P <->
    (   (exists c', c --> c')
     /\ (forall c', c --> c' -> P c')).

(** Statement of the soundness property using omni-small-step. *)

Lemma soundness_of_omnismall_soundness :
  omnismall_soundness ->
  type_soundness.
Proof using.
  introv Sou. intros (t,mu) (Y&T&HT&HY). introv HR.
  gen_eq c: (t,mu). gen t mu Y T. induction HR; intros; subst.
  { intros. forwards [HV|M]: Sou HY HT.
    { left*. }
    { right. rewrite* omnismall_characterization in M. } }
  { lets [HV|M]: Sou HY HT.
    { inverts HV; inverts H. }
    { rewrite omnismall_characterization in M. destruct M as (M1&M2).
      specializes M2 H. destruct c2 as (t2,mu2).
      destruct M2 as (Y'&EY'&HY'&HT'). applys* IHHR HT'. } }
Qed.





(** Value or variable predicate---for A-normal form. *)

Definition val_or_var (t:trm) : Prop :=
     value t
  \/ (exists x, t = trm_fvar x).

(** Typing relation *)

Reserved Notation "E ! Y |= t ~: T" (at level 69).

Inductive typing : env -> phi -> trm -> typ -> Prop :=
  | typing_var : forall E Y x T,
      ok E ->
      binds x T E ->
      E ! Y |= (trm_fvar x) ~: T
  | typing_abs : forall L E Y U T t1,
      (forall x, x \notin L -> (E & x ~ U) ! Y  |= t1 ^ x ~: T) ->
      E ! Y |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_app : forall T1 T2 E Y t1 t2,
      val_or_var t1 ->
      E ! Y |= t1 ~: (typ_arrow T1 T2) -> E ! Y  |= t2 ~: T1 ->
      E ! Y  |= (trm_app t1 t2) ~: T2
  | typing_unit : forall E Y,
      ok E ->
      E ! Y |= trm_unit ~: typ_unit
  | typing_int : forall E Y n,
      ok E ->
      E ! Y |= (trm_int n) ~: typ_int
  | typing_loc : forall E Y l T,
      ok E ->
      binds l T Y ->
      E ! Y |= (trm_loc l) ~: (typ_ref T)
  | typing_ref : forall E Y t1 T,
      val_or_var t1 ->
      E ! Y |= t1 ~: T ->
      E ! Y |= (trm_ref t1) ~: (typ_ref T)
  | typing_get : forall E Y t1 T,
      val_or_var t1 ->
      E ! Y |= t1 ~: (typ_ref T) ->
      E ! Y |= (trm_get t1) ~: T
  | typing_set : forall E Y t1 t2 T,
      val_or_var t1 ->
      val_or_var t2 ->
      E ! Y |= t1 ~: (typ_ref T) ->
      E ! Y |= t2 ~: T ->
      E ! Y |= (trm_set t1 t2) ~: typ_unit
  | typing_rand : forall E Y t1,
      val_or_var t1 ->
      E ! Y |= t1 ~: typ_int ->
      E ! Y |= (trm_rand t1) ~: typ_int

where "E ! Y |= t ~: T" := (typing E Y t T).

(** Typing judgment for stores *)

Definition sto_typing Y mu :=
     sto_ok mu
  /\ (forall l, l # mu -> l # Y)
  /\ (forall l T, binds l T Y ->
        exists t, binds l t mu
               /\ empty ! Y |= t ~: T).

Notation "Y |== mu" := (sto_typing Y mu) (at level 68).


(* ********************************************************************** *)
(** ** Property of [val_or_var] *)

(** [val_of_var] is stable by substitution. *)

Lemma subst_val_or_var : forall t z u,
  value u -> val_or_var t -> val_or_var ([z ~> u]t).
Proof using.
  introv HT [HV|(x&->)].
  { left. applys* subst_value. }
  { simpl. case_var. { left*. } { right*. } }
Qed.

Hint Extern 1 (val_or_var ([_ ~> _]_)) => apply subst_val_or_var.


(** Values and variables don't reduce. *)

Lemma red_val_or_var_inv : forall t mu c,
  val_or_var t ->
  (t,mu) --> c ->
  False.
Proof using.
  introv Ht Hc. inverts Ht as.
  { introv Hv. inverts Hv; inverts Hc. }
  { introv (x&->). inverts Hc. }
Qed.

(** Values-or-variables well-typed in the empty contexts are values. *)

Lemma value_of_not_var : forall t S T,
  typing empty S t T ->
  val_or_var t ->
  value t.
Proof using.
  introv HT [Hv|(x&->)].
  { auto. }
  { inverts HT as. intros K E. false binds_empty_inv E. }
Qed.





(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Weakening, Substitution, and Extension lemmas *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F Y t T,
   (E & G) ! Y |= t ~: T ->
   ok (E & F & G) ->
   (E & F & G) ! Y |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F E Y t T z u U,
  value u ->
  (E & z ~ U & F) ! Y |= t ~: T ->
  E ! Y |= u ~: U ->
  (E & F) ! Y |= [z ~> u]t ~: T.
Proof.
  introv Hu Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; introv Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  eauto 9.
  eauto 9.
  eauto 9.
Qed.

(** Typing is preserved by an extension of store typing. *)

Lemma typing_stability : forall Y E Y' t T,
  E ! Y |= t ~: T ->
  extends Y Y' ->
  E ! Y' |= t ~: T.
Proof.
  introv Typ Ext. induction* Typ.
Qed.

Hint Resolve typing_stability.

(** Store typing preserved by allocation of a well-typed term. *)

Lemma sto_typing_push : forall Y mu l t T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  l # mu -> l # Y ->
  (Y & l ~ T) |== (mu & l ~ t).
Proof.
  unfold sto_typing. introv [StoOk [Dom Ext]]. splits 3.
    auto.
    intros l0 Fr. simpl_dom. lets: (Dom l0).
      asserts* Fr2: (l <> l0). asserts* Fr3: (l0 # Y). auto.
    intros l' T' Has. binds_cases Has.
      destruct (Ext _ _ B) as [t' [Hast' Typt']].
       exists* t'.
      subst. exists* t.
Qed.






(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Omni-Big-Step Soundness Proof *)

(* ########################################################### *)
(** ** Entailment on postconditions *)

Definition himpl (H1 H2:conf->Prop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.


(* ########################################################### *)
(** ** Definition of Omni-Big-Step *)

(** Judgment [omnibig c Q]. Here [Q] is a predicate over configurations,
    but in practice in contains only values. *)

CoInductive coomnibig : conf -> (conf->Prop) -> Prop :=
  | coomnibig_val : forall c Q,
      conf_value c ->
      Q c ->
      coomnibig c Q
  | coomnibig_beta : forall mu t1 t2 Q,
      sto_ok mu ->
      term (trm_abs t1) ->
      value t2 ->
      coomnibig (t1 ^^ t2, mu) Q ->
      coomnibig (trm_app (trm_abs t1) t2, mu) Q
  | coomnibig_rand : forall mu n Q,
      (forall m, 0 <= m < max n 1 -> Q ((trm_int m), mu)) ->
      coomnibig (trm_rand (trm_int n), mu) Q
  | coomnibig_ref : forall mu t1 Q,
      sto_ok mu ->
      value t1 ->
      (forall l, l # mu ->
        Q (trm_loc l, (mu & l ~ t1))) ->
      coomnibig (trm_ref t1, mu) Q
  | coomnibig_get : forall mu l t Q,
      sto_ok mu ->
      binds l t mu ->
      Q (t, mu) ->
      coomnibig (trm_get (trm_loc l), mu) Q
  | coomnibig_set : forall mu l t2 Q,
      sto_ok mu ->
      value t2 ->
      Q (trm_unit, mu & l ~ t2) ->
      coomnibig (trm_set (trm_loc l) t2, mu) Q
  | coomnibig_app_2 : forall mu t1 t2 Q1 Q,
      value t1 ->
      ~ value t2 ->
      coomnibig (t2, mu) Q1 ->
      (forall t2' mu', Q1 (t2',mu') -> coomnibig (trm_app t1 t2', mu') Q) ->
      coomnibig (trm_app t1 t2, mu) Q.

(** [coomnibig] is covariant in the postcondition (omni-big-conseqence) *)

Lemma coomnibig_conseq : forall c Q1 Q2,
  coomnibig c Q1 ->
  Q1 ==> Q2 ->
  coomnibig c Q2.
Proof using.
  introv M W. unfolds himpl. gen c Q1 Q2. cofix IH.
  intros. inverts M; try solve [ constructors* ].
  { applys* coomnibig_get. }
  { applys* coomnibig_app_2. }
Qed.

(** We reuse [post] from the previous section, and
    add two lemmas. *)

Lemma extends_trans : forall Y2 Y1 Y3,
  extends Y1 Y2 ->
  extends Y2 Y3 ->
  extends Y1 Y3.
Proof using. unfolds extends. autos*. Qed.

Lemma post_extends : forall Y Y' T,
  extends Y Y' ->
  (post Y' T) ==> (post Y T).
Proof using.
  introv EY. intros (t,mu) (Y''&EY'&Hs&Hv).
  exists Y''. splits*. { applys* extends_trans Y'. }
Qed.

(** Type soundness proof *)

(** Note: if we try to prove directly the statement:

[[
    Lemma coomnibig_soundness_coinduction : forall t mu Y T,
      Y |== mu ->
      empty ! Y |= t ~: T ->
      coomnibig (t,mu) (post Y T).
]]

  then Cpq's guard checker is not happy because we apply the consequence
  rule for [coomnibig] needs to be applied before the coinduction hypothesis.
  Hence, we need to tweak the statement slightly for the coinduction,
  then derive the desired result. *)

Definition coomnibig_soundness := forall t mu Y T Q,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  (post Y T ==> Q) ->
  coomnibig (t,mu) Q.

Lemma coomnibig_soundness_coinduction :
  coomnibig_soundness.
Proof using.
  unfolds. cofix IH. introv HS HT HQ. inverts HT as.
  { introv HK HT1. false* binds_empty_inv. }
  { intros L M. applys* coomnibig_val. hnf.
    constructors. applys term_abs L. intros x Hx. forwards*: M x. }
  { introv HV1 M1 M2. forwards V1: value_of_not_var M1 HV1.
    inverts V1; inverts M1. tests C: (value t2).
    { applys* coomnibig_beta. applys* IH. pick_fresh x.
      rewrite* (@subst_intro x). apply_empty* typing_subst. }
    { applys* coomnibig_app_2 (post Y T1).
      { applys* IH. hnfs*. }
      { introv (Y'&EY'&HY'&HT'). applys* IH. applys himpl_trans HQ.
        applys post_extends EY'. } } }
  { intros K. applys* coomnibig_val. }
  { intros K. applys* coomnibig_val. }
  { intros K B. applys* coomnibig_val. }
  { intros HV1 M1. forwards V1: value_of_not_var M1 HV1.
    applys* coomnibig_ref.
    { intros l Hl. applys HQ. applys* post_ref. } }
  { introv HV1 M1. forwards V1: value_of_not_var M1 HV1.
    inverts V1; inverts M1.
    destruct~ ((proj33 HS) l0 T) as [t [Hast Typt]].
    applys* coomnibig_get. }
  { introv HV1 HV2 M1 M2. forwards V2: value_of_not_var M2 HV2.
    forwards V1: value_of_not_var M1 HV1. inverts V1; inverts M1.
    applys* coomnibig_set. applys HQ. applys* post_set. }
  { introv HV1 M1. forwards V1: value_of_not_var M1 HV1.
     inverts V1; inverts M1. applys* coomnibig_rand.
     (* details: intros. applys HQ. unfolds. exists Y. splits*. *)  }
Qed.

(** The original statement is a trivial consequence. *)

Lemma coomnibig_soundness_result : forall t mu Y T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  coomnibig (t,mu) (post Y T).
Proof using.
  introv HS HT. applys* coomnibig_soundness_coinduction. hnfs*.
Qed.

(** Note that the statement over which we carried the coinduction
    is equivalent, not stronger. *)

Lemma coomnibig_soundness_coinduction' :
  coomnibig_soundness.
Proof using.
  unfolds. introv HS HT HQ. applys coomnibig_conseq.
  { applys* coomnibig_soundness_result. }
  { auto. }
Qed.

(** We next give a generic proof that [omnibig_soundness_coinduction]
    entails [type soundness]. *)

(** In the file Omnisemantics.v, we proved in lemma [safe_of_coomnibig] that
    [coomnibig c Q] for any [Q] entails [safe Q], for a coinductive-big-step
    definition of safety, which we proved equivalent to the small-step
    characterization of safety used in the present file (lemma [ssafe_eq_safe]).
    To avoid reproducing all the development here, let us simply assume in
    this file the property [safe_of_coomnibig]. *)

Parameter safe_of_coomnibig : forall c Q,
  coomnibig c Q ->
  safe c.

(** We show that the result established by coinduction indeed
    entails type soundess. *)

Lemma soundness_of_coomnibig_soundness :
  coomnibig_soundness ->
  type_soundness.
Proof using.
  intros HS (t,mu) (Y&T&HY&HT). applys* safe_of_coomnibig.
  applys* coomnibig_soundness_result.
Qed.


