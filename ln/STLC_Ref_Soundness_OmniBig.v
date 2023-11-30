(***************************************************************************
* Safety for STLC with References - Proof in Omni-Big-Step                 *
* Arthur Chargueraud, Dec 2023                                             *
***************************************************************************)

(** The proof is explained in the Omni-Semantics paper (TOPLAS'23).
     http://www.chargueraud.org/research/2022/omnisemantics/omnisemantics.pdf *)


Set Implicit Arguments.
Require Import STLC_Ref_Soundness_Common.
Implicit Types Y : phi.

(* ********************************************************************** *)
(** * Definition of Co-Omni-Big-Step Semantics *)

(** The coinductive omni-big-step judgment [omnibig c P], where [P] is a
    postcondition, asserts that all possibly evaluations of [c] are never stuck
    and can only reach final configurations that satisfy [P].
    The judgment is coinductive: it captures partial correctness.
    Technically, this judgment follows the pretty-big-step presentation:
    each rule evaluates exactly one subterm, replacing this subterm with a value. *)

CoInductive coomnibig : conf -> (conf->Prop) -> Prop :=
  | coomnibig_val : forall c P,
      value (fst c) ->
      P c ->
      coomnibig c P
  | coomnibig_beta : forall mu t1 t2 P,
      sto_ok mu ->
      term (trm_abs t1) ->
      value t2 ->
      coomnibig (t1 ^^ t2, mu) P ->
      coomnibig (trm_app (trm_abs t1) t2, mu) P
  | coomnibig_rand : forall mu n P,
      (forall m, 0 <= m < max n 1 -> P ((trm_int m), mu)) ->
      coomnibig (trm_rand (trm_int n), mu) P
  | coomnibig_ref : forall mu t1 P,
      sto_ok mu ->
      value t1 ->
      (forall l, l # mu ->
        P (trm_loc l, (mu & l ~ t1))) ->
      coomnibig (trm_ref t1, mu) P
  | coomnibig_get : forall mu l t P,
      sto_ok mu ->
      binds l t mu ->
      P (t, mu) ->
      coomnibig (trm_get (trm_loc l), mu) P
  | coomnibig_set : forall mu l t2 P,
      sto_ok mu ->
      value t2 ->
      P (trm_unit, mu & l ~ t2) ->
      coomnibig (trm_set (trm_loc l) t2, mu) P

  | coomnibig_app_1 : forall mu t1 t2 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_app t1' t2, mu') P) ->
      coomnibig (trm_app t1 t2, mu) P
  | coomnibig_app_2 : forall mu t1 t2 P1 P,
      value t1 ->
      ~ value t2 ->
      coomnibig (t2, mu) P1 ->
      (forall t2' mu', P1 (t2',mu') -> coomnibig (trm_app t1 t2', mu') P) ->
      coomnibig (trm_app t1 t2, mu) P
  | coomnibig_ref_1 : forall mu t1 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_ref t1', mu') P) ->
      coomnibig (trm_ref t1, mu) P
  | coomnibig_get_1 : forall mu t1 P1 P,
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_get t1', mu') P) ->
      coomnibig (trm_get t1, mu) P
  | coomnibig_set_1 : forall mu t1 t2 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_set t1' t2, mu') P) ->
      coomnibig (trm_set t1 t2, mu) P
  | coomnibig_set_2 : forall mu t1 t2 P1 P,
      value t1 ->
      ~ value t2 ->
      coomnibig (t2, mu) P1 ->
      (forall t2' mu', P1 (t2',mu') -> coomnibig (trm_set t1 t2', mu') P) ->
      coomnibig (trm_set t1 t2, mu) P
  | coomnibig_rand_1 : forall mu t1 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_rand t1', mu') P) ->
      coomnibig (trm_rand t1, mu) P.

(** The folder '/omni' of this repository contains a proof establishing
    that omni-big-step entails the safety property expressed in small-step.
    This proof is explained near the end of the chapter "Triples" in the
    course "Separation Logic Foundations" of the Software Foundations series. *)


(* ********************************************************************** *)
(** * Statement *)

(** Postcondition associated with a well-typed configuration;
    in big-step, postconditions are restricted to final configurations *)

Definition post (Y:phi) (T:typ) : conf->Prop :=
  fun '(t,mu) =>
    exists Y', extends Y Y'
             /\ Y' |== mu
             /\ value t
             /\ empty ! Y' |= t ~: T.

(** Goal is to prove coomnibig-soundness: well-typed configurations
    can only reach final states satisfying the postcondition
    associated with their types. *)

Definition coomnibig_soundness := forall mu t Y T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  coomnibig (t,mu) (post Y T).


(* ########################################################### *)
(** ** Entailment *)

Definition himpl (H1 H2:conf->Prop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

Lemma himpl_refl : forall H,
  (H ==> H).
Proof using. introv M. unfolds* himpl. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.

(** For technical reasons associated with the guard condition of the
    coinductive proof, we need to reformulate the soundness statement,
    by introducing a postcondition [P] that contains [post Y T]. *)

Definition coomnibig_soundness_himpl := forall t mu Y T P,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  (post Y T ==> P) ->
  coomnibig (t,mu) P.

(** The above statement clearly entails the desired result. *)

Lemma coomnibig_soundness_of_himpl_soundness :
  coomnibig_soundness_himpl ->
  coomnibig_soundness.
Proof using. introv M HS HT. applys* M. applys* himpl_refl. Qed.


(* ########################################################### *)
(** ** Lemmas about covariance and extensions *)

(** [coomnibig] is covariant in the postcondition (omni-big-conseqence) *)

Lemma coomnibig_conseq : forall c P1 Q2,
  coomnibig c P1 ->
  P1 ==> Q2 ->
  coomnibig c Q2.
Proof using.
  introv M W. unfolds himpl. gen c P1 Q2. cofix IH.
  intros. inverts M; try solve [ constructors* ].
  { applys* coomnibig_get. }
  { applys* coomnibig_app_1. }
  { applys* coomnibig_app_2. }
  { applys* coomnibig_ref_1. }
  { applys* coomnibig_get_1. }
  { applys* coomnibig_set_1. }
  { applys* coomnibig_set_2. }
  { applys* coomnibig_rand_1. }
Qed.

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

Ltac auto_star ::= eauto 8.

Hint Unfold post.
Hint Constructors value.

(** There are some repeated proof patterns for handling evaluation under a context;
    due to restrictions of the guard condition checker, it is hard to capture
    those patterns using a lemma, hence we need a tactic to factorize the work. *)

Ltac sound_ctx E :=
  let IH := match goal with IH: context [ coomnibig ] |- _ => constr:(IH) end in
  applys E; try match goal with |- value _ => eauto | |- ~value _ => eauto end;
  [ applys* IH; try applys himpl_refl
  | let EY' := fresh "EY'" in
    introv (Y'&EY'&?&?&?); applys* IH;
    try (match goal with HQ: post _ _ ==> _ |- _ => applys himpl_trans HQ end;
         applys post_extends EY') ].

Lemma coomnibig_soundness_himpl_result :
  coomnibig_soundness_himpl.
Proof using.
  unfolds. cofix IH. introv HS HT HQ. inverts HT as.
  { introv HK HT1. false* binds_empty_inv. }
  { intros L M. asserts Wf1: (term (trm_abs t1)).
    { applys term_abs L. intros x Hx. forwards*: M x. }
    applys* coomnibig_val. { simple*. }{ applys* HQ. } }
  { introv Ht1 Ht2. tests V1: (value t1).
    { tests V2: (value t2).
      { inverts V1; inverts Ht1.
        applys* coomnibig_beta. applys* IH. pick_fresh x.
        rewrite* (@subst_intro x). apply_empty* typing_subst. }
      { sound_ctx coomnibig_app_2. } }
    { sound_ctx coomnibig_app_1. } }
  { intros K. applys* coomnibig_val. }
  { intros K. applys* coomnibig_val. simple*. }
  { intros K B. applys* coomnibig_val. simple*. }
  { introv Ht1. tests V1: (value t1).
    { applys* coomnibig_ref. intros l Hl. applys HQ.
      exists (Y & l ~ T0). lets: (proj32 HS) Hl. splits*.
      { applys* sto_typing_push. } }
    { sound_ctx coomnibig_ref_1. } }
  { introv Ht1. tests V1: (value t1).
    { inverts V1; inverts Ht1. forwards (r&Vr&Hr&Tr): (proj33 HS) l0.
      { eauto.  } applys* coomnibig_get. }
    { sound_ctx coomnibig_get_1. } }
  { introv Ht1 Ht2. tests V1: (value t1).
    { tests V2: (value t2).
      { inverts V1; inverts Ht1. forwards (r&Vr&Hr&Tr): (proj33 HS) l0.
        { eauto. } applys* coomnibig_set. applys HQ.
        exists Y. destruct HS as [StoOk [Dom Map]]. splits*.
        { splits*. intros l T' HB. tests: (l = l0).
          { exists t2. rewrites* (>> binds_functional T' T0 HB). }
          { destruct (Map _ _ HB) as (t'&Val&Has&Typ). exists* t'. } } }
      { sound_ctx coomnibig_set_2. } }
    { sound_ctx coomnibig_set_1. } }
  { introv Ht1. tests V1: (value t1).
    { inverts V1; inverts Ht1. applys* coomnibig_rand. }
    { sound_ctx (>> coomnibig_rand_1 (post Y typ_int)). } }
Qed.

