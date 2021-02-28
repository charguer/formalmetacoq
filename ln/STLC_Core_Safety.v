(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Alternative Proofs       *
* Arthur Chargueraud, Feb 2021                                             *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN
  STLC_Core_Definitions
  STLC_Core_Infrastructure
  STLC_Core_Soundness.


(* ********************************************************************** *)
(** General statement of type soundness *)

(** Transitive closure of the reduction relation *)

Inductive reds : trm -> trm -> Prop :=
  | reds_here : forall t,
      term t ->
      reds t t
  | reds_trans : forall t1 t2 t3,
      red t1 t2 ->
      reds t2 t3 ->
      reds t1 t3.

(** A term [t] can reduce, written [canred t], if there exists
    at least one [t'] to which [t] may reduce, i.e. [t --> t']. *)

Definition canred (t:trm) : Prop :=
  exists t', t --> t'.

(** A term is stuck if it is not a value and cannot reduce *)

Definition stuck (t:trm) : Prop :=
  ~ value t /\ ~ canred t.

(** Statement of safety: terms never get stuck. *)

Definition safe (t:trm) : Prop :=
  forall t', reds t t' -> ~ stuck t'.

(** Observe that "not being stuck" is equivalent to being either
    a value, or can take a step. This is the formulation used
    in the statement of the [progress] lemma. Note that proving
    the equivalence requires classical logic for eliminating a
    double negation. *)

Lemma safe_iff : forall t,
  safe t <-> (forall t', reds t t' -> value t' \/ (exists t'', t' --> t'')).
Proof using.
  unfolds safe. iff M.
  { introv R. lets S: M R. unfolds stuck.
    rew_logic in S. (* classical logic *) 
    apply S. }
  { introv R (N1&N2). forwards [S|S]: M R.
    { false. } { unfolds canred. false. } }
Qed.

(** Preservation for empty environments is a restricted form of
    preservation that suffices for establishing safety. *)

Definition preservation_for_empty := forall t t' T,
  empty |= t ~: T ->
  t --> t' ->
  empty |= t' ~: T.

Lemma preservation_for_empty_of_preservation : 
  preservation ->
  preservation_for_empty.
Proof using. introv Pre HT HR. applys Pre HT HR. Qed.

(** From preservation (for empty environemnts) and progress, 
    we can derive that all well-typed terms are safe, by induction 
    on the reduction sequence. *)

Lemma safe_from_preservation_and_progress :
  preservation ->
  progress ->
  forall t T, (empty |= t ~: T) -> safe t.
Proof using.
  introv Pre Pro HT. rewrite safe_iff. introv R. gen T.
  induction R.
  { intros. applys Pro HT. }
  { intros. applys IHR. applys* Pre HT. }
Qed.


(* ********************************************************************** *)
(** Simpler proof technique for the particular case of deterministic languages *)

(** Definition of the determinacy property *)

Definition deterministic :=
  forall t t1' t2',
    t --> t1' ->
    t --> t2' ->
    t1' = t2'.

(** Statement of the preservation+progress combined into one. *)

Definition combined_soundness :=
  forall t T,
    empty |= t ~: T ->
       value t
    \/ (exists t', t --> t' /\ empty |= t' ~: T).

(** Auxiliary lemma: values don't step. *)

Lemma red_value_inv : forall t t',
  t --> t' ->
  ~ value t.
Proof using.
  introv HR HV. inverts HV. inverts HR.
Qed.

(** Proof that this statement entails preservation (for empty environments)
    and progress. *)

Lemma combined_soundness_inv :
  combined_soundness ->
  deterministic ->
     preservation_for_empty
  /\ progress.
Proof using.
  introv Com Det. split.
  { introv HT HR. lets [HV|(t''&HR'&HT')]: Com HT. 
    { false red_value_inv HR HV. }
    { lets E: Det HR HR'. subst t''. applys HT'. } }
  { introv HT. lets [HV|(t'&HR&HT')]: Com HT. { left*. } { right*. } }
Qed.

(** Proof of this result using a single induction, with a proof
    term of linear size in the number of language constructs. *)

Hint Constructors typing.

Lemma combined_soundness_result :
  combined_soundness.
Proof.
  introv Typ. lets Typ': Typ. inductions Typ.
  false* binds_empty_inv.
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' [Red1 Typ1']]].
    destruct~ IHTyp2 as [Val2 | [t2' [Red2 Typ2']]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2). splits*.
      { pick_fresh x. rewrite* (@subst_intro x). apply_empty* typing_subst. }
      exists* (trm_app t1 t2').
    exists* (trm_app t1' t2).
Qed.

