(****************************************************************
* Imperative Lambda-calculus                                    *
* Equivalence Proofs for Small-Step and Big-Step Semantics      *
*****************************************************************)

Set Implicit Arguments.
Require Export Syntax.


(* ########################################################### *)
(** ** Equivalence for Between Standard Small-Step and Standard Big-Step *)

(** In this section, we establish the equivalence between
    the big-step judgment [big s t s' v] and the iterated
    small-step judgment [steps s t s' (trm_val v)]. *)

(** Consider first the direction from small-step to big-step.
    The proof involves a key lemma, which shows how to "glue"
    a one-step reduction with a big-step evaluation to produce
    a (larger) big-step evaluation. *)

Lemma big_of_step_and_eval : forall s1 s2 t1 t2 s3 v,
  step s1 t1 s2 t2 ->
  big s2 t2 s3 v ->
  big s1 t1 s3 v.
Proof using.
  introv M1 M2. gen s3 v. induction M1; intros.
  { inverts M2 as; try false_invert.
    { introv M3 M4. applys* big_let. } }
  { inverts M2; try false_invert. applys big_fix. }
  { applys* big_app_fix. }
  { applys* big_if. }
  { applys* big_let. applys big_val. }
  { inverts M2; try false_invert. applys* big_div. }
  { inverts M2; try false_invert. applys* big_rand. }
  { inverts M2; try false_invert. applys* big_ref. }
  { inverts M2; try false_invert. applys* big_get. }
  { inverts M2; try false_invert. applys* big_set. }
  { inverts M2; try false_invert. applys* big_free. }
Qed.

(** Using the above lemmas, to establish the implication between
    the iterated small-step relation, it remains to perform an
    induction over the sequence of individual steps involved. *)

Lemma big_of_steps : forall s1 s2 t v,
  steps s1 t s2 (trm_val v) ->
  big s1 t s2 v.
Proof.
  introv M. gen_eq t': (trm_val v). gen v.
  induction M; intros; subst.
  { applys* big_val. }
  { applys* big_of_step_and_eval. }
Qed.

(** Let's now tackle the reciprocal direction, from big-step to
    small-step. This time, the key auxiliary lemma is a context
    rule for describing how a sequence of steps can be applied
    under a let-context. *)

Lemma steps_let : forall s1 s2 s3 v1 v3 x t1 t2,
  steps s1 t1 s2 (trm_val v1) ->
  steps s2 (subst x v1 t2) s3 v3 ->
  steps s1 (trm_let x t1 t2) s3 v3.
Proof using.
  introv M1 M2. gen_eq t1': (trm_val v1). gen v1.
  induction M1; intros; subst.
  { applys steps_step. { applys step_let. } { applys M2. } }
  { rename H into R1. applys steps_step.
    { applys step_let_ctx R1. }
    { applys* IHM1 M2. } }
Qed.

(** There remains to perfom an induction over the big-step
    evaluation relation. The only nontrivial case is that of
    the let-binding, for which we need to exploit [steps_let]. *)

Lemma steps_of_eval : forall s1 s2 t v,
  big s1 t s2 v ->
  steps s1 t s2 (trm_val v).
Proof using.
  introv M. induction M.
  { applys steps_refl. }
  { applys steps_step. { applys step_fix. } { applys steps_refl. } }
  { applys steps_step. { applys* step_app_fix. } { applys IHM. } }
  { applys* steps_let IHM1 IHM2. }
  { applys steps_step. { applys* step_if. } { applys IHM. } }
  { applys steps_step. { applys* step_div. } { applys steps_refl. } }
  { applys steps_step. { applys* step_rand. } { applys steps_refl. } }
  { applys steps_step. { applys* step_ref. } { applys steps_refl. } }
  { applys steps_step. { applys* step_get. } { applys steps_refl. } }
  { applys steps_step. { applys* step_set. } { applys steps_refl. } }
  { applys steps_step. { applys* step_free. } { applys steps_refl. } }
Qed.

(** Putting the two directions together yields the desired equivalence. *)

Lemma big_iff_steps : forall s t s' v,
  big s t s' v <-> steps s t s' (trm_val v).
Proof using.
  iff M.
  { applys* steps_of_eval. }
  { applys* big_of_steps. }
Qed.
