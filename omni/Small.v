(****************************************************************
* Imperative Lambda-calculus                                    *
* Small-Step Semantics                                          *
****************************************************************)

Set Implicit Arguments.
Require Export Syntax.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types s : state.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Definitions *)


(* ########################################################### *)
(** ** Small-Step Judgment *)

(** The judgment [step s t s' t'] describes the small-step reduction relation:
    it asserts that the program configuration [(s,t)] can take one reduction
    step towards the program configuration [(s',t')]. *)

Inductive step : state -> trm -> state -> trm -> Prop :=

  (* Unique context rule *)
  | step_let_ctx : forall s1 s2 x t1 t1' t2,
      step s1 t1 s2 t1' ->
      step s1 (trm_let x t1 t2) s2 (trm_let x t1' t2)

  (* Beta reductions *)
  | step_fix : forall s f x t1,
      step s (trm_fix f x t1) s (val_fix f x t1)
  | step_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 ->
      step s (trm_app v1 v2) s (subst x v2 (subst f v1 t1))
  | step_if : forall s b t1 t2,
      step s (trm_if (val_bool b) t1 t2) s (if b then t1 else t2)
  | step_let : forall s x t2 v1,
      step s (trm_let x v1 t2) s (subst x v1 t2)

  (* Primitive operations *)
  | step_div : forall s n1 n2,
      n2 <> 0 ->
      step s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2))
  | step_rand : forall s n n1,
      0 <= n1 < n ->
      step s (val_rand (val_int n)) s (val_int n1)
  | step_ref : forall s v p,
      ~ Fmap.indom s p ->
      step s (val_ref v) (Fmap.update s p v) (val_loc p)
  | step_get : forall s p,
      Fmap.indom s p ->
      step s (val_get (val_loc p)) s (Fmap.read s p)
  | step_set : forall s p v,
      Fmap.indom s p ->
      step s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | step_free : forall s p,
      Fmap.indom s p ->
      step s (val_free (val_loc p)) (Fmap.remove s p) val_unit.


(* ########################################################### *)
(** ** Transitive Closure of the Small-Step Judgment *)

(** The judgment [steps s t s' t'] corresponds to the reflexive-transitive
    closure of [step]. Concretely, this judgment asserts that the configuration
    [(s,t)] can reduce in zero, one, or several steps to [(s',t')]. *)

Inductive steps : state -> trm -> state -> trm -> Prop :=
  | steps_refl : forall s t,
      steps s t s t
  | steps_step : forall s1 s2 s3 t1 t2 t3,
      step s1 t1 s2 t2 ->
      steps s2 t2 s3 t3 ->
      steps s1 t1 s3 t3.


(* ########################################################### *)
(** ** Closure-Based Characterization of Partial Correctness *)

(** [partial s t Q] asserts that the executions of [(t,s)] are safe
    and that if they terminate they satisfy the postcondition [Q]. *)

Definition partial (s1:state) (t1:trm) (Q:val->state->Prop) : Prop :=
  forall s2 t2, steps s1 t1 s2 t2 ->
       (exists v2, t2 = trm_val v2 /\ Q v2 s2)
    \/ (exists s3 t3, step s2 t2 s3 t3).


(* ########################################################### *)
(** ** Closure-Based Characterization of Divergence *)

(** The judgment [sdiv s t] characterize divergence in small-step:
    any execution prefix can be extended. *)

Definition sdiv (s:state) (t:trm) : Prop :=
  forall s2 t2, steps s t s2 t2 ->
  exists s3 t3, step s2 t2 s3 t3.


(* ########################################################### *)
(** ** Coinductive Characterization of Partial Correctness *)

(** [cobigsmall s t Q] asserts that all executions of [(s,t)] are
    safe, and if they terminate then they satisfy the postcondition [Q]. *)

CoInductive cobigsmall : state->trm->(val->hprop)->Prop :=
  | cobigsmall_val : forall s v Q,
      Q v s ->
      cobigsmall s v Q
  | cobigsmall_step : forall s t Q,
      (exists s' t', step s t s' t') ->
      (forall s' t', step s t s' t' -> cobigsmall s' t' Q) ->
      cobigsmall s t Q.


(* ########################################################### *)
(** ** CoInductive Characterization of Divergence *)

(** [costeps s t] is equivalent to [sdiv], but defined coinductively. *)

CoInductive costeps : state -> trm -> Prop :=
  | costeps_step : forall s1 t1,
      (exists s2 t2, step s1 t1 s2 t2) ->
      (forall s2 t2, step s1 t1 s2 t2 -> costeps s2 t2) ->
      costeps s1 t1.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Properties *)


(* ########################################################### *)
(** ** Properties of the Small Step Judgment *)

(** Values can't step. *)

Lemma step_val_inv : forall s v s' t',
  step s (trm_val v) s' t' ->
  False.
Proof using. introv S. inverts S; false_invert. Qed.

(** Reformulation of the above using existentials. *)

Lemma exists_step_val_inv : forall s v,
  (exists s' t', step s v s' t') ->
  False.
Proof using. introv (s'&t'&S). applys* step_val_inv S. Qed.


(* ########################################################### *)
(** ** Properties of the Partial Correctness Judgment *)

(** Inversion lemma *)

Lemma partial_val_inv : forall s v Q,
  partial s v Q ->
  Q v s.
Proof using.
  introv M. forwards N: M s v. { applys steps_refl. }
  destruct N as [(v1&E1&P1)|(s2&t2&R)].
  { inverts* E1. }
  { inverts R; false_invert. } (* patch one line *)
Qed.

(** Preservation property for [partial]. *)

Lemma partial_inv_step : forall s1 t1 s2 t2 Q,
  partial s1 t1 Q ->
  step s1 t1 s2 t2 ->
  partial s2 t2 Q.
Proof using.
  introv M R1. intros s3 t3 R2. applys M s3 t3.
  { applys steps_step R1. applys R2. }
Qed.

(** Progress property for [partial]. *)

Lemma partial_inv : forall s1 t1 Q,
  partial s1 t1 Q ->
     (exists v1, t1 = trm_val v1 /\ Q v1 s1)
  \/ (exists s2 t2, step s1 t1 s2 t2 /\ partial s2 t2 Q).
Proof using.
  introv M. forwards N: M s1 t1. { applys steps_refl. }
  destruct N as [(v1&E1&P1)|(s2&t2&R)].
  { left. exists* v1. }
  { right. exists s2 t2. split~. { applys* partial_inv_step. } }
Qed.

(** An alternative statement of the previous lemma. *)

Lemma partial_not_val_inv : forall s1 t1 Q,
  partial s1 t1 Q ->
  (forall v, t1 <> trm_val v) ->
  exists s2 t2, step s1 t1 s2 t2 /\ partial s2 t2 Q.
Proof using.
  introv M N. destruct (partial_inv M) as [(v1&E1&P1)|R].
  { false* N. }
  { auto. }
Qed.


(* ########################################################### *)
(** ** Equivalence of Divergence and Partial Correctness with Empty Postcondition *)

(** For closure-based definitions, we relate [sdiv] with the specialization
    of [partial] to the empty postcondition [Empty]. *)

Lemma sdiv_iff_omnibigps_Empty : forall s t,
  sdiv s t <-> partial s t Empty.
Proof using.
  iff M.
  { introv R. right. applys M R. }
  { introv R. lets C: M R. destruct C as [(v2&E&HQ)|C].
    { unfolds Empty. false. }
    { applys C. } }
Qed.

(** For coinductive definitions, we relate [costeps] with the specialization
    of [cobigsmall] to the empty postcondition [Empty]. *)

Lemma costeps_iff_cobigsmall_Empty : forall s t,
  costeps s t <-> cobigsmall s t Empty.
Proof using.
  iff M.
  { gen s t. cofix IH. intros. inverts M as S M'.
    applys cobigsmall_step S. introv S'. applys IH. applys M' S'. }
  { gen s t. cofix IH. intros. inverts M as.
    { introv N. unfolds Empty. false. }
    { introv S M'. applys costeps_step S.
      introv S'. applys IH. applys M' S'. } }
Qed.


(* ########################################################### *)
(** ** Equivalence of CoInductive and Closure-Based Characterizations *)

(** [cobigsmall] patches the standard definition of partial correctness
    with respect to standard small-step. *)

Lemma cobigsmall_eq_partial :
  cobigsmall = partial.
Proof using.
  extens. intros s t Q. iff M.
  { introv R. gen M. induction R; intros.
    { inverts M as M1 M2.
      { left*. }
      { right. applys M1. } }
    { rename H into R1, R into R2. inverts M as M1 M2.
      { false. inverts R1; false_invert. }
      { applys IHR. applys M2 R1. } } }
  { gen s t Q. cofix IH. intros.
    tests C: (exists v, t = trm_val v).
    { destruct C as (v&->). applys cobigsmall_val. applys partial_val_inv M. }
    { lets (s2&t2&R2&RS): partial_not_val_inv M C.
      applys cobigsmall_step.
      { exists* s2 t2. }
      { intros s' t' R'. applys IH. applys partial_inv_step M R'. } } }
Qed.

Lemma costeps_eq_sdiv :
  costeps = sdiv.
Proof using.
  extens. intros s t.
  rewrite sdiv_iff_omnibigps_Empty.
  rewrite costeps_iff_cobigsmall_Empty.
  rewrite* cobigsmall_eq_partial.
Qed.
