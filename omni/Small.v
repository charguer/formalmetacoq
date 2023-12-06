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

Implicit Types Q : val->state->Prop.


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
(** ** Reducible and Stuck Configurations *)

(** Consider a configuration [(s,t)], where [t] is not a value. If this
    configuration cannot take any reduction step, it is said to be "stuck". On
    the contrary, a configuration [(s,t)] that may take a step is said to be
    "reducible". *)

Definition reducible (s:state) (t:trm) : Prop :=
  exists s' t', step s t s' t'.

(** The predicate [trm_is_val t] asserts that [t] is a value. *)

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(** The predicate [notstuck s t] asserts that either [t] is a value or [t] is
    reducible. *)

Definition notstuck (s:state) (t:trm) : Prop :=
  trm_is_val t \/ reducible s t.


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
(** ** Small-Step-Eventually Judgment *)

(** [seventually s t P] asserts that all executions starting from [(s,t)]
    eventually reach a configuration [(s',t')] satisfying the predicate [P]. *)

Inductive seventually : state->trm->(state->trm->Prop)->Prop :=
  | seventually_here : forall s t P,
      P s t ->
      seventually s t P
  | seventually_step : forall s t P,
      (reducible s t) ->
      (forall s' t', step s t s' t' -> seventually s' t' P) ->
      seventually s t P.


(* ########################################################### *)
(** ** Viewing postconditions as predicates over configurations *)

Definition pred_of_post (Q:val->hprop) : state->trm->Prop :=
  fun s' t' => exists v', t' = trm_val v' /\ Q v' s'.


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

(** The judgment [stepsinf s t] characterize divergence in small-step:
    any execution prefix can be extended. *)

Definition stepsinf (s:state) (t:trm) : Prop :=
  forall s2 t2, steps s t s2 t2 ->
  exists s3 t3, step s2 t2 s3 t3.


(* ########################################################### *)
(** ** Inductive Characterization of Total Correctness *)

(** [stepsinto s t Q] asserts that all executions starting from [(s,t)]
    eventually reach *final* configurations satisfying the predicate [Q]. *)

Inductive stepsinto : state->trm->(val->hprop)->Prop :=
  | stepsinto_val : forall s v Q,
      Q v s ->
      stepsinto s v Q
  | stepsinto_step : forall s t Q,
      reducible s t ->
      (forall s' t', step s t s' t' -> stepsinto s' t' Q) ->
      stepsinto s t Q.


(* ########################################################### *)
(** ** Coinductive Characterization of Partial Correctness *)

(** [costepsinto s t Q] asserts that all executions of [(s,t)] are
    safe, and if they terminate then they satisfy the postcondition [Q]. *)

CoInductive costepsinto : state->trm->(val->hprop)->Prop :=
  | costepsinto_val : forall s v Q,
      Q v s ->
      costepsinto s v Q
  | costepsinto_step : forall s t Q,
      reducible s t ->
      (forall s' t', step s t s' t' -> costepsinto s' t' Q) ->
      costepsinto s t Q.


(* ########################################################### *)
(** ** CoInductive Characterization of Divergence *)

(** [costeps s t] is equivalent to [stepsinf], but defined coinductively. *)

CoInductive costeps : state -> trm -> Prop :=
  | costeps_step : forall s1 t1,
      reducible s1 t1 ->
      (forall s2 t2, step s1 t1 s2 t2 -> costeps s2 t2) ->
      costeps s1 t1.


(* ########################################################### *)
(** ** Properties of a Small-Step Semantics *)

(** The judgment [safe s t] asserts that no execution may reach a stuck term. In
    other words, for any configuration [(s',t')] reachable from [(s,t)], it is
    the case that the configuration [(s',t')] is either a value or is reducible.
    *)

Definition safe (s:state) (t:trm) : Prop :=
  forall s' t', steps s t s' t' -> notstuck s' t'.

(** The judgment [correct s t Q] asserts that if the execution of [(s,t)]
    reaches a final configuration, then this final configuration satisfies [Q].
    *)

Definition correct (s:state) (t:trm) (Q:val->hprop) : Prop :=
  forall s' v, steps s t s' v -> Q v s'.

(** The judgment [terminates s t] is defined inductively. The execution starting
    from [(s,t)] terminates if, for any possible step leads to a configuration
    that terminates. Note that a configuration that has reached a value cannot
    take a step, hence is considered terminating. *)

Inductive terminates : state->trm->Prop :=
  | terminates_step : forall s t,
      (forall s' t', step s t s' t' -> terminates s' t') ->
      terminates s t.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Properties *)

Hint Unfold reducible trm_is_val.


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
(** ** Covariance of [stepsinto] ands [costepsinto] *)

(** The consequence rule for [stepsinto] is established by induction. *)

Lemma stepsinto_conseq : forall s t Q Q',
  stepsinto s t Q' ->
  Q' ===> Q ->
  stepsinto s t Q.
Proof using.
  introv M WQ. induction M.
  { applys stepsinto_val. applys* WQ. }
  { rename H1 into IH.
    applys stepsinto_step.
    { auto. }
    { introv HR. applys* IH. } }
Qed.

(** The consequence rule for [costepsinto] is established by coinduction. *)

Lemma costepsinto_conseq : forall s t Q Q',
  costepsinto s t Q' ->
  Q' ===> Q ->
  costepsinto s t Q.
Proof using.
  cofix IH. introv M WQ. inverts M.
  { applys costepsinto_val. applys* WQ. }
  { applys costepsinto_step.
    { auto. }
    { introv HR. applys* IH. } }
Qed.


(* ########################################################### *)
(** ** [stepsinto] Included in [seventually] *)

(** If all executions of [(t,s)] eventually fall into the set of configuration
    made the final configurations satisfying [Q], then all executions of [(t,s)]
    terminate with postcondition [Q]. And reciprocally. *)

Lemma stepsinto_iff_eventually : forall s t Q,
  stepsinto s t Q <-> seventually s t (pred_of_post Q).
Proof using.
  iff M.
  { induction M.
    { applys* seventually_here. hnfs*. }
    { applys* seventually_step. } }
  {  gen_eq P: (pred_of_post Q). gen Q. induction M; intros; subst.
    { rename H into K. destruct K as (v&->&?). constructors*. }
    { constructors*. } }
Qed.


(* ########################################################### *)
(** ** Total Correctness Entails Partial Correctness *)

(** Total correctness is a stronger property than partial correctness:
    [omnibig s t Q] entails [coomnibig s t Q]. *)

Lemma costepsinto_of_stepsinto : forall s t Q,
  stepsinto s t Q ->
  costepsinto s t Q.
Proof using.
  introv M. induction M; try solve [ constructors* ].
Qed.


(* ########################################################### *)
(** ** Equivalence of Divergence and Partial Correctness with Empty Postcondition *)

(** For closure-based definitions, we relate [stepsinf] with the specialization
    of [partial] to the empty postcondition [Empty].
    [Empty] is defined in the file [Syntax]. *)

Lemma stepsinf_iff_omnibigps_Empty : forall s t,
  stepsinf s t <-> partial s t Empty.
Proof using.
  iff M.
  { introv R. right. applys M R. }
  { introv R. lets C: M R. destruct C as [(v2&E&HQ)|C].
    { unfolds Empty. false. }
    { applys C. } }
Qed.

(** For coinductive definitions, we relate [costeps] with the specialization
    of [costepsinto] to the empty postcondition [Empty]. *)

Lemma costeps_iff_costepsinto_Empty : forall s t,
  costeps s t <-> costepsinto s t Empty.
Proof using.
  iff M.
  { gen s t. cofix IH. intros. inverts M as S M'.
    applys costepsinto_step S. introv S'. applys IH. applys M' S'. }
  { gen s t. cofix IH. intros. inverts M as.
    { introv N. unfolds Empty. false. }
    { introv S M'. applys costeps_step S.
      introv S'. applys IH. applys M' S'. } }
Qed.


(* ########################################################### *)
(** ** Equivalence of CoInductive and Closure-Based Characterizations *)

(** [costepsinto] patches the standard definition of partial correctness
    with respect to standard small-step. *)

Lemma costepsinto_eq_partial :
  costepsinto = partial.
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
    { destruct C as (v&->). applys costepsinto_val. applys partial_val_inv M. }
    { lets (s2&t2&R2&RS): partial_not_val_inv M C.
      applys costepsinto_step.
      { exists* s2 t2. }
      { intros s' t' R'. applys IH. applys partial_inv_step M R'. } } }
Qed.

Lemma costeps_eq_stepsinf :
  costeps = stepsinf.
Proof using.
  extens. intros s t.
  rewrite stepsinf_iff_omnibigps_Empty.
  rewrite costeps_iff_costepsinto_Empty.
  rewrite* costepsinto_eq_partial.
Qed.


(* ########################################################### *)
(** ** Properties Captured by Total Correctness, for the Inductive Characterization *)

(** Values are not reducible. *)

Lemma reducible_val_inv : forall s v,
  ~ reducible s v.
Proof using. introv (s'&t'&M). inverts M. Qed.

(** [stepsinto] captures safety. *)

Lemma stepsinto_safe : forall s t Q,
  stepsinto s t Q ->
  safe s t.
Proof using.
  introv M R. gen Q. induction R; intros.
  { inverts M. { left. hnfs*. } { right*. } }
  { rename H into S. inverts M. { inverts S. } { applys* IHR. } }
Qed.

(* [stepsinto] captures correctness. *)

Lemma stepsinto_correct : forall s t Q,
  stepsinto s t Q ->
  correct s t Q.
Proof using.
  introv M. induction M; introv R.
  { inverts R as. { auto. } { introv S. inverts S. } }
  { rename H1 into IH. inverts R. { false* reducible_val_inv. } applys* IH. }
Qed.

(** [stepsinto] captures termination. *)

Lemma stepsinto_terminates : forall s t Q,
  stepsinto s t Q ->
  terminates s t.
Proof using.
  introv M. induction M; constructors; introv R.
  { inverts R. }
  { eauto. }
Qed.


(* ########################################################### *)
(** ** Properties Captured by Partial Correctness, for the CoInductive Characterization *)

(** [costepsinto] captures safety. *)

Lemma costepsinto_safe : forall s t Q,
  costepsinto s t Q ->
  safe s t.
Proof using.
  introv M R. gen Q. induction R; intros.
  { inverts M. { left. hnfs*. } { right*. } }
  { rename H into S. inverts M. { inverts S. } { applys* IHR. } }
Qed.

(* [costepsinto] captures correctness. *)

Lemma costepsinto_correct : forall s t Q,
  costepsinto s t Q ->
  correct s t Q.
Proof using.
  introv M R. gen_eq t': (trm_val v). gen v Q. induction R; intros; subst.
  { inverts M as. subst. { auto. } { introv S. false* reducible_val_inv. } }
  { rename H into R1. inverts M as. { inverts R1. }
    introv M1 M2. applys* IHR. }
Qed.


(* ########################################################### *)
(** ** Properties Captured by Partial Correctness, for the Closure-Based Characterization *)

(** [partial] captures safety. *)

Lemma partial_safe : forall s t Q,
  partial s t Q ->
  safe s t.
Proof using.
  introv M R. forwards [(v2&->&?)|(s3&t3&?)]: M R.
  { left*. } { right*. }
Qed.

(** In fact, [partial] instantiated with the always-true postcondition
    captures safety and nothing more. *)

Lemma ssafe_eq_safe : forall s t,
  partial s t Any <-> safe s t.
Proof using.
  intros s t. iff M.
  { applys* partial_safe. }
  { introv R. forwards [K|K]: M R.
    { left. unfold Any. destruct t2; tryfalse; eauto. }
    { right*. } }
Qed.

(* [partial] captures correctness. *)

Lemma partial_correct : forall s t Q,
  partial s t Q ->
  correct s t Q.
Proof using.
  introv M R. forwards [(v2&E&?)|(s3&t3&?)]: M R.
  { inverts* E. } { false_invert. }
Qed.

