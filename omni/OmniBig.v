(****************************************************************
* Imperative Lambda-calculus                                    *
* Omni-Big-Step Semantics                                       *
*****************************************************************)



(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Common definitions  *)

(* ########################################################### *)
(** ** Definition of [strongestpost] and [exactly] *)

(** Let [strongestpost s t] denote the strongest postcondition
    (strongest-post), that is, [fun v s' => big s t s' v]. *)

Definition strongestpost (s:state) (t:trm) : val->hprop :=
  fun v s' => big s t s' v.

(* The postcondition [exactly v s'] to assert that the output of a program
   is exactly the value [v] in the state [s']. This postcondition
   corresponds to a singleton set. *)

Definition exactly (v:val) (s':state) : val->hprop :=
  fun v0 s0 => v0 = v /\ s0 = s'.

(** By definition, the postcondition [exactly v s'] holds only of [v]
    and [s'], thus the only introduction rule for [exactly] is the
    following reflexivity rule. *)

Lemma exactly_intro : forall v s',
  exactly v s' v s'.
Proof using. intros. hnfs*. Qed.




(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Inductive Omni-Big-Step *)

(* ########################################################### *)
(** ** Definition of Omni-Big-Step *)

(** Judgment [omnibig s t Q] *)

Inductive omnibig : state -> trm -> (val->state->Prop) -> Prop :=
  | omnibig_val : forall s v Q,
      Q v s ->
      omnibig s (trm_val v) Q
  | omnibig_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      omnibig s (trm_fix f x t1) Q
  | omnibig_app_fix : forall s v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      omnibig s (subst x v2 (subst f v1 t1)) Q ->
      omnibig s (trm_app v1 v2) Q
  | omnibig_let : forall Q1 s x t1 t2 Q,
      omnibig s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> omnibig s2 (subst x v1 t2) Q) ->
      omnibig s (trm_let x t1 t2) Q
  | omnibig_if : forall s b t1 t2 Q,
      omnibig s (if b then t1 else t2) Q ->
      omnibig s (trm_if (val_bool b) t1 t2) Q
  | omnibig_div : forall s n1 n2 Q,
      n2 <> 0 ->
      Q (val_int (Z.quot n1 n2)) s ->
      omnibig s (val_div (val_int n1) (val_int n2)) Q
  | omnibig_rand : forall s n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 s) ->
      omnibig s (val_rand (val_int n)) Q
  | omnibig_ref : forall s v Q,
      (forall p, ~ Fmap.indom s p ->
         Q (val_loc p) (Fmap.update s p v)) ->
      omnibig s (val_ref v) Q
  | omnibig_get : forall s p Q,
      Fmap.indom s p ->
      Q (Fmap.read s p) s ->
      omnibig s (val_get (val_loc p)) Q
  | omnibig_set : forall s p v Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.update s p v) ->
      omnibig s (val_set (val_loc p) v) Q
  | omnibig_free : forall s p Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.remove s p) ->
      omnibig s (val_free (val_loc p)) Q.

(** [omnibig] is covariant in the postcondition (omni-big-conseqence) *)

Lemma omnibig_conseq : forall s t Q1 Q2,
  omnibig s t Q1 ->
  Q1 ===> Q2 ->
  omnibig s t Q2.
Proof using.
  introv M W.
  asserts W': (forall v h, Q1 v h -> Q2 v h). { auto. } clear W.
  induction M; try solve [ constructors* ].
Qed.


(* ########################################################### *)
(** ** Relationship with WP Formulation *)

(** The rule [omnibig_let] shares similarities with the statement of
    the weakest-precondition style reasoning rule for let-bindings.
    Prove the following alternative statement, with a wp-style flavor. *)

Lemma omnibig_let' : forall s1 x t1 t2 Q,
  omnibig s1 t1 (fun v1 s2 => omnibig s2 (subst x v1 t2) Q) ->
  omnibig s1 (trm_let x t1 t2) Q.
Proof using.
  introv M. applys* omnibig_let M.
Qed.

(** Reciprocally, prove that the statement considered in the inductive
    definition of [omnibig] is derivable from [omnibig_let']. More precisely,
    prove the statement below by using [omnibig_let'] and [omnibig_conseq]. *)

Lemma omnibig_let_of_omnibig_let' : forall Q1 s1 x t1 t2 Q,
  omnibig s1 t1 Q1 ->
  (forall v1 s2, Q1 v1 s2 -> omnibig s2 (subst x v1 t2) Q) ->
  omnibig s1 (trm_let x t1 t2) Q.
Proof using.
  introv M1 M2. applys omnibig_let'. applys omnibig_conseq M1.
  intros v1 s2 K. applys M2 K.
Qed.

(** One way wonder whether we could have used the wp-style formulation
    of the semantics of let-bindings directly in the definition of [omnibig].
    The answer is negative. Doing so would lead to an invalid inductive
    definition, involving a "non strictly positive occurrence". To check it
    out, uncomment the definitions below to observe Coq's complaint.
[[
  Inductive omnibig' : state -> trm -> (val->state->Prop) -> Prop :=
    | omnibig'_let : forall s1 x t1 t2 Q,
       omnibig' s1 t1 (fun v1 s2 => omnibig' s2 (subst x v1 t2) Q) ->
       omnibig' s1 (trm_let x t1 t2) Q.

  Inductive omnibig' : state -> trm -> (val->state->Prop) -> Prop :=
    | omnibig'_let : forall Q1 s1 x t1 t2 Q,
       omnibig' s1 t1 Q1 ->
       Q1 = (fun v1 s2 => omnibig' s2 (subst x v1 t2) Q) ->
       omnibig' s1 (trm_let x t1 t2) Q.
]]

   Yet another unsuccessful try:
[[
  Inductive omnibig' : state -> trm -> (val->state->Prop) -> Prop :=
    | omnibig'_let : forall Q1 s1 x t1 t2 Q,
       omnibig' s1 t1 Q1 ->
       (forall v1 s2, Q1 v1 s2 -> exists Q2, omnibig' s2 (subst x v1 t2) Q2) ->
       Q = (fun v2 s3 => exists v1 s2, Q1 v1 s2 /\ exists Q2, Q2 v2 s3 /\ omnibig' s2 (subst x v1 t2) Q2) ->
       omnibig' s1 (trm_let x t1 t2) Q.
]]
*)


(* ########################################################### *)
(** ** Properties of Omni-Big-Step, Part 1 *)

(** Assume [omnibig s t Q] to hold. Prove that the postcondition [Q] holds of
    any output that [(s,t)] may evaluate to according to the judgment [big]. *)

Lemma omnibig_and_big_inv : forall s t v s' Q,
  omnibig s t Q ->
  big s t s' v ->
  Q v s'.
Proof using.
  introv M R. gen v s'.
  induction M; intros; try solve [inverts* R; tryfalse].
  { invert R; try solve [intros; false].
    introv E R. intros. subst. inverts E. applys* IHM. }
Qed.

(** If [omnibig s t Q] holds, then there exists an output
    [(s',v)] that [(s,t)] may evaluate to according to the judgment
    [big], and that this output satisfies [Q]. *)

Lemma omnibig_to_one_big : forall s t Q,
  omnibig s t Q ->
  exists s' v, big s t s' v /\ Q v s'.
Proof using.
  introv M. cuts (s'&v&R): (exists s' v, big s t s' v).
  { exists. split. { applys R. } { applys omnibig_and_big_inv M R. } }
  induction M.
  { exists. applys big_val. }
  { exists. applys big_fix. }
  { rename IHM into IHM1, M into M1.
    forwards (s'&v&R): IHM1.
    exists. applys* big_app_fix R. }
  { rename IHM into IHM1, H0 into IHM2, M into M1, H into M2.
    forwards (s1'&v1&R1): IHM1.
    lets HQ1: omnibig_and_big_inv M1 R1.
    forwards (s'&v&R2): IHM2 HQ1.
    exists. applys big_let R1 R2. }
  { forwards (s'&v&R1): IHM.
    exists. applys* big_if R1. }
  { exists. applys* big_div. }
  { rename H0 into N.
    exists. applys* big_rand 0. math. }
  { forwards* (p&D&N): (exists_fresh null s).
    exists. applys* big_ref. }
  { exists. applys* big_get. }
  { exists. applys* big_set. }
  { exists. applys* big_free. }
Qed.


(* ########################################################### *)
(** ** Properties of Omni-Big-Step, Part 2 *)

(** A special case is that of programs that admit a unique possible
    execution, that is, of programs that are deterministic even though
    the host language includes potentially non-deterministic features.
    Such a deterministic program admits a unique output. *)

(** A program [(s,t)] admits a unique execution with [(s',v)] as output
    if and only if [omnibig s t (exactly s' v)] holds. This same property
    can be expressed in terms of the judgment [big], by asserting that
    [big s t v2 s2] holds if and only if [v2 = v] and [s2 = s']. Let us
    prove the two characterizations equivalent. *)

(** We prove that if [omnibig s t Q] holds for a singleton set [Q],
    then the big-step judgment holds for that unique result. *)

Lemma big_of_omnibig_exactly : forall s t v s',
  omnibig s t (exactly v s') ->
  big s t s' v.
Proof using.
  introv M. lets (s2&v2&R&E): omnibig_to_one_big M.
  unfolds exactly. destruct E as (->&->). applys R.
Qed.

(** A slightly stronger result, not needed in the other proofs. *)

Lemma evalntb_exactly_iff_big_exactly : forall s t v s',
  omnibig s t (exactly v s') ->
  (forall s2 v2, big s t s2 v2 <-> (v2 = v /\ s2 = s')).
Proof using.
  introv M. iff R (->&->).
  { applys omnibig_and_big_inv M R. }
  { lets (s2&v2&R&E): omnibig_to_one_big M.
    unfolds exactly. destruct E as (->&->). applys R. }
Qed.


(* ########################################################### *)
(** ** Properties of Omni-Big-Step, Part 3 *)

(** If [omnibig s t Q] holds for some [Q], then
    [omnibig s t (strongestpost s t)] holds.
    See also lemma [omnibig_strongestpost_of_terminates]. *)

Lemma omnibig_strongestpost_of_omnibig : forall s t Q,
  omnibig s t Q ->
  omnibig s t (strongestpost s t).
Proof using.
  introv M. unfold strongestpost. induction M.
  { applys omnibig_val. applys big_val. }
  { applys omnibig_fix. applys big_fix. }
  { applys* omnibig_app_fix. applys omnibig_conseq IHM.
    { intros v s' R. applys* big_app_fix R. } }
  { rename IHM into IHM1, H0 into IHM2.
    applys omnibig_let (fun v1 s' => big s t1 s' v1 /\ Q1 v1 s').
    { applys omnibig_conseq IHM1. { intros v1 s' R. split.
      { applys R. }
      { applys omnibig_and_big_inv M R. } } }
    { intros v1 s2 (R1&K). applys omnibig_conseq. applys IHM2 K.
      { intros v s' R2. applys big_let R1 R2. } } }
  { applys omnibig_if. applys omnibig_conseq IHM.
    { intros v s' R. applys big_if R. } }
  { applys omnibig_div. applys big_div. }
  { applys* omnibig_rand. intros n1 N1. applys* big_rand. }
  { applys* omnibig_ref. intros p Hp. applys* big_ref. }
  { applys* omnibig_get. applys* big_get. }
  { applys* omnibig_set. applys* big_set. }
  { applys* omnibig_free. applys* big_free. }
Qed.

(** Reciprocally, the strongest postcondition is the smallest
    possible postcondition for the judgment (strongest-post-minimal). *)

Lemma omnibig_inv_strongestpost_qimpl : forall s t Q,
  omnibig s t Q ->
  strongestpost s t ===> Q.
Proof using.
  introv M. unfold strongestpost. intros v s' K. applys omnibig_and_big_inv M K.
Qed.


(* ########################################################### *)
(** ** Interpretation of Omni-Big-Step w.r.t. [terminates] *)

(** The predicate [terminates s t] asserts that all executions of the
    configuration [t/s] terminate---none of them diverges or get
    stuck. Its definition is a simplified version of [omnibig] where all
    occurences of [Q] are removed. In the rule for let-bindings,
    namely [terminates_let], the quantification over the configuration
    [v1/s2] is done by refering to the big-step judgment [big]. *)

Inductive terminates : state -> trm -> Prop :=
  | terminates_val : forall s v,
      terminates s (trm_val v)
  | terminates_fix : forall s f x t1,
      terminates s (trm_fix f x t1)
  | terminates_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 ->
      terminates s (subst x v2 (subst f v1 t1)) ->
      terminates s (trm_app v1 v2)
  | terminates_let : forall s x t1 t2,
      terminates s t1 ->
      (forall v1 s2, big s t1 s2 v1 -> terminates s2 (subst x v1 t2)) ->
      terminates s (trm_let x t1 t2)
  | terminates_if : forall s b t1 t2,
      terminates s (if b then t1 else t2) ->
      terminates s (trm_if (val_bool b) t1 t2)
  | terminatess_div : forall s n1 n2,
      n2 <> 0 ->
      terminates s (val_div (val_int n1) (val_int n2))
  | terminates_rand : forall s n,
      n > 0 ->
      terminates s (val_rand (val_int n))
  | terminates_ref : forall s v,
      terminates s (val_ref v)
  | terminates_get : forall s p,
      Fmap.indom s p ->
      terminates s (val_get (val_loc p))
  | terminates_set : forall s p v,
      Fmap.indom s p ->
      terminates s (val_set (val_loc p) v)
  | terminates_free : forall s p,
      Fmap.indom s p ->
      terminates s (val_free (val_loc p)).

Section OmnibitTerminates.
Hint Constructors big omnibig.

(** We prove that [omnibig s t Q] is equivalent to the conjunction of
    [terminates s t] and to a partial correctness result asserting that
    if an evaluation of [t/s] terminates on some result then this result
    satisfies [Q]. (omni-big-step-iff-terminates-and-correct) *)

Lemma omnibig_iff_terminates_and_post : forall s t Q,
  omnibig s t Q <-> (terminates s t /\ (forall v s', big s t s' v -> Q v s')).
Proof using.
  iff M.
  { split.
    { induction M; try solve [constructors*].
      { rename M into M1, H into M2, IHM into IH1, H0 into IH2.
        constructors.
        { applys IH1. }
        { introv R. applys IH2. applys omnibig_and_big_inv M1 R. } } }
    { introv R. applys omnibig_and_big_inv M R. } }
  { destruct M as (HS&HQ). gen Q.
    induction HS; try solve [constructors*].
    { rename HS into M1, H into M2, IHHS into IH1, H0 into IH2.
      intros Q HQ.
      applys omnibig_let (fun v1 s2 => big s t1 s2 v1).
      { applys* IH1. }
      { introv R1. applys IH2.
        { applys R1. }
        { introv R2. applys* HQ. } } } }
Qed.

(** We prove that [terminates s t] is equivalent to [omnibig s t Any]. *)

Lemma terminates_iff_omnibig_any : forall s t,
  terminates s t <-> omnibig s t Any.
Proof using.
  intros. rewrite* (omnibig_iff_terminates_and_post s t Any).
Qed.

End OmnibitTerminates.

(** We can reformulate the right to left direction of
    [terminates_iff_omnibig_any] by stating that if [omnibig]
    holds for some [Q], then [terminates s t] holds. *)

Lemma terminates_of_omnibig : forall s t Q,
  omnibig s t Q ->
  terminates s t.
Proof using.
  introv M. rewrite terminates_iff_omnibig_any.
  applys omnibig_conseq M. intros s' v. auto.
Qed.

(** We can reformulate [omnibig_strongestpost_of_omnibig]
    with [terminates] as premise. (strongest-post-correct) *)

Lemma omnibig_strongestpost_of_terminates : forall s t,
  terminates s t ->
  omnibig s t (strongestpost s t).
Proof using.
  introv M. rewrite terminates_iff_omnibig_any in M.
  applys omnibig_strongestpost_of_omnibig M.
Qed.




(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Coinductive Omni-big-step *)

(* ########################################################### *)
(** ** Definition of Coinductive Omni-Big-Step *)

(** The definition of the predicate [coomnibig] is obtained by taking the
    constructors from the inductive definition of [steps], and considering
    the coinductive interpretation of these constructors. The coinductive
    interpretation allows for infinite derivation. It thereby introduces the
    possibility of diverging executions. Importantly, the predicate [coomnibig]
    still disallows executions that get stuck. *)

CoInductive coomnibig : state -> trm -> (val->state->Prop) -> Prop :=
  | coomnibig_val : forall s v Q,
      Q v s ->
      coomnibig s (trm_val v) Q
  | coomnibig_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      coomnibig s (trm_fix f x t1) Q
  | coomnibig_app_fix : forall s1 v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      coomnibig s1 (subst x v2 (subst f v1 t1)) Q ->
      coomnibig s1 (trm_app v1 v2) Q
  | coomnibig_let : forall Q1 s1 x t1 t2 Q,
      coomnibig s1 t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> coomnibig s2 (subst x v1 t2) Q) ->
      coomnibig s1 (trm_let x t1 t2) Q
  | coomnibig_if : forall s1 b t1 t2 Q,
      coomnibig s1 (if b then t1 else t2) Q ->
      coomnibig s1 (trm_if (val_bool b) t1 t2) Q
  | coomnibig_div : forall s n1 n2 Q,
      n2 <> 0 ->
      Q (val_int (Z.quot n1 n2)) s ->
      coomnibig s (val_div (val_int n1) (val_int n2)) Q
  | coomnibig_rand : forall s n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 s) ->
      coomnibig s (val_rand (val_int n)) Q
  | coomnibig_ref : forall s v Q,
      (forall p, ~ Fmap.indom s p ->
         Q (val_loc p) (Fmap.update s p v)) ->
      coomnibig s (val_ref v) Q
  | coomnibig_get : forall s p Q,
      Fmap.indom s p ->
      Q (Fmap.read s p) s ->
      coomnibig s (val_get (val_loc p)) Q
  | coomnibig_set : forall s p v Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.update s p v) ->
      coomnibig s (val_set (val_loc p) v) Q
  | coomnibig_free : forall s p Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.remove s p) ->
      coomnibig s (val_free (val_loc p)) Q.

(** Covariance property. *)

Lemma coomnibig_conseq : forall s t Q1 Q2,
  coomnibig s t Q1 ->
  Q1 ===> Q2 ->
  coomnibig s t Q2.
Proof using.
  introv M W. unfolds qimpl, himpl.
  gen s t Q1 Q2. cofix IH. intros. inverts M; try solve [ constructors* ].
Qed.

(** Assume [coomnibig s t Q] to hold. We prove that the postcondition [Q] holds of
    any output that [(s,t)] may evaluate to according to the judgment [big]. *)

Lemma coomnibig_inv_eval : forall s t v s' Q,
  coomnibig s t Q ->
  big s t s' v ->
  Q v s'.
Proof using.
  introv M R. gen Q. induction R; intros;
   try solve [inverts* M; tryfalse].
  { inverts M; tryfalse. inverts TEMP.
    applys* IHR Q. }
  { inverts M as M1 M2. applys IHR2 M2. applys IHR1 M1. }
  { inverts M. applys* IHR Q. }
Qed.


(* ########################################################### *)
(** ** From Total to Partial Correctness *)

(** Total correctness is a stronger property than partial correctness:
    [omnibig s t Q] entails [coomnibig s t Q]. *)

Lemma coomnibig_of_omnibig : forall s t Q,
  omnibig s t Q ->
  coomnibig s t Q.
Proof using.
  introv M. induction M; try solve [ constructors* ].
Qed.


(* ########################################################### *)
(** ** Interpretation of Coinductive Omni-Big-Step w.r.t. [safe] *)

(** The predicate [safe s t] asserts that an execution of the configuration
    [t/s] can never get stuck. Its definition is a simplified version of
    [coomnibig] where all occurences of [Q] are removed. In the rule for let-
    bindings, namely [safe_let], the quantification over the configuration
    [v1/s2] is done by refering to the big-step judgment [eval]. *)

CoInductive safe : state -> trm -> Prop :=
  | safe_val : forall s v,
      safe s (trm_val v)
  | safe_fix : forall s f x t1,
      safe s (trm_fix f x t1)
  | safe_app_fix : forall s v1 v2 f x t1,
      v1 = val_fix f x t1 ->
      safe s (subst x v2 (subst f v1 t1)) ->
      safe s (trm_app v1 v2)
  | safe_let : forall s x t1 t2,
      safe s t1 ->
      (forall v1 s2, big s t1 s2 v1 -> safe s2 (subst x v1 t2)) ->
      safe s (trm_let x t1 t2)
  | safe_if : forall s b t1 t2,
      safe s (if b then t1 else t2) ->
      safe s (trm_if (val_bool b) t1 t2)
  | safes_div : forall s n1 n2,
      n2 <> 0 ->
      safe s (val_div (val_int n1) (val_int n2))
  | safe_rand : forall s n,
      n > 0 ->
      safe s (val_rand (val_int n))
  | safe_ref : forall s v,
      safe s (val_ref v)
  | safe_get : forall s p,
      Fmap.indom s p ->
      safe s (val_get (val_loc p))
  | safe_set : forall s p v,
      Fmap.indom s p ->
      safe s (val_set (val_loc p) v)
  | safe_free : forall s p,
      Fmap.indom s p ->
      safe s (val_free (val_loc p)).

Section EvalnpSafe.
Hint Constructors big coomnibig.

(** We prove that [coomnibig s t Q] is equivalent to the conjunction of [safe s t]
    and to a partial correctness result asserting that if an evaluation of
    [t/s] terminates on a particular result, then this result satisfies [Q].
    omni-cobig-iff-safe-and-correct *)

Lemma coomnibig_iff_safe_and_post : forall s t Q,
  coomnibig s t Q <-> (safe s t /\ (forall v s', big s t s' v -> Q v s')).
Proof using.
  iff M.
  { split.
    { gen s t Q. cofix IH. introv M. inverts M; try solve [constructors*].
      { rename H into M1, H0 into M2. constructors.
        { applys IH M1. }
        { introv R. applys IH M2. applys coomnibig_inv_eval M1 R. } } }
    { introv R. applys coomnibig_inv_eval M R. } }
  { destruct M as (HS&HQ). gen s t Q. cofix IH. intros. inverts HS;
     try solve [constructors*].
    { rename H into M1, H0 into M2.
      applys coomnibig_let (fun v1 s2 => big s t1 s2 v1).
      { applys* IH M1. }
      { introv R1. applys IH M2.
        { applys R1. }
        { introv R2. applys* HQ. } } } }
Qed.

(** We prove that [safe s t] is equivalent to [coomnibig s t Any]. *)

Lemma safe_iff_coomnibig_any : forall s t,
  safe s t <-> coomnibig s t Any.
Proof using.
  intros. rewrite* (coomnibig_iff_safe_and_post s t Any).
Qed.

End EvalnpSafe.



(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Characterization of Divergence *)

(** We present several characterization of divergence and prove
    them equivalent. *)


(* ########################################################### *)
(** ** Omni-Big-Step Divergence *)

(** The judgment [coomnidiv s t] asserts that every possible
    execution of the program [(s,t)] diverges. It is defined
    in terms of the coinductive Omni-big-step judgment. *)

Definition coomnidiv (s:state) (t:trm) : Prop :=
  coomnibig s t Empty.



(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Beyond A-normal form: Adding the Bind Rule  *)

Module Bind.

(* ########################################################### *)
(** ** Omni-Big-Step Judgment with Evaluation under Context *)

(** Definition of evaluation contexts *)

Inductive ctx : Type :=
  | ctx_hole : ctx
  | ctx_let_1 : var -> ctx -> trm -> ctx
  | ctx_app_1 : ctx -> trm -> ctx
  | ctx_app_2 : val -> ctx -> ctx
  | ctx_if_1 : ctx -> trm -> trm -> ctx.

Fixpoint ctx_app (E:ctx) (u:trm) : trm :=
  match E with
  | ctx_hole => u
  | ctx_let_1 x E1 t2 => trm_let x (ctx_app E1 u) t2
  | ctx_app_1 E1 t2 => trm_app (ctx_app E1 u) t2
  | ctx_app_2 v1 E2 => trm_app (trm_val v1) (ctx_app E2 u)
  | ctx_if_1 E0 t1 t2 => trm_if (ctx_app E0 u) t1 t2
  end.

Definition isvalue (t:trm) : Prop :=
  match t with
  | trm_val v => True
  | _ => False
  end.

(** Judgment [omnibig s t Q] *)

Inductive omnibig : state -> trm -> (val->state->Prop) -> Prop :=
  | omnibig_bind : forall Q1 s t1 E Q,
      ~ isvalue t1 ->
      omnibig s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> omnibig s2 (ctx_app E (trm_val v1)) Q) ->
      omnibig s (ctx_app E t1) Q
  | omnibig_val : forall s v Q,
      Q v s ->
      omnibig s (trm_val v) Q
  | omnibig_fix : forall s f x t1 Q,
      Q (val_fix f x t1) s ->
      omnibig s (trm_fix f x t1) Q
  | omnibig_app_fix : forall s v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      omnibig s (subst x v2 (subst f v1 t1)) Q ->
      omnibig s (trm_app v1 v2) Q
  | omnibig_let : forall s x v1 t2 Q,
      omnibig s (subst x v1 t2) Q ->
      omnibig s (trm_let x v1 t2) Q
  | omnibig_if : forall s b t1 t2 Q,
      omnibig s (if b then t1 else t2) Q ->
      omnibig s (trm_if (val_bool b) t1 t2) Q
  | omnibig_div : forall s n1 n2 Q,
      n2 <> 0 ->
      Q (val_int (Z.quot n1 n2)) s ->
      omnibig s (val_div (val_int n1) (val_int n2)) Q
  | omnibig_rand : forall s n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 s) ->
      omnibig s (val_rand (val_int n)) Q
  | omnibig_ref : forall s v Q,
      (forall p, ~ Fmap.indom s p ->
         Q (val_loc p) (Fmap.update s p v)) ->
      omnibig s (val_ref v) Q
  | omnibig_get : forall s p Q,
      Fmap.indom s p ->
      Q (Fmap.read s p) s ->
      omnibig s (val_get (val_loc p)) Q
  | omnibig_set : forall s p v Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.update s p v) ->
      omnibig s (val_set (val_loc p) v) Q
  | omnibig_free : forall s p Q,
      Fmap.indom s p ->
      Q val_unit (Fmap.remove s p) ->
      omnibig s (val_free (val_loc p)) Q.

Lemma omnibig_conseq : forall s t Q1 Q2,
  omnibig s t Q1 ->
  Q1 ===> Q2 ->
  omnibig s t Q2.
Proof using.
  introv M W.
  asserts W': (forall v h, Q1 v h -> Q2 v h). { auto. } clear W.
  induction M; try solve [ constructors* ].
Qed.

Lemma omnibig_frame : forall h1 h2 t Q,
  omnibig h1 t Q ->
  Fmap.disjoint h1 h2 ->
  omnibig (h1 \u h2) t (fun r => Q r \* (= h2)).
Proof using.
  introv M HD. gen h2. induction M; intros;
    try solve [ hint hstar_intro; constructors* ].
  { rename M into M1, H into NV1, H0 into M2, IHM into IH1, H1 into IH2.
    specializes IH1 HD. applys omnibig_bind NV1 IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): hstar_inv HK. subst. applys* IH2. }
  { rename H into M. applys omnibig_ref. intros p Hp.
    rewrite Fmap.indom_union_eq in Hp. rew_logic in Hp. destruct Hp as [Hp1 Hp2].
    rewrite* Fmap.update_union_not_r. applys hstar_intro.
    { applys* M. } { auto. } { applys* Fmap.disjoint_update_not_r. } }
  { applys omnibig_get. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.read_union_l. applys* hstar_intro. } }
  { applys omnibig_set. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.update_union_l. applys hstar_intro.
      { auto. } { auto. } { applys* Fmap.disjoint_update_l. } } }
  { applys omnibig_free. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.remove_disjoint_union_l. applys hstar_intro.
      { auto. } { auto. } { applys* Fmap.disjoint_remove_l. } } }
Qed.





(* ########################################################### *)
(* ########################################################### *)
(** * Compiler Correctness For Terminating Programs *)

Section CompilerCorrectnessTerminating.

(** Consider a compilation function. For simplicity, we assume
    here that the corresponding compilation phase does not affect
    the memory state during program executions (this is in particular
    the case for compilation of purely functional programs). *)

Parameter compile : trm -> trm.

(** Assume that it satisfies Omni-forward-preservation. *)

Parameter omni_forward_preservation_for_compile : forall s t Q,
  omnibig s t Q ->
  omnibig s (compile t) Q.

(** We show that Omni-forward-preservation entails correctness
    for terminating programs. *)

Lemma compile_correct : forall s t,
  terminates s t ->
     terminates s (compile t)
  /\ (forall s' v, big s (compile t) s' v -> big s t s' v).
Proof using.
  introv HT.
  forwards R: omni_forward_preservation_for_compile s t (strongestpost s t).
  { applys omnibig_strongestpost_of_terminates HT. }
  split.
  { applys terminates_of_omnibig R. }
  { introv M. applys omnibig_and_big_inv R M. }
Qed.

End CompilerCorrectnessTerminating.




(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Inductive PRECISE-Omni-Big-Step  *)

(* ########################################################### *)
(** ** Definition of precise Omni-semantics *)

(** Judgment [pomnibig s t Q] with precise outcome *)

Inductive pomnibig : state -> trm -> (val->state->Prop) -> Prop :=
  | pomnibig_val : forall s v Q,
      Q = exactly v s ->
      pomnibig s (trm_val v) Q
  | pomnibig_fix : forall s f x t1 Q,
      Q = exactly (val_fix f x t1) s ->
      pomnibig s (trm_fix f x t1) Q
  | pomnibig_app_fix : forall s v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      pomnibig s (subst x v2 (subst f v1 t1)) Q ->
      pomnibig s (trm_app v1 v2) Q
  | pomnibig_let : forall Q1 s x t1 t2 Q (Qof:val->state->val->hprop),
      pomnibig s t1 Q1 ->
      (forall v1 s2, Q1 v1 s2 -> pomnibig s2 (subst x v1 t2) (Qof v1 s2)) ->
      Q = (fun v0 s0 => exists s1 v1, Q1 v1 s1 /\ Qof v1 s1 v0 s0) ->
      pomnibig s (trm_let x t1 t2) Q
  | pomnibig_if : forall s b t1 t2 Q,
      pomnibig s (if b then t1 else t2) Q ->
      pomnibig s (trm_if (val_bool b) t1 t2) Q
  | pomnibig_div : forall s n1 n2 Q,
      n2 <> 0 ->
      Q (val_int (Z.quot n1 n2)) s ->
      pomnibig s (val_div (val_int n1) (val_int n2)) Q
  | pomnibig_rand : forall s n Q (Qof:int->val->hprop),
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Qof n1 = exactly (val_int n1) s) ->
      Q = (fun v0 s0 => exists n1, 0 <= n1 < n /\ Qof n1 v0 s0) ->
      pomnibig s (val_rand (val_int n)) Q
  | pomnibig_ref : forall s v Q (Qof:loc->val->hprop),
      (forall p, ~ Fmap.indom s p ->
         Qof p = exactly (val_loc p) (Fmap.update s p v)) ->
      Q = (fun v0 s0 => exists p,  ~ Fmap.indom s p /\ Qof p v0 s0) ->
      pomnibig s (val_ref v) Q
  | pomnibig_get : forall s p Q,
      Fmap.indom s p ->
      Q = exactly (Fmap.read s p) s ->
      pomnibig s (val_get (val_loc p)) Q
  | pomnibig_set : forall s p v Q,
      Fmap.indom s p ->
      Q = exactly val_unit (Fmap.update s p v) ->
      pomnibig s (val_set (val_loc p) v) Q
  | pomnibig_free : forall s p Q,
      Fmap.indom s p ->
      Q = exactly val_unit (Fmap.remove s p) ->
      pomnibig s (val_free (val_loc p)) Q.


(* ########################################################### *)
(** ** Properties of precise Omni-semantics *)

(** [pomnibig s t Q] relates a program with exactly the set [Q]
    that corresponds exactly to the set of possible results,
    no more, no less. *)

Lemma pomnibig_characterizes_strongestpost : forall s t Q,
  pomnibig s t Q ->
  Q = strongestpost s t.
Proof using.
  introv M. induction M.
  { subst. extens; intros v' s'. unfold exactly, strongestpost.
    iff (->&->) M1. { constructors*. } { inverts* M1. } }
  { subst. extens; intros v' s'. unfold exactly, strongestpost.
    iff (->&->) M1. { constructors*. } { inverts* M1. } }
  { subst. extens; intros v' s'. unfold strongestpost. iff M1.
    { constructors*. } { inverts M1 as E. inverts* E. } }
  { rename H0 into K.
    subst. extens; intros v' s'. unfolds strongestpost. iff (s1&v1&R1&M1) M1.
    { rewrite* K in M1. constructors*. }
    { inverts M1 as R1 R2. exists. split*. rewrite* K. } }
  { subst. extens; intros v' s'. unfold strongestpost. iff M1.
    { applys* big_if. } { inverts* M1. } }
  { subst. extens; intros v' s'. unfold exactly, strongestpost.
    iff (->&->) M1. { constructors*. } { inverts* M1. } }
  { rename H0 into K.
    subst. extens; intros v' s'. unfold exactly, strongestpost.
    iff (n1&E1&R1) M1.
    { rewrite* K in R1. inverts R1. applys* big_rand. }
    { inverts M1; tryfalse. exists. split*. rewrite* K. applys exactly_intro. } }
  { rename H into K.
    subst. extens; intros v' s'. unfold exactly, strongestpost.
    iff (p&E1&R1) M1.
    { rewrite* K in R1. inverts R1. applys* big_ref. }
    { inverts M1; tryfalse. exists. split*. rewrite* K. applys exactly_intro. } }
  { subst. extens; intros v' s'. unfold exactly, strongestpost.
    iff (->&->) M1. { constructors*. } { inverts M1; tryfalse. auto. } }
  { subst. extens; intros v' s'. unfold exactly, strongestpost.
    iff (->&->) M1. { constructors*. } { inverts M1; tryfalse. auto. } }
  { subst. extens; intros v' s'. unfold exactly, strongestpost.
    iff (->&->) M1. { constructors*. } { inverts M1; tryfalse. auto. } }
Qed.

(** Assume [pomnibig s t Q] to hold. Prove that the postcondition [Q] holds of
    any output that [(s,t)] may evaluate to according to the judgment [big]. *)

Lemma pomnibig_and_big_inv : forall s t v s' Q,
  pomnibig s t Q ->
  big s t s' v ->
  Q v s'.
Proof using.
  introv M R. lets E: pomnibig_characterizes_strongestpost M.
  rewrite E. apply R.
Qed.

(** If [pomnibig s t Q] holds, then there exists an output
    [(s',v)] that [(s,t)] may evaluate to according to the judgment
    [big], and that this output satisfies [Q]. *)

Lemma pomnibig_to_one_big : forall s t Q,
  pomnibig s t Q ->
  exists s' v, big s t s' v /\ Q v s'.
Proof using.
  introv M. cuts (s'&v&R): (exists s' v, big s t s' v).
  { exists. split. { applys R. } { applys pomnibig_and_big_inv M R. } }
  induction M.
  { exists. applys big_val. }
  { exists. applys big_fix. }
  { rename IHM into IHM1, M into M1.
    forwards (s'&v&R): IHM1.
    exists. applys* big_app_fix R. }
  { rename IHM into IHM1, H0 into IHM2, M into M1, H into M2.
    forwards (s1'&v1&R1): IHM1.
    lets HQ1: pomnibig_and_big_inv M1 R1.
    forwards (s'&v&R2): IHM2 HQ1.
    exists. applys big_let R1 R2. }
  { forwards (s'&v&R1): IHM.
    exists. applys* big_if R1. }
  { exists. applys* big_div. }
  { rename H0 into N.
    exists. applys* big_rand 0. math. }
  { forwards* (p&D&N): (exists_fresh null s).
    exists. applys* big_ref. }
  { exists. applys* big_get. }
  { exists. applys* big_set. }
  { exists. applys* big_free. }
Qed.

(** Auxilary lemma for the next proof *)
Lemma strongestpost_eq_exactly : forall s t v,
  (forall v' s', big s t s' v' <-> v' = v /\ s' = s) ->
  strongestpost s t = exactly v s.
Proof using.
  introv M. unfold strongestpost, exactly. extens*.
Qed.

(** If a term is safe according to [omnibig], which overapproximates
    the set of results, then [pcpbig], which is precise, holds. *)
Lemma pomnibig_of_omnibig : forall s t Q,
  omnibig s t Q ->
  pomnibig s t (strongestpost s t).
Proof using.
  hint exactly_intro. introv M. induction M.
  { constructors. applys strongestpost_eq_exactly.
   intros. iff R (->&->). { inverts* R. } { constructors*. } }
  { constructors. applys strongestpost_eq_exactly.
    intros. iff R (->&->). { inverts* R. } { constructors*. } }
  { applys* pomnibig_app_fix. applys_eq IHM. extens.
    unfold strongestpost. intros v' s'. iff R.
    { subst. inverts R as E. inverts* E. } { applys* big_app_fix. } }
  { rename IHM into IH1, H0 into IH2.
    applys pomnibig_let (strongestpost s t1)
     (fun v1 s2 => strongestpost s2 (subst x v1 t2)) IH1.
    { intros v1 s2 M1. applys IH2. applys* omnibig_inv_strongestpost_qimpl M. }
    { unfold strongestpost. extens. intros v' s'. iff R (?&?&?&?).
      { inverts* R. } { constructors*. } } }
  { constructors. applys_eq IHM. extens. unfold strongestpost.
    intros v' s'. iff R. { inverts* R. } { constructors*. } }
  { constructors. applys strongestpost_eq_exactly.
    intros. iff R (->&->). { inverts* R. } { constructors*. } }
  { applys* pomnibig_rand. simpl. unfold strongestpost. extens.
    intros v' s'. iff R (?&?&(->&->)). { inverts R; tryfalse. exists* n1. }
    { applys* big_rand. } }
  { applys* pomnibig_ref. simpl. unfold strongestpost. extens.
    intros v' s'. iff R (?&?&(->&->)). { inverts R; tryfalse. exists* p. }
    { applys* big_ref. } }
  { constructors*. applys strongestpost_eq_exactly.
    intros. iff R (->&->). { inverts R; tryfalse; eauto. } { constructors*. } }
  { constructors*. unfold strongestpost, exactly. extens*.
    intros v' s'. iff R (->&->). { inverts R; tryfalse; eauto. } { constructors*. } }
  { constructors*. unfold strongestpost, exactly. extens*.
    intros v' s'. iff R (->&->). { inverts R; tryfalse; eauto. } { constructors*. } }
Qed.

(** See also [omnibig_inv_strongestpost_qimpl], which asserts that
    if [omnibig s t Q], then [Q] contains [strongestpost s t]. *)

