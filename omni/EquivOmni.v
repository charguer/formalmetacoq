(****************************************************************
* Imperative Lambda-calculus                                    *
* Equivalence Proofs for Omni-Small and Omni-Big-Step Semantics *
*****************************************************************)

Set Implicit Arguments.
Require Export OmniBig OmniSmall.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types s : state.

Implicit Types P : state->trm->Prop.
Implicit Types Q : val->state->Prop.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Equivalence Proofs for Total Correctness *)

(** We start by establishing the equivalence between [stepsinto] and [omnibig].
    We focus first on the direction from [stepsinto] to [omnibig]. *)


(* ########################################################### *)
(** ** From Omni-Big-Step to Inductive-Small-Steps [stepsinto] *)

(** We begin with a key lemma: if a configuration [(s1,t1)] takes a step to
    [(s2,t2)], then this first configuration admits the same postconditions
    as the second configuration. *)

Lemma omnibig_of_step_and_omnibig : forall s1 t1 Q,
  (exists s2 t2, step s1 t1 s2 t2) ->
  (forall s2 t2, step s1 t1 s2 t2 -> omnibig s2 t2 Q) ->
  omnibig s1 t1 Q.
Proof using.
  introv (s2&t2&R1) RS. gen Q. induction R1; intros.
  { applys omnibig_let (fun v1 s2 => omnibig s2 (subst x v1 t2) Q).
    { applys IHR1. intros s1b t1b Kb.
      forwards M: RS. { applys step_let_ctx Kb. }
      { inverts M as M1 M2. applys omnibig_conseq M1. applys M2. } }
    { intros v1 s' K. applys K. } }
  { applys omnibig_fix. forwards M: RS. { applys step_fix. }
    { inverts* M. } }
  { applys* omnibig_app_fix. forwards M: RS. { applys* step_app_fix. }
    { applys M. } }
  { applys* omnibig_if. forwards M: RS. { applys* step_if. } { applys M. } }
  { applys omnibig_let (fun v' s' => v' = v1 /\ s' = s).
    { applys* omnibig_val. }
    { intros ? ? (->&->). forwards M: RS. { applys* step_let. }
      { applys M. } } }
  { applys* omnibig_div. forwards M: RS. { applys* step_div. }
    { inverts* M. } }
  { applys* omnibig_rand.
    { math. }
    { intros n2 N2. forwards M: RS. { applys* step_rand n2. }
      { inverts* M. } } }
  { applys omnibig_ref. intros p' D.
    forwards M: RS p'. { applys* step_ref. } { inverts* M. } }
  { applys* omnibig_get. forwards M: RS. { applys* step_get. }
    { inverts* M. } }
  { applys* omnibig_set. forwards M: RS. { applys* step_set. }
    { inverts* M. } }
  { applys* omnibig_free. forwards M: RS. { applys* step_free. }
    { inverts* M. } }
Qed.

(** By exploiting the above lemma over all the steps of an execution, we obtain
    the fact that [stepsinto] implies [omnibig]. *)

Lemma omnibig_of_stepsinto : forall s t Q,
  stepsinto s t Q ->
  omnibig s t Q.
Proof using.
  introv M. induction M.
  { applys* omnibig_val. }
  { applys* omnibig_of_step_and_omnibig. }
Qed.


(* ########################################################### *)
(** ** From Inductive-Small-Steps [stepsinto] to Omni-Big-Step *)

(** Let's now turn to the second direction, from [omnibig] to [stepsinto].
    We first need an introduction lemma for let-bindings for [stepsinto]. *)

Lemma stepsinto_let : forall s x t1 t2 Q1 Q,
  stepsinto s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> stepsinto s1 (subst x v1 t2) Q) ->
  stepsinto s (trm_let x t1 t2) Q.
Proof using.
  introv M1 M2. gen_eq Q1': Q1.
  induction M1; intros; subst.
  { apply stepsinto_step.
    { do 2 esplit. applys step_let. }
    { introv R. inverts R as R'. { inverts R'. } applys* M2. } }
  { rename t into t1, H1 into IH.
    destruct H as (s'&t'&RE). applys stepsinto_step.
    { do 2 esplit. constructors. applys RE. }
    { introv R. inverts R as R'.
      { applys* IH R' M2. }
      { false. inverts RE. } } }
Qed.

(** The proof is carried out by induction on the big-step relation. *)

Lemma stepsinto_of_omnibig : forall s t Q,
  omnibig s t Q ->
  stepsinto s t Q.
Proof using.
  introv M. induction M.
  { applys* stepsinto_val. }
  { applys stepsinto_step.
    { do 2 esplit. applys step_fix. }
    { introv K. inverts K. applys* stepsinto_val. } }
  { rename H into E. applys stepsinto_step.
    { do 2 esplit. applys* step_app_fix. }
    { introv K. invert K; try solve [ intros; false ].
      introv -> -> -> -> -> R. inverts E. applys IHM. } }
  { rename M into M1, H into M2, IHM into IHM1, H0 into IHM2.
    tests C: (exists v1, t1 = trm_val v1).
    { destruct C as (v1&->). applys stepsinto_step.
      { do 2 esplit. applys* step_let. }
      { introv K. inverts K as K1 K2.
        { inverts K1. }
        { inverts IHM1 as K3 K4.
          { applys* IHM2. }
          { destruct K3 as (?&?&K5). inverts K5. } } } }
    { applys stepsinto_step.
      { inverts IHM1 as K3 K4.
        { false* C. }
        { destruct K3 as (?&?&K5). do 2 esplit. applys* step_let_ctx. } }
      { introv K. inverts K as K'; [|false* C].
        inverts IHM1 as K5 K6; [false* C|].
        specializes K6 K'. applys* stepsinto_let. } } }
  { applys stepsinto_step.
    { do 2 esplit. applys* step_if. }
    { introv K. inverts K. applys IHM. } }
  { applys stepsinto_step.
    { do 2 esplit. applys* step_div. }
    { introv K. inverts K. applys* stepsinto_val. } }
  { applys stepsinto_step.
    { do 2 esplit. applys* step_rand 0. math. }
    { introv K. inverts K; tryfalse. applys* stepsinto_val. } }
  { applys stepsinto_step.
    { forwards~ (p&D&N): (exists_fresh null s).
      do 2 esplit. applys* step_ref. }
    { introv K. inverts K; tryfalse. applys* stepsinto_val. } }
  { applys stepsinto_step.
    { do 2 esplit. applys* step_get. }
    { introv K. inverts K; tryfalse. applys* stepsinto_val. } }
  { applys stepsinto_step.
    { do 2 esplit. applys* step_set. }
    { introv K. inverts K; tryfalse. applys* stepsinto_val. } }
  { applys stepsinto_step.
    { do 2 esplit. applys* step_free. }
    { introv K. inverts K; tryfalse. applys* stepsinto_val. } }
Qed.


(* ########################################################### *)
(** ** Equivalence of Omni-Big-Step with Small-Step Characterizations *)

(** Combining the two directions, we obtain the desired equivalence between
    omni-big-step and inductive-small-step. *)

Lemma stepsinto_eq_omnibig :
  stepsinto = omnibig.
Proof using.
  extens. intros s t Q. iff M.
  { applys* omnibig_of_stepsinto. }
  { applys* stepsinto_of_omnibig. }
Qed.

(** The final equivalence follows. *)

Lemma omnibig_iff_eventually : forall s t Q,
  omnibig s t Q <-> eventually s t (pred_of_post Q).
Proof using.
  intros. rewrite <- stepsinto_eq_omnibig.
  rewrite* stepsinto_iff_eventually.
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Equivalence Proofs for Partial Correctness *)

(** The first step of the proof is to formally relate [costepsinto]
   and [coomnibig], which are both defined coinductively. *)


(* ########################################################### *)
(** ** From Co-Omni-Big-Step to Co-Inductive-Small-Steps [costepsinto] *)

(** For the first direction, we need one key inversion lemma. It
    is stated below. Its hypothesis is [coomnibig s t Q], and its conclusion
    corresponds to the disjunction of the constructors of the inductive
    definition of [costepsinto s t Q]. *)

Lemma coomnibig_inv_step : forall s t Q,
  coomnibig s t Q ->
     (exists v, t = trm_val v /\ Q v s)
  \/ ((exists s' t', step s t s' t' /\ coomnibig s' t' Q)
      /\ (forall s' t', step s t s' t' -> coomnibig s' t' Q)).
Proof using.
  introv M. gen s Q. induction t; intros; inverts M as.
  { introv R. left. eauto. }
  { introv R. right. split.
    { exists. split. { applys step_fix. } { applys* coomnibig_val. } }
    { intros s' t' S. inverts S. applys* coomnibig_val. } }
  { introv M1. right. split.
    { exists. split. { applys* step_app_fix. } { auto. } }
    { intros s' t' S. inverts S as E. inverts E. auto. } }
  { introv R. right. split.
    { exists. split. { applys* step_div. } { applys* coomnibig_val. } }
    { intros s' t' S. inverts S. applys* coomnibig_val. } }
  { introv N R. right. split.
    { exists. split. { applys* step_rand 0. math. }
       { applys* coomnibig_val. applys R. math. } }
    { intros s' t' S. inverts S; tryfalse. applys* coomnibig_val. } }
  { introv R. right. split.
    { forwards~ (p&D&N): (exists_fresh null s).
      exists. split. { applys* step_ref. } { applys* coomnibig_val. } }
    { intros s' t' S. inverts S; tryfalse. applys* coomnibig_val. } }
  { introv D R. right. split.
    { exists. split. { applys* step_get. } { applys* coomnibig_val. } }
    { intros s' t' S. inverts S; tryfalse. applys* coomnibig_val. } }
  { introv D R. right. split.
    { exists. split. { applys* step_set. } { applys* coomnibig_val. } }
    { intros s' t' S. inverts S; tryfalse. applys* coomnibig_val. } }
  { introv D R. right. split.
    { exists. split. { applys* step_free. } { applys* coomnibig_val. } }
    { intros s' t' S. inverts S; tryfalse. applys* coomnibig_val. } }
  { introv M1 M2. rename v into x. right. split.
    { forwards [(v1&->&HQ1)|((s'&t'&S'&M')&_)]: IHt1 M1.
      { exists. split. { applys step_let. } { applys* M2. } }
      { exists. split.
        { applys step_let_ctx S'. }
        { applys coomnibig_let M'. applys M2. } } }
    { intros s' t' S. inverts S as S.
      { forwards [(v1&->&HQ1)|(_&M3)]: IHt1 M1.
        { inverts S. }
        { specializes M3 S. applys coomnibig_let M3 M2. } }
      { inverts M1 as R. applys* M2. } } }
  { introv M1. right. split.
    { exists. split. { applys step_if. } { auto. } }
    { intros s' t' S. inverts S. auto. } }
Qed.

(** Using this inversion lemma, it is straightforward to derive the
    implication from [coomnibig] to [costepsinto]. *)

Lemma costepsinto_of_coeval : forall s t Q,
  coomnibig s t Q ->
  costepsinto s t Q.
Proof.
  cofix IH. introv M. lets C: coomnibig_inv_step M.
  destruct C as [(v&->&HQ)|((s'&t'&S&M1)&M2)].
  { applys costepsinto_val HQ. }
  { applys costepsinto_step.
    { exists. applys S. }
    { intros s1 t1 S'. applys IH. applys M2 S'. } }
Qed.


(* ########################################################### *)
(** ** From Co-Inductive-Small-Steps [costepsinto] to Co-Omni-Big-Step *)

(** The reciprocal direction is from [costepsinto] to [coomnibig].
    To establish it, we need inversion lemmas for let-bindings. *)

Lemma costepsinto_let_inv_ctx : forall x s1 t1 t2 Q Q1,
  costepsinto s1 (trm_let x t1 t2) Q ->
  (fun v s => steps s1 t1 s v) ===> Q1 ->
  costepsinto s1 t1 Q1.
Proof using.
  cofix IH. introv M WQ. inverts M as M0 M'.
  tests C: (exists v1, t1 = trm_val v1).
  { destruct C as (v1&->). applys costepsinto_val.
    applys WQ. applys steps_refl. }
  { applys costepsinto_step.
    { destruct M0 as (s'&t'&S). inverts S as. 2:{ false* C. }
      intros S. exists. applys S. }
    { intros s2 t1' S. applys IH.
      { applys M'. applys step_let_ctx S. }
      { intros v s R. applys WQ. applys steps_step S R. } } }
Qed.

Lemma costepsinto_let_inv_cont : forall s1 s2 v1 x t1 t2 Q,
  costepsinto s1 (trm_let x t1 t2) Q ->
  steps s1 t1 s2 v1 ->
  costepsinto s2 (subst x v1 t2) Q.
Proof using.
  introv M R. gen_eq t1': (trm_val v1). induction R; intros; subst.
  { inverts M as _ M'. applys M'. applys step_let. }
  { rename H into S, R into R', t0 into t1'.
    inverts M as _ M'. applys* IHR. applys M'.
    applys step_let_ctx S. }
Qed.

Lemma costepsinto_let_inv : forall s1 x t1 t2 Q,
  costepsinto s1 (trm_let x t1 t2) Q ->
  exists Q1, costepsinto s1 t1 Q1
          /\ (forall v1 s2, Q1 v1 s2 -> costepsinto s2 (subst x v1 t2) Q).
Proof using.
  introv M. exists (fun v s => steps s1 t1 s (trm_val v)). split.
  { applys* costepsinto_let_inv_ctx M. }
  { introv K. applys* costepsinto_let_inv_cont M K. }
Qed.

(** Using these inversion lemmas, we can prove by induction the first
    direction, from [costepsinto] to [coomnibig]. *)

Lemma coomnibig_of_costepsinto : forall s t Q,
  costepsinto s t Q ->
  coomnibig s t Q.
Proof using.
  cofix IH. introv M. destruct t; try solve [ inverts M; false_invert ].
  { inverts M as.
    { intros R. applys coomnibig_val R. }
    { intros (s'&t'&S) _. inverts S. } }
  { inverts M as.
    { intros (s'&t'&S) _. inverts S. } }
  { rename v into f, v0 into x, t into t1.
    inverts M as (s'&t'&S) M1. inverts S.
    applys coomnibig_fix.
    forwards M1': M1. { applys step_fix. }
    inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
  { inverts M as (s'&t'&S) M1. inverts S as.
    { applys coomnibig_app_fix. { reflexivity. } applys IH.
      applys M1. applys* step_app_fix. }
    { introv N. applys* coomnibig_div.
      forwards M1': M1. { applys* step_div. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv N. applys* coomnibig_rand. { math. }
      intros n1' N1.
      forwards M1': M1. { applys* step_rand n1'. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv D. applys* coomnibig_ref. intros p' D'.
      forwards M1': M1. { applys* step_ref p'. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv D. applys* coomnibig_get.
      forwards M1': M1. { applys* step_get. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv D. applys* coomnibig_set.
      forwards M1': M1. { applys* step_set. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } }
    { introv D. applys* coomnibig_free.
      forwards M1': M1. { applys* step_free. }
      inverts M1' as. { auto. } { intros. false* exists_step_val_inv. } } }
  { lets (Q1&M1&M2): costepsinto_let_inv M. applys coomnibig_let.
    { applys IH. applys M1. }
    { introv R. applys IH. applys M2 R. } }
  { inverts M as (s'&t'&S) M1. inverts S. applys coomnibig_if.
    applys IH. applys M1. applys step_if. }
Qed.


(* ########################################################### *)
(** ** Equivalence of Co-Omni-Big-Step with Small-Step Characterizations *)

(** Combining the two directions yields the equality between [costepsinto] and
    [coomnibig], and that between [partial] and [coomnibig]. *)

Lemma costepsinto_eq_omnibigp :
   costepsinto = coomnibig.
Proof using.
  extens. intros s t Q. iff M.
  { applys* coomnibig_of_costepsinto. }
  { applys* costepsinto_of_coeval. }
Qed.

(** Finally, we conclude that coinductive Omni-big-step matches the
    standard small-step characterization of partial correctness. *)

Lemma coomnibig_eq_partial :
  coomnibig = partial.
Proof using.
  rewrite <- costepsinto_eq_partial. rewrite* costepsinto_eq_omnibigp.
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Equivalence Proofs for Divergence *)

(** We establish the equivalence between the small-step characterisation
   and the coinductive Omni-big-step characterization of divergence. *)

Lemma stepsinf_eq_coomnidiv :
  stepsinf = coomnidiv.
Proof using.
  extens. intros s t. unfold coomnidiv.
  rewrite stepsinf_iff_omnibigps_Empty.
  rewrite <- costepsinto_eq_omnibigp.
  rewrite* costepsinto_eq_partial.
Qed.
