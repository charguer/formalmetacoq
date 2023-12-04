(****************************************************************
* Imperative Lambda-calculus                                    *
* Equivalence Proofs for Omni-Small and Omni-Big-Step Semantics *
*****************************************************************)

Set Implicit Arguments.
Require Export Syntax.


(* ########################################################### *)
(** ** Equivalence Between Eventually and Omni-Big-Step Semantics *)

(** We start by establishing the equivalence between [bigsmall] and [omnibig].
    We focus first on the direction from [bigsmall] to [omnibig]. *)

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
    the fact that [bigsmall] implies [omnibig]. *)

Lemma omnibig_of_bigsmall : forall s t Q,
  bigsmall s t Q ->
  omnibig s t Q.
Proof using.
  introv M. induction M.
  { applys* omnibig_val. }
  { applys* omnibig_of_step_and_omnibig. }
Qed.

(** Let's now turn to the second direction, from [omnibig] to [bigsmall].
    We first need an introduction lemma for let-bindings for [bigsmall]. *)

Lemma bigsmall_let : forall s x t1 t2 Q1 Q,
  bigsmall s t1 Q1 ->
  (forall s1 v1, Q1 v1 s1 -> bigsmall s1 (subst x v1 t2) Q) ->
  bigsmall s (trm_let x t1 t2) Q.
Proof using.
  introv M1 M2. gen_eq Q1': Q1.
  induction M1; intros; subst.
  { apply bigsmall_step.
    { do 2 esplit. applys step_let. }
    { introv R. inverts R as R'. { inverts R'. } applys* M2. } }
  { rename t into t1, H1 into IH.
    destruct H as (s'&t'&RE). applys bigsmall_step.
    { do 2 esplit. constructors. applys RE. }
    { introv R. inverts R as R'.
      { applys* IH R' M2. }
      { false. inverts RE. } } }
Qed.

(** The proof is carried out by induction on the big-step relation. *)

Lemma bigsmall_of_omnibig : forall s t Q,
  omnibig s t Q ->
  bigsmall s t Q.
Proof using.
  introv M. induction M.
  { applys* bigsmall_val. }
  { applys bigsmall_step.
    { do 2 esplit. applys step_fix. }
    { introv K. inverts K. applys* bigsmall_val. } }
  { rename H into E. applys bigsmall_step.
    { do 2 esplit. applys* step_app_fix. }
    { introv K. invert K; try solve [ intros; false ].
      introv -> -> -> -> -> R. inverts E. applys IHM. } }
  { rename M into M1, H into M2, IHM into IHM1, H0 into IHM2.
    tests C: (exists v1, t1 = trm_val v1).
    { destruct C as (v1&->). applys bigsmall_step.
      { do 2 esplit. applys* step_let. }
      { introv K. inverts K as K1 K2.
        { inverts K1. }
        { inverts IHM1 as K3 K4.
          { applys* IHM2. }
          { destruct K3 as (?&?&K5). inverts K5. } } } }
    { applys bigsmall_step.
      { inverts IHM1 as K3 K4.
        { false* C. }
        { destruct K3 as (?&?&K5). do 2 esplit. applys* step_let_ctx. } }
      { introv K. inverts K as K'; [|false* C].
        inverts IHM1 as K5 K6; [false* C|].
        specializes K6 K'. applys* bigsmall_let. } } }
  { applys bigsmall_step.
    { do 2 esplit. applys* step_if. }
    { introv K. inverts K. applys IHM. } }
  { applys bigsmall_step.
    { do 2 esplit. applys* step_div. }
    { introv K. inverts K. applys* bigsmall_val. } }
  { applys bigsmall_step.
    { do 2 esplit. applys* step_rand 0. math. }
    { introv K. inverts K; tryfalse. applys* bigsmall_val. } }
  { applys bigsmall_step.
    { forwards~ (p&D&N): (exists_fresh null s).
      do 2 esplit. applys* step_ref. }
    { introv K. inverts K; tryfalse. applys* bigsmall_val. } }
  { applys bigsmall_step.
    { do 2 esplit. applys* step_get. }
    { introv K. inverts K; tryfalse. applys* bigsmall_val. } }
  { applys bigsmall_step.
    { do 2 esplit. applys* step_set. }
    { introv K. inverts K; tryfalse. applys* bigsmall_val. } }
  { applys bigsmall_step.
    { do 2 esplit. applys* step_free. }
    { introv K. inverts K; tryfalse. applys* bigsmall_val. } }
Qed.

(** Combining the two directions, we obtain the desired equivalence between
    omni-big-step and inductive-small-step. *)

Lemma bigsmall_eq_omnibig :
  bigsmall = omnibig.
Proof using.
  extens. intros s t Q. iff M.
  { applys* omnibig_of_bigsmall. }
  { applys* bigsmall_of_omnibig. }
Qed.

(** The final equivalence follows. *)

Lemma omnibig_iff_eventually : forall s t Q,
  omnibig s t Q <-> eventually s t (pred_of_post Q).
Proof using.
  intros. rewrite <- bigsmall_eq_omnibig.
  rewrite* bigsmall_iff_eventually.
Qed.



(* ########################################################### *)
(** ** Equivalence Between CoInductive Big-Step and Standard Partial Correctness *)

(** The first step of the proof is to formally relate [cobigsmall]
   and [coomnibig], which are both defined coinductively. *)

(** The first direction is from [cobigsmall] to [coomnibig].
    To establish it, we need inversion lemmas for let-bindings. *)

Lemma cobigsmall_let_inv_ctx : forall x s1 t1 t2 Q Q1,
  cobigsmall s1 (trm_let x t1 t2) Q ->
  (fun v s => steps s1 t1 s v) ===> Q1 ->
  cobigsmall s1 t1 Q1.
Proof using.
  cofix IH. introv M WQ. inverts M as M0 M'.
  tests C: (exists v1, t1 = trm_val v1).
  { destruct C as (v1&->). applys cobigsmall_val.
    applys WQ. applys steps_refl. }
  { applys cobigsmall_step.
    { destruct M0 as (s'&t'&S). inverts S as. 2:{ false* C. }
      intros S. exists. applys S. }
    { intros s2 t1' S. applys IH.
      { applys M'. applys step_let_ctx S. }
      { intros v s R. applys WQ. applys steps_step S R. } } }
Qed.

Lemma cobigsmall_let_inv_cont : forall s1 s2 v1 x t1 t2 Q,
  cobigsmall s1 (trm_let x t1 t2) Q ->
  steps s1 t1 s2 v1 ->
  cobigsmall s2 (subst x v1 t2) Q.
Proof using.
  introv M R. gen_eq t1': (trm_val v1). induction R; intros; subst.
  { inverts M as _ M'. applys M'. applys step_let. }
  { rename H into S, R into R', t0 into t1'.
    inverts M as _ M'. applys* IHR. applys M'.
    applys step_let_ctx S. }
Qed.

Lemma cobigsmall_let_inv : forall s1 x t1 t2 Q,
  cobigsmall s1 (trm_let x t1 t2) Q ->
  exists Q1, cobigsmall s1 t1 Q1
          /\ (forall v1 s2, Q1 v1 s2 -> cobigsmall s2 (subst x v1 t2) Q).
Proof using.
  introv M. exists (fun v s => steps s1 t1 s (trm_val v)). split.
  { applys* cobigsmall_let_inv_ctx M. }
  { introv K. applys* cobigsmall_let_inv_cont M K. }
Qed.

(** Using these inversion lemmas, we can prove by induction the first
    direction, from [cobigsmall] to [coomnibig]. *)

Lemma coomnibig_of_cobigsmall : forall s t Q,
  cobigsmall s t Q ->
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
    { applys coomnibig_div.
      forwards M1': M1. { applys step_div. }
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
  { lets (Q1&M1&M2): cobigsmall_let_inv M. applys coomnibig_let.
    { applys IH. applys M1. }
    { introv R. applys IH. applys M2 R. } }
  { inverts M as (s'&t'&S) M1. inverts S. applys coomnibig_if.
    applys IH. applys M1. applys step_if. }
Qed.

(** For the reciprocal direction, we also need one key inversion lemma. It
    is stated below. Its hypothesis is [coomnibig s t Q], and its conclusion
    corresponds to the disjunction of the constructors of the inductive
    definition of [cobigsmall s t Q]. *)

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
    { exists. split. { applys step_div. } { applys* coomnibig_val. } }
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
    implication from [coomnibig] to [cobigsmall]. *)

Lemma cobigsmall_of_coeval : forall s t Q,
  coomnibig s t Q ->
  cobigsmall s t Q.
Proof.
  cofix IH. introv M. lets C: coomnibig_inv_step M.
  destruct C as [(v&->&HQ)|((s'&t'&S&M1)&M2)].
  { applys cobigsmall_val HQ. }
  { applys cobigsmall_step.
    { exists. applys S. }
    { intros s1 t1 S'. applys IH. applys M2 S'. } }
Qed.

(** Combining the two directions yields the equality between [cobigsmall] and
    [coomnibig], and that between [partial] and [coomnibig]. *)

Lemma cobigsmall_eq_omnibigp :
   cobigsmall = coomnibig.
Proof using.
  extens. intros s t Q. iff M.
  { applys* coomnibig_of_cobigsmall. }
  { applys* cobigsmall_of_coeval. }
Qed.

(** Finally, we conclude that coinductive Omni-big-step matches the
    standard small-step characterization of partial correctness. *)

Lemma coomnibig_eq_partial :
  coomnibig = partial.
Proof using.
  rewrite <- cobigsmall_eq_partial. rewrite* cobigsmall_eq_omnibigp.
Qed.



(* ########################################################### *)
(** ** Small-Step Characterization of Safety *)

(** Safety corresponds to partial correctness with the always-true
    postcondition. We let [ssafe] denote the corresponding
    judgment. *)

Definition ssafe (s:state) (t:trm) : Prop :=
  partial s t Any.

(** [ssafe] is equivalent to [safe] *)

Lemma ssafe_eq_safe :
  ssafe = safe.
Proof using.
  extens. intros s t. unfold ssafe.
  rewrite <- coomnibig_eq_partial.
  rewrite* safe_iff_coomnibig_any.
Qed.




(* ########################################################### *)
(** ** Equivalence Between Definitions of Divergence *)

(** We prove that [sdiv] matches [costeps] and [coomnidiv]. *)



(** We establish the equivalence between the small-step characterisation
   and the coinductive Omni-big-step characterization of divergence. *)

Lemma sdiv_eq_coomnidiv :
  sdiv = coomnidiv.
Proof using.
  extens. intros s t. unfold coomnidiv.
  rewrite sdiv_iff_omnibigps_Empty.
  rewrite <- cobigsmall_eq_omnibigp.
  rewrite* cobigsmall_eq_partial.
Qed.




(* ########################################################### *)
(** ** Equivalence of Omni-Small-Step with Standard Small Step *)

Section OmnismallEquiv.
Hint Constructors step.

(* Characterization lemma (omni-small-step-iff-progress-and-correct). *)

Lemma omnismall_iff_step_st : forall s t P,
       omnismall s t P
  <-> (   (exists s' t', step s t s' t')
       /\ (forall s' t', step s t s' t' -> P s' t')).
Proof using.
  iff M.
  { induction M.
    { forwards (R&M1): IHM. split.
      { destruct R as (s'&t'&S). exists. applys step_let_ctx S. }
      { intros s' t' S. inverts S as.
        { rename H into IHM1. introv S1. lets K1: M1 S1. applys IHM1 K1. }
        { destruct R as (s''&t''&S'). false* step_val_inv. } } }
    { split*. { intros s' t' S. inverts S as; try false_invert. { auto. } } }
    { split*. { intros s' t' S. inverts S as; try false_invert.
                { inverts* TEMP. } } }
    { split*. { intros s' t' S. inverts S as; try false_invert. { auto. } } }
    { split*. { intros s' t' S. inverts S as; try false_invert. { auto. } } }
    { split*. { intros s' t' S. inverts S as; try false_invert. { auto. } } }
    { split.
       { exists. applys step_rand 0. math. }
       { intros s' t' S. inverts S as; try false_invert.
         { intros R. inverts R. auto. } } }
    { split.
       { forwards~ (p&F&N): (exists_fresh null s).
         exists. applys* step_ref p. }
       { intros s' t' S. inverts S as; try false_invert. { auto. } } }
    { split*. { intros s' t' S. inverts S as; try false_invert. { auto. } } }
    { split*. { intros s' t' S. inverts S as; try false_invert. { auto. } } }
    { split*. { intros s' t' S. inverts S as; try false_invert. { auto. } } } }
  { destruct M as (R&M). destruct R as (s'&t'&S).
    gen P. induction S; intros.
    { rename S into S1. applys omnismall_let_ctx (step s1 t1).
      { applys IHS. auto. }
      { intros s' t' S1'. applys M. applys step_let_ctx S1'. } }
    { applys* omnismall_fix. }
    { applys* omnismall_app_fix. }
    { applys* omnismall_if. }
    { applys* omnismall_let. }
    { applys* omnismall_div. }
    { applys* omnismall_rand. math. }
    { applys* omnismall_ref. }
    { applys* omnismall_get. }
    { applys* omnismall_set. }
    { applys* omnismall_free. } }
Qed.

End OmnismallEquiv.




(* ########################################################### *)
(** ** Inductive Small-Step Judgment *)

(** The judgment [bigsmall] introduced in this section helps
    carrying out several proofs of equivalence---see the next
    section. *)

(** Viewing postconditions as predicates over configurations *)

Definition pred_of_post (Q:val->hprop) : state->trm->Prop :=
  fun s' t' => exists v', t' = trm_val v' /\ Q v' s'.

(** We introduce the inductive small-step judgment, as it is useful
    to relate Omni-Small-Step with Omni-Big-Step.

(** [bigsmall] is equivalent to [eventually]. *)

Lemma bigsmall_iff_eventually : forall s t Q,
  bigsmall s t Q <-> eventually s t (pred_of_post Q).
Proof using.
  rewrite eventually_eq_eventually'.
  iff M.
  { induction M.
    { applys eventually'_here. hnf. exists*. }
    { rename H into R, H0 into M1, H1 into IH1.
      applys eventually'_step R. applys IH1. } }
  { gen_eq C: (pred_of_post Q). induction M; intros; subst.
    { destruct H as (v'&->&Hv'). applys bigsmall_val Hv'. }
    { rename H into R, H0 into M1, H1 into IH1.
      applys bigsmall_step R.
      intros s' t' S. applys* IH1 S. } }
Qed.


