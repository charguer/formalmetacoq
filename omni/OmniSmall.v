(****************************************************************
* Imperative Lambda-calculus                                    *
* Omni-Small-Step Semantics                                     *
*****************************************************************)

Set Implicit Arguments.
Require Export Syntax.

(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Omni-Small-Step *)

Implicit Types P : state->trm->Prop.


(* ########################################################### *)
(** ** Definition of Omni-Small-Step *)

(** [omnismall s t P] asserts that a configuration [(s,t)] can
    take a step, and that for any step it takes it reaches a
    configuration that satisfies [P]. *)

Inductive omnismall : state -> trm -> (state->trm->Prop) -> Prop :=
  (* under context *)
  | omnismall_let_ctx : forall s1 x t1 t2 P1 P,
      omnismall s1 t1 P1 ->
      (forall s2 t1', P1 s2 t1' -> P s2 (trm_let x t1' t2)) ->
      omnismall s1 (trm_let x t1 t2) P
  (* term constructs *)
  | omnismall_fix : forall s f x t1 P,
      P s (val_fix f x t1) ->
      omnismall s (trm_fix f x t1) P
  | omnismall_app_fix : forall s v1 v2 f x t1 P,
      v1 = val_fix f x t1 ->
      P s (subst x v2 (subst f v1 t1)) ->
      omnismall s (trm_app v1 v2) P
  | omnismall_if : forall s b t1 t2 P,
      P s (if b then t1 else t2) ->
      omnismall s (trm_if (val_bool b) t1 t2) P
  | omnismall_let : forall s x t2 v1 P,
      P s (subst x v1 t2) ->
      omnismall s (trm_let x v1 t2) P
  (* primitive operations *)
  | omnismall_div : forall s n1 n2 P,
      P s (val_int (Z.quot n1 n2)) ->
      n2 <> 0 ->
      omnismall s (val_div (val_int n1) (val_int n2)) P
  | omnismall_rand : forall s n P,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> P s n1) -> (* non-det *)
      omnismall s (val_rand (val_int n)) P
  | omnismall_ref : forall s v P,
      (forall p, ~ Fmap.indom s p ->
         P (Fmap.update s p v) (val_loc p)) -> (* non-det *)
      omnismall s (val_ref v) P
  | omnismall_get : forall s p P,
      Fmap.indom s p ->
      P s (Fmap.read s p) ->
      omnismall s (val_get (val_loc p)) P
  | omnismall_set : forall s p v P,
      Fmap.indom s p ->
      P (Fmap.update s p v) val_unit ->
      omnismall s (val_set (val_loc p) v) P
  | omnismall_free : forall s p P,
      Fmap.indom s p ->
      P (Fmap.remove s p) val_unit ->
      omnismall s (val_free (val_loc p)) P.


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
(** ** Eventually Judgment *)

(** [eventually s t P] asserts that all executions starting from [(s,t)]
    eventually reach a configuration [(s',t')] satisfying the predicate [P]. *)

(** Definition of [eventually s t P] in terms of [omnismall]. *)

Inductive eventually : state->trm->(state->trm->Prop)->Prop :=
  | eventually_here : forall s t P,
      P s t ->
      eventually s t P
  | eventually_step : forall s t P1 P,
      omnismall s t P1 ->
      (forall s' t', P1 s' t' -> eventually s' t' P) ->
      eventually s t P.

(** Alternative definition of [eventually], with respect to standard small-step.
    (eventually-step-using-standard-small-step) *)

Inductive eventually' : state->trm->(state->trm->Prop)->Prop :=
  | eventually'_here : forall s t P,
      P s t ->
      eventually' s t P
  | eventually'_step : forall s t P,
      (exists s' t', step s t s' t') ->
      (forall s' t', step s t s' t' -> eventually' s' t' P) ->
      eventually' s t P.

(** [eventually] is equivalent to [eventually']. *)

Lemma eventually_eq_eventually' :
  eventually = eventually'.
Proof using.
  extens. intros s t P. iff M.
  { induction M.
    { applys* eventually'_here. }
    { rename H into M1, H0 into M2, H1 into IHM2.
      rewrite omnismall_iff_step_st in M1. destruct M1 as (R&M1).
      applys* eventually'_step R. } }
  { induction M.
    { applys* eventually_here. }
    { rename H into R, H0 into M1, H1 into IHM1.
      applys eventually_step (step s t).
      { rewrite omnismall_iff_step_st. split*. }
      { autos*. } } }
Qed.

(** Chained rule for [eventually_step]. *)

Lemma eventually_step_chained : forall s t P,
  omnismall s t (fun s' t' => eventually s' t' P) ->
  eventually s t P.
Proof using. introv M. applys* eventually_step M. Qed.

(** The cut rule for [eventually]. *)

Lemma eventually_cut : forall s t P1 P2,
  eventually s t P1 ->
  (forall s' t', P1 s' t' -> eventually s' t' P2) ->
  eventually s t P2.
Proof using.
  introv M HK. induction M.
  { rename H into M1. applys HK M1. }
  { rename H into R, H0 into M1, H1 into IH1.
    applys eventually_step R. intros s' t' S.
    applys IH1 S HK. }
Qed.

(** Chained rule for [eventually_cut]. *)

Lemma eventually_cut_chained : forall s t P,
  eventually s t (fun s' t' => eventually s' t' P) ->
  eventually s t P.
Proof using. introv M. applys* eventually_cut M. Qed.


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

    [bigsmall s t Q] asserts that executions of [(t,s)] terminate,
    and the results satisfy the postcondition [Q]. *)

Inductive bigsmall : state->trm->(val->hprop)->Prop :=
  | bigsmall_val : forall s v Q,
      Q v s ->
      bigsmall s v Q
  | bigsmall_step : forall s t Q,
      (exists s' t', step s t s' t') ->
      (forall s' t', step s t s' t' -> bigsmall s' t' Q) ->
      bigsmall s t Q.

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
