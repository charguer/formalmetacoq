(****************************************************************
* Imperative Lambda-calculus                                    *
* Omni-Small-Step Semantics                                     *
*****************************************************************)

Set Implicit Arguments.
Require Export Syntax Small.

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
(** * Definitions *)

(* ########################################################### *)
(** ** Omni-Small-Step Judgment *)

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
(** ** Eventually Judgment with Omni-Small-Step *)

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

(** [ostepsinto s t Q] asserts that all executions starting from [(s,t)]
    eventually reach *final* configurations satisfying the predicate [Q].
    Unlike [stepsinto s t Q], [ostepsinto] does not involve the predicate
    [reducible]. Indeed, the omni-small-step judgment inherently captures
    safety. *)

Definition ostepsinto (s:state) (t:trm) (Q:val->hprop) : Prop :=
    eventually s t (pred_of_post Q).


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Properties *)

Hint Constructors eventually.


(* ########################################################### *)
(** ** Covariance of the judgment *)

(** [omnismall] is covariant in the postcondition *)

Lemma omnismall_conseq : forall s t P1 P2,
  omnismall s t P1 ->
  (forall s' t', P1 s' t' -> P2 s' t') ->
  omnismall s t P2.
Proof using. introv M W. induction M; try solve [ constructors* ]. Qed.

(** [eventually] is covariant in the postcondition *)

Lemma eventually_conseq : forall s t P1 P2,
  eventually s t P1 ->
  (forall s' t', P1 s' t' -> P2 s' t') ->
  eventually s t P2.
Proof using. introv M W. induction* M. Qed.

(** [ostepsinto] is covariant in the postcondition *)

Lemma ostepsinto_conseq : forall s t Q1 Q2,
  ostepsinto s t Q1 ->
  Q1 ===> Q2 ->
  ostepsinto s t Q2.
Proof using.
  introv M W. unfolds ostepsinto. applys* eventually_conseq.
  { unfolds pred_of_post, qimpl, himpl. introv (v&->&?). eauto. }
Qed.

(* ########################################################### *)
(** ** Chained Rules and Cut Rules *)

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

(** One-Step Chained rule [eventually]. *)

Lemma eventually_step_chained : forall s t P,
  omnismall s t (fun s' t' => eventually s' t' P) ->
  eventually s t P.
Proof using. introv M. applys* eventually_step M. Qed.

(** Chained rule for [eventually]. *)

Lemma eventually_cut_chained : forall s t P,
  eventually s t (fun s' t' => eventually s' t' P) ->
  eventually s t P.
Proof using. introv M. applys* eventually_cut M. Qed.

(** Chained induction principle for [eventually]. *)

Lemma eventually_ind_chained :
  forall K : state -> trm -> (state -> trm -> Prop) -> Prop,
  (forall s t P,
     P s t ->
     K s t P) ->
  (forall s t P,
    omnismall s t (fun s' t' => eventually s' t' P) ->
    omnismall s t (fun s' t' => K s' t' P) ->
    K s t P) ->
  (forall s t P, eventually s t P -> K s t P).
Proof using.
  introv M1 M2 R. induction R.
  { applys* M1. }
  { applys M2; applys* omnismall_conseq H. }
Qed.

(** Chain rule for let-bindings *)

Lemma omnismall_let_ctx_chained : forall s1 x t1 t2 P,
  omnismall s1 t1 (fun s2 t1' => P s2 (trm_let x t1' t2)) ->
  omnismall s1 (trm_let x t1 t2) P.
Proof using. introv M. constructors*. Qed.


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
(** ** Equivalence of Eventually is Small-Step and Omni-Small-Step *)

(** [eventually] is equivalent to [seventually]. *)

Lemma eventually_eq_seventually :
  eventually = seventually.
Proof using.
  extens. intros s t P. iff M.
  { induction M.
    { applys* seventually_here. }
    { rename H into M1, H0 into M2, H1 into IHM2.
      rewrite omnismall_iff_step_st in M1. destruct M1 as (R&M1).
      applys* seventually_step R. } }
  { induction M.
    { applys* eventually_here. }
    { rename H into R, H0 into M1, H1 into IHM1.
      applys eventually_step (step s t).
      { rewrite omnismall_iff_step_st. split*. }
      { autos*. } } }
Qed.


(* ########################################################### *)
(** ** Equivalence of Steps-Into is Small-Step and Omni-Small-Step *)

Lemma ostepsinto_eq_stepsinto :
  ostepsinto = stepsinto.
Proof using.
  extens. intros s t Q. unfold ostepsinto.
  rewrite eventually_eq_seventually. rewrite* stepsinto_iff_eventually.
Qed.

(** Another direct proof *)

Lemma ostepsinto_eq_stepsinto' :
  ostepsinto = stepsinto.
Proof using.
  unfold ostepsinto. rewrite eventually_eq_seventually.
  extens. intros s t Q. iff M.
  { gen_eq C: (pred_of_post Q). induction M; intros; subst.
    { destruct H as (v'&->&Hv'). applys stepsinto_val Hv'. }
    { rename H into R, H0 into M1, H1 into IH1.
      applys stepsinto_step R.
      intros s' t' S. applys* IH1 S. } }
  { induction M.
    { applys seventually_here. hnf. exists*. }
    { rename H into R, H0 into M1, H1 into IH1.
      applys seventually_step R. applys IH1. } }
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Deriving Big-Step Evaluation Rules for [eventually] *)

(** Rule for values *)

Lemma eventually_val : forall s v Q,
  Q v s ->
  eventually s v (pred_of_post Q).
Proof using. introv M. applys eventually_here. exists* v. Qed.

Lemma ostepsinto_val : forall s v Q,
  Q v s ->
  ostepsinto s v Q.
Proof using. introv M. applys* eventually_val. Qed.

(** Rule for let-bindings *)

Lemma eventually_let : forall s x t1 t2 Q1 P,
  eventually s t1 (pred_of_post Q1) ->
  (forall v1 s, Q1 v1 s -> eventually s (subst x v1 t2) P) ->
  eventually s (trm_let x t1 t2) P.
Proof.
  introv M1. gen_eq P1: (pred_of_post Q1). gen Q1.
  induction M1 using eventually_ind_chained; introv E M2; subst.
  { destruct H as (v&->&K). applys eventually_step_chained. constructors*. }
  { applys eventually_step_chained. applys omnismall_let_ctx_chained.
    applys omnismall_conseq H0. introv K. applys* K. }
Qed.

Lemma eventually_let_chained : forall s x t1 t2 P,
  eventually s t1 (pred_of_post (fun v1 s => eventually s (subst x v1 t2) P) )->
  eventually s (trm_let x t1 t2) P.
Proof using. introv M. applys* eventually_let. Qed.
