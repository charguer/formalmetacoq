(****************************************************************
* Imperative Lambda-calculus                                    *
* Separation Logic on Small-Step                                *
*****************************************************************)

Set Implicit Arguments.
Require Export SepLogicCommon Small.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types s : state.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Proof of the Frame Property for the Small-Step-Based [stepsinto] Relation *)

Hint Constructors step.

Lemma stepsinto_frame : forall h1 h2 t Q,
  stepsinto h1 t Q ->
  Fmap.disjoint h1 h2 ->
  stepsinto (h1 \u h2) t (Q \*+ (= h2)).
Proof using.
  introv M HD. gen h2. induction M; intros.
  { applys stepsinto_val. applys* hstar_intro. }
  { rename H into M1, H0 into M2, H1 into IH2.
    applys stepsinto_step.
    { unfolds reducible. clear M2 IH2. destruct M1 as (s'&t'&R).
      induction R; tryfalse; try solve [ do 2 esplit; constructors* ].
      { forwards* (s'&t'&R'): IHR. }
      { lets (p'&F&_): exists_fresh null (union s h2). do 2 esplit.
        applys step_ref v p'. eauto. }
      { do 2 esplit. applys step_get. applys* indom_union_l. }
      { do 2 esplit. applys step_set. applys* indom_union_l. }
      { do 2 esplit. applys step_free. applys* indom_union_l. } }
    { introv R. cuts (s1'&E'&D'&R'):
        (exists s1', s' = s1' \u h2 /\ disjoint s1' h2 /\ step s t s1' t').
      { subst. applys* IH2. }
      clear M2 IH2.
      gen_eq su: (s \u h2). gen s.
      unfolds reducible. induction R; intros; subst; eauto.
      { destruct M1 as (s0&t0&R0).
        rename R into R1. forwards* (s1'&E&D&R1'): IHR s.
        { inverts R0. { eauto. } { inverts R1. } } }
      { rename H into D. rewrite indom_union_eq in D. rew_logic in D.
        destruct D as (D1&D2). esplit. splits.
        { rewrite* update_union_not_r. }
        { applys* disjoint_update_not_r. }
        { eauto. } }
      { destruct M1 as (se&te&Re). inverts Re; tryfalse.
        rewrite* read_union_l. }
      { destruct M1 as (se&te&Re). inverts Re; tryfalse. esplit. splits.
        { rewrite* update_union_l. }
        { applys* disjoint_update_l. }
        { eauto. } }
      { destruct M1 as (se&te&Re). inverts Re; tryfalse. esplit. splits.
        { rewrite* remove_disjoint_union_l. }
        { applys* disjoint_remove_l. }
        { eauto. } } } }
Qed.




(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Construction of Separation Logic *)

(* ########################################################### *)
(** ** Definition of Separation Logic triples *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> stepsinto s t Q.

(* ########################################################### *)
(** ** Structural Rules *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. unfolds triple. introv M MH MQ HF. applys* stepsinto_conseq. Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof.
  introv M. intros h HF. lets (h1&h2&M1&M2&MD&MU): (rm HF).
  subst. specializes M M1. applys stepsinto_conseq.
  { applys stepsinto_frame M MD. } { xsimpl. intros h' ->. applys M2. }
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  inverts HP. subst. rewrite union_empty_l. applys~ M.
Qed.


(* ########################################################### *)
(** ** Reasoning Rules for Terms *)

(** These proofs look short, but in fact they require nontrival results
    established by induction near the end of the file [Small.v], in the
    section "Deriving Big-Step Evaluation Rules for [stepsinto]".
    There might exist a different route for establishing these rules, thought. *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. introv M Hs. applys* stepsinto_val. Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using. introv M Hs. applys* stepsinto_fix. Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using. introv M Hs. applys* stepsinto_if. Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M Hs. applys* stepsinto_app_fix. Qed.

Lemma triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using. unfolds triple. introv M1 M2 Hs. applys* stepsinto_let. Qed.


(* ########################################################### *)
(** ** Specification of Primitive Operations *)

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using.
  introv Hn2 Hs. applys* stepsinto_step.
  { introv R. inverts R. applys* stepsinto_val. hnfs*. }
Qed.

Lemma triple_rand : forall n,
  n > 0 ->
  triple (val_rand n)
    \[]
    (fun r => \[exists n1, r = val_int n1 /\ 0 <= n1 < n]).
Proof using.
  introv Hn2 Hs. applys* stepsinto_step.
  { exists s 0. constructors. math. }
  { introv R. inverts R; tryfalse. applys* stepsinto_val. hnfs*. }
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof using.
  intros. intros s1 K. applys* stepsinto_step.
  { forwards~ (p&D&N): (exists_fresh null s1). do 2 esplit. applys* step_ref. }
  { introv R. inverts R; tryfalse. applys stepsinto_val.
    inverts K. rewrite update_empty. exists p.
    rewrite hstar_hpure_l. split*. hnfs*. }
Qed.

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. intros s K. inverts K. applys* stepsinto_step.
  { do 2 esplit. applys* step_get. applys* indom_single. }
  { introv R. inverts R; tryfalse. applys stepsinto_val.
    rewrite hstar_hpure_l. split*. rewrite* read_single. hnfs*. }
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun r => (p ~~> v)).
Proof using.
  intros. intros s1 K. inverts K. applys* stepsinto_step.
  { do 2 esplit. applys* step_set. applys* indom_single. }
  { introv R. inverts R; tryfalse. applys stepsinto_val.
    rewrite update_single. hnfs*. }
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun r => \[]).
Proof using.
  intros. intros s1 K. inverts K. applys* stepsinto_step.
  { do 2 esplit. applys* step_free. applys* indom_single. }
  { introv R. inverts R; tryfalse. applys stepsinto_val.
    rewrite* remove_single. hnfs*. }
Qed.
