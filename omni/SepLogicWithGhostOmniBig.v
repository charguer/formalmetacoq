(****************************************************************
* Imperative Lambda-calculus                                    *
* Separation Logic on Omni-Big-Step                             *
*****************************************************************)

Set Implicit Arguments.
From TLC Require Import LibRelation.
Require Export Syntax OmniBig.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types s : state.



(* ########################################################### *)
(** ** Ghost State Axiomatization *)

(** Heap is a synonymous for ghost state *)

Parameter heap : Type.

(** Projection of the physical state component from a ghost state *)

Parameter heap_state : heap -> state.

(** Update of the physical state component from a ghost state *)

Parameter heap_with_state : heap -> state -> heap.

(** Ghost step *)

Parameter gstep : heap -> heap -> Prop.

(** Ghost step is a reflexive-transitive relation *)

Parameter gstep_refl : refl gstep.
Parameter gstep_trans : trans gstep.

(** Ghost step do not modify the physical state *)

Parameter heap_state_gstep : forall h h',
  gstep h h' ->
  heap_state h' = heap_state h.

(** Reading an updated physical state from a ghost state is a expected *)

Parameter heap_state_heap_with_state : forall h s,
  heap_state (heap_with_state h s) = s.


(* ########################################################### *)
(** ** Heap Predicates *)

(** Heap predicate *)

Definition hprop := heap -> Prop.

Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(** Heap entailment *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2)
  (at level 55) : heap_scope.

(** Entailment on postconditions *)

Definition qimpl (Q1 Q2:val->hprop) :=
  forall v, himpl (Q1 v) (Q2 v).

Notation "Q1 ===> Q2" := (qimpl Q1 Q2)
  (at level 55) : heap_scope.


(* ########################################################### *)
(** ** Properties of Entailments *)

(** Properties of [himpl] *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

Hint Resolve himpl_refl.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

#[global] Hint Resolve himpl_refl.

(** Properties of [qimpl] *)

Lemma qimpl_refl : forall Q,
  Q ===> Q.
Proof using. intros. unfolds*. Qed.

Lemma qimpl_trans : forall Q1 Q2 Q3,
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. eapply himpl_trans; eauto. Qed.

#[global] Hint Resolve qimpl_refl.


(* ########################################################### *)
(** ** Ghoste Update *)

(** Ghost update modality: [hupdate H] asserts that [H] holds
    after a [gstep] update to the current ghost state. *)

Definition hupdate (H : hprop) : hprop :=
  fun h => exists h', gstep h h' /\ H h'.

(** Ghost update modality for postconditions *)

Definition qupdate (Q : val->hprop) : val->hprop :=
  fun v => hupdate (Q v).

(** Ghost update (view shift) *)

Definition ghimpl (H1 H2 : hprop) : Prop :=
  H1 ==> hupdate H2.

Notation "H1 |==> H2" := (ghimpl H1 H2)
  (at level 55) : heap_scope.

(** Ghost update on postconditions *)

Definition gqimpl (Q1 Q2 : val->hprop) : Prop :=
  forall v, ghimpl (Q1 v) (Q2 v).

Notation "Q1 |===> Q2" := (gqimpl Q1 Q2)
  (at level 55) : heap_scope.

(** Alternative definition of [gqimpl] *)

Lemma gqimpl_eq_qimpl : forall Q1 Q2,
  gqimpl Q1 Q2 = qimpl Q1 (qupdate Q2).
Proof using. extens. unfolds gqimpl, ghimpl. iff*. Qed.


(* ########################################################### *)
(** ** Properties of Ghost Updates *)

Lemma hupdate_intro : forall H h h',
  gstep h h' ->
  H h' ->
  hupdate H h.
Proof using. introv G K. hnfs*. Qed.

(** Introduction of [hupdate] in the particular case where no
    update is needed. *)

Lemma gupdate_intro_same : forall H h,
  H h ->
  hupdate H h.
Proof using. introv K. applys* hupdate_intro h. applys gstep_refl. Qed.

(** Entailments are included in ghost updates *)

Lemma ghimpl_of_himpl : forall H1 H2,
  H1 ==> H2 ->
  H1 |==> H2.
Proof using. introv M Hh. exists h. split. applys gstep_refl. eauto. Qed.

Lemma ghimpl_of_qimpl : forall Q1 Q2,
  Q1 ===> Q2 ->
  Q1 |===> Q2.
Proof using. introv M. intros v. applys* ghimpl_of_himpl. Qed.

Lemma hupdate_conseq : forall H1 H2,
  H1 ==> H2 ->
  hupdate H1 ==> hupdate H2.
Proof using. introv W. introv (h'&G&K). exists* h'. Qed.

Lemma qupdate_conseq : forall Q1 Q2,
  Q1 ===> Q2 ->
  qupdate Q1 ===> qupdate Q2.
Proof using. introv W. intros v. applys* hupdate_conseq. Qed.


(* ########################################################### *)
(** ** Auxiliary Defintitions for State-Manipulating Primitives *)

Definition heap_state_ref (h:heap) (p:loc) (v:val) (h':heap) : Prop :=
  let s := heap_state h in
  ~ Fmap.indom s p /\ h' = heap_with_state h (Fmap.update s p v).

Definition heap_state_get (h:heap) (p:loc) (v:val) : Prop :=
  let s := heap_state h in
  Fmap.indom s p /\ v = Fmap.read s p.

Definition heap_state_set (h:heap) (p:loc) (v:val) (h':heap) : Prop :=
  let s := heap_state h in
  Fmap.indom s p /\ h' = heap_with_state h (Fmap.update s p v).

Definition heap_state_free (h:heap) (p:loc) (h':heap) : Prop :=
  let s := heap_state h in
  Fmap.indom s p /\ h' = heap_with_state h (Fmap.remove s p).


(* ########################################################### *)
(** ** Inductive WP over Ghost State *)

(** The judgment [eval g t Q] asserts that all executions of [t] in a
    ghost state [g] (which includes the physical state) terminate
    and satisfy the postcondition Q. *)

Inductive eval : heap -> trm -> (val->hprop) -> Prop :=
  | eval_val : forall h v Q,
      Q v h ->
      eval h (trm_val v) Q
  | eval_fix : forall h f x t1 Q,
      Q (val_fix f x t1) h ->
      eval h (trm_fix f x t1) Q
  | eval_app_fix : forall h v1 v2 f x t1 Q,
      v1 = val_fix f x t1 ->
      eval h (subst x v2 (subst f v1 t1)) Q ->
      eval h (trm_app v1 v2) Q
  | eval_let : forall Q1 h x t1 t2 Q,
      eval h t1 Q1 ->
      (forall v1 h2, Q1 v1 h2 -> eval h2 (subst x v1 t2) Q) ->
      eval h (trm_let x t1 t2) Q
  | eval_if : forall h b t1 t2 Q,
      eval h (if b then t1 else t2) Q ->
      eval h (trm_if (val_bool b) t1 t2) Q
  | eval_div : forall h n1 n2 Q,
      n2 <> 0 ->
      Q (val_int (Z.quot n1 n2)) h ->
      eval h (val_div (val_int n1) (val_int n2)) Q
  | eval_rand : forall h n Q,
      n > 0 ->
      (forall n1, 0 <= n1 < n -> Q n1 h) ->
      eval h (val_rand (val_int n)) Q
  | eval_ref : forall h v Q,
      (forall p h', heap_state_ref h p v h' ->
         Q (val_loc p) h') ->
      eval h (val_ref v) Q
  | eval_get : forall h p v Q,
      heap_state_get h p v ->
      Q v h ->
      eval h (val_get (val_loc p)) Q
  | eval_set : forall h' h p v Q,
      heap_state_set h p v h' ->
      Q val_unit h' ->
      eval h (val_set (val_loc p) v) Q
  | eval_free : forall h' h p Q,
      heap_state_free h p h' ->
      Q val_unit h' ->
      eval h (val_free (val_loc p)) Q
  | eval_ghost_pre : forall h' h t Q,
      gstep h h' ->
      eval h' t Q ->
      eval h t Q
  | eval_ghost_post : forall h t Q,
      eval h t (qupdate Q) ->
      eval h t Q.

(** Definition of Separation Logic triples *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall h, H h -> eval h t Q.


(* ########################################################### *)
(** ** Soundness of WP *)

Definition state_st (H:hprop) (s:state) : Prop :=
  exists h, H h /\ s = heap_state h.

Lemma state_st_heap_state : forall H h,
  H h ->
  state_st H (heap_state h).
Proof using. introv M. hnfs*. Qed.

Hint Resolve state_st_heap_state.

Lemma omnibig_of_eval : forall h t Q,
  eval h t Q ->
  omnibig (heap_state h) t (fun v => state_st (Q v)).
Proof using.
  introv M. induction M; try solve [constructors*].
  { constructors*. { introv (h2&K2&->). eauto. } }
  { unfolds heap_state_ref. constructors*.
    { intros p Hp. esplit. split.
    applys* H. rewrite* heap_state_heap_with_state. } }
  { destruct H as (?&->). constructors*. }
  { destruct H as (?&->). constructors*. esplit. split*.
    rewrite* heap_state_heap_with_state. }
  { destruct H as (?&->). constructors*. esplit. split*.
    rewrite* heap_state_heap_with_state. }
  { rename H into G. rewrite* <- (heap_state_gstep G). }
  { applys omnibig_conseq IHM. intros v. intros h' (hb&(ha&G&R0)&->).
    exists ha. splits*. rewrite* <- (heap_state_gstep G). }
Qed.

Lemma triple_sound : forall t H Q,
  triple t H Q ->
  forall s, state_st H s -> omnibig s t (fun v => state_st (Q v)).
Proof using. introv M (h&Hh&->). applys* omnibig_of_eval. Qed.


(* ########################################################### *)
(** ** Consequence property for WP *)

Lemma eval_conseq : forall h t Q1 Q2,
  eval h t Q1 ->
  Q1 ===> Q2 ->
  eval h t Q2.
Proof using.
  introv M W.
  gen Q2. induction M; intros; try solve [ constructors; try (intros; applys W); eauto].
  { applys eval_ghost_post. applys IHM. applys* qupdate_conseq. }
Qed.

Lemma eval_conseq_ghost : forall h t Q1 Q2,
  eval h t Q1 ->
  Q1 |===> Q2 ->
  eval h t Q2.
Proof using. introv M W. applys eval_ghost_post. applys* eval_conseq M. Qed.

(** Note: proof sketch without [eval_ghost_post], gets stuck on [rand].
  introv M W. induction M; try solve [ constructors* ].
  { lets (h'&G&K): W H. applys eval_ghost G. constructors*. }
  { lets (h'&G&K): W H. applys eval_ghost G. constructors*. }
  { lets (h'&G&K): W H0. applys eval_ghost G. constructors*. }
  { constructors*. introv Hn1. applys W... *)








(**
(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Affine *)

Definition haffine (H:hprop) : Prop :=
  forall h, H h -> heap_affine h.


Lemma haffine_hempty :
  haffine \[].
Proof using.
  introv K. lets E: hempty_inv K. subst. applys heap_affine_empty.
Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using.
  intros. intros h K. lets (HP&M): hpure_inv K.
  subst. applys heap_affine_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  introv M1 M2 K. lets (h1&h2&K1&K2&D&U): hstar_inv K.
  subst. applys* heap_affine_union.
Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall' : forall A (J:A->hprop),
  (exists x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using.
  introv (x&Hx) M. lets N: hforall_inv M. applys* Hx.
Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).
Proof using.
  introv IA M. applys haffine_hforall'. exists (arbitrary (A:=A)). applys M.
Qed.

Lemma haffine_hstar_hpure_l : forall P H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using. introv M. intros h K. rewrite hstar_hpure_l in K. applys* M. Qed.


(* ########################################################### *)
(** ** Definition of the "Affine Top" Heap Predicates *)

(** We next introduce a new heap predicate, called "affine top" and written
    [\GC], that is very handy for describing "the possibility to discard a heap
    predicate". We use this predicate to reformulate the discard rules in a more
    concise and more usable manner. This predicate is written [\GC] and named
    [hgc] in the formalization. The predicate [\GC] holds of any affine heap.
    [\GC] can be defined as [exists H, \[haffine H] \* H]. As we prove further
    on, it could be equivalently defined as [fun h => heap_affine h]. We prefer
    the former definition, which is easier to manipulate using the [xsimpl]
    tactic. *)

Definition hgc : hprop :=
  \exists H, \[haffine H] \* H.

Declare Scope hgc_scope.
Open Scope hgc_scope.

Notation "\GC" := (hgc) : hgc_scope.

Lemma hgc_intro : forall h,
  heap_affine h ->
  \GC h.
Proof using.
  unfold hgc. intros h K. applys hexists_intro (=h).
  rewrite hstar_hpure_l. split. { intros h' E. subst. auto. } { auto. }
Qed.

Lemma hgc_inv : forall h,
  \GC h ->
  heap_affine h.
Proof using.
  unfold hgc. intros h M. lets (H&K): hexists_inv M.
  rewrite hstar_hpure_l in K. destruct K as (K&Hh).
  unfold haffine in K. applys K. auto.
Qed.

Lemma hstar_hgc_hgc :
  (\GC \* \GC) = \GC.
Proof using.
  unfold hgc. applys himpl_antisym.
  { xpull. intros H1 K1 H2 K2. xsimpl (H1 \* H2). applys* haffine_hstar. }
  { xpull. intros H K. xsimpl H \[]. auto. applys haffine_hempty. }
Qed.

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  applys haffine_hexists. intros H. applys haffine_hstar_hpure_l. auto.
Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. intros h K. applys hgc_intro. applys M K. Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Proof of the Frame Property for Omni-Big-Step *)

Lemma eval_frame : forall h1 h2 t Q,
  eval h1 t Q ->
  Fmap.disjoint h1 h2 ->
  eval (h1 \u h2) t (Q \*+ (= h2)).
Proof using.
  introv M HD. gen h2. induction M; intros;
    try solve [ hint hstar_intro; constructors* ].
  { rename M into M1, H into M2, IHM into IH1, H0 into IH2.
    specializes IH1 HD. applys eval_let IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): HK. subst. applys* IH2. }
  { rename H into M. applys eval_ref. intros p Hp.
    rewrite indom_union_eq in Hp. rew_logic in Hp.
    destruct Hp as [Hp1 Hp2].
    rewrite* update_union_not_r. applys hstar_intro.
    { applys* M. } { auto. } { applys* disjoint_update_not_r. } }
  { applys eval_get. { rewrite* indom_union_eq. }
    { rewrite* read_union_l. applys* hstar_intro. } }
  { applys eval_set. { rewrite* indom_union_eq. }
    { rewrite* update_union_l. applys hstar_intro.
      { auto. } { auto. } { applys* disjoint_update_l. } } }
  { applys eval_free. { rewrite* indom_union_eq. }
    { rewrite* remove_disjoint_union_l. applys hstar_intro.
      { auto. } { auto. } { applys* disjoint_remove_l. } } }
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Construction of Separation Logic *)


(* ########################################################### *)
(** ** Structural Rules *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. unfolds triple. introv M MH MQ HF. applys* eval_conseq. Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof.
  introv M. intros h HF. lets (h1&h2&M1&M2&MD&MU): (rm HF).
  subst. specializes M M1. applys eval_conseq.
  { applys eval_frame M MD. } { xsimpl. intros h' ->. applys M2. }
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

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. introv M Hs. applys* eval_val. Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using. introv M Hs. applys* eval_fix. Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using. introv M Hs. applys* eval_if. Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M Hs. applys* eval_app_fix. Qed.

Lemma triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using. introv M1 M2 Hs. applys* eval_let. Qed.


(* ########################################################### *)
(** ** Specification of Primitive Operations *)

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using.
  introv Hn2 Hs. applys* eval_div. inverts Hs. exists*. hnfs*.
Qed.

Lemma triple_rand : forall n,
  n > 0 ->
  triple (val_rand n)
    \[]
    (fun r => \[exists n1, r = val_int n1 /\ 0 <= n1 < n]).
Proof using.
  introv Hn2 Hs. applys* eval_rand. inverts Hs.
  intros n1 Hn1. hnfs. exists*. hnfs*.
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof using.
  intros. intros s1 K. applys eval_ref. intros p D.
  inverts K. rewrite update_empty. exists p.
  rewrite hstar_hpure_l. split*. hnfs*.
Qed.

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. intros s K. inverts K. applys eval_get.
  { applys* indom_single. }
  { rewrite hstar_hpure_l. split*. rewrite* read_single. hnfs*. }
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun r => (p ~~> v)).
Proof using.
  intros. intros s1 K. inverts K. applys eval_set.
  { applys* indom_single. }
  { rewrite update_single. hnfs*. }
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun r => \[]).
Proof using.
  intros. intros s1 K. inverts K. applys eval_free.
  { applys* indom_single. }
  { rewrite* remove_single. hnfs*. }
Qed.

(** For example proofs in Separation Logic, see the course:
    Separation Logic Foundations, vol 6 of the Software Foundations series:
    https://softwarefoundations.cis.upenn.edu/slf-current/index.html *)
*)
