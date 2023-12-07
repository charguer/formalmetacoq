(** Work in progress *)


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
(* ########################################################### *)
(* ########################################################### *)
(** * Construction of Ghost State Based WP *)

(* ########################################################### *)
(** ** Ghost State Axiomatization *)

(** Heap is a synonymous for ghost state *)

Parameter heap : Type.

(** Projection of the physical state component from a ghost state *)

Parameter heap_state : heap -> state.

Coercion heap_state : heap >-> state.

(** Update of the physical state component from a ghost state *)

Parameter heap_with_state : heap -> state -> heap.

(** Empty heap *)

Parameter heap_empty : heap.

(** Compatibility of two heaps *)

Parameter heap_compat : heap -> heap -> Prop.

(** Union of two compatible heaps *)

Parameter heap_union : heap -> heap -> heap.

Declare Scope heap_union_scope.

Notation "h1 \u h2" := (heap_union h1 h2)
   (at level 37, right associativity) : heap_union_scope.

Open Scope heap_union_scope.

(** Properties of [heap_state] *)

Parameter heap_state_heap_empty :
  heap_state heap_empty = Fmap.empty.

Parameter heap_state_union : forall h1 h2,
  heap_state (h1 \u h2) = Fmap.union (heap_state h1) (heap_state h2).

(** Properties of [heap_with_state] *)

Parameter heap_state_heap_with_state : forall h s,
  heap_state (heap_with_state h s) = s.

Parameter heap_with_state_eq : forall h' h s,
  heap_with_state h s = heap_with_state h' s.

Parameter heap_with_state_heap_with_state : forall h s s',
  heap_with_state (heap_with_state h s) s' = heap_with_state h s'.

Parameter heap_with_state_heap_empty_state_empty :
   heap_with_state heap_empty state_empty = heap_empty.

(** Properties of [heap_with_state] on [union] *)

Parameter heap_with_state_union_update : forall h1 h2 p v,
  heap_compat h1 h2 ->
  Fmap.indom (heap_state h1) p ->
    heap_with_state (h1 \u h2) (Fmap.union (update (heap_state h1) p v) (heap_state h2))
  = (heap_with_state h1 (update (heap_state h1) p v)) \u h2.

Parameter heap_with_state_union_alloc : forall h1 h2 p v,
  heap_compat h1 h2 ->
  ~ indom (heap_state h1) p ->
  ~ indom (heap_state h2) p ->
    heap_with_state (h1 \u h2) (Fmap.union (update (heap_state h1) p v) (heap_state h2))
  = (heap_with_state h1 (update (heap_state h1) p v)) \u h2.

Parameter heap_with_state_union_remove : forall h1 h2 p,
    heap_with_state (h1 \u h2) (Fmap.union (remove (heap_state h1) p) (heap_state h2))
  = (heap_with_state h1 (remove (heap_state h1) p)) \u h2.

(** Properties of [heap_compat] *)

Parameter heap_compat_update : forall h1 h2 p v,
  heap_compat h1 h2 ->
  Fmap.indom (heap_state h1) p ->
  heap_compat (heap_with_state h1 (update (heap_state h1) p v)) h2.
  (* disjoint union l *)

Parameter heap_compat_alloc : forall h1 h2 p v,
  heap_compat h1 h2 ->
  ~ indom (heap_state h1) p ->
  ~ indom (heap_state h2) p ->
  heap_compat (heap_with_state h1 (update (heap_state h1) p v)) h2.

Parameter heap_compat_remove : forall h1 h2 p,
  heap_compat h1 h2 ->
  heap_compat (heap_with_state h1 (remove (heap_state h1) p)) h2.
  (* disjoint_remove_l *)

Parameter disjoint_heap_state_of_heap_compat : forall h1 h2,
   heap_compat h1 h2 ->
   Fmap.disjoint (heap_state h1) (heap_state h2).

(** Symmetry of [heap_compat] *)

Parameter heap_compat_sym : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h2 h1.

(** [heap_compat] on [heap_empty] *)

Parameter heap_compat_empty_l : forall h,
  heap_compat heap_empty h.

(** [heap_compat] on [heap_union] *)

Parameter heap_compat_union_l_eq: forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat (h1 \u h2) h3 = (heap_compat h1 h3 /\ heap_compat h2 h3).

(** [heap_union] neutral, commutativity, and asociativity *)

Parameter heap_union_empty_l : forall h,
  heap_empty \u h = h.

Parameter heap_union_comm : forall h1 h2,
  heap_compat h1 h2 ->
  h1 \u h2 = h2 \u h1.

Parameter heap_union_assoc : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h2 h3 ->
  heap_compat h1 h3 ->
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).


(* ########################################################### *)
(* ** Axiomatization of ghost updates *)

(** Ghost step *)

Parameter gstep : heap -> heap -> Prop.

(** Ghost step is a reflexive-transitive relation *)

Parameter gstep_refl : refl gstep.
Parameter gstep_trans : trans gstep.

(** Ghost step do not modify the physical state *)

Parameter heap_state_gstep : forall h h',
  gstep h h' ->
  heap_state h' = heap_state h.

(** Ghost step is frame-compatible *)

Parameter gstep_frame_l : forall h2 h1 h1',
 gstep h1 h1' ->
 heap_compat h1 h2 ->
 heap_compat h1' h2 /\ gstep (h1 \u h2) (h1' \u h2).


(* ########################################################### *)
(* ** Derived properties of operations on heaps *)

Lemma heap_compat_sym_eq : forall h1 h2,
  heap_compat h1 h2 = heap_compat h2 h1.
Proof using. hint heap_compat_sym. extens. iff*. Qed.

Lemma heap_compat_empty_r : forall h,
  heap_compat h heap_empty.
Proof using. autos* heap_compat_sym heap_compat_empty_l. Qed.

Lemma heap_union_empty_r : forall h,
  h \u heap_empty = h.
Proof using.
  intros. rewrite* heap_union_comm. apply* heap_union_empty_l.
  applys* heap_compat_empty_r.
Qed.

Lemma heap_compat_union_r_eq: forall h1 h2 h3,
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3) = (heap_compat h1 h2 /\ heap_compat h1 h3).
Proof using.
  introv M. rewrite heap_compat_sym_eq. rewrite* heap_compat_union_l_eq.
  rewrite (heap_compat_sym_eq h2). rewrite* (heap_compat_sym_eq h3).
Qed.

Lemma heap_compat_union_l : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat (h1 \u h2) h3.
Proof using. introv M1 M2 M3. rewrite* heap_compat_union_l_eq. Qed.

Lemma heap_compat_union_r : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3).
Proof using. hint heap_compat_sym, heap_compat_union_l. autos*. Qed.


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
(** ** Properties of the Ghost Update Modality *)

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


(* ########################################################### *)
(** ** Properties of Ghost Updates *)

(** The ghost update modality is idempotent *)

Lemma hupdate_hupdate : forall H,
  hupdate (hupdate H) = hupdate H.
Proof using.
  hint gstep_refl, gstep_trans.
  intros. unfold hupdate. applys himpl_antisym.
  { intros h (h'&G'&(h''&G''&K)). exists* h''. }
  { intros h (h'&G'&K). exists* h'. }
Qed.

(** The ghost update modality is covariant *)

Lemma hupdate_conseq : forall H1 H2,
  H1 ==> H2 ->
  hupdate H1 ==> hupdate H2.
Proof using. introv W. introv (h'&G&K). exists* h'. Qed.

Lemma qupdate_conseq : forall Q1 Q2,
  Q1 ===> Q2 ->
  qupdate Q1 ===> qupdate Q2.
Proof using. introv W. intros v. applys* hupdate_conseq. Qed.

(** Ghost update is reflexive and transitive *)

Lemma ghimpl_refl : forall H,
  H |==> H.
Proof using. introv Hh. applys* gupdate_intro_same. Qed.

Lemma gqimpl_refl : forall Q,
  Q |===> Q.
Proof using. intros Q v. applys* ghimpl_refl. Qed.

Lemma ghimpl_trans : forall H2 H1 H3,
  (H1 |==> H2) ->
  (H2 |==> H3) ->
  (H1 |==> H3).
Proof using.
  unfolds ghimpl. introv M1 M2. applys himpl_trans M1.
  rewrite <- (hupdate_hupdate H3). applys* hupdate_conseq.
Qed.

Lemma gqimpl_trans : forall Q1 Q2 Q3,
  (Q1 |===> Q2) ->
  (Q2 |===> Q3) ->
  (Q1 |===> Q3).
Proof using. introv M1 M2. intros v. applys* ghimpl_trans. Qed.

(** Entailments are included in ghost updates *)

Lemma ghimpl_of_himpl : forall H1 H2,
  H1 ==> H2 ->
  H1 |==> H2.
Proof using. introv M Hh. exists h. split. applys gstep_refl. eauto. Qed.

Lemma gqimpl_of_qimpl : forall Q1 Q2,
  Q1 ===> Q2 ->
  Q1 |===> Q2.
Proof using. introv M. intros v. applys* ghimpl_of_himpl. Qed.


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
      (forall p, ~ Fmap.indom (heap_state h) p ->
         Q (val_loc p) (heap_with_state h (Fmap.update (heap_state h) p v))) ->
      eval h (val_ref v) Q
  | eval_get : forall h p Q,
      Fmap.indom (heap_state h) p ->
      Q (Fmap.read (heap_state h) p) h ->
      eval h (val_get (val_loc p)) Q
  | eval_set : forall h p v Q,
      Fmap.indom (heap_state h) p ->
      Q val_unit (heap_with_state h (Fmap.update (heap_state h) p v)) ->
      eval h (val_set (val_loc p) v) Q
  | eval_free : forall h p Q,
      Fmap.indom (heap_state h) p ->
      Q val_unit ( heap_with_state h (Fmap.remove (heap_state h) p)) ->
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
  { constructors*. intros p Hp. esplit. split*.
    rewrite* heap_state_heap_with_state. }
  { constructors*. hnf. esplit. split*. rewrite* heap_state_heap_with_state. }
  { constructors*. esplit. split*. rewrite* heap_state_heap_with_state. }
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

(** Consequence wrt entailement *)

Lemma eval_conseq : forall h t Q1 Q2,
  eval h t Q1 ->
  Q1 ===> Q2 ->
  eval h t Q2.
Proof using.
  introv M W.
  gen Q2. induction M; intros; try solve [ constructors; try (intros; applys W); eauto].
  { applys eval_ghost_post. applys IHM. applys* qupdate_conseq. }
Qed.

(** Consequence wrt ghost update *)

Lemma eval_conseq_ghost : forall h t Q1 Q2,
  eval h t Q1 ->
  Q1 |===> Q2 ->
  eval h t Q2.
Proof using. introv M W. applys eval_ghost_post. applys* eval_conseq M. Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Construction of Separation Logic Predicates *)

(* ########################################################### *)
(** ** Core Heap Predicates *)

(** Core heap predicates, and their associated notations:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [H1 \-* H2] denotes the magic wand
    - [Q1 \--* Q2] denotes the magic wand on postconditions
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential
    - [\forall x, H] denotes a universal. *)

Definition hempty : hprop :=
  fun h => (h = heap_empty).

Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = heap_with_state heap_empty (Fmap.single p v)).

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                      /\ H2 h2
                      /\ heap_compat h1 h2
                      /\ h = heap_union h1 h2.

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Definition hpure (P:Prop) : hprop := (* encoded as [\exists (p:P), \[]] *)
  hexists (fun (p:P) => hempty).

Declare Scope hprop_scope.
Open Scope hprop_scope.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Definition hwand (H1 H2:hprop) : hprop :=
  \exists H0, H0 \* \[ H1 \* H0 ==> H2 ].

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Definition qwand (Q1 Q2:val->hprop) : hprop :=
  \forall v, (Q1 v) \-* (Q2 v).

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.


(* ########################################################### *)
(** ** Automation for Heap Equality and Heap Disjointness *)

(** For goals asserting equalities between heaps, i.e., of the form [h1 = h2],
    we set up automation so that it performs some tidying: substitution,
    removal of empty heaps, normalization with respect to associativity. *)

#[global] Hint Rewrite union_assoc union_empty_l union_empty_r : fmap.
#[global] Hint Extern 1 (_ = _ :> heap) => subst; autorewrite with fmap.

(** For goals asserting disjointness between heaps, i.e., of the form
    [Fmap.disjoint h1 h2], we set up automation to perform simplifications:
    substitution, exploit distributivity of the disjointness predicate over
    unions of heaps, and exploit disjointness with empty heaps. The tactic
    [jauto_set] used here comes from the TLC library; essentially, it destructs
    conjunctions and existentials. *)

#[global] Hint Resolve Fmap.disjoint_empty_l Fmap.disjoint_empty_r.
#[global] Hint Rewrite disjoint_union_eq_l disjoint_union_eq_r : disjoint.
#[global] Hint Extern 1 (Fmap.disjoint _ _) =>
  subst; autorewrite with rew_disjoint in *; jauto_set.


(* ########################################################### *)
(* ** Introduction and Inversion Lemmas for Core Heap Predicates *)

(** Core heap predicates *)

Lemma hempty_intro :
  \[] heap_empty.
Proof using. hnfs~. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = heap_empty.
Proof using. introv M. auto. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  heap_compat h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ heap_compat h1 h2 /\ h = h1 \u h2.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hexists_intro : forall A (J:A->hprop) x h,
  J x h ->
  (hexists J) h.
Proof using. introv M. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hforall_intro : forall A (J:A->hprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

(** Derived heap predicates *)

Lemma hpure_intro : forall P,
  P ->
  \[P] heap_empty.
Proof using. introv M. exists*. apply hempty_intro. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = heap_empty.
Proof using. introv (p&M). split*. Qed.


(* ########################################################### *)
(** ** Rewriting tactic [rew_heaps] *)

Hint Rewrite heap_union_empty_l heap_union_empty_r heap_union_assoc : rew_heaps.

Tactic Notation "rew_heaps" :=
  autorewrite with rew_heaps.
Tactic Notation "rew_heaps" "in" hyp(H) :=
  autorewrite with rew_heaps in H.
Tactic Notation "rew_heaps" "in" "*" :=
  autorewrite with rew_heaps in *.

Tactic Notation "rew_heaps" "~" :=
  rew_heaps; auto_tilde.
Tactic Notation "rew_heaps" "~" "in" hyp(H) :=
  rew_heaps in H; auto_tilde.
Tactic Notation "rew_heaps" "~" "in" "*" :=
  rew_heaps in *; auto_tilde.

Tactic Notation "rew_heaps" "*" :=
  rew_heaps; auto_star.
Tactic Notation "rew_heaps" "*" "in" hyp(H) :=
  rew_heaps in H; auto_star.
Tactic Notation "rew_heaps" "*" "in" "*" :=
  rew_heaps in *; auto_star.


(* ########################################################### *)
(** ** Properties of [hstar] *)

Section CoreProperties.
Hint Resolve heap_compat_empty_l heap_compat_empty_r
  heap_union_empty_l heap_union_empty_r hempty_intro
  heap_compat_union_l heap_compat_union_r.

(** Star is commutative *)

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  hint heap_union_comm, heap_compat_sym.
  intros. unfold hstar. extens. intros h.
  iff (h1&h2&M1&M2&D&U).
  { exists h2 h1. subst~. }
  { exists h2 h1. subst~. }
Qed.

(** Star is associative *)

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  hint heap_compat_union_r, heap_compat_union_l, hstar_intro.
  intros. extens. intros h. split.
  { intros (h'&h3&(h1&h2&M2&P1&P2&->)&M3&M1&->).
    rewrite* heap_compat_union_l_eq in M1.
    exists* h1 (h2 \u h3). rewrite* heap_union_assoc. }
  { intros (h1&h'&P1&(h2&h3&M2&P2&P3&->)&M1&->).
    rewrite* heap_compat_union_r_eq in M1.
    exists* (h1 \u h2) h3. rewrite* heap_union_assoc. }
Qed.

(** Empty is neutral for star *)

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using.
  intros. applys pred_ext_1. intros h.
  iff (h1&h2&M1&M2&D&->) M.
  { rewrite (hempty_inv M1). rew_heaps*. }
  { exists~ heap_empty h. }
Qed.

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof.
  applys neutral_r_of_comm_neutral_l. applys* hstar_comm. applys* hstar_hempty_l.
Qed.

(** Extrusion of existentials out of star *)

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  hint hexists_intro.
  intros. applys pred_ext_1. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists* x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists* h1 h2. }
Qed.

(** Extrusion of foralls out of star *)

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U).
  intros x. exists~ h1 h2.
Qed.

(** The frame property (star on H2) holds for entailment *)

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof.
  introv M. do 2 rewrite (@hstar_comm H1). applys* himpl_frame_l.
Qed.

(** The frame property (star on H2) holds for ghost update *)

Lemma ghimpl_frame_l : forall H1 H2 H1',
  H1 |==> H1' ->
  H1 \* H2 |==> H1' \* H2.
Proof using.
  introv W (h1&h2&K1&K2&D&->).
  unfolds ghimpl, hupdate.
  lets (h1'&G1&R1): W K1.
  forwards* (D'&G'): gstep_frame_l h2 G1.
  hint hstar_intro. exists* (h1' \u h2).
Qed.

Lemma qhimpl_frame_l : forall Q1 H2 Q1',
  Q1 |===> Q1' ->
  Q1 \*+ H2 |===> Q1' \*+ H2.
Proof using. introv M. intros v. applys* ghimpl_frame_l. Qed.

(** Properties of [hpure] *)

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. extens. unfold hpure.
  rewrite hstar_hexists.
  rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.


(* ########################################################### *)
(** ** Properties of [hpure] *)

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof. introv W Hh. rewrite hstar_hpure_l in Hh. applys* W. Qed.


(* ########################################################### *)
(** ** Properties of [hexists] *)

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof. introv W. intros h. exists x. apply* W. Qed.

Lemma himpl_hexists : forall (J1 J2:val->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.


(* ########################################################### *)
(** ** Properties of [hforall] *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof. introv M. intros h Hh x. apply* M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof. introv M. intros h Hh. apply* M. Qed.

Lemma himpl_hforall : forall (J1 J2:val->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.


(* ########################################################### *)
(** ** Basic Tactics for Simplifying Entailments *)

(** [xsimpl] performs immediate simplifications on entailment relations.
    For a more powerful version of [xsimpl], see the course
    Separation Logic Foundations, or the implementation of the CFML tool. *)

Hint Rewrite hstar_assoc hstar_hempty_l hstar_hempty_r : hstar.

Tactic Notation "xsimpl" :=
  try solve [ apply qimpl_refl ];
  try match goal with |- _ ===> _ => intros ? end;
  autorewrite with hstar; repeat match goal with
  | |- ?H \* _ ==> ?H \* _ => apply himpl_frame_r
  | |- _ \* ?H ==> _ \* ?H => apply himpl_frame_l
  | |- _ \* ?H ==> ?H \* _ => rewrite hstar_comm; apply himpl_frame_r
  | |- ?H \* _ ==> _ \* ?H => rewrite hstar_comm; apply himpl_frame_l
  | |- ?H ==> ?H => apply himpl_refl
  | |- ?H ==> ?H' => is_evar H'; apply himpl_refl end.

Tactic Notation "xsimpl" "*" := xsimpl; auto_star.

(** [xchange] helps rewriting in entailments. *)

Lemma xchange_lemma : forall H1 H1',
  H1 ==> H1' -> forall H H' H2,
  H ==> H1 \* H2 ->
  H1' \* H2 ==> H' ->
  H ==> H'.
Proof.
  introv M1 M2 M3. applys himpl_trans M2. applys himpl_trans M3.
  applys himpl_frame_l. applys M1.
Qed.

Tactic Notation "xchange" constr(M) :=
  forwards_nounfold_then M ltac:(fun K =>
    eapply xchange_lemma; [ eapply K | xsimpl | ]).


(* ########################################################### *)
(** ** Properties of [hwand] *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { xchange M. rewrite hstar_hexists.
    applys himpl_hexists_l. intros H. rewrite (hstar_comm H).
    rewrite hstar_assoc. applys himpl_hstar_hpure_l. intros N.
    rewrite hstar_comm. auto. }
  { applys himpl_hexists_r H0. rewrite hstar_comm.
    applys* himpl_hstar_hpure_r. }
Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. rewrite* <- hwand_equiv. Qed.

Arguments hwand_cancel : clear implicits.


(* ########################################################### *)
(** ** Properties of [qwand] *)

Lemma qwand_specialize : forall (v:val) (Q1 Q2:val->hprop),
  (Q1 \--* Q2) ==> (Q1 v \-* Q2 v).
Proof using.
  intros. unfold qwand. applys himpl_hforall_l v. xsimpl.
Qed.

Lemma qwand_cancel : forall Q1 Q2,
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using.
  intros. intros v. applys himpl_trans.
  applys himpl_frame_r. applys qwand_specialize v.
  applys hwand_cancel.
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Affine *)

(* ########################################################### *)
(** ** Definition and properties of [heap_affine] *)

(** [heap_affine h] asserts that [h] may be discarded, in the
    sense that via a ghost update it may reduce to [heap_empty]. *)

Definition heap_affine (h:heap) : Prop :=
  gstep h heap_empty.

Lemma heap_affine_empty :
  heap_affine heap_empty.
Proof using. applys gstep_refl. Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  heap_compat h1 h2 ->
  heap_affine (h1 \u h2).
Proof using.
  introv M1 M2 D. unfolds heap_affine. applys gstep_trans.
  { applys* gstep_frame_l M1. } { rew_heaps*. }
Qed.


(* ########################################################### *)
(** ** Definition and properties of [haffine] *)

(** [haffine H] asserts that [H] characterizes only heaps that
    may be reduced to [heap_empty] via a ghost update. *)

Definition haffine (H:hprop) : Prop :=
  forall h, H h -> heap_affine h.

(** Alternative definition of [haffine] *)

Definition haffine' (H:hprop) : Prop :=
  H |==> \[].

Lemma haffine_eq_haffine' :
  haffine = haffine'.
Proof using.
  unfolds haffine, haffine', ghimpl, heap_affine, hupdate.
  extens. intros H. iff M.
  { introv Hh. specializes M Hh. eauto. }
  { introv Hh. forwards (h'&G&K): M Hh. hnf in K. subst*. }
Qed.

(** Properties of [haffine] *)

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
    [\GC] and named [hgc] in the formalization. The predicate [\GC] holds of any
    affine heap. [\GC] can be defined as [exists H, \[haffine H] \* H], or
    as [heap_affine]. We prefer the former definition, which is easier to manipulate
    using the [xsimpl] tactic. *)

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
(** ** Ghost updates for [haffine] *)

Lemma ghimpl_haffine_hempty : forall H,
  haffine H ->
  H |==> \[].
Proof using.
  unfold haffine, heap_affine. introv M Hh. esplit. splits*.
Qed.

Lemma ghimpl_hgc_hempty :
  \GC |==> \[].
Proof using. applys ghimpl_haffine_hempty. applys haffine_hgc. Qed.

Lemma ghimpl_hstar_haffine_l : forall H H',
  haffine H' ->
  H' \* H |==> H.
Proof using.
  introv N. applys ghimpl_trans. applys ghimpl_frame_l.
  { applys* ghimpl_haffine_hempty. }
  { rewrite hstar_hempty_l. applys ghimpl_refl. }
Qed.

Lemma ghimpl_hstar_hgc_l : forall H,
  H \* \GC |==> H.
Proof using.
  intros. rewrite hstar_comm. applys ghimpl_trans. applys ghimpl_frame_l.
  { applys* ghimpl_hgc_hempty. }
  { rewrite hstar_hempty_l. applys ghimpl_refl. }
Qed.

Lemma gqimpl_hstar_hgc_l : forall Q,
  Q \*+ \GC |===> Q.
Proof using. intros Q v. applys* ghimpl_hstar_hgc_l. Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Rules of Separation Logic that Don't Depend on the Ghost State *)


(* ########################################################### *)
(** ** Frame property for Ghost update *)

(** The ghost update modality satisfies the frame property *)

Lemma hupdate_frame : forall H1 H2,
  (hupdate H1) \* H2 ==> hupdate (H1 \* H2).
Proof using.
  unfold hupdate. introv Hh. lets (h1&h2&(h1'&G&H1')&?&?&->): hstar_inv (rm Hh).
  forwards* (D'&G'): gstep_frame_l h2 G. exists (h1' \u h2). splits*. applys* hstar_intro.
Qed.

Lemma qupdate_frame : forall Q H,
  qupdate Q \*+ H ===> qupdate (Q \*+ H).
Proof using. intros. intros v. applys hupdate_frame. Qed.


(* ########################################################### *)
(** ** Frame property for WP *)

Hint Constructors eval.

Lemma eval_frame : forall h1 h2 t Q,
  eval h1 t Q ->
  heap_compat h1 h2 ->
  eval (h1 \u h2) t (Q \*+ (= h2)).
Proof using.
  introv M HD. gen h2. induction M; intros;
    try solve [ hint hstar_intro; constructors* ].
  { eauto 8. }
  { rename M into M1, H into M2, IHM into IH1, H0 into IH2.
    specializes IH1 HD. applys eval_let IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): HK. subst. applys* IH2. }
  { applys eval_ref. intros p Hp.
    rewrite heap_state_union in *.
    rewrite indom_union_eq in Hp. rew_logic in Hp.
    destruct Hp as [Hp1 Hp2]. rewrite* update_union_not_r.
    rewrite* heap_with_state_union_alloc. applys* hstar_intro.
    { applys* heap_compat_alloc. } }
  { applys eval_get; rewrite heap_state_union.
     { rewrite* indom_union_eq. }
     { rewrite* read_union_l. applys* hstar_intro. } }
  { applys eval_set; rewrite heap_state_union.
     { rewrite* indom_union_eq. }
     { rewrite* update_union_l. rewrite* heap_with_state_union_update.
      applys* hstar_intro. { applys* heap_compat_update. } } }
  { applys eval_free; rewrite heap_state_union.
     { rewrite* indom_union_eq. }
     { lets D': disjoint_heap_state_of_heap_compat HD.
       rewrite* remove_disjoint_union_l. rewrite heap_with_state_union_remove.
       applys* hstar_intro. { applys* heap_compat_remove. } } }
  { forwards* (?&?): gstep_frame_l h2 h h'. }
  { applys eval_ghost_post. applys* eval_conseq. applys* qupdate_frame. }
Qed.


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

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq W.
  applys* triple_frame (Q1 \--* Q) M.
  applys qwand_cancel.
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
  inverts HP. subst. rew_heaps*.
Qed.

(** Ghost updates *)

Lemma triple_conseq_post_ghost : forall t H Q1 Q2,
  triple t H Q1 ->
  Q1 |===> Q2 ->
  triple t H Q2.
Proof using. unfolds triple. introv M MH Hh. applys* eval_conseq_ghost. Qed.

Lemma triple_conseq_pre_ghost : forall t H1 H2 Q,
  triple t H2 Q ->
  H1 |==> H2 ->
  triple t H1 Q.
Proof using.
  unfolds triple. introv M MH Hh.
  lets (h'&G&H'): MH Hh. applys* eval_ghost_pre.
Qed.

Lemma triple_post_ghost : forall t H Q,
  triple t H (qupdate Q) ->
  triple t H Q.
Proof using.
  unfolds triple. introv M Hh. applys* eval_conseq_ghost.
  intros v. applys himpl_refl.
Qed.

Lemma triple_ramified_frame_ghost : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H |==> (H1 \* (Q1 \--* qupdate Q)) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_post_ghost.
  applys triple_conseq_pre_ghost W.
  applys triple_conseq_post_ghost.
  applys* triple_frame (Q1 \--* qupdate Q) M.
  applys gqimpl_of_qimpl. applys qwand_cancel.
Qed.

(** Garbage-collection rules *)

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. applys triple_conseq_post_ghost M.
  applys gqimpl_hstar_hgc_l.
Qed.

Lemma triple_haffine_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  haffine H' ->
  triple t H Q.
Proof using.
  introv M K. applys triple_hgc_post.
  applys* triple_conseq M.
  intros v. xsimpl. applys* himpl_hgc_r.
Qed.

Lemma triple_haffine_pre : forall t H H' Q,
  triple t H Q ->
  haffine H' ->
  triple t (H' \* H) Q.
Proof using.
  introv M K. applys triple_conseq_pre_ghost M.
  applys* ghimpl_hstar_haffine_l.
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
  introv Hn2 Hs. applys* eval_div. inverts Hs. exists*.
Qed.

Lemma triple_rand : forall n,
  n > 0 ->
  triple (val_rand n)
    \[]
    (fun r => \[exists n1, r = val_int n1 /\ 0 <= n1 < n]).
Proof using.
  introv Hn2 Hs. applys* eval_rand. inverts Hs.
  intros n1 Hn1. hnfs. exists*.
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof using.
  intros. intros s1 K. inverts K. applys eval_ref. intros p Hp.
  exists p. rewrite hstar_hpure_l. split*.
  rewrite heap_state_heap_empty. rewrite update_empty. hnfs*.
Qed.

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. intros s K. inverts K.
  applys eval_get; rewrite heap_state_heap_with_state.
  { applys* indom_single. }
  { rewrite hstar_hpure_l. split*.
    { rewrite* read_single. }
    { hnfs*. } }
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun r => (p ~~> v)).
Proof using.
  intros. intros s1 K. inverts K.
  applys eval_set; rewrite heap_state_heap_with_state.
  { applys* indom_single. }
  { rewrite update_single. rew_heaps. hnfs. applys* heap_with_state_eq. }
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun r => \[]).
Proof using.
  intros. intros s1 K. inverts K.
  applys eval_free; rewrite heap_state_heap_with_state.
  { applys* indom_single. }
  { rewrite* remove_single. rew_heaps.
    rewrite heap_with_state_heap_with_state. hnfs*.
    rewrite* heap_with_state_heap_empty_state_empty. }
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Instantiation to a Concrete Ghost State *)

(* Example of a ghost state that carries times credits *)

(* ########################################################### *)
(** ** Properties of [hsingle] *)

(* TODO
Lemma hstar_hsingle_same_loc : forall p v1 v2,
  (p ~~> v1) \* (p ~~> v2) ==> \[False].
Proof.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.
*)



