(****************************************************************
* Imperative Lambda-calculus                                    *
* Heap predicates                                               *
****************************************************************)

Set Implicit Arguments.
Require Export Syntax.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Heap Predicates and Entailment *)

(* ########################################################### *)
(** ** Heap Predicates *)

Declare Scope heap_scope.
Open Scope heap_scope.

(** Heap is a synonymous for state *)

Definition heap : Type := state.

(** Heap predicate *)

Definition hprop := state -> Prop.

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(** ** Entailment *)

(** Heap entailment *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2)
  (at level 55) : heap_scope.

(** Properties *)

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


(* ########################################################### *)
(** ** Entailment on Postconditions *)

(** Entailment on postconditions *)

Definition qimpl A (Q1 Q2:A->hprop) :=
  forall x, himpl (Q1 x) (Q2 x).

Notation "Q1 ===> Q2" := (qimpl Q1 Q2)
  (at level 55) : heap_scope.

(** Properties *)

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. unfolds*. Qed.

Lemma qimpl_trans : forall A (Q1 Q2 Q3:A->hprop),
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. eapply himpl_trans; eauto. Qed.

#[global] Hint Resolve qimpl_refl.


(* ########################################################### *)
(** ** The Always-True and Always-False Postconditions *)

(** Let [Any] denotes the postcondition that accepts any result. *)

Definition Any : val->state->Prop :=
  fun v s => True.

Hint Unfold Any.

(** Let [Empty] denotes the postcondition that rejects any result. *)

Definition Empty : val->state->Prop :=
  fun v s => False.

Hint Unfold Empty.
