(****************************************************************
* Imperative Lambda-calculus                                    *
* Syntax                                                        *
****************************************************************)

Set Implicit Arguments.
From TLC Require Export LibCore LibVar LibLogic.
Require Export LibSepFmap.
Module Fmap := LibSepFmap.
Definition var_eq := var_compare.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Syntax and Substitution *)

(* ########################################################### *)
(** ** Syntax *)

(** The grammar of the deeply embedded language includes terms and
    values. Values include basic values such as [int] and [bool],
    locations (memory addresses, represented by natural numbers),
    and primitive operations. *)

(** The grammar of primitive operations includes operations on the
    mutable store, a nondeterministic operator [val_rand], and
    a partial operation [val_div]. *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_rand : prim
  | val_div : prim.

Definition loc : Type := nat.

Definition null : loc := 0%nat.

(** The grammar of values. *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fix : var -> var -> trm -> val
  | val_error : val

(** The grammar of terms. *)

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.


(** The types of values and heap values are inhabited. *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.


(* ########################################################### *)
(** ** Mutable State *)

(** A state consists of a finite map from location to values.
    Records and arrays are represented as sets of consecutive cells,
    preceeded by a header field describing the length of the block. *)

Definition state : Type := fmap loc val.

(** [state_empty] is a handy notation to avoid providing
    type arguments to [Fmap.empty] *)

Notation "'state_empty'" := (@Fmap.empty loc val)
  (at level 0).

(** [h1 \u h2] is an optional notation for union of two states;
    in this file, it is only used for pretty-printing. *)

Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity).


(* ########################################################### *)
(** ** Coercions *)

(** Coercions to improve conciseness in the statment of evaluation rules. *)

Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion val_prim : prim >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.


(* ########################################################### *)
(** ** Substitution *)

(** Capture-avoiding substitution, standard definition. *)

Fixpoint subst (y:var) (v':val) (t:trm) : trm :=
  let aux t := subst y v' t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val v') t
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.


(* ########################################################### *)
(** ** Implicit Types *)

(** These definitions need to be reproduced in each file. *)

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
(** * Heap Predicates and Entailment *)

(* ########################################################### *)
(** ** Heap Predicates *)

Declare Scope heap_scope.
Open Scope heap_scope.

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

Hint Resolve qimpl_refl.


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


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * TLC LibTactic Patch *)

Ltac false_invert_iter ::=
  match goal with H:_ |- _ =>
    solve [ inversion H; false
          | clear H; false_invert_iter
          | fail 2 ] end.

