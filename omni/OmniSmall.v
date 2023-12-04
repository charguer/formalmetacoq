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


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Properties *)

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


