(****************************************************************
* Imperative Lambda-calculus                                    *
* Big-Step Semantics                                            *
****************************************************************)

Set Implicit Arguments.
Require Export Syntax.

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
(** * Standard semantics *)

(* ########################################################### *)
(** ** Standard Big-step *)

(** Judgment [big s t s' v]. *)

Inductive big : state -> trm -> state -> val -> Prop :=
  | big_val : forall s v,
      big s (trm_val v) s v
  | big_fix : forall s f x t1,
      big s (trm_fix f x t1) s (val_fix f x t1)
  | big_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      big s1 (subst x v2 (subst f v1 t1)) s2 v ->
      big s1 (trm_app v1 v2) s2 v
  | big_let : forall s1 s2 s3 x t1 t2 v1 r,
      big s1 t1 s2 v1 ->
      big s2 (subst x v1 t2) s3 r ->
      big s1 (trm_let x t1 t2) s3 r
  | big_if : forall s1 s2 b v t1 t2,
      big s1 (if b then t1 else t2) s2 v ->
      big s1 (trm_if (val_bool b) t1 t2) s2 v
  | big_div : forall s n1 n2,
      n2 <> 0 ->
      big s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2))
  | big_rand : forall s n n1,
      0 <= n1 < n ->
      big s (val_rand (val_int n)) s (val_int n1)
  | big_ref : forall s v p,
      ~ Fmap.indom s p ->
      big s (val_ref v) (Fmap.update s p v) (val_loc p)
  | big_get : forall s p,
      Fmap.indom s p ->
      big s (val_get (val_loc p)) s (Fmap.read s p)
  | big_set : forall s p v,
      Fmap.indom s p ->
      big s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | big_free : forall s p,
      Fmap.indom s p ->
      big s (val_free (val_loc p)) (Fmap.remove s p) val_unit.


(* ########################################################### *)
(** ** Coinductive Big-step *)

(** [codiv s t] asserts that there exists a diverging execution
    of the program [(s,t)]. This judgment is defined coinductively,
    and depends on the judgment [big]. *)

CoInductive codiv : state -> trm -> Prop :=
  | codiv_app_fix : forall s1 v1 v2 f x t1,
      v1 = val_fix f x t1 ->
      codiv s1 (subst x v2 (subst f v1 t1)) ->
      codiv s1 (trm_app v1 v2)
  | codiv_let_ctx : forall s1 x t1 t2,
      codiv s1 t1 ->
      codiv s1 (trm_let x t1 t2)
  | codiv_let : forall s1 s2 x t1 t2 v1,
      big s1 t1 s2 v1 ->
      codiv s2 (subst x v1 t2) ->
      codiv s1 (trm_let x t1 t2)
  | codiv_if : forall s1 b t1 t2,
      codiv s1 (if b then t1 else t2) ->
      codiv s1 (trm_if (val_bool b) t1 t2).
