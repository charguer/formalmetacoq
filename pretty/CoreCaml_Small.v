(************************************************************
* Core Caml                                                 *
* Small-big-step semantics                                  *
*************************************************************)

Set Implicit Arguments.
Require Export LibEnv CoreCaml_Syntax.


(*==========================================================*)
(* * Updated Definitions *)


(************************************************************)
(* ** Syntax of the language *)

(** Grammar of values *)

Inductive val : Type :=
  | val_cst : cst -> val
  | val_loc : loc -> val
  | val_abs : option var -> pat -> trm -> val
  | val_constr : constr -> list val -> val
  | val_tuple : list val -> val
  | val_record : list (lab*val) -> val

(** Grammar of terms *)

with trm : Type :=
  | trm_var : var -> trm
  | trm_cst : cst -> trm
  | trm_abs : option var -> pat -> trm -> trm
  | trm_constr : constr -> list trm -> trm
  | trm_tuple : list trm -> trm
  | trm_record : list (lab*trm) -> trm
  | trm_unary : prim -> trm -> trm
  | trm_binary : prim -> trm -> trm -> trm
  | trm_lazy_binary : prim -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : pat -> trm -> trm -> trm
  | trm_get : trm -> lab -> trm
  | trm_set : trm -> lab -> trm -> trm
  | trm_if : trm -> trm -> option trm -> trm
  | trm_while : trm -> trm -> trm
  | trm_for : var -> dir -> trm -> trm -> trm -> trm
  | trm_match : trm -> list branch -> trm
  | trm_try : trm -> list branch -> trm
  | trm_assert : trm -> trm
  | trm_rand : trm

(** including intermediate forms for the semantics *)

  | trm_val : val -> trm
  | trm_match_1 : val -> list branch -> trm -> trm -> trm
  | trm_try_1 : val -> list branch -> trm
  | trm_try_2 : val -> list branch -> trm -> trm -> trm

with branch : Type :=
  | branch_intro : pat -> option trm -> trm -> branch.

(** Representation of the memory store *)

Definition mem := Heap.heap loc val.


(************************************************************)
(* ** Auxiliary definitions *)

(** Substitution *)

Definition inst := LibEnv.env val.

Parameter subst : forall (x:var) (v:val) (t:trm), trm.
Parameter substs : forall (i:inst) (t:trm), trm.

(** [val] is inhabited *)

Instance val_inhab : Inhab val.
Proof. intros. apply (Inhab_of_val (val_cst (cst_bool true))). Qed.

(** Coercions *)
(*
Coercion cst_int : Z >-> cst.
Coercion cst_bool : bool >-> cst.
Coercion pat_var : var >-> pat.
*)
Coercion val_loc : loc >-> val.
Coercion val_cst : cst >-> val.

(** Shortnames for lists of terms and values *)

Definition trms := list trm.
Definition vals := list val.
Definition labtrms := list (lab*trm).
Definition labvals := list (lab*val).

(** Shortcuts for building terms and values *)

Definition val_exn k := val_constr k nil.

Definition val_unit := val_constr constr_unit nil.

(** Fresh locations *)

Definition fresh (m:mem) l :=
  ~ Heap.indom m l.


(************************************************************)
(* ** Auxiliary definitions specific to small-step *)

Coercion trm_val : val >-> trm.

(** From list of values to list of terms *)

Definition trms_vals (vs : vals) : trms :=
  LibList.map trm_val vs.

Definition trms_lab_vals (avs : labvals) : labtrms :=
  LibList.map (fun av => let '(a,v) := av in (a, trm_val v)) avs.

(** Auxiliary terms *)

Definition trm_raise := trm_unary prim_raise.

Definition trm_error k := trm_raise (val_exn k).



(*==========================================================*)
(* * Definitions *)

Implicit Types x : var.
Implicit Types c : cst.
Implicit Types f : prim.
Implicit Types k : constr.
Implicit Types v : val.
Implicit Types t : trm.
Implicit Types m : mem.
Implicit Types b : branch.
Implicit Types a : lab.
Implicit Types l : loc.
Implicit Types i : inst.
Implicit Types n : int.
Implicit Types r : bool.


(************************************************************)
(* ** Auxiliary semantics definitions *)

(** Semantics of Pattern matching *)

Inductive matching (i : inst) : val -> pat -> Prop :=
  | matching_var : forall x v,
      LibEnv.binds x v i ->
      matching i v (pat_var x)
  | matching_wild : forall v,
      matching i v pat_wild
  | matching_alias : forall x v p,
      matching i v p ->
      LibEnv.binds x v i ->
      matching i v (pat_alias p x)
  | matching_or : forall v p p1 p2,
      matching i v p ->
      (p = p1 \/ p = p2) ->
      matching i v (pat_or p1 p2)
  | matching_cst : forall c,
      matching i c (pat_cst c)
  | matching_constr : forall k vs ps,
      Forall2 (matching i) vs ps ->
      matching i (val_constr k vs) (pat_constr k ps)
  | matching_tuple : forall vs ps,
      Forall2 (matching i) vs ps ->
      matching i (val_tuple vs) (pat_tuple ps)
  | matching_record_nil : forall avs,
      matching i (val_tuple avs) (pat_tuple nil)
  | matching_record_cons : forall avs a v p aps,
      LibListAssoc.Assoc a v avs ->
      matching i v p ->
      matching i (val_record avs) (pat_record aps) ->
      matching i (val_record avs) (pat_record ((a,p)::aps)).

Definition mismatching v p :=
  forall i, ~ matching i v p.

(** Semantics of primitive equality *)

Parameter primitive_eq : val -> val -> bool -> Prop.



(************************************************************)
(* ** Reduction contexts *)

(** Grammar of contexts *)

Inductive ctx :=
  | ctx_hole : ctx
  | ctx_constr : constr -> list val -> ctx -> list trm -> ctx
  | ctx_tuple : list val -> ctx -> list trm -> ctx
  | ctx_record : list (lab*val) -> lab -> ctx -> list (lab*trm) -> ctx
  | ctx_unary : prim -> ctx -> ctx
  | ctx_binary_1 : prim -> ctx -> trm -> ctx
  | ctx_binary_2 : prim ->val -> ctx -> ctx
  | ctx_lazy_binary : prim ->ctx -> trm -> ctx
  | ctx_app_1 : ctx -> trm -> ctx
  | ctx_app_2 : val -> ctx -> ctx
  | ctx_seq : ctx -> trm -> ctx
  | ctx_let : pat -> ctx -> trm -> ctx
  | ctx_get : ctx -> lab -> ctx
  | ctx_set_1 : ctx -> lab -> trm -> ctx
  | ctx_set_2 : val -> lab -> ctx -> ctx
  | ctx_if : ctx -> trm -> option trm -> ctx
  | ctx_for_1 : var -> dir -> ctx -> trm -> trm -> ctx
  | ctx_for_2 : var -> dir -> val -> ctx -> trm -> ctx
  | ctx_match : ctx -> list branch -> ctx
  | ctx_try : ctx -> list branch -> ctx
  | ctx_assert : ctx -> ctx
  | ctx_match_1 : val -> list branch -> ctx -> trm -> ctx
  | ctx_try_2 : val -> list branch -> ctx -> trm -> ctx.

Implicit Types C : ctx.

(** Application of contexts *)

Fixpoint ctx_apply C t :=
  let r C' := ctx_apply C' t in
  match C with
  | ctx_hole => t
  | ctx_constr k vs C' ts => trm_constr k (trms_vals vs ++ (r C') :: ts)
  | ctx_tuple vs C' ts => trm_tuple (trms_vals vs ++ (r C') :: ts)
  | ctx_record avs a C' ats => trm_record (trms_lab_vals avs ++ (a, (r C')) :: ats)
  | ctx_unary f C' => trm_unary f (r C')
  | ctx_binary_1 f C' t2 => trm_binary f (r C') t2
  | ctx_binary_2 f v1 C' => trm_binary f v1 (r C')
  | ctx_lazy_binary f C' t2 => trm_lazy_binary f (r C') t2
  | ctx_app_1 C' t2 => trm_app (r C') t2
  | ctx_app_2 v1 C' => trm_app v1 (r C')
  | ctx_seq C' t2 => trm_seq (r C') t2
  | ctx_let p C' t2 => trm_let p (r C') t2
  | ctx_get C' a => trm_get (r C') a
  | ctx_set_1 C' a t2 => trm_set (r C') a t2
  | ctx_set_2 v1 a C' => trm_set v1 a (r C')
  | ctx_if C' t2 ot3 => trm_if (r C') t2 ot3
  | ctx_for_1 x d C' t2 t3 => trm_for x d (r C') t2 t3
  | ctx_for_2 x d v1 C' t3 => trm_for x d v1 (r C') t3
  | ctx_match C' bs => trm_match (r C') bs
  | ctx_try C' bs => trm_try (r C') bs
  | ctx_assert C' => trm_assert (r C')
  | ctx_match_1 v bs C' t => trm_match_1 v bs (r C') t
  | ctx_try_2 v bs C' t => trm_try_2 v bs (r C') t
  end.

(** Contexts that do not contain [try] construct *)

Fixpoint ctx_notry C :=
  let r := ctx_notry in
  match C with
  | ctx_try C' bs => False
  | ctx_hole => True
  | ctx_constr k vs C' ts => r C'
  | ctx_tuple vs C' ts => r C'
  | ctx_record avs a C' ats => r C'
  | ctx_unary f C' => r C'
  | ctx_binary_1 f C' t2 => r C'
  | ctx_binary_2 f v1 C' => r C'
  | ctx_lazy_binary f C' t2 => r C'
  | ctx_app_1 C' t2 => r C'
  | ctx_app_2 v1 C' => r C'
  | ctx_seq C' t2 => r C'
  | ctx_let p C' t2 => r C'
  | ctx_get C' a => r C'
  | ctx_set_1 C' a t2 => r C'
  | ctx_set_2 v1 a C' => r C'
  | ctx_if C' t2 ot3 => r C'
  | ctx_for_1 x d C' t2 t3 => r C'
  | ctx_for_2 x d v1 C' t3 => r C'
  | ctx_match C' bs => r C'
  | ctx_assert C' => r C'
  | ctx_match_1 v bs C' t => r C'
  | ctx_try_2 v bs C' t => r C'
  end.


(************************************************************)
(* ** Small-step reduction relation *)

(** Configuration *)

Definition conf := (trm * mem)%type.

(** Reduction *)

Reserved Notation "t1 '/' m1 '--->' t2 '/' m2"
  (at level 40, m1 at level 30, t2 at level 30, m2 at level 30).

Inductive step : binary conf :=

  | step_ctx : forall C t1 m1 t2 m2,
      t1 / m1 ---> t2 / m2 ->
      (ctx_apply C t1) / m1 --->
      (ctx_apply C t2) / m2
  | step_raise : forall C v m,
      ctx_notry C ->
      (ctx_apply C (trm_raise v)) / m --->
      (trm_raise v) / m

  | step_abs : forall oy p t m,
      (trm_abs oy p t) / m --->
      (val_abs oy p t) / m
  | step_constr : forall k vs m,
      (trm_constr k (trms_vals vs)) / m --->
      (val_constr k vs) / m
  | step_tuple : forall vs m,
      (trm_tuple (trms_vals vs)) / m --->
      (val_tuple vs) / m

  | step_unary_not : forall r m,
      (trm_unary prim_not r) / m --->
      (neg r) / m
  | step_unary_neg : forall n m,
      (trm_unary prim_not n) / m --->
      (cst_int (-n)) / m
  | step_binary_eq : forall v1 v2 r m,
      primitive_eq v1 v2 r ->
      (trm_binary prim_eq v1 v2) / m --->
      r / m
  | step_binary_add : forall n1 n2 m,
      (trm_binary prim_add n1 n2) / m --->
      (n1+n2) / m
  | step_binary_sub : forall n1 n2 m,
      (trm_binary prim_sub n1 n2) / m --->
      (n1-n2) / m
  | step_binary_mul : forall n1 n2 m,
      (trm_binary prim_mul n1 n2) / m --->
      (n1*n2) / m
  | step_binary_div_notzero : forall n1 n2 m,
      n2 <> 0 ->
      (trm_binary prim_div n1 n2) / m --->
      (Z.div n1 n2) / m
  | step_binary_div_zero : forall n1 n2 m,
      (trm_binary prim_div n1 0) / m --->
      (trm_error constr_div_by_zero) / m
  | step_lazy_binary_and_true : forall v1 t2 m,
      (trm_lazy_binary prim_and true t2) / m --->
      t2 / m
  | step_lazy_binary_and_false : forall v1 t2 m,
      (trm_lazy_binary prim_and false t2) / m --->
      false / m
  | step_lazy_binary_or_true : forall v1 t2 m,
      (trm_lazy_binary prim_or true t2) / m --->
      true / m
  | step_lazy_binary_or_false : forall v1 t2 m,
      (trm_lazy_binary prim_or false t2) / m --->
      t2 / m

  | step_app_mismatch : forall p oy t3 v2 m,
      mismatching v2 p ->
      (trm_app (val_abs oy p t3) v2) / m --->
      (trm_error constr_matching_failure) / m
  | step_app_match : forall i p oy t3 t4 t5 v2 m,
      matching i v2 p ->
      t4 = substs i t3 ->
      t5 = match oy with
         | None => t4
         | Some y => (subst y (val_abs oy p t3) t4) end ->
      (trm_app (val_abs None p t3) v2) / m --->
      t5 / m

  | step_seq : forall v1 t2 m,
      (trm_seq v1 t2) / m --->
      t2 / m
  | step_let_match : forall i p x v1 t2 m,
      matching i v1 p ->
      (trm_let p v1 t2) / m --->
      (substs i t2) / m
  | step_let_mismatch : forall p x v1 t2 m,
       mismatching v1 p ->
      (trm_let p v1 t2) / m --->
      (trm_error constr_matching_failure) / m

  | step_record : forall avs l m1 m2,
      fresh m1 l ->
      m2 = Heap.write m1 l (val_record avs) ->
      (trm_record (trms_lab_vals avs)) / m1 --->
      l / m2
  | step_get : forall l a v avs m,
      Heap.binds m l (val_record avs) ->
      LibListAssoc.Assoc a v avs ->
      (trm_get l a) / m --->
      v / m
  | step_set : forall l a v avs m1 m2,
      Heap.binds m1 l (val_record avs) ->
      m2 = Heap.write m1 l (val_record ((a,v)::avs)) ->
      (trm_set l a v) / m1 --->
      val_unit / m2

  | step_while : forall t1 t2 m,
      (trm_while t1 t2) / m --->
      (trm_if t1 (trm_seq t2 (trm_while t1 t2)) None) / m
  | step_if_true : forall t2 ot3 m,
      (trm_if true t2 ot3) / m --->
      t2 / m
  | step_if_false_none : forall t2 m,
      (trm_if false t2 None) / m --->
      val_unit / m
  | step_if_false_some : forall t2 t3 m,
      (trm_if false t2 (Some t3)) / m --->
      t3 / m
  | step_for_upto_leq : forall x n1 n2 t3 m,
      n1 <= n2 ->
      (trm_for x dir_upto n1 n2 t3) / m --->
      (trm_seq (trm_let x n1 t3) (trm_for x dir_upto (n1+1) n2 t3)) / m
  | step_for_upto_gt : forall x n1 n2 t3 m,
      n1 > n2 ->
      (trm_for x dir_upto n1 n2 t3) / m --->
      val_unit / m
  | step_for_downto_geq : forall x n1 n2 t3 m,
      n1 >= n2 ->
      (trm_for x dir_downto n1 n2 t3) / m --->
      (trm_seq (trm_let x n1 t3) (trm_for x dir_upto (n1-1) n2 t3)) / m
  | step_for_downto_lt : forall x n1 n2 t3 m,
      n1 < n2 ->
      (trm_for x dir_downto n1 n2 t3) / m --->
      val_unit / m

  | step_match_nil : forall v m,
      (trm_match v nil) / m --->
      (trm_error constr_matching_failure) / m
  | step_match_cons_mismatch : forall v p bs ot1 t2 m,
      mismatching v p ->
      (trm_match v ((branch_intro p ot1 t2)::bs)) / m --->
      (trm_match v bs) / m
  | step_match_cons_match_unguarded : forall v p bs t2 i m,
      matching i v p ->
      (trm_match v ((branch_intro p None t2)::bs)) / m --->
      (substs i t2) / m
  | step_match_cons_match_guarded : forall v p bs t1 t2 i m,
      matching i v p ->
      (trm_match v ((branch_intro p (Some t1) t2)::bs)) / m --->
      (trm_match_1 v bs (substs i t1) (substs i t2)) / m
  | step_match_1_true : forall v bs t2 m,
      (trm_match_1 v bs true t2) / m --->
      t2 / m
  | step_match_1_false : forall v bs t2 m,
      (trm_match_1 v bs false t2) / m --->
      (trm_match v bs) / m

  | step_try_val : forall v bs m,
      (trm_try v bs) / m ---> v / m
  | step_try_raise : forall v bs m,
      (trm_try (trm_raise v) bs) / m --->
      (trm_try_1 v bs) / m
  | step_try_1_nil : forall v m,
      (trm_try_1 v nil) / m --->
      (trm_raise v) / m
  | step_try_1_cons_mismatch : forall v p bs ot1 t2 m,
      mismatching v p ->
      (trm_try_1 v ((branch_intro p ot1 t2)::bs)) / m --->
      (trm_try_1 v bs) / m
  | step_try_1_cons_match_unguarded : forall v p bs t2 i m,
      matching i v p ->
      (trm_try_1 v ((branch_intro p None t2)::bs)) / m --->
      (substs i t2) / m
  | step_try_1_cons_match_guarded : forall v p bs t1 t2 i m,
      matching i v p ->
      (trm_try_1 v ((branch_intro p (Some t1) t2)::bs)) / m --->
      (trm_try_2 v bs (substs i t1) (substs i t2)) / m
  | step_try_2_true : forall v bs t2 m,
      (trm_try_2 v bs true t2) / m --->
      t2 / m
  | step_try_2_false : forall v bs t2 m,
      (trm_try_2 v bs false t2) / m --->
      (trm_try_1 v bs) / m

  | step_assert_true : forall m,
      (trm_assert true) / m --->
      val_unit / m
  | step_assert_false : forall m,
      (trm_assert false) / m --->
      (trm_error constr_assert_failure) / m

  | step_rand : forall m z,
      trm_rand / m --->
      (val_cst z) / m

where "t1 / m1 ---> t2 / m2" := (step (t1:trm,m1) (t2:trm,m2)).




(************************************************************)
(* ** Complete reduction sequences *)

(** Complete evaluation  [TODO]

Definition sredstar t t' := (rtclosure step) t t'.

Definition sredplus t t' := (tclosure step) t t'.

Definition sredval t v := sredstar t v.

Definition sredexn t v := sredstar t (trm_raise v).

Definition sdiverge t := (infclosure step) t.

*)