(************************************************************
* Core Caml                                                 *
* Big-step semantics                                        *
*************************************************************)

Set Implicit Arguments.
Require Export CoreCaml_Syntax.

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


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Auxiliary definitions *)

(** Grammar of behaviors *)

Inductive beh :=
  | beh_ret : val -> beh
  | beh_exn : val -> beh.

Coercion beh_ret : val >-> beh.

Definition beh_error k := beh_exn (val_constr k nil).


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
(* ** Evaluation of primitive functions *)

Inductive unary_pure : prim -> val -> beh -> Prop :=
  | unrary_pure_not : forall r,
      unary_pure prim_neg r (neg r)
  | unrary_pure_neg : forall n,
      unary_pure prim_not n (-n).

Inductive unary_red : mem -> prim -> val -> mem -> beh -> Prop :=
  | unary_red_pure : forall m f v (b:beh),
      unary_pure f v b ->
      unary_red m f v m b.

Inductive binary_pure : prim -> val -> val -> beh -> Prop :=
  | binary_pure_eq : forall v1 v2 r,
      primitive_eq v1 v2 r ->
      binary_pure prim_eq v1 v2 r
  | binary_pure_add : forall n1 n2,
      binary_pure prim_add n1 n2 (n1+n2)
  | binary_pure_sub : forall n1 n2,
      binary_pure prim_sub n1 n2 (n1-n2)
  | binary_pure_mul : forall n1 n2,
      binary_pure prim_mul n1 n2 (n1*n2)
  | binary_pure_div_notzero : forall n1 n2,
      n2 <> 0 ->
      binary_pure prim_div n1 n2 (Z.div n1 n2)
  | binary_pure_div_zero : forall n1 n2,
      binary_pure prim_div n1 0 (beh_exn (val_exn constr_div_by_zero)).

Inductive binary_red : mem -> prim -> val -> val -> mem -> beh -> Prop :=
  | binary_red_pure : forall m f v1 v2 (b:beh),
      binary_pure f v1 v2 b ->
      binary_red m f v1 v2 m b.


(************************************************************)
(* ** Evaluation judgment *)

Inductive bigred : mem -> trm -> mem -> beh -> Prop :=

  | bigred_cst : forall c m,
      bigred m (trm_cst c) m c
  | bigred_abs : forall oy p t m,
      bigred m (trm_abs oy p t) m (val_abs oy p t)
  | bigred_constr : forall k ts m1 m2 vs,
      bigred_list m1 ts m2 vs ->
      bigred m1 (trm_constr k ts) m2 (val_constr k vs)
  | bigred_constr_exn : forall k ts m1 m2 v,
      bigred_list_exn m1 ts m2 v ->
      bigred m1 (trm_constr k ts) m2 (beh_exn v)
  | bigred_tuple : forall ts m1 m2 vs,
      bigred_list m1 ts m2 vs ->
      bigred m1 (trm_tuple ts) m2 (val_tuple vs)
  | bigred_tuple_exn : forall ts m1 m2 v,
      bigred_list_exn m1 ts m2 v ->
      bigred m1 (trm_tuple ts) m2 (beh_exn v)
  | bigred_record : forall ats m1 m2 m3 l avs vs ts As,
      (As,ts) = LibList.split ats ->
      bigred_list m1 ts m2 vs ->
      avs = LibList.combine As vs ->
      fresh m2 l ->
      m3 = Heap.write m2 l (val_record avs) ->
      bigred m1 (trm_record ats) m3 l
  | bigred_record_exn : forall ats m1 m2 v,
      bigred_list_exn m1 (LibList.map snd ats) m2 v ->
      bigred m1 (trm_record ats) m2 (beh_exn v)

  | bigred_unary : forall f t1 v1 m1 m2 m3 B,
      bigred m1 t1 m2 v1 ->
      unary_red m2 f v1 m3 B ->
      bigred m1 (trm_unary f t1) m2 B
  | bigred_unary_exn : forall f t1 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_unary f t1) m2 (beh_exn v)
  | bigred_binary : forall f t1 t2 v1 v2 m1 m2 m3 m4 B,
      bigred m1 t1 m2 v1 ->
      bigred m2 t2 m3 v2 ->
      binary_red m3 f v1 v2 m4 B ->
      bigred m1 (trm_binary f t1 t2) m4 B
  | bigred_binary_exn_1 : forall f t1 t2 v m1 m2,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_binary f t1 t2) m2 (beh_exn v)
  | bigred_binary_exn_2 : forall f t1 t2 v1 v m1 m2 m3,
      bigred m1 t1 m2 v1 ->
      bigred m2 t2 m3 (beh_exn v) ->
      bigred m1 (trm_binary f t1 t2) m3 (beh_exn v)

  | bigred_lazy_binary_exn_1 : forall f t1 t2 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_lazy_binary f t1 t2) m2 (beh_exn v)
  | bigred_lazy_binary_and_true : forall t1 t2 B m1 m2 m3,
      bigred m1 t1 m2 true ->
      bigred m2 t2 m3 B ->
      bigred m1 (trm_lazy_binary prim_and t1 t2) m3 B
  | bigred_lazy_binary_and_false : forall t1 t2 m1 m2,
      bigred m1 t1 m2 false ->
      bigred m1 (trm_lazy_binary prim_and t1 t2) m2 false
  | bigred_lazy_binary_or_true : forall t1 t2 m1 m2,
      bigred m1 t1 m2 true ->
      bigred m1 (trm_lazy_binary prim_or t1 t2) m2 true
  | bigred_lazy_binary_or_false : forall t1 t2 B m1 m2 m3,
      bigred m1 t1 m2 false ->
      bigred m2 t2 m3 B ->
      bigred m1 (trm_lazy_binary prim_and t1 t2) m3 B

  | bigred_app_match : forall t1 t2 t3 t4 t5 m1 m2 m3 m4 v2 i p oy B,
      bigred m1 t1 m2 (val_abs oy p t3) ->
      bigred m2 t2 m3 v2 ->
      matching i v2 p ->
      t4 = substs i t3 ->
      t5 = match oy with
         | None => t4
         | Some y => (subst y (val_abs oy p t3) t4) end ->
      bigred m3 t5 m4 B ->
      bigred m1 (trm_app t1 t2) m4 B
  | bigred_app_mismatch : forall t1 t2 t3 m1 m2 m3 v2 p oy,
      bigred m1 t1 m2 (val_abs oy p t3) ->
      bigred m2 t2 m3 v2 ->
      mismatching v2 p ->
      bigred m1 (trm_app t1 t2) m3 (beh_error constr_matching_failure)
  | bigred_app_exn_1 : forall t1 t2 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_app t1 t2) m2 (beh_exn v)
  | bigred_app_exn_2 : forall t1 t2 t3 oy p m1 m2 m3 v,
      bigred m1 t1 m2 (val_abs oy p t3) ->
      bigred m2 t2 m3 (beh_exn v) ->
      bigred m1 (trm_app t1 t2) m3 (beh_exn v)

  | bigred_seq : forall t1 t2 m1 m2 m3 v1 B,
      bigred m1 t1 m2 v1 ->
      bigred m2 t2 m3 B ->
      bigred m1 (trm_seq t1 t2) m3 B
  | bigred_seq_exn_1 : forall t1 t2 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_seq t1 t2) m2 (beh_exn v)
  | bigred_let_match : forall p t1 t2 m1 m2 m3 v1 B i,
      bigred m1 t1 m2 v1 ->
      matching i v1 p ->
      bigred m2 (substs i t2) m3 B ->
      bigred m1 (trm_let p t1 t2) m3 B
  | bigred_let_mismatch : forall p t1 t2 m1 m2 m3 v1,
      bigred m1 t1 m2 v1 ->
      mismatching v1 p ->
      bigred m1 (trm_let p t1 t2) m3 (beh_error constr_matching_failure)
  | bigred_let_exn : forall p t1 t2 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_let p t1 t2) m2 (beh_exn v)

  | bigred_get : forall t1 a m1 m2 l v avs,
      bigred m1 t1 m2 l ->
      Heap.binds m2 l (val_record avs) ->
      LibListAssoc.Assoc a v avs ->
      bigred m1 (trm_get t1 a) m2 v
  | bigred_get_exn_1 : forall t1 a m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_get t1 a) m2 (beh_exn v)
  | bigred_set : forall a t1 t2 m1 m2 m3 m4 l v avs,
      bigred m1 t1 m2 l ->
      bigred m2 t2 m3 v ->
      Heap.binds m3 l (val_record avs) ->
      m4 = Heap.write m3 l (val_record ((a,v)::avs)) ->
      bigred m1 (trm_set t1 a t2) m4 val_unit
  | bigred_set_exn_1 : forall a t1 t2 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_set t1 a t2) m2 (beh_exn v)
  | bigred_set_exn_2 : forall a t1 t2 m1 m2 m3 l v,
      bigred m1 t1 m2 l ->
      bigred m2 t2 m3 (beh_exn v) ->
      bigred m1 (trm_set t1 a t2) m3 (beh_exn v)

  | bigred_if_true : forall t1 t2 ot3 m1 m2 m3 B,
      bigred m1 t1 m2 true ->
      bigred m2 t2 m3 B ->
      bigred m1 (trm_if t1 t2 ot3) m3 B
  | bigred_if_false_none : forall t1 t2 m1 m2,
      bigred m1 t1 m2 false ->
      bigred m1 (trm_if t1 t2 None) m2 val_unit
  | bigred_if_false_some : forall t1 t2 t3 m1 m2 m3 B,
      bigred m1 t1 m2 false ->
      bigred m2 t2 m3 B ->
      bigred m1 (trm_if t1 t2 (Some t3)) m3 B
  | bigred_if_exn_1 : forall t1 t2 ot3 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_if t1 t2 ot3) m2 (beh_exn v)
  | bigred_while : forall t1 t2 m1 m2 B,
      bigred m1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) None) m2 B ->
      bigred m1 (trm_while t1 t2) m2 B

  | bigred_for_upto_leq : forall x t1 t2 t3 m1 m2 m3 m4 n1 n2 B,
      bigred m1 t1 m2 n1 ->
      bigred m2 t2 m3 n2 ->
      n1 <= n2 ->
      bigred m3 (trm_seq (trm_let x n1 t3) (trm_for x dir_upto (n1+1) n2 t3)) m4 B ->
      bigred m1 (trm_for x dir_upto t1 t2 t3) m4 B
  | bigred_for_upto_gt : forall x t1 t2 t3 m1 m2 m3 n1 n2,
      bigred m1 t1 m2 n1 ->
      bigred m2 t2 m3 n2 ->
      n1 > n2 ->
      bigred m1 (trm_for x dir_upto t1 t2 t3) m3 val_unit
  | bigred_for_downto_geq : forall x t1 t2 t3 m1 m2 m3 m4 n1 n2 B,
      bigred m1 t1 m2 n1 ->
      bigred m2 t2 m3 n2 ->
      n1 >= n2 ->
      bigred m3 (trm_seq (trm_let x n1 t3) (trm_for x dir_downto (n1-1) n2 t3)) m4 B ->
      bigred m1 (trm_for x dir_downto t1 t2 t3) m4 B
  | bigred_for_downto_lt : forall x t1 t2 t3 m1 m2 m3 n1 n2,
      bigred m1 t1 m2 n1 ->
      bigred m2 t2 m3 n2 ->
      n1 < n2 ->
      bigred m1 (trm_for x dir_downto t1 t2 t3) m3 val_unit
  | bigred_for_exn_1 : forall x t1 t2 t3 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_for x dir_upto t1 t2 t3) m2 (beh_exn v)
  | bigred_for_exn_2 : forall x t1 t2 t3 m1 m2 m3 v1 v,
      bigred m1 t1 m2 v1 ->
      bigred m2 t2 m3 (beh_exn v) ->
      bigred m1 (trm_for x dir_upto t1 t2 t3) m3 (beh_exn v)

  | bigred_match : forall t1 bs m1 v1 m2 m3 b3 B,
      bigred m1 t1 m2 v1 ->
      bigred_branches (beh_error constr_matching_failure) v1 m2 bs m3 B ->
      bigred m1 (trm_match t1 bs) m3 B
  | bigred_match_exn_1 : forall t1 bs m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_match t1 bs) m2 (beh_exn v)
  | bigred_try_val : forall t1 bs m1 m2 v1,
      bigred m1 t1 m2 v1 ->
      bigred m1 (trm_match t1 bs) m2 v1
  | bigred_try_exn : forall t1 bs m1 v m2 m3 b3 B,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred_branches (beh_exn v) v m2 bs m3 B ->
      bigred m1 (trm_match t1 bs) m3 B

  | bigred_assert_true : forall t1 m1 m2,
      bigred m1 t1 m2 true ->
      bigred m1 (trm_assert t1) m2 val_unit
  | bigred_assert_false : forall t1 m1 m2,
      bigred m1 t1 m2 false ->
      bigred m1 (trm_assert t1) m2 (beh_error constr_assert_failure)
  | bigred_assert_exn_1 : forall t1 m1 m2 v,
      bigred m1 t1 m2 (beh_exn v) ->
      bigred m1 (trm_assert t1) m2 (beh_exn v)

  | bigred_rand : forall m z,
      bigred m trm_rand m (val_cst z)

with bigred_list : mem -> trms -> mem -> vals -> Prop :=
  | bigred_list_nil : forall m,
      bigred_list m nil m nil
  | bigred_list_cons : forall ts t vs v m1 m2 m3,
      bigred m1 t m2 v ->
      bigred_list m2 ts m3 vs ->
      bigred_list m1 (t::ts) m3 (v::vs)

with bigred_list_exn : mem -> trms -> mem -> val -> Prop :=
  | bigred_list_exn_here : forall m1 m2 t ts ve,
      bigred m1 t m2 (beh_exn ve) ->
      bigred_list_exn m1 (t::ts) m2 ve
  | bigred_list_exn_cons : forall ts t v ve m1 m2 m3,
      bigred m1 t m2 v ->
      bigred_list_exn m2 ts m3 ve ->
      bigred_list_exn m1 (t::ts) m3 ve

with bigred_branches : beh -> val -> mem -> branches -> mem -> beh -> Prop :=
  | bigred_branches_nil : forall m v BE,
      bigred_branches BE v m nil m BE
  | bigred_branches_cons_mismatch : forall m1 m2 v BE B bs p ot1 t2,
      mismatching v p ->
      bigred_branches BE v m1 bs m2 B ->
      bigred_branches BE v m1 ((branch_intro p ot1 t2)::bs) m2 B
  | bigred_branches_cons_match_unguarded : forall i m1 m2 v BE B bs p t2,
      matching i v p ->
      bigred m1 (substs i t2) m2 B ->
      bigred_branches BE v m1 ((branch_intro p None t2)::bs) m2 B
  | bigred_branches_cons_match_guarded_true : forall i m1 m2 m3 v BE B bs p t1 t2,
      matching i v p ->
      bigred m1 (substs i t1) m2 true ->
      bigred m2 (substs i t2) m3 B ->
      bigred_branches BE v m1 ((branch_intro p (Some t1) t2)::bs) m2 B
  | bigred_branches_cons_match_guarded_false : forall i m1 m2 m3 v BE B bs p t1 t2,
      matching i v p ->
      bigred m1 (substs i t1) m2 false ->
      bigred_branches BE v m2 bs m3 B ->
      bigred_branches BE v m1 ((branch_intro p (Some t1) t2)::bs) m3 B
  | bigred_branches_cons_match_guarded_exn : forall i m1 m2 v ve BE bs p t1 t2,
      matching i v p ->
      bigred m1 (substs i t1) m2 (beh_exn ve) ->
      bigred_branches BE v m1 ((branch_intro p (Some t1) t2)::bs) m2 (beh_exn ve).


(************************************************************)
(* ** Divergence judgment *)

Inductive bigdiv : mem -> trm -> Prop :=

  | bigdiv_constr : forall k ts m,
      bigdiv_list m ts ->
      bigdiv m (trm_constr k ts)
  | bigdiv_tuple : forall ts m,
      bigdiv_list m ts ->
      bigdiv m (trm_tuple ts)
  | bigdiv_record : forall ats m,
      bigdiv_list m (LibList.map snd ats) ->
      bigdiv m (trm_record ats)

  | bigdiv_unary : forall m f t1,
      bigdiv m t1 ->
      bigdiv m (trm_unary f t1)
  | bigdiv_binary_1 : forall f t1 t2 m,
      bigdiv m t1 ->
      bigdiv m (trm_binary f t1 t2)
  | bigred_binary_2 : forall f t1 t2 v1 m1 m2,
      bigred m1 t1 m2 v1 ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_binary f t1 t2)

  | bigdiv_lazy_binary_1 : forall f t1 t2 m,
      bigdiv m t1 ->
      bigdiv m (trm_lazy_binary f t1 t2)
  | bigdiv_lazy_binary_and_true : forall t1 t2 m1 m2,
      bigred m1 t1 m2 true ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_lazy_binary prim_and t1 t2)
  | bigdiv_lazy_binary_or_false : forall t1 t2 m1 m2,
      bigred m1 t1 m2 false ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_lazy_binary prim_and t1 t2)

  | bigdiv_app_match : forall t1 t2 t3 t4 t5 m1 m2 m3 v2 i p oy,
      bigred m1 t1 m2 (val_abs oy p t3) ->
      bigred m2 t2 m3 v2 ->
      matching i v2 p ->
      t4 = substs i t3 ->
      t5 = match oy with
         | None => t4
         | Some y => (subst y (val_abs oy p t3) t4) end ->
      bigdiv m3 t5 ->
      bigdiv m1 (trm_app t1 t2)
  | bigdiv_app_1 : forall t1 t2 m1,
      bigdiv m1 t1 ->
      bigdiv m1 (trm_app t1 t2)
  | bigdiv_app_2 : forall t1 t2 v1 m1 m2,
      bigred m1 t1 m2 v1 ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_app t1 t2)

  | bigdiv_seq : forall t1 t2 m1 m2 v1,
      bigred m1 t1 m2 v1 ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_seq t1 t2)
  | bigdiv_seq_1 : forall t1 t2 m,
      bigdiv m t1 ->
      bigdiv m (trm_seq t1 t2)
  | bigdiv_let_match : forall p t1 t2 m1 m2 v1 i,
      bigred m1 t1 m2 v1 ->
      matching i v1 p ->
      bigdiv m2 (substs i t2) ->
      bigdiv m1 (trm_let p t1 t2)
  | bigdiv_let_1 : forall p t1 t2 m1,
      bigdiv m1 t1 ->
      bigdiv m1 (trm_let p t1 t2)

  | bigdiv_get : forall t1 a m1,
      bigdiv m1 t1 ->
      bigdiv m1 (trm_get t1 a)
  | bigdiv_set_1 : forall a t1 t2 m1,
      bigdiv m1 t1 ->
      bigdiv m1 (trm_set t1 a t2)
  | bigdiv_set_exn_2 : forall a t1 t2 m1 m2 v1,
      bigred m1 t1 m2 v1 ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_set t1 a t2)

  | bigdiv_if_true : forall t1 t2 ot3 m1 m2,
      bigred m1 t1 m2 true ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_if t1 t2 ot3)
  | bigdiv_if_false_some : forall t1 t2 t3 m1 m2,
      bigred m1 t1 m2 false ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_if t1 t2 (Some t3))
  | bigdiv_if_1 : forall t1 t2 ot3 m1,
      bigdiv m1 t1->
      bigdiv m1 (trm_if t1 t2 ot3)
  | bigdiv_while : forall t1 t2 m1,
      bigdiv m1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) None) ->
      bigdiv m1 (trm_while t1 t2)
  | bigdiv_for_upto_leq : forall x t1 t2 t3 m1 m2 m3 n1 n2,
      bigred m1 t1 m2 n1 ->
      bigred m2 t2 m3 n2 ->
      n1 <= n2 ->
      bigdiv m3 (trm_seq (trm_let x n1 t3) (trm_for x dir_upto (n1+1) n2 t3)) ->
      bigdiv m1 (trm_for x dir_upto t1 t2 t3)
  | bigdiv_for_downto_geq : forall x t1 t2 t3 m1 m2 m3 n1 n2,
      bigred m1 t1 m2 n1 ->
      bigred m2 t2 m3 n2 ->
      n1 >= n2 ->
      bigdiv m3 (trm_seq (trm_let x n1 t3) (trm_for x dir_downto (n1-1) n2 t3)) ->
      bigdiv m1 (trm_for x dir_downto t1 t2 t3)
  | bigdiv_for_1 : forall x t1 t2 t3 m1,
      bigdiv m1 t1 ->
      bigdiv m1 (trm_for x dir_upto t1 t2 t3)
  | bigdiv_for_2 : forall x t1 t2 t3 m1 m2 m3 v1 v,
      bigred m1 t1 m2 v1 ->
      bigdiv m2 t2 ->
      bigdiv m1 (trm_for x dir_upto t1 t2 t3)

  | bigdiv_match : forall t1 bs m1 v1 m2,
      bigred m1 t1 m2 v1 ->
      bigdiv_branches v1 m2 bs ->
      bigdiv m1 (trm_match t1 bs)
  | bigdiv_match_1 : forall t1 bs m,
      bigdiv m t1 ->
      bigdiv m (trm_match t1 bs)
  | bigdiv_try : forall t1 bs m1 v m2,
      bigred m1 t1 m2 (beh_exn v) ->
      bigdiv_branches v m2 bs ->
      bigdiv m2 (trm_match t1 bs)
  | bigdiv_try_1 : forall t1 bs m,
      bigdiv m t1 ->
      bigdiv m (trm_match t1 bs)

  | bigdiv_assert_exn_1 : forall t1 m1,
      bigdiv m1 t1 ->
      bigdiv m1 (trm_assert t1)

with bigdiv_list : mem -> trms -> Prop :=
  | bigdiv_list_here : forall m t ts,
      bigdiv m t ->
      bigdiv_list m (t::ts)
  | bigdiv_list_cons : forall ts t v m1 m2,
      bigred m1 t m2 v ->
      bigdiv_list m2 ts ->
      bigdiv_list m1 (t::ts)

with bigdiv_branches : val -> mem -> branches -> Prop :=
  | bigdiv_branches_cons_mismatch : forall m v bs p ot1 t2,
      mismatching v p ->
      bigdiv_branches v m bs ->
      bigdiv_branches v m ((branch_intro p ot1 t2)::bs)
  | bigdiv_branches_cons_match_unguarded : forall i m v bs p t2,
      matching i v p ->
      bigdiv m (substs i t2) ->
      bigdiv_branches v m ((branch_intro p None t2)::bs)
  | bigdiv_branches_cons_match_guarded_true : forall i m1 m2 v bs p t1 t2,
      matching i v p ->
      bigred m1 (substs i t1) m2 true ->
      bigdiv m2 (substs i t2) ->
      bigdiv_branches v m1 ((branch_intro p (Some t1) t2)::bs)
  | bigdiv_branches_cons_match_guarded_false : forall i m1 m2 v bs p t1 t2,
      matching i v p ->
      bigred m1 (substs i t1) m2 false ->
      bigdiv_branches v m2 bs ->
      bigdiv_branches v m1 ((branch_intro p (Some t1) t2)::bs)
  | bigdiv_branches_cons_match_guarded_here : forall i m v bs p t1 t2,
      matching i v p ->
      bigdiv m (substs i t1) ->
      bigdiv_branches v m ((branch_intro p (Some t1) t2)::bs).
