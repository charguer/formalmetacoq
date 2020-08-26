(************************************************************
* Core Caml                                                 *
* Pretty-big-step semantics                                 *
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
Implicit Types a : lab.
Implicit Types l : loc.
Implicit Types i : inst.
Implicit Types n : int.
Implicit Types z : bool.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Auxiliary definitions *)

(** Grammar of behaviors *)

Inductive beh :=
  | beh_ret : val -> beh
  | beh_exn : val -> beh.

Coercion beh_ret : val >-> beh.

(** Grammar of outcomes *)

Inductive out :=
  | out_ter : mem -> beh -> out
  | out_div : out.

Implicit Types o : out.

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_record_1 : labvals -> ext
  | ext_unary_1 : prim -> out -> ext
  | ext_binary_1 : prim -> out -> trm -> ext
  | ext_binary_2 : prim -> val -> out -> ext
  | ext_lazy_binary_1 : prim -> out -> trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext
  | ext_seq_1 : out -> trm -> ext
  | ext_let_1 : pat -> out -> trm -> ext
  | ext_get_1 : out -> lab -> ext
  | ext_set_1 : out -> lab -> trm -> ext
  | ext_set_2 : val -> lab -> out -> ext
  | ext_if_1 : out -> trm -> option trm -> ext
  | ext_for_1 : var -> dir -> out -> trm -> trm -> ext
  | ext_for_2 : var -> dir -> int -> out -> trm -> ext
  | ext_for_3 : var -> dir -> int -> int -> trm -> ext
  | ext_match_1 : out -> branches -> ext
  | ext_try_1 : out -> branches -> ext
  | ext_assert_1 : out -> ext
  | ext_build_1 : (vals -> val) -> vals -> ext
  | ext_list_1 : trms -> vals -> (vals -> ext) -> ext
  | ext_list_2 : out -> trms -> vals -> (vals -> ext) -> ext
  | ext_lablist_1 : labtrms -> labvals -> (labvals -> ext) -> ext
  | ext_lablist_2 : out -> lab -> labtrms -> labvals -> (labvals -> ext) -> ext
  | ext_branches_1 : beh -> val -> branches -> ext
  | ext_branches_2 : beh -> val -> branches -> out -> trm -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

(** Outcomes in intermediate forms *)

Definition out_of_ext e :=
  match e with
  | ext_unary_1 _ o => Some o
  | ext_binary_1 _ o _ => Some o
  | ext_binary_2 _ _ o => Some o
  | ext_lazy_binary_1 _ o _ => Some o
  | ext_app_1 o _ => Some o
  | ext_app_2 _ o  => Some o
  | ext_seq_1 o _  => Some o
  | ext_let_1 _ o _ => Some o
  | ext_get_1 o _ => Some o
  | ext_set_1 o _ _ => Some o
  | ext_set_2 _ _ o => Some o
  | ext_if_1 o _ _ => Some o
  | ext_for_1 _ _ o _ _ => Some o
  | ext_for_2 _ _ _ o _ => Some o
  | ext_match_1 o _  => Some o
  | ext_try_1 o _ => Some o
  | ext_assert_1 o => Some o
  | ext_list_2 o _ _ _ => Some o
  | ext_lablist_2 o _ _ _ _ => Some o
  | ext_branches_2 _ _ _ o _ => Some o
  | _ => None
  end.
(*
  | ext_record_1 _ => None
  | ext_list_1 _ _ _ _ => None
  | ext_lablist_1 _ _ _ _ => None
  | ext_for_3 _ _ _ _ _ => None
  ext_branches_1
*)

 (** Abort behavior *)

Inductive abort : out -> Prop :=
  | abort_exn : forall m v, abort (out_ter m (beh_exn v))
  | abort_div : abort out_div.

Inductive intercept : ext -> Prop :=
  | intercept_try_1 : forall m v bs,
      intercept (ext_try_1 (out_ter m (beh_exn v)) bs).


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
  | unary_pure_neg : forall z,
      unary_pure prim_neg z (neg z)
  | unary_pure_not : forall n,
      unary_pure prim_not n (-n).

Inductive unary_red : mem -> prim -> val -> out -> Prop :=
  | unary_red_pure : forall m f v (b:beh),
      unary_pure f v b ->
      unary_red m f v (out_ter m b)
  | unary_red_raise : forall m v,
      unary_red m prim_raise v (out_ter m (beh_exn v)).

Inductive binary_pure : prim -> val -> val -> beh -> Prop :=
  | binary_pure_eq : forall v1 v2 z,
      primitive_eq v1 v2 z ->
      binary_pure prim_eq v1 v2 z
  | binary_pure_add : forall n1 n2,
      binary_pure prim_add n1 n2 (n1+n2)
  | binary_pure_sub : forall n1 n2,
      binary_pure prim_sub n1 n2 (n1-n2)
  | binary_pure_mul : forall n1 n2,
      binary_pure prim_mul n1 n2 (n1*n2)
  | binary_pure_div_notzero : forall n1 n2,
      n2 <> 0 ->
      binary_pure prim_div n1 n2 (Z.div n1 n2)
  | binary_pure_div_zero : forall n1,
      binary_pure prim_div n1 0 (beh_exn (val_exn constr_div_by_zero)).

Inductive binary_red : mem -> prim -> val -> val -> out -> Prop :=
  | binary_red_pure : forall m f v1 v2 (b:beh),
      binary_pure f v1 v2 b ->
      binary_red m f v1 v2 (out_ter m b).


(************************************************************)
(* ** Evaluation judgment *)

Inductive red : mem -> ext -> out -> Prop :=
  | red_abort : forall m e o,
      out_of_ext e = Some o ->
      ~ intercept e ->
      abort o ->
      red m e o

  | red_cst : forall c m,
      red m (trm_cst c) (out_ter m c)
  | red_abs : forall oy p t m,
      red m (trm_abs oy p t) (out_ter m (val_abs oy p t))
  | red_constr : forall k ts m o,
      red m (ext_list_1 ts nil (ext_build_1 (val_constr k))) o ->
      red m (trm_constr k ts) o
  | red_tuple : forall ts m o,
      red m (ext_list_1 ts nil (ext_build_1 val_tuple)) o ->
      red m (trm_tuple ts) o
  | red_record : forall ats As ts m o,
      (As,ts) = LibList.split ats ->
      red m (ext_list_1 ts nil
              (fun vs => ext_record_1 (LibList.combine As vs))) o ->
      red m (trm_record ats) o
  | red_unary : forall o1 f t1 m o,
      red m t1 o1 ->
      red m (ext_unary_1 f o1) o ->
      red m (trm_unary f t1) o
  | red_unary_1 : forall f v m m0 o,
      unary_red m f v o ->
      red m0 (ext_unary_1 f (out_ter m v)) o
  | red_binary : forall o1 f t1 t2 m o,
      red m t1 o1 ->
      red m (ext_binary_1 f o1 t2) o ->
      red m (trm_binary f t1 t2) o
  | red_binary_1 : forall f v1 t2 o2 m m0 o,
      red m t2 o2 ->
      red m (ext_binary_2 f v1 o2) o ->
      red m0 (ext_binary_1 f (out_ter m v1) t2) o
  | red_binary_2 : forall f v1 v2 m m0 o,
      binary_red m f v1 v2 o ->
      red m0 (ext_binary_2 f v1 (out_ter m v2)) o
  | red_lazy_binary : forall o1 f t1 t2 m o,
      red m t1 o1 ->
      red m (ext_lazy_binary_1 f o1 t2) o ->
      red m (trm_lazy_binary f t1 t2) o
  | red_lazy_binary_1_and_true : forall t2 m m0 o,
      red m t2 o ->
      red m0 (ext_binary_1 prim_and (out_ter m true) t2) o
  | red_lazy_binary_1_and_false : forall t2 m m0,
      red m0 (ext_binary_1 prim_and (out_ter m false) t2) (out_ter m false)
  | red_lazy_binary_1_or_true : forall t2 m m0,
      red m0 (ext_binary_1 prim_or (out_ter m true) t2) (out_ter m true)
  | red_lazy_binary_1_or_false : forall t2 m m0 o,
      red m t2 o ->
      red m0 (ext_binary_1 prim_or (out_ter m false) t2) o

  | red_app : forall t1 t2 m o1 o,
      red m t1 o1 ->
      red m (ext_app_1 o1 t2) o ->
      red m (trm_app t1 t2) o
  | red_app_1 : forall v1 t2 m m0 o2 o,
      red m t2 o2 ->
      red m (ext_app_2 v1 o2) o ->
      red m0 (ext_app_1 (out_ter m v1) t2) o
  | red_app_2_mismatch : forall oy p t3 v2 m m0,
      mismatching v2 p ->
      red m0 (ext_app_2 (val_abs oy p t3) (out_ter m v2))
             (out_ter m (beh_exn constr_matching_failure))
  | red_app_2_match : forall oy p i t4 t5 t3 v2 m m0 o,
      matching i v2 p ->
      t4 = substs i t3 ->
      t5 = match oy with
         | None => t4
         | Some y => (subst y (val_abs oy p t3) t4) end ->
      red m t5 o ->
      red m0 (ext_app_2 (val_abs oy p t3) (out_ter m v2)) o

  | red_seq : forall t1 t2 m o1 o,
      red m t1 o1 ->
      red m (ext_seq_1 o1 t2) o ->
      red m (trm_seq t1 t2) o
  | red_seq_1 : forall v1 t2 m m0 o,
      red m t2 o ->
      red m0 (ext_seq_1 (out_ter m v1) t2) o
  | red_let : forall p t1 t2 m o1 o,
      red m t1 o1 ->
      red m (ext_let_1 p o1 t2) o ->
      red m (trm_let p t1 t2) o
  | red_let_1_match : forall i p v1 t2 m m0 o,
      matching i v1 p ->
      red m (substs i t2) o ->
      red m0 (ext_let_1 p (out_ter m v1) t2) o
  | red_let_1_mismatch : forall p v1 t2 m m0,
      mismatching v1 p ->
      red m0 (ext_let_1 p (out_ter m v1) t2)
             (out_ter m (beh_exn constr_matching_failure))

  | red_record_1 : forall avs m1 m2 l,
      fresh m1 l ->
      m2 = Heap.write m1 l (val_record avs) ->
      red m1 (ext_record_1 avs)
             (out_ter m2 l)
  | red_get : forall t1 a m o1 o,
      red m t1 o1 ->
      red m (ext_get_1 o1 a) o ->
      red m (trm_get t1 a) o
  | red_get_1 : forall avs l a m v m0,
      Heap.binds m l (val_record avs) ->
      LibListAssoc.Assoc a v avs ->
      red m0 (ext_get_1 (out_ter m l) a)
             (out_ter m v)
  | red_set : forall o1 a t1 t2 m o,
      red m t1 o1 ->
      red m (ext_set_1 o1 a t2) o ->
      red m (trm_set t1 a t2) o
  | red_set_1 : forall v1 t2 a o2 f m m0 o,
      red m t2 o2 ->
      red m (ext_set_2 v1 a o2) o ->
      red m0 (ext_set_1 (out_ter m v1) a t2) o
  | red_set_2 : forall l v avs a m1 m2 m0 o,
      Heap.binds m1 l (val_record avs) ->
      m2 = Heap.write m1 l (val_record ((a,v)::avs)) ->
      red m0 (ext_set_2 l a (out_ter m1 v))
             (out_ter m2 val_unit)

  | red_if : forall t1 t2 ot3 m o1 o,
      red m t1 o1 ->
      red m (ext_if_1 o1 t2 ot3) o ->
      red m (trm_if t1 t2 ot3) o
  | red_if_1_true : forall t2 ot3 m m0 o,
      red m t2 o ->
      red m0 (ext_if_1 (out_ter m true) t2 ot3) o
  | red_if_1_false_none : forall t2 m m0,
      red m0 (ext_if_1 (out_ter m false) t2 None)
             (out_ter m val_unit)
  | red_if_1_false_some : forall t2 t3 m m0 o,
      red m t3 o ->
      red m0 (ext_if_1 (out_ter m false) t2 (Some t3)) o

    (* TODO: change *)
  | red_while : forall t1 t2 m o,
      red m (trm_if t1 (trm_seq t2 (trm_while t1 t2)) None) o ->
      red m (trm_while t1 t2) o
  | red_for : forall x d t1 t2 t3 m m0 o1 o,
      red m t1 o1 ->
      red m (ext_for_1 x d o1 t2 t3) o ->
      red m (trm_for x d t1 t2 t3) o
  | red_for_1 : forall x d n1 t2 t3 m m0 o2 o,
      red m t2 o2 ->
      red m (ext_for_2 x d n1 o2 t3) o ->
      red m0 (ext_for_1 x d (out_ter m n1) t2 t3) o
  | red_for_2 : forall x d n1 n2 t3 m m0 o,
      red m (ext_for_3 x d n1 n2 t3) o ->
      red m0 (ext_for_2 x d n1 (out_ter m n2) t3) o
  | red_for_3_upto_leq : forall x n1 n2 t3 m o,
      n1 <= n2 ->
      red m (trm_seq (trm_let x n1 t3) (trm_for x dir_upto (n1+1) n2 t3)) o ->
      red m (ext_for_3 x dir_upto n1 n2 t3) o
  | red_for_3_upto_gt : forall x n1 n2 t3 m o,
      n1 > n2 ->
      red m (ext_for_3 x dir_upto n1 n2 t3)
            (out_ter m val_unit)
  | red_for_3_upto_geq : forall x n1 n2 t3 m o,
      n1 >= n2 ->
      red m (trm_seq (trm_let x (trm_cst n1) t3) (trm_for x dir_upto (n1-1) n2 t3)) o ->
      red m (ext_for_3 x dir_downto n1 n2 t3) o
  | red_for_3_upto_lt : forall x n1 n2 t3 m o,
      n1 < n2 ->
      red m (ext_for_3 x dir_downto n1 n2 t3)
            (out_ter m val_unit)

  | red_match : forall t1 bs m o1 o,
      red m t1 o1 ->
      red m (ext_match_1 o1 bs) o ->
      red m (trm_match t1 bs) o
  | red_match_1 : forall v bs m m0 o,
      red m (ext_branches_1 (beh_exn constr_matching_failure) v bs) o ->
      red m0 (ext_match_1 (out_ter m v) bs) o
  | red_try : forall t1 bs m o1 o,
      red m t1 o1 ->
      red m (ext_try_1 o1 bs) o ->
      red m (trm_try t1 bs) o
  | red_try_1_val : forall v bs m m0,
      red m0 (ext_try_1 (out_ter m v) bs) (out_ter m v)
  | red_try_1_exn : forall v bs m m0 o,
      red m (ext_branches_1 (beh_exn v) v bs) o ->
      red m0 (ext_try_1 (out_ter m (beh_exn v)) bs) o

  | red_assert : forall t1 m o1 o,
      red m t1 o1 ->
      red m (ext_assert_1 o1) o ->
      red m (trm_assert t1) o
  | red_assert_1_true : forall m m0,
      red m0 (ext_assert_1 (out_ter m true))
             (out_ter m val_unit)
  | red_assert_1_false : forall m m0,
      red m0 (ext_assert_1 (out_ter m false))
             (out_ter m (beh_exn constr_assert_failure))

  | red_rand : forall m z,
      red m trm_rand (out_ter m (val_cst z))

  | red_build_1 : forall m F vs,
      red m (ext_build_1 F vs) (out_ter m (F vs))
  | red_list_1_nil : forall K vs m o,
      red m (K vs) o ->
      red m (ext_list_1 nil vs K) o
  | red_list_1_cons : forall K t1 ts o1 vs m o,
      red m t1 o1 ->
      red m (ext_list_2 o1 ts vs K) o ->
      red m (ext_list_1 (t1::ts) vs K) o
  | red_list_2 : forall K v1 ts vs m m0 o,
      red m (ext_list_1 ts (vs++v1::nil) K) o ->
      red m0 (ext_list_2 (out_ter m v1) ts vs K) o

  | red_branches_1_nil : forall B v m,
      red m (ext_branches_1 B v nil)
            (out_ter m B)
  | red_branches_1_cons_mismatch : forall p ot1 t2 B v bs m o,
      mismatching v p ->
      red m (ext_branches_1 B v bs) o ->
      red m (ext_branches_1 B v ((branch_intro p ot1 t2)::bs)) o
  | red_branches_1_cons_match_unguarded : forall i p t2 B v bs m o,
      matching i v p ->
      red m (substs i t2) o ->
      red m (ext_branches_1 B v ((branch_intro p None t2)::bs)) o
  | red_branches_1_cons_match_guarded : forall i p t1 o1 t2 B v bs m o,
      matching i v p ->
      red m (substs i t1) o1 ->
      red m (ext_branches_2 B v bs o1 (substs i t2)) o ->
      red m (ext_branches_1 B v ((branch_intro p (Some t1) t2)::bs)) o
  | red_branches_2_true : forall t B v bs m m0 o,
      red m t o ->
      red m0 (ext_branches_2 B v bs (out_ter m true) t) o
  | red_branches_2_false : forall B t v bs m m0 o,
      red m (ext_branches_1 B v bs) o ->
      red m0 (ext_branches_2 B v bs (out_ter m false) t) o.


