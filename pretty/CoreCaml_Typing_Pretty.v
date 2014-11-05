

(************************************************************)
(* ** Grammar of simple types *)

Definition tconstr := var.

CoInductive typ :=
  | typ_exn : typ
  | typ_bool : typ
  | typ_int : typ
  | typ_arrow : typ -> typ -> typ
  | typ_tconstr : tconstr -> list typ -> typ
  | typ_tuple : list typ -> typ
  | typ_record : list (lab*typ) -> typ.

Implicit Types T : typ.

Notation "T1 --> t2" := (typ_arrow T1 T2, right associativity) (at level 60).

(************************************************************)
(* ** Typing of constructors *)

Parameter constr_typing : constr -> list typ -> typ -> Prop.


(************************************************************)
(* ** Typing of environments and memory stores *)

Definition env := LibEnv.env typ.

Definition sto := LibEnv.env typ.


(************************************************************)
(* ** Typing of constants *)

Inductive cst_typing : cst -> typ -> Prop :=
   | cst_typing_bool : forall b,
       cst_typing (cst_bool b) typ_bool.
   | cst_typing_int : forall n,
       cst_typing (cst_int n) typ_int.


(************************************************************)
(* ** Typing of primitives *)

Inductive primtyping : prim -> typ -> Prop :=
  | prim_typing_eq : forall T,
      prim_typing prim_eq (T --> T --> typ_bool)
  | prim_typing_not : 
      prim_typing prim_not (typ_bool --> typ_bool)
  | prim_typing_and : 
      prim_typing prim_and (typ_bool --> typ_bool -> typ_bool)
  | prim_typing_or : 
      prim_typing prim_or (typ_bool --> typ_bool --> typ_bool)
  | prim_typing_neg : 
      prim_typing prim_neg (typ_int --> typ_int)
  | prim_typing_add : 
      prim_typing prim_add (typ_int --> typ_int --> typ_int)
  | prim_typing_sub : 
      prim_typing prim_sub (typ_int --> typ_int --> typ_int)
  | prim_typing_mul : 
      prim_typing prim_mul (typ_int --> typ_int --> typ_int)
  | prim_typing_div : 
      prim_typing prim_div (typ_int --> typ_int --> typ_int).


(************************************************************)
(* ** Typing of patterns *)

Inductive pat_typing : env -> pat -> typ -> Prop :=
  | pat_typing_var : forall E x T, 
      binds E x T ->
      pat_typing E (pat_var x) T
  | pat_typing_wild : forall E T,
      pat_typing E pat_wild T
  | pat_typing_alias : forall E p x T,
      pat_typing E p T ->
      binds E x T ->
      pat_typing E (pat_alias p x) T
  | pat_typing_or : forall E p1 p2 T,
      pat_typing E p1 T ->
      pat_typing E p2 T ->
      pat_typing E (pat_or p1 p2) T
  | pat_typing_cst : forall E c T,
      cst_typing c T ->
      pat_typing E c T 
  | pat_typing_constr : forall E k ps Ts T,
      constr_typing k Ts T ->
      Forall2 (pat_typing E) ps Ts ->
      pat_typing E (pat_constr k ps) T
  | pat_typing_tuple : forall E ps Ts,
      Forall2 (pat_typing E) ps Ts ->
      pat_typing E (pat_tuple ps) (typ_tuple Ts)
(* TODO
  | pat_typing_record : forall E aps aTs,
      Forall2 (pat_typing E) aps aTs ->
      pat_typing E (pat_record aps) (typ_record aTs)
  | pat_typing_record_weaken : forall E aps aTs,
      pat_typing E (pat_record aps) (typ_record aTs) ->
      pat_typing E (pat_record aps) (typ_record aTs) ->

  | matching_record_nil : forall avs,
      matching i (val_tuple avs) (pat_tuple nil)
  | matching_record_cons : forall avs a v p aps,
      LibList.Assoc a v avs ->
      matching i v p ->
      matching i (val_record avs) (pat_record aps) ->
      matching i (val_record avs) (pat_record ((a,p)::aps)).
*)

(************************************************************)
(* ** Typing of terms *)


Inductive trm_typing : env -> trm -> typ -> Prop :=
(*  | trm_typing_int : forall E k,
      ok E ->
      typing E (val_int k) typ_int
  | trm_typing_clo : forall E x T1 T2 t1,
      ok E ->
      typing (empty & x ~~ T1) t1 T2 ->
      typing E (val_clo x t1) (typ_arrow T1 T2)
  | trm_typing_var : forall E x T,
      ok E ->
      binds x T E ->
      typing E (trm_var x) T
  | trm_typing_abs : forall x E U T t1,
      typing (E & x ~~ U) t1 T ->
      typing E (trm_abs x t1) (typ_arrow U T)
  | trm_typing_app : forall T1 T2 E t1 t2,
      typing E t1 (typ_arrow T1 T2) -> 
      typing E t2 T1 ->
      typing E (trm_app t1 t2) T2.


Inductive trm : Type :=
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

*)

with branch_typing : env -> typ -> branch -> typ -> Prop :=
  | branch_typing_intro : forall E F Tp T p ot1 t2,
      pat_typing F p Tp ->
      (forall t1, ot1 = Some t1 -> trm_typing (E & F) t1 typ_bool) ->
      trm_typing (E & F) t2 T
      branch_typing E Tp (branch_intro p ot1 t2) T.



(************************************************************)
(* ** Typing of values *)

Definition ctx := LibEnv.env val. (* todo: move *)

Inductive val_typing : sto -> val -> typ -> Prop :=
  | val_typing_cst : forall c T,
      cst_typing c T ->
      val_typing S (val_cst c) T
  | val_typing_loc : forall S l T,
      binds S l T ->
      val_typing S (val_loc l) T
  | val_typing_abs : forall (* TODO oy*) S p t C E T1 T2,
      ctx_typing C E ->
      pat_typing p T1 ->
      trm_typing E t T2 ->
      val_typing S (val_clo C None p t) (T1 --> T2)
  | val_typing_constr : forall E k vs Ts T,
      constr_typing k Ts T ->
      Forall2 (val_typing E) vs Ts ->
      val_typing E (val_constr k vs) T
  | val_typing_tuple : forall E vs Ts,
      Forall2 (val_typing E) vs Ts ->
      pat_typing E (val_tuple vs) (typ_tuple Ts)
  | val_typing_record : forall E avs As vs Ts avs aTs,
      (As,vs) = LibList.split avs ->
      (As,Ts) = LibList.split aTs ->
      Forall2 (val_typing E) vs Ts ->
      pat_typing E (val_record avs) (typ_record aTs)

(*
with ctx_typing : sto -> ctx -> env -> Prop :=
  | ctx_typing_empty : forall S,
      ctx_typing S empty empty
  | ctx_typing_push : forall S C E v T,
      ctx_typing S C E ->
      val_typing S v T ->
      ctx_typing S (C & x ~ v) (E & x ~ T).
*)

with ctx_typing : sto -> ctx -> env :=
  | ctx_typing_intro : forall S C E v,
      binds S x v ->
      exists T, binds E x T /\ val_typing S v T.


(************************************************************)
(* ** Typing of memory *)

Definition mem_typing S m :=
  forall l v, Heap.binds m l v -> 
  exists T, Heap.binds S l T /\ val_typing S v T.


(************************************************************)
(* ** Typing of behaviors *)

Inductive beh_typing : sto -> beh -> Typ -> Prop :=
  | beh_typing_ret : forall S v T, 
      val_typing S v T ->
      beh_typing S (beh_ret v) T
  | beh_typing_exn : forall S v T, 
      val_typing S v typ_exn ->
      beh_typing S (beh_exn v) T.


(************************************************************)
(* ** Typing of outcomes *)

Inductive out_typing : sto -> out -> Typ -> Prop :=
  | out_typing_beh : forall S B T, 
      mem_typing S m ->
      beh_typing S B T ->
      out_typing S (out_ter m B) T
  | out_typing_div : forall S T, 
      out_typing S out_div T.


(************************************************************)
(* ** Typing of extended terms *)

(** TODO: stack? *)

Inductive ext_typing : sto -> ext -> typ -> Prop :=
  | ext_typing_trm : forall t T,
      trm_typing empty t T ->
      ext_typing S (ext_trm t) T 
  | ext_typing_app_1 : forall S t T1 T2,
      out_typing S o1 (T1 --> T2) ->
      trm_typing S t2 T1 ->
      ext_typing S (ext_app_1 o1 t2) T2
  | ext_typing_list_1 : forall S ts vs Ts1 Ts2 T,
      Forall2 (trm_typing empty) ts Ts1 ->
      Forall2 (val_typing S) vs Ts2 ->
      (forall S' vs', Forall2 (val_typing S') vs' (Ts1++Ts2) -> ext_typing S' (K vs') T) ->
      ext_typing S (ext_list_1 ts vs K) T

.
(*
Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_constr_1 : constr -> vals -> ext
  | ext_tuple_1 : vals -> ext
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
  | ext_list_1 : trms -> vals -> (vals -> ext) -> ext
  | ext_list_2 : out -> trms -> vals -> (vals -> ext) -> ext
  | ext_lablist_1 : labtrms -> labvals -> (labvals -> ext) -> ext
  | ext_lablist_2 : out -> lab -> labtrms -> labvals -> (labvals -> ext) -> ext
  | ext_branches_1 : beh -> val -> branches -> ext 
  | ext_branches_2 : beh -> val -> branches -> out -> trm -> ext.
*)