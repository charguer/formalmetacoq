(************************************************************
* Core Caml                                                 *
* Syntax                                                    *
*************************************************************)

Set Implicit Arguments.
Require Export Common LibHeap.
Module Heap := LibHeap.HeapList.
Notation "x ~~ a" := (single x a)
  (at level 27, left associativity) : env_scope.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Auxiliary definitions for the syntax *)

(** Representation of record labels *)

Definition lab := var.

(** Representation of constructors *)

Definition constr := var.

(** Particular exceptions *)

Parameter constr_unit : constr.
Parameter constr_div_by_zero : constr.
Parameter constr_matching_failure : constr.
Parameter constr_assert_failure : constr.

(** Representation of locations *)

Definition loc := var.

(** Representation of the direction of a for-loop *)

Inductive dir : Type := dir_upto | dir_downto.

(** Grammar of primitive operators *)

Inductive prim : Type :=
  | prim_raise : prim
  | prim_eq : prim
  | prim_not : prim
  | prim_neg : prim
  | prim_add : prim
  | prim_sub : prim
  | prim_mul : prim
  | prim_div : prim
  | prim_and : prim
  | prim_or : prim.

(** Grammar of constants *)

Inductive cst : Type :=
  | cst_bool : bool -> cst
  | cst_int : int -> cst.

(** Grammar of patterns *)

Inductive pat : Type :=
  | pat_var : var -> pat
  | pat_wild : pat
  | pat_alias : pat -> var -> pat
  | pat_or : pat -> pat -> pat
  | pat_cst : cst -> pat
  | pat_constr : constr -> list pat -> pat
  | pat_tuple : list pat -> pat
  | pat_record : list (lab*pat) -> pat.

(** Grammar of terms *)

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
  | trm_rand : trm

with branch : Type := 
  | branch_intro : pat -> option trm -> trm -> branch.

(** Grammar of values *)

Inductive val : Type :=
  | val_cst : cst -> val
  | val_loc : loc -> val
  | val_abs : option var -> pat -> trm -> val
  | val_constr : constr -> list val -> val
  | val_tuple : list val -> val
  | val_record : list (lab*val) -> val.

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
Proof. intros. apply (prove_Inhab (val_cst (cst_bool true))). Qed.

(** Shortnames for lists of terms and values *)

Definition trms := list trm.
Definition vals := list val.
Definition labtrms := list (lab*trm).
Definition labvals := list (lab*val).
Definition branches := list branch.

(** Shortcuts for building terms and values *)

Definition val_exn k := val_constr k nil.

Definition val_unit := val_constr constr_unit nil.

(** Coercions *)

Coercion val_exn : constr >-> val.
Coercion cst_int : Z >-> cst.
Coercion cst_bool : bool >-> cst.
Coercion pat_var : var >-> pat.
Coercion val_loc : loc >-> val.
Coercion val_cst : cst >-> val.
Coercion trm_cst : cst >-> trm.


(** Fresh locations *)

Definition fresh (m:mem) l :=
  ~ Heap.indom m l.


