(***************************************************************************
* Functional Translation of a Calculus of Capabilities - Definitions       *
* Arthur Charguéraud, January 2009, Coq v8.1                               *
***************************************************************************)

Set Implicit Arguments.
Require Export Eff_Definitions LibClosure.
Implicit Types x : var.



(* ********************************************************************** *)
(** ** Instanciation of tactics *)

(** Tactic [gather_vars] returns a set of variables occurring in
    the context of proofs, including domain of environments and
    free variables in terms mentionned in the context. *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let C := gather_vars_with (fun x : ctx => dom x) in
(*   let D := gather_vars_with (fun x : trm => fv x) in
  let D := gather_vars_with (fun x : trm => fv x) in *)
  constr:(A \u B \u C).

(** Tactic [pick_fresh x] adds to the context a new variable x
    and a proof that it is fresh from all of the other variables
    gathered by tactic [gather_vars]. *)

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

(** Tactic [apply_fresh T as y] takes a lemma T of the form 
    [forall L ..., (forall x, x \notin L, P x) -> ... -> Q.]
    instanciate L to be the set of variables occuring in the
    context (by [gather_vars]), then introduces for the premise
    with the cofinite quantification the name x as "y" (the second
    parameter of the tactic), and the proof that x is not in L. *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.



(* ********************************************************************** *)
(** ** Induction Schemes *)

Scheme term_induct := Induction for term Sort Prop
  with value_induct := Induction for value Sort Prop.
Combined Scheme term_value_induct 
  from term_induct, value_induct.

Scheme tval_induct := Induction for tval Sort Prop
  with ttrm_induct := Induction for ttrm Sort Prop.
Combined Scheme tval_ttrm_induct
  from tval_induct, ttrm_induct.



(* ********************************************************************** *)
(** ** Regularity lemmas *)
