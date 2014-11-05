(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Encoding of exceptions into sums                          *
*************************************************************)

Set Implicit Arguments.
Require Export LambdaExnSum_Syntax.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Variables introduced by the translation *)

Parameter x1 x2 x3 : var.
Parameter x1_neq_x2 : x1 <> x2.
Parameter x1_neq_x3 : x1 <> x3.
Parameter x2_neq_x3 : x2 <> x3.

Definition L := x1::x2::x3::nil.
Lemma L_eq : L = x1::x2::x3::nil.
Proof. auto. Defined.
Global Opaque L.

Hint Resolve x1_neq_x2 x2_neq_x3 x1_neq_x3.

Hint Extern 1 (_ \notin _) => rewrite L_eq in *. 

Coercion trm_var : var >-> trm.

(************************************************************)
(* ** Definition of the translation *)

Definition tr_ret t := trm_inj true t.
Definition tr_exn t := trm_inj false t.

Definition tr_bind t' x k :=
  trm_case t' (trm_abs x k) (trm_abs x (tr_exn (trm_var x))).

Definition tr_cont t' :=
  trm_abs x2 (tr_bind t' x3 (trm_app x3 x2)).

Fixpoint tr_trm (t:trm) : trm := 
  let s := tr_trm in
  match t with
  | trm_val v => tr_ret (tr_val v)
  | trm_var y => tr_ret t
  | trm_abs y t3 => tr_ret (trm_abs y (s t3))
  | trm_app t1 t2 => 
      tr_bind (s t1) x1 
       (tr_bind (s t2) x2 
         (trm_app x1 x2))
  | trm_inj b t1 => 
      tr_bind (s t1) x1 (tr_ret (trm_inj b x1))
  | trm_case t1 t2 t3 => 
      tr_bind (s t1) x1 
       (trm_case x1 (tr_cont (s t2)) (tr_cont (s t3)))
  | trm_try t1 t2 => 
     trm_case (s t1) (trm_abs x1 (tr_ret x1)) 
                     (tr_cont (s t2))
  | trm_raise t1 => 
      tr_bind (s t1) x1 (tr_exn x1)
  end

with tr_val (v:val) : val := 
  match v with
  | val_abs y t3 => val_abs y (tr_trm t3)
  | val_inj b v1 => val_inj b (tr_val v1)
  | _ => v
  end.



(*==========================================================*)
(* * Proofs *)


(************************************************************)
(* * Freshness *)

(** Distribution of substitution over the translation *)

Ltac imp x :=
  try rewrite L_eq in *;
  asserts: (x \notin \{x}); [ auto | notin_false ]. 

Ltac imp_any :=
  solve [ imp x1 | imp x2 | imp x3 ].

Ltac neq_any :=
  solve [ false x1_neq_x2; assumption
        | false x1_neq_x3; assumption
        | false x2_neq_x3; assumption ].

Ltac simpl_subst :=
  repeat (case_if; try neq_any; try imp_any).

Lemma tr_val_subst : forall x v t, 
  fresh (trm_vars not_used t \u \{x}) 3 L ->
  tr_trm (subst x v t) = subst x (tr_val v) (tr_trm t).
Proof.
  induction t; introv F; simpls.
  fequals.
  simpl_subst; fequals.
  simpl_subst; fequals. rewrite~ IHt.
  simpl_subst. rewrite~ IHt1. rewrite~ IHt2.
  simpl_subst. rewrite~ IHt.
  simpl_subst. rewrite~ IHt1.
   rewrite~ IHt2. rewrite~ IHt3.
  simpl_subst. rewrite~ IHt1. rewrite~ IHt2.
  simpl_subst. rewrite~ IHt.
Qed.

Lemma subst_tr_bind : forall t x k y v,
  x <> y ->
    subst y v (tr_bind t x k) 
  = tr_bind (subst y v t) x (subst y v k).
Proof. introv N. simpl. case_if. fequals. Qed.

Lemma subst_tr_cont : forall t y v,
  fresh (\{y}) 2 (x2::x3::nil) ->
    subst y v (tr_cont t) 
  = tr_cont (subst y v t).
Proof. introv H. simpl. simpl_subst. fequals. Qed.

Lemma tr_trm_vars : forall t,
  fresh (trm_vars not_used t) 3 L ->
  fresh (trm_vars not_free (tr_trm t)) 3 L
with tr_val_vars : forall v,
  fresh (trm_vars not_used v) 3 L ->
  fresh (trm_vars not_free (tr_val v)) 3 L.
Proof.
  (* trm *)
  induction t; introv F; simpls.
  apply~ tr_val_vars.
  auto.
  applys~ fresh_remove_weaken.
  specializes~ IHt1. specializes~ IHt2. fset_simpl.
   do 2 (rewrite union_remove; [ | apply~ notin_elim_single ]).
   auto.
  specializes~ IHt. fset_simpl. auto.
  specializes~ IHt1. specializes~ IHt2. specializes~ IHt3.
   fset_simpl.
   rewrite (@union_remove' _ \{x2}); [ | apply~ notin_elim_single ]. 
   do 2 (rewrite union_remove; [ | apply~ notin_elim_single ]).
   rewrite union_remove'; [ | apply~ notin_elim_single ].
   auto.
  specializes~ IHt1. specializes~ IHt2. fset_simpl.
   rewrite union_remove'; [ | apply~ notin_elim_single ]. 
   rewrite union_remove; [ | apply~ notin_elim_single ]. 
   auto.
  specializes~ IHt. fset_simpl. auto.
  (* val *)
  induction v; introv F; simpls.
  auto.
  applys fresh_remove_weaken. applys~ tr_trm_vars.
  auto.
Qed.

