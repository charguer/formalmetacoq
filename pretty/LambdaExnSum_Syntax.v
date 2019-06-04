(************************************************************
* Lambda-calculus with exceptions and sums,                 *
* Syntax                                                    *
*************************************************************)

Set Implicit Arguments.
Require Export LibVar Common.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Syntax *)

(** Grammar of values and terms *)

Inductive val : Type :=
  | val_int : int -> val
  | val_abs : var -> trm -> val
  | val_inj : bool -> val -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_abs : var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_inj : bool -> trm -> trm
  | trm_case : trm -> trm -> trm -> trm
  | trm_try : trm -> trm -> trm
  | trm_raise : trm -> trm.

Coercion trm_val : val >-> trm.
Implicit Types v : val.
Implicit Types t : trm.

(** Substitution *)

Fixpoint subst (x:var) (v:val) (t:trm) : trm :=
  let s := subst x v in
  match t with
  | trm_val v1 => trm_val v1
  | trm_var y => If x = y then v else t
  | trm_abs y t3 => trm_abs y (If x = y then t3 else s t3)
  | trm_app t1 t2 => trm_app (s t1) (s t2)  
  | trm_inj b t1 => trm_inj b (s t1)
  | trm_case t1 t2 t3 => trm_case (s t1) (s t2) (s t3)
  | trm_try t1 t2 => trm_try (s t1) (s t2)
  | trm_raise t1 => trm_raise (s t1)
  end.


(************************************************************)
(* ** Freshness *)

(** Two modes for freshness: "not used" and "not free" *)

Inductive vars_opt := not_used | not_free.

Definition add_bound f E (x:var) :=
  match f with 
  | not_used => E \u \{x}
  | not_free => E \- \{x}
  end.

(** Set of free variables and used variables *)

Fixpoint trm_vars (f:vars_opt) (t:trm) : vars :=
  let r := trm_vars f in
  match t with
  | trm_val v1 => val_vars f v1
  | trm_var x => \{x}
  | trm_abs x t1 => add_bound f (r t1) x
  | trm_app t1 t2 => (r t1) \u (r t2)
  | trm_inj b t1 => (r t1)
  | trm_case t1 t2 t3 => (r t1) \u (r t2) \u (r t3)
  | trm_try t1 t2 => (r t1) \u (r t2)
  | trm_raise t1 => (r t1)
  end 

with val_vars (f:vars_opt) (v:val) : vars :=
  match v with
  | val_int n => \{}
  | val_abs x t1 => add_bound f (trm_vars f t1) x
  | val_inj b v1 => val_vars f v1
  end.


(*==========================================================*)
(* * Proofs *)


(************************************************************)
(* ** Specific lemmas for reasoning on sets of variables *)

Lemma notin_remove : forall A x (E F:fset A),
  x \notin (E \- F) = (x \notin E \/ x \in F).
Proof.
  intros. unfolds notin. rewrite in_remove.
  unfolds notin. rew_logic*.
Qed.

Lemma notin_remove_l : forall A x (E F:fset A),
  x \notin (E \- F) -> x \notin E \/ x \in F.
Proof. introv H. rewrite~ notin_remove in H. Qed.

Lemma notin_remove_r : forall A x (E F:fset A),
  (x \notin E \/ x \in F) -> x \notin (E \- F).
Proof. introv H. rewrite~ notin_remove. Qed.

Lemma notin_remove_inv : forall A x (E F:fset A),
  x \notin (E \- F) -> x \notin F -> x \notin E.
Proof. introv H1 H2. destruct~ (notin_remove_l H1). false. Qed.

Lemma notin_remove_weaken : forall E F (x:var),
  x \notin E ->
  x \notin (E \- F).
Proof. intros. applys~ notin_remove_r. Qed.

Lemma notin_to_fresh : forall xs n E F,
  fresh E n xs -> 
  (forall x, x \notin E -> x \notin F) ->
  fresh F n xs.
Proof.
  induction xs; introv Fr H.
  auto.
  destruct n. false. simpls. destruct Fr.
   split~. applys* IHxs.
Qed. 

Lemma fresh_remove_weaken : forall E F n xs,
  fresh E n xs ->
  fresh (E \- F) n xs.
Proof.
  intros. applys* notin_to_fresh. applys* notin_remove_weaken.
Qed.

Lemma remove_self : forall A (E:fset A),
  E \- E = \{}.
Proof.
  intros. applys fset_extens; intros x H.
  rewrite in_remove in H. false*.
  rewrite in_empty in H. false.
Qed.

Lemma union_remove : forall A (E F:fset A),
  (forall x, x \in E -> x \notin F) ->
  (E \u F) \- F = E.
Proof.
  introv M. applys fset_extens; intros x H.
  rewrite in_remove, in_union in H. destruct H as [[?|?] ?].
    auto.
    false*.
  rewrite in_remove, in_union. auto.
Qed.

Lemma union_remove' : forall A (E F:fset A),
  (forall x, x \in E -> x \notin F) ->
  (F \u E) \- F = E.
Proof.
  introv M. applys fset_extens; intros x H.
  rewrite in_remove, in_union in H. destruct H as [[?|?] ?].
    false*.
    auto.
  rewrite in_remove, in_union. auto.
Qed.

Hint Rewrite union_empty_l union_empty_r remove_self : fset_simpl.
Ltac fset_simpl := autorewrite with fset_simpl.

Lemma notin_elim_single : forall A (y:A) (E:fset A),
  y \notin E ->
 (forall x, x \in E -> x \notin \{y}).
Proof.
  introv H M. rewrite notin_singleton. intro_subst. false.
Qed.

Lemma notin_remove_single_inv : forall A x y (E:fset A),
  x \notin (E \- \{y}) -> x <> y -> x \notin E.
Proof.
  introv H1 H2. applys* notin_remove_inv. 
  rewrite~ notin_singleton. 
Qed.


(************************************************************)
(* ** Freshness *)

(** Properties of [add_bound] *)

Lemma notin_add_bound : forall x f y E,
  x \notin add_bound f E y ->
  x \notin E \- \{y}.
Proof.
  intros. destruct f; simpls.
  applys~ notin_remove_weaken.
  auto.
Qed.

(** Substitution is the identity function on fresh vars *)

Lemma subst_id : forall f x v t, 
  x \notin trm_vars f t -> 
  subst x v t = t. 
Proof.
  induction t; introv F; simpls; fequals~.
  case_if*. subst. notin_false.
  case_if*. applys IHt. destruct f; simpls~.
   applys~ notin_remove_inv F.
Qed.
  
Lemma subst_notin : forall t x y v,
  x \notin (trm_vars not_used t) ->
  x \notin (val_vars not_used v) ->
  x \notin (trm_vars not_used (subst y v t)).
Proof. induction t; introv Frt Frv; simpls~; try case_if*. Qed.

Lemma fresh_subst : forall xs n t y v,
  fresh (trm_vars not_used t) n xs ->
  fresh (val_vars not_used v) n xs ->
  fresh (trm_vars not_used (subst y v t)) n xs.
Proof. 
  induction xs; introv Frt Frv.
  auto.
  destruct n. false. simpls. 
   destruct Frt. destruct Frv.
   hint subst_notin. auto.
Qed.

