(***************************************************************************
* Correctness of the CPS-transformation                                    *
* Arthur Charguéraud, January 2009, Coq v8.1pl4                            *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory.
Implicit Types x : var.


(* ********************************************************************** *)
(** ** Description of the task *)

(* ********************************************************************** *)
(** Grammar of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_cst  : nat -> trm
  | trm_app  : trm -> trm -> trm
  | trm_abs  : trm -> trm.


(* ********************************************************************** *)
(** Operation to open up abstractions. *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => if k === i then u else (trm_bvar i)
  | trm_fvar x    => t
  | trm_cst k     => t
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1    => trm_abs (open_rec (S k) u t1) 
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).


(* ********************************************************************** *)
(** Definition of well-formedness of a trm *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_cst : forall k, 
      term (trm_cst k)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> term (trm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1). 


(* ********************************************************************** *)
(** Definition of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).


(* ********************************************************************** *)
(** Definition of values *)

Inductive value : trm -> Prop :=
  | value_cst : forall k,
      value (trm_cst k)
  | value_abs : forall t1, 
      term (trm_abs t1) -> 
      value (trm_abs t1).


(* ********************************************************************** *)
(** Definition of the big-step reduction *)

Inductive eval : trm -> trm -> Prop := 
  | eval_val : forall t1, 
      value t1 ->
      eval t1 t1
  | eval_red : forall v2 t3 v3 t1 t2,
      eval t1 (trm_abs t3) ->
      eval t2 v2 -> 
      eval (t3 ^^ v2) v3 ->
      eval (trm_app t1 t2) v3.


(* ********************************************************************** *)
(** Computing free variables of a trm *)

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => {}
  | trm_fvar x    => {{x}}
  | trm_cst k     => {}
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  | trm_abs t1    => (fv t1)
  end.

(* ********************************************************************** *)
(** Abstracting a name out of a trm *)

Fixpoint close_var_rec (k : nat) (z : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => if x == z then (trm_bvar k) else t
  | trm_cst k     => t
  | trm_app t1 t2 => trm_app (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_abs t1    => trm_abs (close_var_rec (S k) z t1) 
  end.

Definition close_var z t := close_var_rec 0 z t.

(* ********************************************************************** *)
(** Substitution for a name *)

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => t
  | trm_fvar x    => if x == z then u else (trm_fvar x)
  | trm_cst k     => t 
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_abs t1    => trm_abs (subst z u t1) 
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

(* ********************************************************************** *)
(** ** Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let C := gather_vars_with (fun x : trm => fv x) in
  constr:(A \u B \u C).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

(*
Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.
*)

Hint Constructors trm.


(* ********************************************************************** *)
(** ** Properties of substitution *)

(* begin hide *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  {j ~> v}t = {i ~> u}({j ~> v}t) -> t = {i ~> u}t.
Proof.
  induction t; introv Neq Equ; simpls; inversion* Equ; fequals*.  
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; fequals*. unfolds open.
  pick_fresh x. apply* (@open_rec_term_core t1 0 (trm_fvar x)).
Qed.

(* end hide *)

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t ->  [x ~> u] t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. notin_false.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; fequals*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u t, y <> x -> term u ->
  ([x ~> u]t) ^ y = [x ~> u] (t ^ y).
Proof.
  introv Neq Wu. rewrite* subst_open. simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.


(* ********************************************************************** *)
(** ** Terms are stable through substitutions *)

Hint Constructors term.

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  induction 2; simpls*.
  case_var*.
  apply_fresh term_abs. rewrite* subst_open_var.
Qed.

Hint Resolve subst_term.


(* ********************************************************************** *)
(** ** Terms are stable through open *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> body t1.
Proof. intros. unfold body. inversion* H. Qed.

Lemma body_to_term_abs : forall t1, 
  body t1 -> term (trm_abs t1).
Proof. intros. inversion* H. Qed.

Hint Resolve term_abs_to_body body_to_term_abs.

(** ** Opening a body with a term gives a term *)

Lemma open_term : forall t u,
  body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Hint Resolve open_term.


(* ********************************************************************** *)
(** ** Additional results on primitive operations *)

(** Open_var with fresh names is an injective operation *)

Lemma open_var_inj : forall x t1 t2, 
  x \notin (fv t1) -> x \notin (fv t2) -> 
  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold open. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal* 
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

(* begin hide *)

(** Close var commutes with open with some freshness conditions,
  this is used in the proofs of [close_var_body] and [close_var_open] *)

Lemma close_var_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (fv t1) ->
    {i ~> trm_fvar y} ({j ~> trm_fvar z} (close_var_rec j x t1) )
  = {j ~> trm_fvar z} (close_var_rec j x ({i ~> trm_fvar y}t1) ).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ]. 
  case_var*. simpl. case_nat*. 
Qed.

(* end hide *)

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_fresh : forall x t,
  x \notin fv (close_var x t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simple*.
Qed.

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_body : forall x t,
  term t -> body (close_var x t).
Proof.
  introv W. exists {{x}}. intros y Fr.
  unfold open, close_var. generalize 0. gen y.
  induction W; intros y Fr j; simpls.
  case_var; simple*. case_nat*.
  autos*.
  autos*.
  apply_fresh* term_abs as z.
   unfolds open. rewrite* close_var_rec_open.
Qed.

(** Close var is the right inverse of open_var *)

Lemma close_var_open : forall x t,
  term t -> t = (close_var x t) ^ x.
Proof.
  introv W. unfold close_var, open. generalize 0.
  induction W; intros j; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.
Qed.
 
(** An abstract specification of close_var, which packages the
  result of the operation and all the properties about it. *)

Lemma close_var_spec : forall t x, term t -> 
  exists u, t = u ^ x /\ body u /\ x \notin (fv u).
Proof.
  intros. exists (close_var x t). splits 3.
  apply* close_var_open.
  apply* close_var_body.
  apply* close_var_fresh.
Qed. 



(* ********************************************************************** *)
(** Automation *)

Hint Extern 1 (term ?t) => skip.
(* match goal with
  | H: value t |- _ => skip  
  | H: eval t _ |- _ => skip
  | H: eval _ t |- _ => skip
  end.*)

Hint Constructors value.


Lemma open_rec_term_core' : forall t j v i u, i <> j ->
  {i ~> u}({j ~> v}t) = {j ~> v}t -> {i ~> u}t = t.
Proof.
  induction t; introv Neq Equ; simpls; inversion* Equ; fequals*.  
  case_nat*. case_nat*.
Qed.

Lemma open_lc : forall t u k,
  term t -> {k ~> u}t = t.
Proof.
  introv H. gen k. induction H; intros; simpl; fequals*. 
  unfolds open. pick_fresh x. 
   apply* (@open_rec_term_core' t1 0 (trm_fvar x)).
Qed.


(* ********************************************************************** *)
(** Equivalence *)

Lemma eval_value_only : forall v v', 
  eval v v' -> value v -> v' = v.
Proof.
  introv E V. inverts V; inverts~ E. 
Qed.

Definition trm_undefined := trm_bvar 0.

(* todo: make an inductive instead ! or well-founded recursion .. *)

Inductive cps : trm -> trm -> Prop :=
  | cps_var : forall x, 
      cps (trm_fvar x)
          (trm_abs (trm_app (trm_bvar 0) (trm_fvar x)))
  | cps_cst : forall k, 
      cps (trm_cst k)
          (trm_abs (trm_app (trm_bvar 0) (trm_cst k)))
  | cps_abs : forall L t1 t1', 
      (forall x, x \notin L -> cps (t1^x) (t1'^x)) ->
      cps (trm_abs t1)
         (trm_abs (trm_app (trm_bvar 0) (trm_abs t1'))) 
  | cps_app : forall t1 t2 t1' t2',
      cps t1 t1' ->
      cps t2 t2' ->
      cps (trm_app t1 t2)
          (let k := trm_abs (trm_app (trm_app (trm_bvar 1) (trm_bvar 0)) (trm_bvar 2)) in
           trm_abs (trm_app t1' (trm_abs (trm_app t2' k)))).

Lemma eval_value : forall t v,
  eval t v -> value v.
Proof.
  introv H. induction H; auto.
Qed.


Hint Constructors cps.
Lemma cps_function : forall t, term t ->
  exists t', cps t t'.
Proof.
  introv T. induction T.
  eauto. 
  eauto.
  destruct IHT1 as [t1' ?]. destruct IHT2 as [t2' ?].
   exists~ (let k := trm_abs (trm_app (trm_app (trm_bvar 1) (trm_bvar 0)) (trm_bvar 2)) in
            trm_abs (trm_app t1' (trm_abs (trm_app t2' k)))).
  exists __. apply_fresh cps_abs.
 skip. (* close again ! *)
Admitted.

Hint Resolve eval_value.
Hint Constructors cps.
Lemma cps_subst_var : forall x y t t', 
  cps t t' ->
  cps (subst x (trm_fvar y) t) (subst x (trm_fvar y) t'). 
Proof.
  introv C. induction C; simpl.
  case_var~.
  auto.
  apply_fresh cps_abs. do 2 rewrite~ subst_open_var.
  auto.
Qed.

Lemma cps_functional : forall t t1' t2',
  cps t t1' -> cps t t2' -> t1' = t2'.
Admitted.


Inductive cps_value : trm -> trm -> Prop :=
  | cps_value_cst : forall k,
      cps_value (trm_cst k) (trm_cst k)
  | cps_value_abs : forall L t1 t1',
      (forall x, x \notin L -> cps (t1^x) (t1'^x)) ->
      cps_value (trm_abs t1) (trm_abs t1').



Lemma cps_value_functional : forall v v1' v2',
  cps_value v v1' -> cps_value v v2' -> v1' = v2'.
Admitted.

Lemma cps_value_function : forall v, value v ->
  exists v', cps_value v v'.
Admitted.




Lemma cps_value_abs_exists : forall x t1 t1',
  cps (t1 ^ x) (t1' ^ x) ->
  x \notin fv t1 \u fv t1' -> 
  cps_value (trm_abs t1) (trm_abs t1').
Proof.
  introv C Fr. apply_fresh cps_value_abs.
  rewrite~ (@subst_intro x t1).
  rewrite~ (@subst_intro x t1').
  apply~ cps_subst_var.
Qed.


Lemma cps_of_value : forall v' v, 
  value v -> 
  cps_value v v' ->
  cps v (trm_abs (trm_app (trm_bvar 0) v')).
Proof.
  introv V C. inverts C.
  auto.
  apply_fresh* cps_abs.
Qed.

Hint Rewrite
 union_empty_r
 union_empty_l
 union_assoc
 union_same : set.
Tactic Notation "calc_set" :=
  autorewrite with set.
Tactic Notation "calc_set" "*" := 
  calc_set; autos*.

Lemma cps_fv : forall t t',
  cps t t' -> fv t' = fv t.
Proof.
  introv C. induction C; simpl.
  calc_set*.
  calc_set*.
  calc_set. skip.
  calc_set. congruence.
Qed.

Lemma cps_subst : forall x v v' t t', 
  value v ->
  cps_value v v' ->
  cps t t' ->
  cps (subst x v t) (subst x v' t'). 
Proof.
  introv V CV CT.
  induction CT; simpl.
  case_var.
    apply~ cps_of_value.
    auto.
  auto.
  apply_fresh cps_abs. do 2 rewrite~ subst_open_var.
  auto.
Qed.

Lemma cps_open : forall v v' t t', 
  value v ->
  cps_value v v' ->
  cps_value (trm_abs t) (trm_abs t') ->
  cps (t ^^ v) (t' ^^ v'). 
Proof.
  introv V CV CT. inverts CT.
  pick_fresh x. 
  rewrite~ (@subst_intro x t).
  rewrite~ (@subst_intro x t').
  apply~ cps_subst.
Qed.

Lemma cps_value_value : forall v v',
  cps_value v v' -> value v'.
Proof.
  introv V. inverts~ V.
Qed.

Ltac prove_term := 
  match goal with |- term _ => skip end.
Ltac calc_open := 
  unfold open; simpl; rewrite_all open_lc; try prove_term.



Check eval_red.

Hint Resolve eval_val.
Lemma eval_red_values : forall t1 v2 r,
  term t1 -> value v2 ->
  eval (t1 ^^ v2) r ->
  eval (trm_app (trm_abs t1) v2) r.
Proof.
  intros. apply~ eval_red.
Qed.
Hint Resolve eval_red_values.
Hint Resolve cps_value_value.

Lemma eval_red_values_bis : forall t1 v2 v3 r,
  term t1 -> value v2 -> value v3 ->
  eval (trm_app (t1 ^^ v2) v3) r ->
  eval (trm_app (trm_app (trm_abs t1) v2) v3) r.
Proof.
  introv T1 V2 V3 E. inverts E. inverts H.
  apply~ eval_red.
  apply* eval_red_values.
  rewrite~ <- (eval_value_only H2). 
Qed.

Lemma cps_value_abs_of : forall t3, body t3 ->
  exists t3', cps_value (trm_abs t3) (trm_abs t3').
Proof.
  introv B. pick_fresh x.
  forwards~ H: (@cps_function (t3^x)). destruct H as [t3x C].
  exists (close_var x t3x).
  apply~ (@cps_value_abs_exists x).
  rewrite~ <- close_var_open.
  notin_simpl. auto. apply close_var_fresh.
Qed.  

Lemma cps_correct_ind : forall v v' t t' k r,
  eval t v -> 
  cps_value v v' ->
  eval (trm_app k v') r -> 
  value k -> 
  cps t t' ->
  eval (trm_app t' k) r.
Proof.
  introv E. gen v' t' k r. induction E; introv CV EV V CT.
  (* case: value *)
  lets CT': (cps_of_value H CV).
  rewrite (cps_functional CT CT').
  apply~ eval_red_values. calc_open. auto.
  (* case: red *)
  inverts CT as CT1 CT2.
  forwards~ H: (@cps_value_abs_of t3). destruct H as [t3' T3].
  apply~ eval_red_values. calc_open.
  apply~ IHE1; clear IHE1. eauto.
  apply~ eval_red_values. calc_open.
  forwardv H: (@cps_value_function v2). eauto. destruct H as [v2' T2]. 
  apply~ IHE2; clear IHE2. eauto.
  apply~ eval_red_values. eauto. calc_open.
  apply~ eval_red_values_bis. eauto.
  apply~ IHE3; clear IHE3. eauto. eauto.
  apply~ cps_open. eauto.
Qed.

Definition trm_id := trm_abs (trm_bvar 0).

Lemma cps_correct : forall v v' t t',
   eval t v -> 
   cps t t' ->
   cps_value v v' ->
   eval (trm_app t' trm_id) v'.
Proof.
  introv E CT CV. unfold trm_id.
  apply* (@cps_correct_ind v).
Qed.



(*------------------*)

Require Import SuperFix.

Definition Cps_body (Cps:trm->trm) (t:trm) : trm :=
  match t with
  | trm_bvar _ => trm_undefined
  | trm_fvar _ => 
      trm_abs (trm_app (trm_bvar 0) t)
  | trm_cst _ => 
      trm_abs (trm_app (trm_bvar 0) t)
  | trm_abs t1 => 
      let x := var_gen (fv t1) in
      let t1' := close_var x (Cps (t1 ^ x)) in
      trm_abs (trm_app (trm_bvar 0) (trm_abs t1'))
  | trm_app t1 t2 => 
      let k := trm_abs (trm_app (trm_app (trm_bvar 1) (trm_bvar 0)) (trm_bvar 2)) in
           trm_abs (trm_app (Cps t1) (trm_abs (trm_app (Cps t2) k)))
  end.

Fixpoint trm_size (t:trm) :=
  match t with
  | trm_bvar _ => 1
  | trm_fvar _ => 1
  | trm_cst _ => 1
  | trm_abs t1 => 1+(trm_size t1)
  | trm_app t1 t2 => 1+(trm_size t1)+(trm_size t2)
  end.

Require Import Omega.

Lemma trm_size_rename : forall x y t,
  trm_size ([x ~> trm_fvar y]t) = trm_size t.
Proof.
  induction t; simpl; fequals. case_var~.
Qed.

Lemma trm_size_open : forall x t,
  trm_size (t^x) = trm_size t.
Proof.
  intros. unfold open. generalize 0.
  induction t; intros; simpl; fequals.
  case_nat~.
  rewrite IHt1. rewrite~ IHt2.
  rewrite~ IHt.
Qed.

Definition Cps := fixmu trm_undefined Cps_body trm_size.

Lemma fixCps : forall x:trm, 
  Cps x = Cps_body Cps x.
Proof.
  prove_fixf. destruct x; fequals.
  rewrite IH. rewrite IH. auto. simpl; omega. simpl; omega.
  rewrite IH. auto. simpl. rewrite trm_size_open. omega.
Qed.
Hint Resolve fixCps.

Lemma Cps_cps : forall t,
  term t -> cps t (Cps t).
Proof.
  introv H. induction H; simpl_fix~ Cps.
  sets x: (var_gen (fv t1)). apply_fresh cps_abs.
  applya_in H0 (>>> y __). auto.
  rewrite~ (@subst_intro y t1 (trm_fvar x)).
  skip_rewrite (Cps ([y ~> trm_fvar x](t1 ^ y))
    = [y ~> trm_fvar x](Cps (t1^y))).
  skip_rewrite (forall t, close_var x ([y ~> trm_fvar x]t)
    = close_var y t).
  skip_rewrite (forall t, (close_var y t)^y = t). 
  auto.
Qed.




