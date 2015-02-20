
(*
Ltac math := simpls; omega.

Axiom peano_induction : 
  forall (P:nat->Prop),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    (forall n, P n).
Lemma measure_induction : 
  forall (A:Type) (mu:A->nat) (P:A->Prop),
    (forall x, (forall y, mu y < mu x -> P y) -> P x) ->
    (forall x, P x).
Proof.
  introv IH. intros x. gen_eq n: (mu x). gen x.
  induction n using peano_induction. introv Eq. subst*.
Qed.
*)


(* ********************************************************************** *)
(** Equivalence of [rename] and [rename'] *)

Lemma rename_eq_rename' : forall x y t,
  rename x y t = rename' x y t.
Proof.
  introv. unfold rename. induction t; simpl; fequals~.
  case_var~; case_var~.
Qed.

(* ********************************************************************** *)
(** Working modulo [rename] *)

Lemma open_var_rename : forall x y t,
  x \notin fv t ->
  open_var t y = rename x y (open_var t x).
Proof.
  introv. unfold open_var, rename. generalize 0.
  induction t; simpl; intros k F; fequals~.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.

Lemma open_var_rename' : forall x y t,
  x \notin fv t ->
  open_var t y = rename' x y (open_var t x).
Proof.
  introv. unfold open_var. generalize 0.
  induction t; simpl; intros k F; fequals~.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.

Lemma open_var'_rename : forall x y t,
  x \notin fv t ->
  open_var' t y = rename x y (open_var' t x).
Proof.
  introv F. unfold rename. apply~ subst_intro.
Qed.

Lemma close_var_rename : forall x y t,
  x \notin fv t ->
  close_var y t = close_var x (rename y x t).
Proof.
  introv. unfold close_var, rename. generalize 0.
  induction t; simpl; intros k F; fequals~.
  case_var; simpl; case_var~.
Qed.

Lemma close_var_rename' : forall x y t,
  x \notin fv t ->
  close_var y t = close_var x (rename' y x t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; simpl; intros k F; fequals~.
  case_var; case_var; simpl; case_var~.
Qed.

Lemma lc_rename : forall t x y,
  lc t -> lc (rename x y t).
Proof.
  introv T. unfold rename. induction T; simple~.
  case_var~.
  apply_fresh lc_abs. rewrite~ <- subst_open_var.
Qed.

Lemma lc'_rename : forall t x y,
  lc' t -> lc' (rename x y t).
Proof.
  introv. unfold rename, lc'. generalize 0.
  induction t; simpl; intros; autos*.
  case_var~.
Qed.


(* ********************************************************************** *)
(** Equivalence between [open_var] and [open_var'] *)

Lemma open_var_eq_open_var' : forall x t,
  open_var t x = open_var' t x.
Proof.
  introv. unfold open_var, open_var', open. generalize 0.
  induction t; intros k; simpl; fequals~.
Qed.

(* all lemmas on [open_var] can be ported to [open_var'], e.g.: *)

Lemma size_open_var' : forall x t,
  size (open_var' t x) = size t.
Proof.
  intros. unfold open_var', open. generalize 0.
  induction t; intros; simple~. case_nat~.
Qed.


Lemma open_var_lc : forall x t,
  body t -> lc (open_var t x).
Proof.
  introv [L H]. pick_fresh y. rewrite~ (@open_var_rename y).
  apply~ lc_rename.
Qed.

Lemma subst_open_var'_lc' : forall x y u t, 
  y <> x -> lc u ->
  subst x u (open_var' t y) = open_var' (subst x u t) y.
Proof.
  introv N U. unfold open_var', open. generalize 0.
  induction t; simpl; intros; fequals~.
  case_nat~. simpl. case_var~.
  case_var~. rewrite~ open_rec_lc.
Qed


Lemma subst_intro_' : forall x t u, 
  x \notin (fv t) -> 
  open t u = subst x u (open_var' t x).
Proof.
  introv. unfold open_var', open. generalize 0.
  induction t; simpl; intros; fequals*.
  case_nat~. simpl. case_var~.
  case_var~.
Qed.



(* ********************************************************************** *)
(** Variable opening --subsumed by "opening" *)

Fixpoint open_var'_rec (k : nat) (z : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then (trm_fvar z) else t
  | trm_fvar x    => t
  | trm_app t1 t2 => trm_app (open_var'_rec k z t1) (open_var'_rec k z t2)
  | trm_abs t1    => trm_abs (open_var'_rec (S k) z t1) 
  end.

Definition open_var' t x := open_var'_rec 0 x t.





(* ********************************************************************** *)
(** Renaming *)

Fixpoint rename' (x y : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => t
  | trm_fvar z    => If x = z then trm_fvar y else t
  | trm_app t1 t2 => trm_app (rename' x y t1) (rename' x y t2)
  | trm_abs t1    => trm_abs (rename' x y t1) 
  end.

(* ********************************************************************** *)
(** Renaming, in terms of substitution *)

Definition rename x y t := subst x (trm_fvar y) t.


Lemma size_rename : forall x y t,
  size (rename x y t) = size t.
Proof.
  unfold rename. induction t; simpl; fequals. case_var~.
Qed.



DEC=\
	STLC_Dec_Definitions \
	STLC_Dec_Infrastructure \
	STLC_Dec_Soundness \
	STLC_Dec_Decidability 



H1 : sch_fv M << fv_in sch_fv E
______________________________________(1/20)
Z \notin sch_fv M

(** Specification of the above function in terms of [bind]. *)

Lemma fv_in_spec : forall (A : Type) (fv : A -> vars) x a (E : env A),
  binds x a E -> (fv a) << (fv_in fv E).
Proof.
  unfold binds; induction E as [|(y,b)]; simpl; intros B.
  false.
  case_var.
    inversions B. apply subset_union_weak_l.
    apply* (@subset_trans (fv_in fv E)). apply subset_union_weak_r.
Qed.

Axiom fv_in_spec : forall (A : Type) (fv : A -> vars) x a (E : env A),
  binds x a E -> (fv a) << (fv_in fv E).


Lemma ok_concat_singles : forall n xs vs E,
  ok E ->
  fresh (dom E) n xs ->
  ok (E & xs ~* vs).
Proof.
  induction n; introv Ok Fr; destruct xs; simpls.
  unfold singles. simpls. rew_env_concat. auto.
  simpl. 
Qed. 
  


(* TODO: get rid of this section using non-constructive comparisons *)

Lemma eq_var_dec : forall x y : var, {x = y} + {x <> y}.
Proof. intros. apply classicT. Qed.

(** We define notations for the equality of variables (our free variables)
  and for the equality of naturals (our bound variables represented using
  de Bruijn indices). *)

Notation "x == y" := (eq_var_dec x y) (at level 70, no associativity).
Notation "i === j" := (Peano_dec.eq_nat_dec i j) (at level 70, no associativity).

(** Tactic for comparing two bound or free variables. *)

Ltac case_nat_base :=
  let destr x y := destruct (x === y); [try subst x | idtac] in
  match goal with
  | H: context [?x === ?y] |- _ => destr x y
  | |- context [?x === ?y]      => destr x y
  end.

Tactic Notation "case_nat" := 
  case_nat_base;
  try solve [ match goal with H: ?x <> ?x |- _ => 
               false_goal; apply H; reflexivity end ].
Tactic Notation "case_nat" "~" := case_nat; auto_tilde.
Tactic Notation "case_nat" "*" := case_nat; auto_star.

Tactic Notation "case_var" constr(x) constr(y)  :=
  destruct (x == y); [try subst x | idtac].

Ltac case_var_base :=
  match goal with
  | H: context [?x == ?y] |- _ => case_var x y
  | |- context [?x == ?y]      => case_var x y
  end.

Tactic Notation "case_var" := 
  case_var_base; try solve [ notin_false ].
Tactic Notation "case_var" "~" := case_var; auto_tilde.
Tactic Notation "case_var" "*" := case_var; auto_star.







(* -todo: old implem with list visible
Tactic Notation "apply_empty" constr(H) :=
  applys (@H empty); 
  rewrite_all concat_empty_r.

Tactic Notation "apply_empty" "~" constr(H) :=
  apply_empty H; auto_tilde.
Tactic Notation "apply_empty" "*" constr(H) :=
  apply_empty H; auto_star.
*)

(* Whether bindings are or not in the context is decidable *)

Lemma binds_dec : forall E x a,
  (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
  decidable (binds x a E).
Proof.
  introv Dec. remember (get x E) as B. symmetry in HeqB.
  unfold binds. destruct B as [a'|].
  destruct (Dec a a'). subst. 
    left*.
    right. intros H. congruence.
  right. intros H. congruence.
Qed.




(* ********************************************************************** *)

Section OpProperties.
Variable A : Type.
Implicit Types E F : env A.
Implicit Types a b : A.

(** Simplification tactics *)

Hint Rewrite 
  concat_empty 
  map_concat
  dom_empty dom_single dom_push dom_cons dom_concat dom_map : rew_env.
  
Hint Rewrite <- concat_assoc : rew_env.

Tactic Notation "simpl_env" :=
  autorewrite with rew_env in *.

Hint Extern 1 (_ # _) => simpl_env; notin_solve.

(** The [env_fix] tactic is used to convert environments
  from [(x,a)::E] to [E & x ~ a]. *)

(* Duplication in first two cases is to work around a Coq bug
   of the change tactic *)

Ltac env_fix_core :=
  let go := try env_fix_core in
  match goal with 
  | H: context [(?x,?a)::?E] |- _ =>
     (   (progress (change ((x,a)::E) with (E & x ~ a) in H))
      || (progress (unsimpl (E & x ~ a) in H))   ); go
  | |- context [(?x,?a)::?E] =>
    (   (progress (change ((x,a)::E) with (E & x ~ a)))
      || (progress (unsimpl (E & x ~ a)))  ); go
  |  H: context [@nil ((var * ?A)%type)] |- _ =>
      progress (change (@nil ((var * A)%type)) with (@empty A) in H); go
  | |- context [@nil ((var * ?A)%type)] => 
     progress (change (@nil ((var * A)%type)) with (@empty A)); go
  end.

Ltac env_fix := try env_fix_core.



(* ********************************************************************** *)
(** ** Tactics *)

Opaque binds.

(** [binds_get H as EQ] produces from an hypothesis [H] of
  the form [binds x a (E & x ~ b & F)] the equality [EQ: a = b]. *)

Tactic Notation "binds_get" constr(H) "as" ident(EQ) :=
  match type of H with binds ?z ?a (?E & ?x ~ ?b & ?F) =>
    let K := fresh in assert (K : ok (E & x ~ b & F)); 
    [ auto | lets EQ: (@binds_mid_eq _ z a b E F H K); clear K ] end.

(** [binds_get H] expects an hypothesis [H] of the form 
  [binds x a (E & x ~ b & F)] and substitute [a] for [b] in the goal. *)

Tactic Notation "binds_get" constr(H) :=
  let EQ := fresh in binds_get H as EQ;
  try match type of EQ with 
  | ?f _ = ?f _ => inversions EQ; clear EQ
  | ?x = ?y => subst x end.

(** [binds_single H] derives from an hypothesis [H] of the form 
  [binds x a (y ~ b)] the equalities [x = y] and [a = b], then
  it substitutes [x] for [y] in the goal or deduce a contradiction
  if [x <> y] can be found in the context. *)

Ltac binds_single H :=
  match type of H with binds ?x ?a (?y ~ ?b) =>
    destruct (binds_single_inv H); 
    try discriminate; try subst y; 
    try match goal with N: ?x <> ?x |- _ =>
      false; apply N; reflexivity end end.

(** [binds_case H as B1 B2] derives from an hypothesis [H] of the form 
  [binds x a (E & F)] two subcases: [B1: binds x a E] (with a freshness
  condition [x # F]) and [B2: binds x a F]. *)

Tactic Notation "binds_case" constr(H) "as" ident(B1) ident(B2) :=
   let Fr := fresh "Fr" in 
   destruct (binds_concat_inv H) as [[Fr B1] | B2].

(** [binds_case H] makes a case analysis on an hypothesis [H] of the form 
  [binds x a E] where E can be constructed using concatenation and
  singletons. It calls [binds_single] when reaching a singleton. *)

Ltac binds_cases H :=
  let go B := clear H; 
    first [ binds_single B | binds_cases B | idtac ] in
  let B1 := fresh "B" in let B2 := fresh "B" in
  binds_case H as B1 B2; simpl_env; [ go B1 | go B2 ].


(** Automation *)

Hint Resolve 
  binds_concat_fresh binds_concat_ok 
  binds_prepend binds_map.




(** Subset relation properties *)

Lemma subset_refl : forall E,
  E << E.
Proof. intros_all~. Qed.

Lemma subset_trans : forall F E G,
  E << F -> F << G -> E << G.
Proof. intros_all~. Qed.

(** Interaction of subset with constructions *)

Lemma subset_empty_l : forall E,
  {} << E.
Proof. intros_all. false. apply* in_empty. Qed.

Lemma subset_singleton : forall x E,
  x \in E <-> {{x}} << E.
Proof.
  split; introv H. 
  introv M. rewrite in_singleton in M. subst*.
  apply H. apply in_singleton_self.
Qed.

Lemma subset_union_weak_l : forall E F,
  E << (E \u F).
Proof. intros_all. rewrite~ in_union. Qed.

Lemma subset_union_weak_r : forall E F,
  F << (E \u F).
Proof. intros_all. rewrite~ in_union. Qed.

Lemma subset_union_l : forall E F G,
  (E \u F) << G <-> (E << G) /\ (F << G).
Proof.
  split; introv H.
    split; intros_all.
      apply H. apply* subset_union_weak_l.
      apply H. apply* subset_union_weak_r.
    introv M. rewrite* in_union in M.
Qed.

(** Proving subset relations using \notin *)

Axiom subset_by_notin : forall E F,
  (forall x, x \notin F -> x \notin E) ->
  E << F.
(* TODO: il faudrait mettre mem dans bool ! 
  Proof.
  introv H IE. unfolds notin. autos*.
*)