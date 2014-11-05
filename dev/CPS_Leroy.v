(* CPS transformation *)

Definition var: Set := nat.

Lemma var_eq: forall (v1 v2: var), {v1=v2} + {v1<>v2}.
Proof.
  decide equality.
Qed.

Lemma var_eq_true:
  forall (A: Set) (a1 a2: A) (x: var),
  (if var_eq x x then a1 else a2) = a1.
Proof.
  intros. destruct (var_eq x x); congruence.
Qed.

Lemma var_eq_false:
  forall (A: Set) (a1 a2: A) (x y: var),
  x <> y -> (if var_eq x y then a1 else a2) = a2.
Proof.
  intros. destruct (var_eq x y); congruence.
Qed.

Parameter const: Set.
Parameters zero one: const.

Inductive term: Set :=
  | Var: var -> term
  | Const: const -> term
  | Fun: var -> term -> term
  | App: term -> term -> term.

Fixpoint subst (x: var) (b: term) (a: term) {struct a}: term :=
  match a with
  | Var y => if var_eq x y then b else Var y
  | Const n => Const n
  | Fun y a1 => Fun y (if var_eq x y then a1 else subst x b a1)
  | App a1 a2 => App (subst x b a1) (subst x b a2)
  end.

Inductive isvalue: term -> Prop :=
  | isvalue_const: forall c,
      isvalue (Const c)
  | isvalue_fun: forall x a,
      isvalue (Fun x a).

(** Big-step semantics **)

Inductive eval: term -> term -> Prop :=
  | eval_const: forall c,
      eval (Const c) (Const c)
  | eval_fun: forall x a,
      eval (Fun x a) (Fun x a)
  | eval_app: forall a b x c vb v,
      eval a (Fun x c) ->
      eval b vb ->
      eval (subst x vb c) v ->
      eval (App a b) v.

Lemma eval_isvalue:
  forall a b, eval a b -> isvalue b.
Proof.
  induction 1; intros.
  constructor.
  constructor.
  auto.
Qed.

Lemma eval_value:
  forall v, isvalue v -> eval v v.
Proof.
  induction 1; constructor.
Qed.

Lemma eval_value_only:
  forall v, isvalue v -> forall v', eval v v' -> v' = v.
Proof.
  induction 1; intros; inversion H; auto.
Qed.

Fixpoint notfree (x: var) (a: term) {struct a} : Prop :=
  match a with
  | Var y => x <> y
  | Const _ => True
  | Fun y b => x = y \/ notfree x b
  | App b c => notfree x b /\ notfree x c
  end.

Lemma subst_notfree:
  forall x v a, notfree x a -> subst x v a = a.
Proof.
  induction a; simpl; intros.
  apply var_eq_false; auto. 
  auto.
  destruct (var_eq x v0). auto.
  rewrite IHa. auto. tauto.
  rewrite IHa1. rewrite IHa2. auto. tauto. tauto.
Qed.

Require Omega.

(** CPS transformation *)

Definition evar (x: var) : var := x + 3.
Definition vk : var := 0.
Definition v1 : var := 1.
Definition v2 : var := 2.
Definition istemp (x: var) : Prop := x < 3.
Remark istemp_vk: istemp vk.
Proof. unfold istemp, vk; omega. Qed.
Remark istemp_v1: istemp v1.
Proof. unfold istemp, v1; omega. Qed.
Remark istemp_v2: istemp v2.
Proof. unfold istemp, v2; omega. Qed.
Remark evar_nottemp: forall x t, istemp t -> evar x <> t.
Proof. unfold istemp, evar, var; intros; omega. Qed.

Fixpoint cps (a: term) : term :=
  match a with
  | Var v =>
      Fun vk (App (Var vk) (Var (evar v)))
  | Const n =>
      Fun vk (App (Var vk) (Const n))
  | Fun x b =>
      Fun vk (App (Var vk) (Fun (evar x) (cps b)))
  | App b c =>
      Fun vk (App (cps b)
                  (Fun v1 (App (cps c)
                               (Fun v2 (App (App (Var v1) (Var v2)) (Var vk))))))
  end.

Definition cps_value (v: term) : term :=
  match v with
  | Const n => Const n
  | Fun x b => Fun (evar x) (cps b)
  | _ => Const zero (* never happens *)
  end.

Lemma cps_of_value:
  forall v, isvalue v -> cps v = Fun vk (App (Var vk) (cps_value v)).
Proof.
  induction 1; intros; reflexivity.
Qed.

Ltac var_diff :=
  unfold evar, vk, v1, v2; omega.

Lemma cps_temp_not_free:
  forall t, istemp t -> forall a, notfree t (cps a).
Proof.
  induction a; simpl.
  destruct (var_eq t vk). auto. right. split. auto. 
  apply sym_not_equal. apply evar_nottemp; auto.

  destruct (var_eq t vk); tauto.

  destruct (var_eq t vk); tauto.

  destruct (var_eq t vk). auto. right.
  split. auto. 
  destruct (var_eq t v1). auto. right.
  split. auto. 
  destruct (var_eq t v2); tauto.
Qed.

Lemma cps_subst_temp:
  forall t v a, istemp t -> subst t v (cps a) = cps a.
Proof.
  intros. apply subst_notfree. apply cps_temp_not_free; auto.
Qed.

Lemma var_eq_evar_vk:
  forall (A: Set) (x: var) (a1 a2: A),
  (if var_eq (evar x) vk then a1 else a2) = a2.
Proof.
  intros. apply var_eq_false. apply evar_nottemp. apply istemp_vk.
Qed.

Lemma var_eq_evar_v1:
  forall (A: Set) (x: var) (a1 a2: A),
  (if var_eq (evar x) v1 then a1 else a2) = a2.
Proof.
  intros. apply var_eq_false. apply evar_nottemp. apply istemp_v1.
Qed.

Lemma var_eq_evar_v2:
  forall (A: Set) (x: var) (a1 a2: A),
  (if var_eq (evar x) v2 then a1 else a2) = a2.
Proof.
  intros. apply var_eq_false. apply evar_nottemp. apply istemp_v2.
Qed.

Lemma cps_subst_evar: 
  forall x v, isvalue v ->
  forall a,
  subst (evar x) (cps_value v) (cps a) = cps (subst x v a).
Proof.
  induction a; simpl;
  repeat rewrite var_eq_evar_vk;
  repeat rewrite var_eq_evar_v1;
  repeat rewrite var_eq_evar_v2.

  destruct (var_eq x v0).
  subst v0; rewrite var_eq_true. symmetry; apply cps_of_value; auto.
  rewrite var_eq_false. reflexivity. 
  unfold evar; unfold var in *; omega.

  reflexivity.

  destruct (var_eq x v0).
  subst v0; rewrite var_eq_true. auto.
  rewrite var_eq_false. rewrite IHa. reflexivity. 
  unfold evar; unfold var in *; omega.

  rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Lemma cps_value_isvalue:
  forall v, isvalue (cps_value v).
Proof.
  intros. destruct v; simpl; constructor.
Qed.

Definition no_temp_free (k: term) : Prop :=
  forall t, istemp t -> notfree t k.

Lemma cps_correct_rec:
  forall a v, eval a v ->
  forall k r, isvalue k -> no_temp_free k ->
  eval (App k (cps_value v)) r -> eval (App (cps a) k) r.
Proof.
  induction 1; simpl; intros.

  econstructor. constructor. apply eval_value; auto. 
  simpl. rewrite var_eq_true. assumption.

  econstructor. constructor. apply eval_value; auto.
  simpl. rewrite var_eq_true. rewrite var_eq_false. 
  rewrite cps_subst_temp. auto. apply istemp_vk. 
  unfold vk, evar; omega. 

  generalize (IHeval3 _ _ H2 H3 H4); intro. 
  inversion H5; clear H5; subst.
  assert (vb0 = k). eapply eval_value_only; eauto. subst vb0.  
  
  econstructor. constructor. apply eval_value; auto.
  simpl. rewrite var_eq_true. 
  repeat rewrite var_eq_false; try var_diff.
  repeat rewrite cps_subst_temp; try apply istemp_vk.

  apply IHeval1. constructor. 
  red; intros; simpl. 
  destruct (var_eq t v1); auto; right; split.
  apply cps_temp_not_free; auto. 
  destruct (var_eq t v2); auto.

  econstructor. constructor. apply eval_value. apply cps_value_isvalue.
  simpl. rewrite var_eq_true. repeat rewrite var_eq_false; try var_diff.
  rewrite cps_subst_temp. 2: apply istemp_v1. 
  rewrite subst_notfree. 2: apply H3; apply istemp_v1. 

  apply IHeval2. constructor.
  red; intros; simpl. 
  destruct (var_eq t v2); auto; right; split.
  split. right. apply cps_temp_not_free; auto. auto.
  apply H3; auto.

  econstructor. constructor. apply eval_value. apply cps_value_isvalue.
  simpl. rewrite var_eq_true. rewrite var_eq_false. 2: var_diff. 
  econstructor. econstructor. constructor. apply eval_value. apply cps_value_isvalue.
  rewrite cps_subst_temp. 2: apply istemp_v2. 
  rewrite cps_subst_evar. 2: eapply eval_isvalue; eauto. 
  eassumption. 
  rewrite subst_notfree. eassumption. apply H3. apply istemp_v2.
  auto.
Qed.

Lemma cps_correct:
  forall a v, eval a v -> eval (App (cps a) (Fun vk (Var vk))) (cps_value v).
Proof.
  intros. apply cps_correct_rec with v. auto. constructor. 
  red. intros. simpl. destruct (var_eq t vk); auto. 
  econstructor. constructor. apply eval_value. apply cps_value_isvalue. 
  simpl. rewrite var_eq_true. apply eval_value. apply cps_value_isvalue.
Qed.
