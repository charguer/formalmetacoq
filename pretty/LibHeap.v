(************************************************************
* Heaps: finite maps from keys to values                    *
*************************************************************)

(** This file aims to provide an executable implementation of finite
    maps, implemented as lists.

    LibHeap is similar to LibEnv, but LibEnv is specialized for keys
    that are variables, whereas LibHeap is typically instantiated with
    locations (natural numbers) as keys.

    For a non-executable yet more complete module for representing
    finite maps, consider using TLC's LibMap module (designed using
    typeclasses) or the LibSepFmap module used in the CFML tool and
    in the course "Separation Logic Foundations". *)

Set Implicit Arguments.
From TLC Require Import LibTactics LibReflect LibList LibListAssoc
  LibSet LibListExec LibVar.
Generalizable Variable K V.


(* ********************************************************************** *)
(** * Decidable predicates *)

(** [Decidable P] asserts that there exists a boolean
    value indicating whether [P] is true. The definition
    is interesting when this boolean is computable and
    can lead to code extraction. *)

Class Decidable (P:Prop) := decidable_make {
  decide : bool;
  decide_spec : decide = isTrue P }.

Arguments decide P {Decidable}.

(** The tactic [rew_bool_eq], used by [case_if], is extended
    with support for [decide] *)

Hint Rewrite (@decide_spec) : rew_bool_eq.

(** The notation [ifb P then x else y] can be used for
    testing a proposition [P] for which there exists an
    instance of [Decidable P]. *)

Notation "'ifb' P 'then' v1 'else' v2" :=
  (if decide P then v1 else v2)
  (at level 200, right associativity) : type_scope.


(* ********************************************************************** *)
(** * Comparable types *)

(** [Comparable A] asserts that there exists a decidable
    equality over values of type [A] *)

Class Comparable (A:Type) := make_comparable {
  comparable : forall (x y:A), Decidable (x = y) }.

Hint Resolve comparable : typeclass_instances.

(** [Comparable] can be proved by exhibiting a boolean
    comparison function *)

Lemma comparable_beq : forall A (f:A->A->bool),
  (forall x y, (istrue (f x y)) <-> (x = y)) ->
  Comparable A.
Proof using.
  introv H. constructors. intros.
  applys decidable_make (f x y).
  extens. rewrite H. rew_bool_eq*.
Qed.

(** [Comparable] can be proved by exhibiting a decidability
    result in the form of a strong sum *)

Lemma dec_to_comparable : forall (A:Type),
  (forall x y : A, {x = y} + {x <> y}) ->
  Comparable A.
Proof using.
  introv H. constructors. intros.
  applys decidable_make (if H x y then true else false).
  case_if; rew_bool_eq*.
Qed.

(** Comparison for bool *)

Global Instance comparable_bool : Comparable bool.
Proof using.
  applys (comparable_beq Bool.eqb).
  destruct x; destruct y; simpl; rew_bool_eq; auto_false*.
Qed.

(** Comparison for nat *)

Global Instance comparable_nat : Comparable nat.
Proof using.
  applys (comparable_beq Nat.eqb).
  intros x. induction x; intros y; destruct y; simpl; rew_bool_eq; auto_false*.
  rewrite IHx. iff M. { auto. } { inverts* M. }
Qed.

(** Comparison for var *)

Global Instance comparable_var : Comparable var.
Proof using.
  applys (comparable_beq var_compare). intros.
  rewrite var_compare_eq. rew_bool_eq*.
Qed.


(***********************************************************)
(***********************************************************)
(***********************************************************)
(* Abstract interface of a heap *)

Module Type HeapSpec.

(** Abstract Type *)

Parameter heap : Type -> Type -> Type.

(** Required operations *)

Section HeapDef.
Parameter empty : forall K V, heap K V.
Parameter write : forall K V, heap K V -> K -> V -> heap K V.
Parameter rem : forall K `{Comparable K} V, heap K V -> K -> heap K V.
Parameter read_opt : forall K `{Comparable K} V, heap K V -> K -> option V.
End HeapDef.

(** Required properties *)

Section HeapProp.
Context (K:Type) (HK:Comparable K) (V:Type).
Implicit Types k : K.
Implicit Types v : V.
Implicit Types h : heap K V.

Parameter read_opt_empty : forall k,
  read_opt (@empty K V) k = None.

Parameter read_opt_write : forall k k' v h,
  read_opt (write h k' v) k = ifb k = k' then Some v else read_opt h k.

Parameter read_opt_rem : forall k k' h,
  read_opt (rem h k') k = ifb k = k' then None else read_opt h k.

End HeapProp.

End HeapSpec.


(***********************************************************)
(***********************************************************)
(***********************************************************)
(** Implementation of heaps as lists *)

Lemma filter_eq' : forall A (P:A->Prop) (p:A->bool) l,
  isTrue_pred p P ->
  filter p l = LibList.filter P l.
Proof using. intros. applys* filter_eq. Qed.

Module Export HeapImpl : HeapSpec.

(** Realize Type *)

Definition heap K V := list (K*V).

(** Realize operations *)

Section HeapDef.
Context `{Comparable K} (V : Type).
Implicit Types k : K.
Implicit Types v : V.
Implicit Types h : heap K V.

Definition empty : heap K V :=
  nil.

Definition write h k v :=
  (k, v) :: h.

Definition rem h k :=
  LibListExec.filter (fun '(k',v) => ! (decide (k' = k))) h.

Fixpoint read_opt h k :=
  match h with
  | nil => None
  | (k', v) :: h' => ifb k = k' then Some v else read_opt h' k
  end.

End HeapDef.

(** Realize properties *)

Section HeapProp.
Context (K:Type) (HK:Comparable K) (V:Type).
Implicit Types k : K.
Implicit Types v : V.
Implicit Types h : heap K V.

Lemma read_opt_empty : forall k,
  read_opt (@empty K V) k = None.
Proof using. auto. Qed.

Lemma read_opt_write : forall k k' v h,
  read_opt (write h k' v) k = ifb k = k' then Some v else read_opt h k.
Proof using. auto. Qed.

Lemma rem_eq_filter : forall h k,
  rem h k = LibList.filter (fun '(k',v) => k' <> k) h.
Proof using.
  intros. unfold rem. rewrite (@filter_eq' _ (fun (kvi:K*V) => fst kvi <> k)).
  { fequal. extens. intros (ki,vi). simple*. }
  { intros (ki,vi). simpl. rewrite decide_spec. rewrite* isTrue_not. }
Qed.

Lemma read_opt_rem : forall k k' h,
  read_opt (rem h k') k = ifb k = k' then None else read_opt h k.
Proof using HK.
  intros. rewrite rem_eq_filter. case_if.
  { induction h as [|[ki vi] h']; rew_listx.
    { auto. }
    { case_if*. { simpl. case_if*. } } }
  { induction h as [|[ki vi] h']; rew_listx.
    { auto. }
    { simpl. case_if. { simpl. case_if*. } { case_if*. } } }
Qed.

End HeapProp.

End HeapImpl.


(***********************************************************)
(***********************************************************)
(***********************************************************)
(** Derived properties of any heap implementation *)

Module Heap.
Include HeapImpl.

(** Additional operators *)

Section HeapMoreDef.
Context `{Comparable K} (V : Type).
Implicit Types k : K.
Implicit Types v : V.
Implicit Types h : heap K V.

Definition indom_dec h k :=
  match read_opt h k with
  | None => false
  | Some v => true
  end.

Definition indom h k :=
  match read_opt h k with
  | None => False
  | Some v => True
  end.

Definition read `{Inhab V} h k :=
  match read_opt h k with
  | None => arbitrary
  | Some v => v
  end.

Definition binds h k v :=
  match read_opt h k with
  | None => False
  | Some v' => (v = v')
  end.

End HeapMoreDef.

(** Properties of additional operators *)

Section HeapMoreProp.
Context (K:Type) (HK:Comparable K) (V:Type) (IV:Inhab V).
Implicit Types k : K.
Implicit Types v : V.
Implicit Types h : heap K V.

(** Properties of [indom] on [empty] *)

Lemma not_indom_empty : forall k,
  ~ indom (@empty K V) k.
Proof using. intros. unfold indom. rewrite* read_opt_empty. Qed.

(** Properties of [indom] on [write] *)

Lemma indom_write_eq : forall k k' v h,
  indom (write h k' v) k = ((k = k') \/ indom h k).
Proof using HK IV. (*  why using IV? *)
  intros. extens. unfold indom. rewrite read_opt_write.
  destruct (read_opt h k); case_if; case_if; rew_bool_eq in *; subst*.
Qed.

Lemma indom_write_same : forall h k v,
  indom (write h k v) k.
Proof using HK IV. intros. rewrite* indom_write_eq. Qed.

Lemma indom_write : forall h k k' v',
  indom h k ->
  indom (write h k' v') k.
Proof using HK IV. intros. rewrite* indom_write_eq. Qed.

Lemma indom_write_inv_neq : forall h k k' v',
  indom (write h k' v') k ->
  k <> k' ->
  indom h k.
Proof using HK IV. introv M N. rewrite* indom_write_eq in M. Qed.

(** Properties of [indom] on [rem] *)

Lemma indom_rem_eq : forall k k' h,
  indom (rem h k') k = ((k <> k') /\ indom h k).
Proof using HK IV.
  intros. extens. unfold indom. rewrite read_opt_rem.
  destruct (read_opt h k); case_if; case_if; rew_bool_eq in *; subst*.
Qed.

Lemma indom_rem : forall h k k',
  indom h k ->
  k <> k' ->
  indom (rem h k') k.
Proof using HK IV. intros. rewrite* indom_rem_eq. Qed.

Lemma indom_rem_inv : forall h k k',
  indom (rem h k) k' ->
  k <> k' /\ indom h k'.
Proof using HK IV. introv M. rewrite* indom_rem_eq in M. Qed.

Lemma not_indom_rem : forall h k,
  ~ indom (rem h k) k.
Proof using HK IV. intros. rewrite* indom_rem_eq. Qed.


(** Properties of [indom] on [decide] *)

Global Instance indom_decidable : forall `{Comparable K} V (h:heap K V) k,
  Decidable (indom h k).
Proof using HK.
  intros. applys decidable_make (indom_dec h k). unfold indom_dec, indom.
  destruct (read_opt h k); rew_bool_eq*.
Qed.

(** Properties of [read] on [write] *)

Lemma read_write : forall k k' v h,
  indom h k ->
  read (write h k' v) k = If (k = k') then v else read h k.
Proof using HK IV.
  introv _. unfold read. rewrite read_opt_write. repeat case_if*.
Qed.

Lemma read_write_same : forall h k v,
  indom h k ->
  read (write h k v) k = v.
Proof using HK IV. intros. rewrite* read_write. case_if*. Qed.

Lemma read_write_neq : forall h k k' v,
  indom h k ->
  k <> k' ->
  read (write h k' v) k = read h k.
Proof using HK IV. intros. rewrite* read_write. case_if*. Qed.

(** Properties of [read] on [rem] *)

Lemma read_rem : forall k k' h,
  indom h k ->
  k <> k' ->
  read (rem h k') k = read h k.
Proof using HK.
  intros. unfold read. rewrite read_opt_rem. case_if*.
Qed.

(** Properties of [binds]: functional *)

Lemma binds_functional : forall h k v v',
  binds h k v ->
  binds h k v' ->
  v = v'.
Proof using.
  introv M1 M2. unfold binds in *. destruct (read_opt h k); subst*.
Qed.

(** Properties of [binds] on [indom] *)

Lemma indom_eq_exists_binds : forall h k,
  indom h k = (exists v, binds h k v).
Proof using.
  intros. extens. unfold indom, binds. destruct (read_opt h k).
  { autos*. } { iff ? (?&?); false. }
Qed.

Lemma indom_inv_binds : forall h k,
  indom h k ->
  exists v, binds h k v.
Proof using. introv M. rewrite* indom_eq_exists_binds in M. Qed.

Lemma binds_indom : forall h k v,
  binds h k v ->
  indom h k.
Proof using. introv H. rewrite* indom_eq_exists_binds. Qed.

(** Properties of [binds] on [read_opt] *)

Lemma binds_eq_read_opt : forall h k v,
  binds h k v = (read_opt h k = Some v).
Proof using.
  intros. extens. unfold binds, read. destruct (read_opt h k).
  { iff M. { subst*. } { inverts* M. } }
  { iff; false. }
Qed.

Lemma binds_inv_read_opt : forall h k v,
  binds h k v ->
  read_opt h k = Some v.
Proof using. introv M. rewrite* binds_eq_read_opt in M. Qed.

Lemma binds_of_read_opt : forall h k v,
  read_opt h k = Some v ->
  binds h k v.
Proof using. intros. rewrite* binds_eq_read_opt. Qed.

Lemma not_binds_of_read_opt : forall h k,
  read_opt h k = None ->
  forall v, ~ binds h k v.
Proof using. introv E. intros. rewrite* binds_eq_read_opt. rewrite E; auto_false. Qed.

(** Properties of [binds] on [read] *)

Lemma binds_eq_indom_read : forall h k v,
  binds h k v = (indom h k /\ read h k = v).
Proof using. intros. extens. unfold binds, read, indom. destruct* (read_opt h k). Qed.

Lemma binds_eq_read_of_indom : forall h k,
  indom h k ->
  (forall v, (binds h k v) = (read h k = v)).
Proof using. introv M. extens. rewrite* binds_eq_indom_read. Qed.

Lemma binds_inv_read : forall h k v,
  binds h k v ->
  read h k = v.
Proof using. introv M. rewrite* binds_eq_indom_read in M. Qed.

Lemma binds_of_read_indom : forall h k v,
  read h k = v ->
  indom h k ->
  binds h k v.
Proof using. intros. rewrite* binds_eq_indom_read. Qed.

(** Properties of [binds] on [empty] *)

Lemma not_binds_empty : forall k v,
  ~ binds (@empty K V) k v.
Proof using. intros. unfold binds. rewrite* read_opt_empty. Qed.

(** Properties of [binds] on [write] *)

Lemma binds_write_eq : forall h k v k' v',
    binds (write h k' v') k v
  = If k = k' then v = v' else binds h k v.
Proof using. intros. unfold binds. rewrite* read_opt_write. repeat case_if*. Qed.

Lemma binds_write_same : forall k v h,
  binds (write h k v) k v.
Proof using. intros. rewrite binds_write_eq. case_if*. Qed.

Lemma binds_write_neq : forall h k v k' v',
  binds h k v ->
  k <> k' ->
  binds (write h k' v') k v.
Proof using. intros. rewrite binds_write_eq. case_if*. Qed.

Lemma binds_write_same_inv : forall h k v v',
  binds (write h k v') k v ->
  v = v'.
Proof using. introv M. rewrite binds_write_eq in M. case_if*. Qed.

Lemma binds_write_neq_inv : forall h k k' v v',
  binds (write h k' v') k v ->
  k <> k' ->
  binds h k v.
Proof using. introv M N. rewrite binds_write_eq in M. case_if*. Qed.

(** Properties of [binds] on [rem] *)

Lemma binds_rem_eq : forall h k k' v,
    binds (rem h k') k v
  = (k <> k' /\ binds h k v).
Proof using.
  intros. extens. unfold binds. rewrite* read_opt_rem. repeat case_if*.
Qed.

Lemma not_binds_rem_same : forall h k v,
  ~ binds (rem h k) k v.
Proof using. intros. rewrite binds_rem_eq. rew_logic*. Qed.

Lemma binds_rem : forall h k k' v,
  binds h k v ->
  k <> k' ->
  binds (rem h k') k v.
Proof using. intros. rewrite* binds_rem_eq. Qed.

Lemma binds_rem_inv : forall h k k' v,
  binds (rem h k') k v ->
  k <> k' /\ binds h k v.
Proof using. introv M. rewrite* binds_rem_eq in M. Qed.

End HeapMoreProp.


End Heap.
