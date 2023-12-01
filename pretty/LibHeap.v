(************************************************************
* Heaps: finite maps from keys to values                    *
*************************************************************)

(** This file aims to provide what would be a TLC LibMapExec library,
    that is, a counterpart to LibMap with executable implementation.
    LibHeap is similar to LibEnv, but LibEnv is specialized for keys
    that are variables, whereas LibHeap is typically instantiated with
    locations (natural numbers) as keys. *)

Set Implicit Arguments.
From TLC Require Import LibTactics LibReflect LibList LibListAssoc
  LibSet LibListExec.
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

Hint Rewrite @decide_spec : rew_refl.
Arguments decide P {Decidable}.

(** Notation [ifb P then x else y] can be used for
    testing a proposition [P] for which there exists an
    instance of [Decidable P]. *)

Notation "'ifb' P 'then' v1 'else' v2" :=
  (if decide P then v1 else v2)
  (at level 200, right associativity) : type_scope.

(** In classical logic, any proposition is decidable; of course,
    we do not want to use this lemma as an instance because
    it cannot be extracted to executable code. *)

Lemma prop_decidable : forall (P:Prop), Decidable P.
Proof using. intros. applys~ decidable_make (isTrue P). Qed.

(** In constructive logic, any proposition with a proof of
    that is constructively true or false is decidable. *)

Definition sumbool_decidable : forall (P:Prop),
  {P}+{~P} -> Decidable P.
Proof using.
  introv H. applys decidable_make
    (match H with left _ => true | right _ => false end).
  destruct H; rew_bool_eq~.
Defined.

(*

Definition decidable_sumbool : forall P : Prop,
    Decidable P -> {P}+{~P}.
Proof using.
  introv D. destruct (decide P) eqn: H. rew_bool_eq in H; [left*|right*].

Defined.

(** [sumbool_decidable] and [decidable_sumbool] just wrap their
    property as expected. *)

Lemma sumbool_decidable_decidable_sumbool : forall P (d : {P}+{~P}),
  decidable_sumbool (sumbool_decidable d) = d.
Proof using.
  introv. unfolds.
  asserts R1: (forall (d : bool) B C C1 C2,
    d ->
    (if d as b return (d = b -> B) then
      fun H => C1 H
    else fun H => C2 H) eq_refl = C ->
    exists E, C1 E = C).
   clear. introv D Eq. destruct d; tryfalse. eexists. apply Eq.
  lets R1': (rm R1) (@decide P (sumbool_decidable d)).
  asserts R2: (forall (d : bool) B C C1 C2,
    !d ->
    (if d as b return (d = b -> B) then
      fun H => C1 H
    else fun H => C2 H) eq_refl = C ->
    exists E, C2 E = C).
   clear. introv D Eq. destruct d; tryfalse. eexists. apply Eq.
  lets R2': (rm R2) (@decide P (sumbool_decidable d)).
  unfold sumbool_decidable. case_if as I.
   forwards (E&Eq): R1'.
     rewrite decide_spec. rew_refl*.
     reflexivity.
    rewrite <- Eq. fequals.
   forwards (E&Eq): R2'.
     rewrite decide_spec. rew_refl*.
     reflexivity.
    rewrite <- Eq. fequals.
Qed.


Global Instance Decidable_impl : forall A B : Prop,
    Decidable A -> Decidable B -> Decidable (A -> B).
  introv (da&Ha) (db&Hb).
  destruct da; destruct db; fold_bool; rew_refl in *;
    ((apply decidable_make with true; solve [ fold_bool; rew_refl* ]) ||
     (apply decidable_make with false; solve [ fold_bool; rew_refl* ])).
Defined.

Global Instance Decidable_equiv : forall A B : Prop,
    (A <-> B) -> Decidable A -> Decidable B.
  introv E. apply prop_ext in E. substs~.
Defined.

(** Extending the [case_if] tactic to support [if decide] *)

Lemma Decidable_dec : forall (P:Prop) {H: Decidable P} (A:Type) (x y:A),
  exists (Q : {P}+{~P}),
  (if decide P then x else y) = (if Q then x else y).
Proof using.
  intros. exists (classicT P).
  rewrite decide_spec.
  tautotest P; case_if as C; case_if as C';
  first [ rewrite isTrue_True in C
        | rewrite isTrue_False in C
        | idtac ]; autos*; false*.
Qed.

Ltac case_if_on_tactic_core E Eq ::=
  match E with
  | @decide ?P ?M =>
      let Q := fresh in let Eq := fresh in
      forwards (Q&Eq): (@Decidable_dec P M);
      rewrite Eq in *; clear Eq; destruct Q
  | _ =>
    match type of E with
    | {_}+{_} => destruct E as [Eq|Eq]; try subst_hyp Eq
    | _ => let X := fresh in
           sets_eq <- X Eq: E;
           destruct X
    end
  end.

(** Rewriting lemma *)

Lemma istrue_decide : forall `{Decidable P},
  istrue (decide P) = P.
Proof using. intros. rew_refl~. Qed.

Lemma decide_prove : forall `{Decidable P},
  P -> istrue (decide P).
Proof using. intros. rewrite~ istrue_decide. Qed.

Lemma decide_def : forall `{Decidable P},
  (decide P) = (If P then true else false).
Proof using. intros. rewrite decide_spec. rewrite isTrue_to_if. case_if*. Qed.

Lemma decide_cases : forall `{Decidable P},
  (P /\ decide P = true) \/ (~ P /\ decide P = false).
Proof using. intros. rewrite decide_spec. rewrite isTrue_to_if. case_if*. Qed.

(** Dedicability instances *)

Global Instance true_decidable : Decidable True.
Proof using. applys decidable_make true. rew_refl~. Qed.

Global Instance false_decidable : Decidable False.
Proof using. applys decidable_make false. rew_refl~. Qed.

Global Instance bool_decidable : forall (b : bool), Decidable (b).
Proof using. introv. applys (@decidable_make (istrue b) b). rew_refl~. Qed.

Global Instance not_decidable : forall (P : Prop),
  Decidable P -> Decidable (~ P).
Proof using.
  (* --TODO: cleanup proof *)
  introv [dec spec]. applys decidable_make (neg dec).
  rew_refl. rewrite~ spec.
Qed.

Global Instance or_decidable : forall (P Q : Prop),
  Decidable P -> Decidable Q ->
  Decidable (P \/ Q).
Proof using.
  intros. applys decidable_make (decide P || decide Q).
  rew_refl. subst~.
Qed.

Global Instance and_decidable : forall P Q,
  Decidable P -> Decidable Q ->
  Decidable (P /\ Q).
Proof using.
  intros. applys decidable_make (decide P && decide Q).
  rew_refl. subst~.
Qed.

Global Instance If_dec : forall P Q R,
  Decidable P -> Decidable Q -> Decidable R ->
  Decidable (If P then Q else R).
Proof using.
  intros. applys decidable_make (if decide P then decide Q else decide R).
  rew_refl. subst~.
Qed.

*)


(* ********************************************************************** *)
(** * Comparable types *)

(** [Comparable A] asserts that there exists a decidable
    equality over values of type [A] *)

Class Comparable (A:Type) := make_comparable {
  comparable : forall (x y:A), Decidable (x = y) }.

Hint Resolve comparable : typeclass_instances.

(** In classical logic, any type is comparable; of course,
    we do not want to use this lemma as an instance because
    it cannot be extracted to executable code. *)

Lemma type_comparable : forall (A:Type), Comparable A.
Proof using. constructor. intros. applys~ prop_decidable. Qed.

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

(** Comparison for booleans *)

Instance bool_comparable : Comparable bool.
Proof using.
  applys (comparable_beq Bool.eqb).
  destruct x; destruct y; simpl; rew_bool_eq; auto_false*.
Qed.

(*
Global Instance prop_eq_decidable : forall P Q,
  Decidable P -> Decidable Q ->
  Decidable (P = Q).
Proof using.
  intros. applys decidable_make (decide (decide P = decide Q)).
  extens. rew_bool_eq in *.
  iff E.
    do 2 rewrite isTrue_to_if in E.
     extens. case_if; case_if; auto_false*.
    subst*.
Qed.
*)



(***********************************************************)
(***********************************************************)
(***********************************************************)
(* Abstract interface of a heap *)

Module Type HeapSpec.

(** Abstract Type *)

Parameter heap : Type -> Type -> Type.

(** Required operations *)

Section HeapDef.
Variables K V : Type.
Parameter empty : heap K V.
Parameter write : heap K V -> K -> V -> heap K V.
Parameter rem : forall `{Comparable K} V, heap K V -> K -> heap K V.
Parameter read_opt : forall `{Comparable K} V, heap K V -> K -> option V.
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

Parameter read_opt_rem : forall k k' v h,
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

Module HeapList : HeapSpec.

(** Realize Type *)

Definition heap K V := list (K*V).

(** Realize operations *)

Section HeapDef.
Variables K V : Type.
Implicit Types k : K.
Implicit Types v : V.
Implicit Types h : heap K V.

Definition empty : heap K V :=
  nil.

Definition write h k v :=
  (k, v) :: h.

Definition rem `{Comparable K} h k :=
  LibListExec.filter (fun '(k',v) => ! (decide (k' = k))) h.

Fixpoint read_opt `{Comparable K} h k :=
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

Hint Rewrite (@decide_spec) : rew_bool_eq.

Lemma read_opt_rem : forall k k' v h,
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

End HeapList.






(***********************************************************)
(***********************************************************)
(***********************************************************)
(* Note: move to LibListAssocExec *)

Generalizable Variable A B.

Fixpoint assoc `{Comparable A} `{Inhab B} k (l:list (A*B)) : B :=
  match l with
  | nil => arbitrary
  | (x, v) :: l' => ifb x = k then v else assoc k l'
  end.


Module HeapList : HeapSpec.

Definition heap K V := list (K*V).

Section HeapDefs.
Context `{Comparable K} `{Inhab V}.
Implicit Types h : heap K V.

Definition empty : heap K V := nil.

Definition dom h : set K :=
  fold_right (fun p acc => acc \u \{fst p}) \{} h.

Definition binds h k v :=
  Assoc k v h.

Definition to_list h :=
  h.

Definition read h k :=
  assoc k h.

Definition write h k v :=
  (k, v) :: h.

Definition rem K `{Comparable K} V (h : heap K V) k :=
  LibList.filter (fun p => ifb (fst p) = k then false else true) h.

Definition indom h r :=
  List.Exists (fun '(k,v) => k = r) h.
  (*(r \in dom h).*)

Fixpoint read_opt (h : heap K V) k :=
  match l with
  | nil => None
  | (x, v) :: h' => ifb x = k then Some v else read_opt h' k
  end.

End HeapDefs.

Arguments empty {K} {V}.

Generalizable Variable A.

Fixpoint mem_assoc B `{Comparable A} k (l : list (A * B)) : bool :=
  match l with
  | nil => false
  | (x, _) :: l' => decide (x = k) || mem_assoc k l'
  end.

Definition indom_dec `{Comparable K} V (h:heap K V) (k:K) : bool :=
  mem_assoc k h.

(** Properties *)

Section HeapParameters.
Context (K:Type) (HK: Comparable K) (V:Type) (IV: Inhab V).
Implicit Types h : heap K V.

Lemma dom_empty :
  dom (@empty K V) = \{}.
Proof using. auto. Qed.

Lemma dom_write : forall h r v,
  dom (write h r v) = dom h \u \{r}.
Proof. intros. unfold dom, write. rew_list. auto. Qed.

Lemma indom_equiv_binds : forall h k,
  indom h k = (exists v, binds h k v).
Proof using.
  intros. unfold indom, binds, dom.
Admitted.

(r \in dom h)

Lemma binds_equiv_read : forall h k,
  indom h k -> (forall v, (binds h k v) = (read h k = v)).
Proof using HK IV.
Admitted. (* File will be soon deprecated *)

Arguments binds_equiv_read : clear implicits.


Lemma binds_write_eq : forall h k v,
  binds (write h k v) k v.
Proof. unfolds @binds, @write. intros. constructors. Qed.

Lemma binds_write_neq : forall h k v k' v',
  binds h k v -> k <> k' ->
  binds (write h k' v') k v.
Proof. unfolds @binds, @write. intros. constructors~. Qed.

Lemma binds_write_inv : forall h k v k' v',
  binds (write h k' v') k v ->
  (k = k' /\ v = v') \/ (k <> k' /\ binds h k v).
Proof. unfolds @binds, @write. introv M. inverts* M. Qed.

Lemma binds_rem : forall h k k' v,
  binds h k v -> k <> k' -> binds (rem h k') k v.
Proof using HK.
Admitted. (* File will be soon deprecated *)

Lemma binds_rem_inv : forall h k v k',
  binds (rem h k') k v -> k <> k' /\ binds h k v.
Proof using HK.
Admitted. (* File will be soon deprecated *)


Lemma not_indom_rem : forall h k,
  ~ indom (rem h k) k.
Proof using HK.
Admitted. (* File will be soon deprecated *)


Lemma binds_equiv_read_opt : forall h k v,
  (binds h k v) = (read_opt h k = Some v).
Admitted. (* File will be soon deprecated *)

(*
Proof using. clear IV.
  unfolds @binds. introv. extens.
  induction h as [|(x&v0)].
   splits ; intro N ; invert* N.
   simpl. case_if.
     subst. splits ; intro N ; inverts* N. constructors.
     splits ; intro N.
      inverts* N.
      constructors*.
Qed.
*)

Lemma not_indom_equiv_read_opt : forall h k,
  (~ indom h k) = (read_opt h k = None).
Proof using IV.
Admitted. (* File will be soon deprecated *)
(*
  introv. apply* injective_not. rew_logic. rewrite indom_equiv_binds.
  splits ; intro N.
   lets (v & B): rm N.
    rewrite binds_equiv_read_opt in B. rewrite* B. discriminate.
   asserts (v & E): (exists v, read_opt h k = Some v).
     destruct* @read_opt.
    rewrite* <- binds_equiv_read_opt in E.
Qed.
*)

Lemma read_opt_def : forall h k,
  read_opt h k = (If indom h k then Some (read h k) else None).
Proof using.
(* --TODO
  introv. cases_if.
   rewrite* <- binds_equiv_read_opt.
    rewrites* binds_equiv_read.
   rewrite* <- @not_indom_equiv_read_opt.
*)
Admitted. (* File will be soon deprecated *)

(* --TODO: move *)



Lemma indom_dec_spec : forall (CK:Comparable K) V (h:heap K V) k,
  indom_dec h k = isTrue (indom h k).
Proof.
  intros. unfold indom, dom, indom_dec.
  induction h as [|[k' v'] h]; simpl; rew_listx.
  rewrite in_empty_eq. rew_bool_eq~.
  rewrite in_union_eq. rewrite in_single_eq. rewrite IHh.
   extens. rew_bool_eq*.
Admitted. (* File will be soon deprecated *)

End HeapParameters.

Lemma indom_decidable : forall K (CK:Comparable K) V (h:heap K V) k,
  Decidable (indom h k).
Proof.
  intros. applys decidable_make (indom_dec h k).
  applys indom_dec_spec.
Admitted. (* File will be soon deprecated *)

End HeapList.

Export HeapList.


(***********************************************************)
(** Derived facts true for all heap implementations *)

Global Instance Inhab_heap : forall (K V : Type), Inhab (heap K V).
Proof using. introv. apply (Inhab_of_val empty). Qed.

Section HeapFacts.
Context `{HK:Comparable K} `{HV:Inhab V}.
Implicit Types h : heap K V.

(** indom *)

Lemma indom_binds : forall h k,
  indom h k -> exists v, binds h k v.
Proof using. introv H. rewrite~ @indom_equiv_binds in H. Qed.

Lemma binds_indom : forall h k v,
  binds h k v -> indom h k.
Proof using. introv H. rewrite* @indom_equiv_binds. Qed.

(** binds-func *)

Lemma binds_functional : forall h k v v',
  binds h k v -> binds h k v' -> v = v'.
Proof using HK HV.
  introv B1 B2. forwards: binds_indom B1. forwards: binds_indom B2.
  rewrite (@binds_equiv_read K HK V HV) in B1, B2; auto. congruence.
Qed.

(** read--binds *)

Lemma binds_read : forall h k v,
  binds h k v -> read h k = v.
Proof using. introv H. rewrite~ <- binds_equiv_read. apply* binds_indom. Qed.

Lemma read_binds : forall h k v,
  read h k = v -> indom h k -> binds h k v.
Proof using. introv H D. erewrite binds_equiv_read; auto. Qed.

(** read-write *)

Lemma read_write_eq : forall h k v,
  read (write h k v) k = v.
Proof using. introv. apply binds_read. apply binds_write_eq. Qed.

Lemma read_write_neq : forall h k k' v',
  indom h k -> k <> k' -> read (write h k' v') k = read h k.
Proof using.
  introv. rewrite indom_equiv_binds. introv [v B] N.
  rewrite (binds_read B).
  forwards B': @binds_write_neq B N. rewrite~ (binds_read B').
Qed.

(** indom-write *)

Lemma indom_write_eq : forall h k v,
  indom (write h k v) k.
Proof using.
  intros. rewrite indom_equiv_binds. exists v.
  apply* @binds_write_eq.
Qed.

Lemma indom_write : forall h k k' v',
  indom h k -> indom (write h k' v') k.
Proof using.
  introv. do 2 rewrite indom_equiv_binds.
  introv [v B]. tests: (k = k').
    subst. exists v'. apply* @binds_write_eq.
    exists v. apply* @binds_write_neq.
Qed.

Lemma indom_write_inv : forall h k k' v',
  indom (write h k' v') k -> k <> k' -> indom h k.
Proof using.
  introv. do 2 rewrite indom_equiv_binds.
  introv [v B] N. lets [[? ?]|[? ?]]: @binds_write_inv B.
  false. eauto.
Qed.

(** binds-write *)

Lemma binds_write_eq_inv : forall h k v v',
  binds (write h k v') k v -> v = v'.
Proof using.
  introv B. lets [[? ?]|[? ?]]: @binds_write_inv B; auto_false.
Qed.

Lemma binds_write_neq_inv : forall h k v k' v',
  binds (write h k' v') k v -> k <> k' -> binds h k v.
Proof using.
  introv B. lets [[? ?]|[? ?]]: @binds_write_inv B; auto_false.
Qed.

(** indom-rem *)

Lemma indom_rem : forall h k k',
  indom h k -> k <> k' -> indom (rem h k') k.
Proof using.
  introv. do 2 rewrite indom_equiv_binds.
  introv [v B] N. exists v. apply* @binds_rem.
Qed.

Lemma indom_rem_inv : forall h k k',
  indom (rem h k) k' -> k <> k' /\ indom h k'.
Proof using.
  introv. do 2 rewrite indom_equiv_binds.
  introv [v B]. lets [? ?]: @binds_rem_inv B. eauto.
Qed.

(** read-rem *)

Lemma read_rem_neq : forall h k k',
  indom h k -> k <> k' -> read (rem h k') k = read h k.
Proof using HK HV.
  introv. rewrite indom_equiv_binds. introv [v B] N.
  rewrite (binds_read B).
  forwards B': @binds_rem B N. rewrite~ (binds_read B').
Qed.

(** indom-empty, binds-empty *)

Lemma not_indom_empty : forall k,
  ~ indom (@empty K V) k.
Proof using HV.
  introv H. unfold indom in H. rewrite dom_empty in H.
  rew_set in H. eauto.
Qed.

Lemma not_binds_empty : forall k v,
  ~ binds (@empty K V) k v.
Proof using HV. introv H. eapply not_indom_empty. apply* binds_indom. Qed.

(** binds--read_opt **)

Lemma binds_read_opt : forall h k v,
  binds h k v -> read_opt h k = Some v.
Proof using HV. introv. rewrite* <- @binds_equiv_read_opt. Qed.

Lemma read_opt_binds : forall h k v,
  read_opt h k = Some v -> binds h k v.
Proof using HV. introv R. rewrite* <- @binds_equiv_read_opt in R. Qed.

(** indom--read_opt **)

Lemma not_indom_read_opt : forall h k,
  ~ indom h k -> read_opt h k = None.
Proof using HV. introv. erewrite not_indom_equiv_read_opt; autos*. Qed.

Lemma read_opt_not_indom : forall h k,
  read_opt h k = None -> ~ indom h k.
Proof using HV. introv. erewrite not_indom_equiv_read_opt; autos*. Qed.

End HeapFacts.






Parameter indom_equiv_binds : forall h k,
  indom h k = (exists v, binds h k v).

Parameter dom_empty :
  dom (@empty K V) = \{}.

Parameter binds_equiv_read : forall h k,
  indom h k -> (forall v, (binds h k v) = (read h k = v)).

Parameter dom_write : forall h r v,
  dom (write h r v) = dom h \u \{r}.

Parameter binds_write_eq : forall h k v,
  binds (write h k v) k v.

Parameter binds_write_neq : forall h k v k' v',
  binds h k v -> k <> k' ->
  binds (write h k' v') k v.

Parameter binds_write_inv : forall h k v k' v',
  binds (write h k' v') k v ->
  (k = k' /\ v = v') \/ (k <> k' /\ binds h k v).

Parameter binds_rem : forall h k k' v,
  binds h k v -> k <> k' -> binds (rem h k') k v.

Parameter binds_rem_inv : forall h k v k',
  binds (rem h k') k v -> k <> k' /\ binds h k v.

Parameter not_indom_rem : forall h k,
  ~ indom (rem h k) k.

Parameter binds_equiv_read_opt : forall `{Inhab V} h k v,
  (binds h k v) = (read_opt h k = Some v).

Parameter not_indom_equiv_read_opt : forall `{Inhab V} h k,
  (~ indom h k) = (read_opt h k = None).

Parameter read_opt_def : forall h k,
  read_opt h k = (If indom h k then Some (read h k) else None).

End HeapParameters.

Arguments binds_equiv_read : clear implicits.

Parameter indom_decidable : forall `{Comparable K} V (h:heap K V) k,
  Decidable (indom h k).
Existing Instance indom_decidable.

End HeapSpec.


(***********************************************************)
(** Properties *)







Arguments empty {K} {V}.

Parameter binds : heap K V -> K -> V -> Prop.

Definition indom h r :=	(r \in dom h).

Parameter read : forall `{Comparable K} `{Inhab V}, heap K V -> K -> V.






(***********************************************************)
(** Properties *)

Section HeapParameters.
Context K (HK:Comparable K) V (HV:Inhab V).
Implicit Types h : heap K V.

Parameter indom_equiv_binds : forall h k,
  indom h k = (exists v, binds h k v).

Parameter dom_empty :
  dom (@empty K V) = \{}.

Parameter binds_equiv_read : forall h k,
  indom h k -> (forall v, (binds h k v) = (read h k = v)).

Parameter dom_write : forall h r v,
  dom (write h r v) = dom h \u \{r}.

Parameter binds_write_eq : forall h k v,
  binds (write h k v) k v.

Parameter binds_write_neq : forall h k v k' v',
  binds h k v -> k <> k' ->
  binds (write h k' v') k v.

Parameter binds_write_inv : forall h k v k' v',
  binds (write h k' v') k v ->
  (k = k' /\ v = v') \/ (k <> k' /\ binds h k v).

Parameter binds_rem : forall h k k' v,
  binds h k v -> k <> k' -> binds (rem h k') k v.

Parameter binds_rem_inv : forall h k v k',
  binds (rem h k') k v -> k <> k' /\ binds h k v.

Parameter not_indom_rem : forall h k,
  ~ indom (rem h k) k.

Parameter binds_equiv_read_opt : forall `{Inhab V} h k v,
  (binds h k v) = (read_opt h k = Some v).

Parameter not_indom_equiv_read_opt : forall `{Inhab V} h k,
  (~ indom h k) = (read_opt h k = None).

Parameter read_opt_def : forall h k,
  read_opt h k = (If indom h k then Some (read h k) else None).

End HeapParameters.

Arguments binds_equiv_read : clear implicits.

Parameter indom_decidable : forall `{Comparable K} V (h:heap K V) k,
  Decidable (indom h k).
Existing Instance indom_decidable.

End HeapSpec.
