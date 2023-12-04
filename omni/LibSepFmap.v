(** * LibSepFmap: Appendix - Finite Maps *)

Set Implicit Arguments.
From TLC Require Import LibCore.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Representation of Finite Maps *)

(** This file provides a representation of finite maps, which may be used
    to represent the memory state of a program.

    - It implements basic operations such as creation of a singleton map,
       union of maps, read and update operations.
    - It includes predicates to assert disjointness of two maps (predicate
      [disjoint]), and coherence of two maps on the intersection of their
      domain (predicate [agree]).
    - It comes with a tactic for [fmap_eq] proving equalities modulo
      commutativity and associativity of map union.

    The definition of the type [fmap] is slightly technical in that it
    involves a dependent pair to pack the partial function of type
    [A -> option B] that represents the map, together with a proof of
    finiteness of the domain of this map. One useful lemma established
    in this file is the existence of fresh keys: for any finite map whose
    keys are natural numbers, there exists a natural number that does not
    already belong to the domain of that map. *)


(* ########################################################### *)
(** ** Representation of Potentially-Infinite Maps as Partial Functions *)

(* ########################################################### *)
(** *** Representation *)

(** Type of partial functions from A to B *)

Definition map (A B : Type) : Type :=
  A -> option B.


(* ########################################################### *)
(** *** Operations *)

(** Disjoint union of two partial functions *)

Definition map_union (A B : Type) (f1 f2 : map A B) : map A B :=
  fun (x:A) => match f1 x with
           | Some y => Some y
           | None => f2 x
           end.

(** Removal from a partial functions *)

Definition map_remove (A B : Type) (f : map A B) (k:A) : map A B :=
  fun (x:A) => If x = k then None else f x.

(** Finite domain of a partial function *)

Definition map_finite (A B : Type) (f : map A B) :=
  exists (L : list A), forall (x:A), f x <> None -> mem x L.

(** Disjointness of domain of two partial functions *)

Definition map_disjoint (A B : Type) (f1 f2 : map A B) :=
  forall (x:A), f1 x = None \/ f2 x = None.
(* LATER: might be simpler as a definition in terms of indom *)

(** Compatibility of two partial functions on the intersection
    of their domains (only for Separation Logic with RO-permissions) *)

Definition map_agree (A B : Type) (f1 f2 : map A B) :=
  forall x v1 v2,
  f1 x = Some v1 ->
  f2 x = Some v2 ->
  v1 = v2.

(** Domain of a map (as a predicate) *)

Definition map_indom (A B : Type) (f1 : map A B) : (A->Prop) :=
  fun (x:A) => f1 x <> None.

(** Filter the bindings of a map *)

Definition map_filter A B (F:A->B->Prop) (f:map A B) : map A B :=
  fun (x:A) => match f x with
    | None => None
    | Some y => If F x y then Some y else None
    end.

(** Map a function on the values of a map *)

Definition map_map A B1 B2 (F:A->B1->B2) (f:map A B1) : map A B2 :=
  fun (x:A) => match f x with
    | None => None
    | Some y => Some (F x y)
    end.


(* ########################################################### *)
(** *** Properties *)

Section MapOps.
Variables (A B : Type).
Implicit Types f : map A B.

(** Disjointness and domains *)

Lemma map_disjoint_eq : forall f1 f2,
  map_disjoint f1 f2 = (forall x, map_indom f1 x -> map_indom f2 x -> False).
Proof using.
  intros. unfold map_disjoint, map_indom. extens. iff M.
  { intros x. specializes M x. gen M. case_eq (f1 x); case_eq (f2 x); auto_false*. }
  { intros x. specializes M x. gen M. case_eq (f1 x); case_eq (f2 x); auto_false*.
    { intros. false. applys M; auto_false. } }
Qed.

(** Symmetry of disjointness *)

Lemma map_disjoint_sym :
  sym (@map_disjoint A B).
Proof using.
  introv H. unfolds map_disjoint. intros z. specializes H z. intuition.
Qed.

(** Commutativity of disjoint union *)

Lemma map_union_comm : forall f1 f2,
  map_disjoint f1 f2 ->
  map_union f1 f2 = map_union f2 f1.
Proof using.
  introv H. unfold map.
  extens. intros x. unfolds map_disjoint, map_union.
  specializes H x. cases (f1 x); cases (f2 x); auto. destruct H; false.
Qed.

(** Finiteness of union *)

Lemma map_union_finite : forall f1 f2,
  map_finite f1 ->
  map_finite f2 ->
  map_finite (map_union f1 f2).
Proof using.
  introv [L1 F1] [L2 F2]. exists (L1 ++ L2). intros x M.
  specializes F1 x. specializes F2 x. unfold map_union in M.
  apply mem_app. destruct~ (f1 x).
Qed.

(** Finiteness of removal *)

Definition map_remove_finite : forall x f,
  map_finite f ->
  map_finite (map_remove f x).
Proof using.
  introv [L F]. exists L. intros x' M.
  specializes F x'. unfold map_remove in M. case_if~.
Qed.

(** Finiteness of filter *)

Definition map_filter_finite : forall (F:A->B->Prop) f,
  map_finite f ->
  map_finite (map_filter F f).
Proof using.
  introv [L N]. exists L. intros x' M.
  specializes N x'. unfold map_filter in M.
  destruct (f x'); tryfalse. case_if. applys N; auto_false.
Qed.

(** Finiteness of map *)

Definition map_map_finite : forall C (F:A->B->C) f,
  map_finite f ->
  map_finite (map_map F f).
Proof using.
  introv [L N]. exists L. intros x' M.
  specializes N x'. unfold map_map in M.
  destruct (f x'); tryfalse. applys N; auto_false.
Qed.

End MapOps.


(* ########################################################### *)
(** ** Representation of Finite Maps as Dependent Pairs *)

(* ########################################################### *)
(** *** Representation *)

Inductive fmap (A B : Type) : Type := make {
  fmap_data :> map A B;
  fmap_finite : map_finite fmap_data }.

Arguments make [A] [B].


(* ########################################################### *)
(** *** Operations *)

Declare Scope fmap_scope.

(** Domain of a fmap (as a predicate) *)

Definition indom (A B: Type) (h:fmap A B) : (A->Prop) :=
  map_indom h.

(** Empty fmap *)

Program Definition empty (A B : Type) : fmap A B :=
  make (fun l => None) _.
Next Obligation. exists (@nil A). auto_false. Qed.

Arguments empty {A} {B}.

(** Singleton fmap *)

Program Definition single A B (x:A) (v:B) : fmap A B :=
  make (fun x' => If x = x' then Some v else None) _.
Next Obligation.
  exists (x::nil). intros. case_if. subst~.
Qed.

(** Union of fmaps *)

Program Definition union A B (h1 h2:fmap A B) : fmap A B :=
  make (map_union h1 h2) _.
Next Obligation. destruct h1. destruct h2. apply~ map_union_finite. Qed.

Notation "h1 \+ h2" := (union h1 h2)
   (at level 51, right associativity) : fmap_scope.

Open Scope fmap_scope.

(** Update of a fmap *)

Definition update A B (h:fmap A B) (x:A) (v:B) : fmap A B :=
  union (single x v) h.
  (* Note: the union operation first reads in the first argument. *)

(** Read in a fmap *)

Definition read (A B : Type) {IB:Inhab B} (h:fmap A B) (x:A) : B :=
  match fmap_data h x with
  | Some y => y
  | None => arbitrary
  end.

(** Removal from a fmap *)

Program Definition remove A B (h:fmap A B) (x:A) : fmap A B :=
  make (map_remove h x) _.
Next Obligation. destruct h. apply~ map_remove_finite. Qed.

(** Filter from a fmap *)

Program Definition filter A B (F:A->B->Prop) (h:fmap A B) : fmap A B :=
  make (map_filter F h) _.
Next Obligation. destruct h. apply~ map_filter_finite. Qed.

(** Map a function onto the keys of a fmap *)

Program Definition map_ A B1 B2 (F:A->B1->B2) (h:fmap A B1) : fmap A B2 :=
  make (map_map F h) _.
Next Obligation. destruct h. apply~ map_map_finite. Qed.

(** Inhabited type [fmap] *)

Global Instance Inhab_fmap A B : Inhab (fmap A B).
Proof using. intros. applys Inhab_of_val (@empty A B). Qed.


(* ########################################################### *)
(** ** Predicates on Finite Maps *)

(** Compatible fmaps (only for Separation Logic with RO-permissions) *)

Definition agree A B (h1 h2:fmap A B) :=
  map_agree h1 h2.

(** Disjoint fmaps *)

Definition disjoint A B (h1 h2 : fmap A B) : Prop :=
  map_disjoint h1 h2.

(** Three disjoint fmaps (not needed for basic separation logic) *)

Definition disjoint_3 A B (h1 h2 h3 : fmap A B) :=
     disjoint h1 h2
  /\ disjoint h2 h3
  /\ disjoint h1 h3.

(** Notation for disjointness *)

Module NotationForFmapDisjoint.

Notation "\# h1 h2" := (disjoint h1 h2)
  (at level 40, h1 at level 0, h2 at level 0, no associativity) : fmap_scope.

Notation "\# h1 h2 h3" := (disjoint_3 h1 h2 h3)
  (at level 40, h1 at level 0, h2 at level 0, h3 at level 0, no associativity)
  : fmap_scope.

End NotationForFmapDisjoint.

Import NotationForFmapDisjoint.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Poperties of Operations on Finite Maps *)

Section FmapProp.
Variables (A B : Type).
Implicit Types f g h : fmap A B.
Implicit Types x : A.
Implicit Types v : B.


(* ########################################################### *)
(** ** Equality *)

Lemma make_eq : forall (f1 f2:map A B) F1 F2,
  (forall x, f1 x = f2 x) ->
  make f1 F1 = make f2 F2.
Proof using.
  introv H. asserts: (f1 = f2). { unfold map. extens~. }
  subst. fequals. (* note: involves proof irrelevance *)
Qed.

Lemma eq_inv_fmap_data_eq : forall h1 h2,
  h1 = h2 ->
  forall x, fmap_data h1 x = fmap_data h2 x.
Proof using. intros. fequals. Qed.

Lemma fmap_extens : forall h1 h2,
  (forall x, fmap_data h1 x = fmap_data h2 x) ->
  h1 = h2.
Proof using. intros [f1 F1] [f2 F2] M. simpls. applys~ make_eq. Qed.



(* ########################################################### *)
(** ** Domain *)

Lemma indom_single_eq : forall x y v,
  indom (single x v) y = (x = y).
Proof using.
  intros. unfold single, indom, map_indom. simpl. extens. case_if; auto_false.
Qed.

Lemma indom_single : forall x v,
  indom (single x v) x.
Proof using. intros. rewrite* indom_single_eq. Qed.

Lemma indom_union_eq : forall h1 h2 x,
  indom (union h1 h2) x = (indom h1 x \/ indom h2 x).
Proof using.
  intros. extens. unfolds indom, union, map_indom, map_union. simpls.
  case_eq (fmap_data h1 x); case_eq (fmap_data h2 x); auto_false*.
Qed.

Lemma indom_union_l : forall h1 h2 x,
  indom h1 x ->
  indom (union h1 h2) x.
Proof using. intros. rewrite* indom_union_eq. Qed.

Lemma indom_union_r : forall h1 h2 x,
  indom h2 x ->
  indom (union h1 h2) x.
Proof using. intros. rewrite* indom_union_eq. Qed.

Lemma indom_update_eq : forall h x v y,
  indom (update h x v) y = (x = y \/ indom h y).
Proof using.
  intros. unfold update. rewrite indom_union_eq, indom_single_eq. auto.
Qed.

Lemma indom_remove_eq : forall h x y,
  indom (remove h x) y = (x <> y /\ indom h y).
Proof using.
  intros. extens. unfolds indom, remove, map_indom, map_remove. simpls.
  case_if; auto_false*.
Qed.


(* ########################################################### *)
(** ** Disjoint and Domain *)

Lemma disjoint_eq : forall h1 h2,
  disjoint h1 h2 = (forall x, indom h1 x -> indom h2 x -> False).
Proof using. intros [f1 F1] [f2 F2]. apply map_disjoint_eq. Qed.

Lemma disjoint_eq' : forall h1 h2,
  disjoint h1 h2 = (forall x, indom h1 x -> indom h2 x -> False).
Proof using.
  extens. iff D E.
  { introv M1 M2. destruct (D x); false*. }
  { intros x. specializes E x. unfolds indom, map_indom.
    applys not_not_inv. intros N. rew_logic in N. false*. }
Qed. (* LATER: choose which proof to keep *)

Lemma disjoint_of_not_indom_both : forall h1 h2,
  (forall x, indom h1 x -> indom h2 x -> False) ->
  disjoint h1 h2.
Proof using. introv M. rewrite~ disjoint_eq. Qed.

Lemma disjoint_inv_not_indom_both : forall h1 h2 x,
  disjoint h1 h2 ->
  indom h1 x ->
  indom h2 x ->
  False.
Proof using. introv. rewrite* disjoint_eq. Qed.

Lemma disjoint_single_of_not_indom : forall h x v,
  ~ indom h x ->
  disjoint (single x v) h.
Proof using.
  introv N. unfolds disjoint, map_disjoint. unfolds single, indom, map_indom.
  simpl. rew_logic in N. intros l'. case_if; subst; autos*.
Qed.

(** Note that the reciprocal of the above lemma is a special instance of
   [disjoint_inv_not_indom_both] *)


(* ########################################################### *)
(** ** Disjointness *)

Lemma disjoint_sym : forall h1 h2,
  \# h1 h2 ->
  \# h2 h1.
Proof using. intros [f1 F1] [f2 F2]. apply map_disjoint_sym. Qed.

Lemma disjoint_comm : forall h1 h2,
  \# h1 h2 = \# h2 h1.
Proof using. lets: disjoint_sym. extens*. Qed.

Lemma disjoint_empty_l : forall h,
  \# empty h.
Proof using. intros [f F] x. simple~. Qed.

Lemma disjoint_empty_r : forall h,
  \# h empty.
Proof using. intros [f F] x. simple~. Qed.

Hint Immediate disjoint_sym.
Hint Resolve disjoint_empty_l disjoint_empty_r.

Lemma disjoint_union_eq_r : forall h1 h2 h3,
  \# h1 (h2 \+ h3) =
  (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3].
  unfolds disjoint, union. simpls.
  unfolds map_disjoint, map_union. extens. iff M [M1 M2].
  split; intros x; specializes M x;
   destruct (f2 x); intuition; tryfalse.
  intros x. specializes M1 x. specializes M2 x.
   destruct (f2 x); intuition.
Qed.

Lemma disjoint_union_eq_l : forall h1 h2 h3,
  \# (h2 \+ h3) h1 =
  (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros. rewrite disjoint_comm.
  apply disjoint_union_eq_r.
Qed.

Lemma disjoint_single_single : forall (x1 x2:A) (v1 v2:B),
  x1 <> x2 ->
  \# (single x1 v1) (single x2 v2).
Proof using.
  introv N. intros x. simpls. do 2 case_if; auto.
Qed.

Lemma disjoint_single_single_same_inv : forall (x:A) (v1 v2:B),
  \# (single x v1) (single x v2) ->
  False.
Proof using.
  introv D. specializes D x. simpls. case_if. destruct D; tryfalse.
Qed.

Lemma disjoint_3_unfold : forall h1 h2 h3,
  \# h1 h2 h3 = (\# h1 h2 /\ \# h2 h3 /\ \# h1 h3).
Proof using. auto. Qed.

Lemma disjoint_single_set : forall h l v1 v2,
  \# (single l v1) h ->
  \# (single l v2) h.
Proof using.
  introv M. unfolds disjoint, single, map_disjoint; simpls.
  intros l'. specializes M l'. case_if~. destruct M; auto_false.
Qed.

Lemma disjoint_update_l : forall h1 h2 x v,
  disjoint h1 h2 ->
  indom h1 x ->
  disjoint (update h1 x v) h2.
Proof using.
  introv HD Hx. rewrite disjoint_eq in *. intros y Hy1 Hy2.
  rewrite indom_update_eq in Hy1. destruct Hy1.
  { subst. false*. }
  { applys* HD y. }
Qed.

Lemma disjoint_update_not_r : forall h1 h2 x v,
  disjoint h1 h2 ->
  ~ indom h2 x ->
  disjoint (update h1 x v) h2.
Proof using.
  introv HD Hx. rewrite disjoint_eq in *. intros y Hy1 Hy2.
  rewrite indom_update_eq in Hy1. destruct Hy1.
  { subst. false*. }
  { applys* HD y. }
Qed. (* LATER: factorize proof *)

Lemma disjoint_remove_l : forall h1 h2 x,
  disjoint h1 h2 ->
  disjoint (remove h1 x) h2.
Proof using.
  introv M. rewrite disjoint_eq in *. intros y Hy1 Hy2.
  rewrite* indom_remove_eq in Hy1.
Qed.


(* ########################################################### *)
(** ** Union *)

Lemma union_self : forall h,
  h \+ h = h.
Proof using.
  intros [f F]. apply~ make_eq. simpl. intros x.
  unfold map_union. cases~ (f x).
Qed.

Lemma union_empty_l : forall h,
  empty \+ h = h.
Proof using.
  intros [f F]. unfold union, map_union, empty. simpl.
  apply~ make_eq.
Qed.

Lemma union_empty_r : forall h,
  h \+ empty = h.
Proof using.
  intros [f F]. unfold union, map_union, empty. simpl.
  apply make_eq. intros x. destruct~ (f x).
Qed.

Lemma union_eq_empty_inv_l : forall h1 h2,
  h1 \+ h2 = empty ->
  h1 = empty.
Proof using.
  intros (f1&F1) (f2&F2) M. inverts M as M.
  applys make_eq. intros l.
  unfolds map_union.
  lets: fun_eq_1 l M.
  cases (f1 l); auto_false.
Qed.

Lemma union_eq_empty_inv_r : forall h1 h2,
  h1 \+ h2 = empty ->
  h2 = empty.
Proof using.
  intros (f1&F1) (f2&F2) M. inverts M as M.
  applys make_eq. intros l.
  unfolds map_union.
  lets: fun_eq_1 l M.
  cases (f1 l); auto_false.
Qed.

Lemma union_comm_of_disjoint : forall h1 h2,
  \# h1 h2 ->
  h1 \+ h2 = h2 \+ h1.
Proof using.
  intros [f1 F1] [f2 F2] H. simpls. apply make_eq. simpl.
  intros. rewrite~ map_union_comm.
Qed.

Lemma union_comm_of_agree : forall h1 h2,
  agree h1 h2 ->
  h1 \+ h2 = h2 \+ h1.
Proof using.
  intros [f1 F1] [f2 F2] H. simpls. apply make_eq. simpl.
  intros l. specializes H l. unfolds map_union. simpls.
  cases (f1 l); cases (f2 l); auto. fequals. applys* H.
Qed.

Lemma union_assoc : forall h1 h2 h3,
  (h1 \+ h2) \+ h3 = h1 \+ (h2 \+ h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3]. unfolds union. simpls.
  apply make_eq. intros x. unfold map_union. destruct~ (f1 x).
Qed.

(* LATER:
Lemma union_eq_inv_of_disjoint : forall h2 h1 h1' : fmap,
  \# h1 h2 ->
  agree h1' h2 ->
  h1 \+ h2 = h1' \+ h2 ->
  h1 = h1'.
Proof using.
  intros [f2 F2] [f1 F1] [f1' F1'] D D' E.
  applys make_eq. intros x. specializes D x. specializes D' x.
  lets E': eq_inv_fmap_data_eq (rm E) x. simpls.
  unfolds map_union.
  cases (f1 x); cases (f2 x); try solve [cases (f1' x); destruct D; congruence ].
  destruct D; try false.
  rewrite H in E'. inverts E'.
  cases (f1' x); cases (f1 x);
    destruct D; try congruence.
  false.
    destruct D'; try congruence.
Qed.
*)

Lemma union_eq_inv_of_disjoint : forall h2 h1 h1',
  \# h1 h2 ->
  \# h1' h2 ->
  h1 \+ h2 = h1' \+ h2 ->
  h1 = h1'.
Proof using.
  intros [f2 F2] [f1' F1'] [f1 F1] D D' E.
  applys make_eq. intros x. specializes D x. specializes D' x.
  lets E': eq_inv_fmap_data_eq (rm E) x. simpls.
  unfolds map_union.
  cases (f1' x); cases (f1 x);
    destruct D; try congruence;
    destruct D'; try congruence.
Qed.


(* ########################################################### *)
(** ** Compatibility *)

Lemma agree_refl : forall h,
  agree h h.
Proof using.
  intros h. introv M1 M2. congruence.
Qed.

Lemma agree_sym : forall f1 f2,
  agree f1 f2 ->
  agree f2 f1.
Proof using.
  introv M. intros l v1 v2 E1 E2.
  specializes M l E1.
Qed.

Lemma agree_of_disjoint : forall h1 h2,
  disjoint h1 h2 ->
  agree h1 h2.
Proof using.
  introv HD. intros l v1 v2 M1 M2. destruct (HD l); false.
Qed.

Lemma agree_empty_l : forall h,
  agree empty h.
Proof using. intros h l v1 v2 E1 E2. simpls. false. Qed.

Lemma agree_empty_r : forall h,
  agree h empty.
Proof using.
  hint agree_sym, agree_empty_l. eauto.
Qed.

Lemma agree_union_l : forall f1 f2 f3,
  agree f1 f3 ->
  agree f2 f3 ->
  agree (f1 \+ f2) f3.
Proof using.
  introv M1 M2. intros l v1 v2 E1 E2.
  specializes M1 l. specializes M2 l.
  simpls. unfolds map_union. cases (fmap_data f1 l).
  { inverts E1. applys* M1. }
  { applys* M2. }
Qed.

Lemma agree_union_r : forall f1 f2 f3,
  agree f1 f2 ->
  agree f1 f3 ->
  agree f1 (f2 \+ f3).
Proof using.
  hint agree_sym, agree_union_l. eauto.
Qed.

Lemma agree_union_lr : forall f1 g1 f2 g2,
  agree g1 g2 ->
  \# f1 f2 (g1 \+ g2) ->
  agree (f1 \+ g1) (f2 \+ g2).
Proof using.
  introv M1 (M2a&M2b&M2c).
  rewrite disjoint_union_eq_r in *.
  applys agree_union_l; applys agree_union_r;
    try solve [ applys* agree_of_disjoint ].
  auto.
Qed.

Lemma agree_union_ll_inv : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f3.
Proof using.
  introv M. intros l v1 v2 E1 E2.
  specializes M l. simpls. unfolds map_union.
  rewrite E1 in M. applys* M.
Qed.

Lemma agree_union_rl_inv : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f1 f2.
Proof using.
  hint agree_union_ll_inv, agree_sym. eauto.
Qed.

Lemma agree_union_lr_inv_agree_agree : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f2 ->
  agree f2 f3.
Proof using.
  introv M D. rewrite~ (@union_comm_of_agree f1 f2) in M.
  applys* agree_union_ll_inv.
Qed.

Lemma agree_union_rr_inv_agree : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f2 f3 ->
  agree f1 f3.
Proof using.
  hint agree_union_lr_inv_agree_agree, agree_sym. eauto.
Qed.

Lemma agree_union_l_inv : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f2 ->
     agree f1 f3
  /\ agree f2 f3.
Proof using.
  introv M1 M2. split.
  { applys* agree_union_ll_inv. }
  { applys* agree_union_lr_inv_agree_agree. }
Qed.

Lemma agree_union_r_inv : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f2 f3 ->
     agree f1 f2
  /\ agree f1 f3.
Proof using.
  hint agree_sym.
  intros. forwards~ (M1&M2): agree_union_l_inv f2 f3 f1.
Qed.


(* ########################################################### *)
(** ** Read *)

Lemma read_single : forall {IB:Inhab B} x v,
  read (single x v) x = v.
Proof using.
  intros. unfold read, single. simpl. case_if~.
Qed.

Lemma read_union_l : forall {IB:Inhab B} h1 h2 x,
  indom h1 x ->
  read (union h1 h2) x = read h1 x.
Proof using.
  intros. unfold read, union, map_union. simpl.
  case_eq (fmap_data h1 x); auto_false.
Qed.

Lemma read_union_r : forall {IB:Inhab B} h1 h2 x,
  ~ indom h1 x ->
  read (union h1 h2) x = read h2 x.
Proof using.
  intros. unfold read, union, map_union. simpl.
  case_eq (fmap_data h1 x).
  { intros v Hv. false H. auto_false. }
  { auto_false. }
Qed.


(* ########################################################### *)
(** ** Update *)

Lemma update_eq_union_single : forall h x v,
  update h x v = union (single x v) h.
Proof using. auto. Qed.

Lemma update_empty : forall x v,
  update empty x v = single x v.
Proof using.
  intros. rewrite update_eq_union_single. rewrite* union_empty_r.
Qed.

Lemma update_single : forall x v w,
  update (single x v) x w = single x w.
Proof using.
  intros. rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, single. simpl. case_if~.
Qed.

Lemma update_union_l : forall h1 h2 x v,
  indom h1 x ->
  update (union h1 h2) x v = union (update h1 x v) h2.
Proof using.
  intros. do 2 rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, union, map_union. simpl. case_if~.
Qed.

Lemma update_union_r : forall h1 h2 x v,
  ~ indom h1 x ->
  update (union h1 h2) x v = union h1 (update h2 x v).
Proof using.
  introv M. asserts IB: (Inhab B). { applys Inhab_of_val v. }
  do 2 rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, union, map_union. simpl. case_if~.
  { subst. case_eq (fmap_data h1 y); auto_false.
    { intros w Hw. false M. auto_false. } }
Qed.

Lemma update_union_not_r : forall h1 h2 x v,
  ~ indom h2 x ->
  update (union h1 h2) x v = union (update h1 x v) h2.
Proof using.
  intros. do 2 rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, union, map_union. simpl. case_if~.
Qed.

Lemma update_union_not_l : forall h1 h2 x v,
  ~ indom h1 x ->
  update (union h1 h2) x v = union h1 (update h2 x v).
Proof using.
  introv M. asserts IB: (Inhab B). { applys Inhab_of_val v. }
  do 2 rewrite update_eq_union_single.
  applys make_eq. intros y.
  unfold map_union, union, map_union. simpl. case_if~.
  { subst. case_eq (fmap_data h1 y); auto_false.
    { intros w Hw. false M. auto_false. } }
Qed.

(* LATER: factorize proofs of the "_not_" versions *)


(* ########################################################### *)
(** ** Removal *)

Lemma remove_single : forall x v,
  remove (single x v) x = empty.
Proof using.
  intros. applys fmap_extens. intros y.
  unfold remove, map_remove, single, empty. simpl.
  case_if*. case_if*.
Qed.

Lemma remove_disjoint_union_l : forall h1 h2 x,
  indom h1 x ->
  disjoint h1 h2 ->
  remove (union h1 h2) x = union (remove h1 x) h2.
Proof using.
  introv M D. applys fmap_extens. intros y.
  rewrite disjoint_eq in D. specializes D M. asserts* D': (~ indom h2 x).
  unfold remove, map_remove, union, map_union, single. simpls. case_if.
  { destruct h1 as [f1 F1]. unfolds indom, map_indom. simpls. subst.
    rew_logic~ in D'. }
  { auto. }
Qed.

Lemma remove_union_single_l : forall h x v,
  ~ indom h x ->
  remove (union (single x v) h) x = h.
Proof using.
  introv M. applys fmap_extens. intros y.
  unfold remove, map_remove, union, map_union, single. simpls. case_if.
  { destruct h as [f F]. unfolds indom, map_indom. simpls. subst. rew_logic~ in M. }
  { case_if~. }
Qed.

End FmapProp.

(** Fixing arguments *)

Arguments union_assoc [A] [B].
Arguments union_comm_of_disjoint [A] [B].
Arguments union_comm_of_agree [A] [B].


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Tactics for Finite Maps *)

(* ########################################################### *)
(** ** Tactic [disjoint] for proving disjointness results *)

(** [disjoint] proves goals of the form [\# h1 h2] and
    [\# h1 h2 h3] by expanding all hypotheses into binary forms
    [\# h1 h2] and then exploiting symmetry and disjointness
    with [empty]. *)

Module Export DisjointHints.
#[export]
Hint Resolve disjoint_sym disjoint_empty_l disjoint_empty_r.
End DisjointHints.

#[global]
Hint Rewrite
  disjoint_union_eq_l
  disjoint_union_eq_r
  disjoint_3_unfold : rew_disjoint.

Tactic Notation "rew_disjoint" :=
  autorewrite with rew_disjoint in *.
Tactic Notation "rew_disjoint" "*" :=
  rew_disjoint; auto_star.

Ltac fmap_disjoint_pre tt :=
  subst; rew_disjoint; jauto_set.

Tactic Notation "fmap_disjoint" :=
  solve [ fmap_disjoint_pre tt; auto ].

Lemma disjoint_demo : forall A B (h1 h2 h3 h4 h5:fmap A B),
  h1 = h2 \+ h3 ->
  \# h2 h3 ->
  \# h1 h4 h5 ->
  \# h3 h2 h5 /\ \# h4 h5.
Proof using.
  intros. dup 2.
  { subst. rew_disjoint. jauto_set. auto. auto. auto. auto. }
  { fmap_disjoint. }
Qed.


(* ########################################################### *)
(** ** Tactic [rew_map] for Normalizing Expressions *)

#[global]
Hint Rewrite
  union_assoc
  union_empty_l
  union_empty_r : rew_fmap rew_fmap_for_fmap_eq.

Tactic Notation "rew_fmap" :=
  autorewrite with rew_fmap in *.

Tactic Notation "rew_fmap" "~" :=
  rew_fmap; auto_tilde.

Tactic Notation "rew_fmap" "*" :=
  rew_fmap; auto_star.


(* ########################################################### *)
(** ** Tactic [fmap_eq] for Proving Equalities *)

Section StateEq.
Variables (A B : Type).
Implicit Types h : fmap A B.

(** [eq] proves equalities between unions of fmaps, of the form
    [h1 \+ h2 \+ h3 \+ h4 = h1' \+ h2' \+ h3' \+ h4']
    It attempts to discharge the disjointness side-conditions.
    Disclaimer: it cancels heaps at depth up to 4, but no more. *)

Lemma union_eq_cancel_1 : forall h1 h2 h2',
  h2 = h2' ->
  h1 \+ h2 = h1 \+ h2'.
Proof using. intros. subst. auto. Qed.

Lemma union_eq_cancel_1' : forall h1,
  h1 = h1.
Proof using. intros. auto. Qed.

Lemma union_eq_cancel_2 : forall h1 h1' h2 h2',
  \# h1 h1' ->
  h2 = h1' \+ h2' ->
  h1 \+ h2 = h1' \+ h1 \+ h2'.
Proof using.
  intros. subst. rewrite <- union_assoc.
  rewrite (union_comm_of_disjoint h1 h1').
  rewrite~ union_assoc. auto.
Qed.

Lemma union_eq_cancel_2' : forall h1 h1' h2,
  \# h1 h1' ->
  h2 = h1' ->
  h1 \+ h2 = h1' \+ h1.
Proof using.
  intros. subst. apply~ union_comm_of_disjoint.
Qed.

Lemma union_eq_cancel_3 : forall h1 h1' h2 h2' h3',
  \# h1 (h1' \+ h2') ->
  h2 = h1' \+ h2' \+ h3' ->
  h1 \+ h2 = h1' \+ h2' \+ h1 \+ h3'.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' h3').
  rewrite <- (union_assoc h1' h2' (h1 \+ h3')).
  apply~ union_eq_cancel_2.
Qed.

Lemma union_eq_cancel_3' : forall h1 h1' h2 h2',
  \# h1 (h1' \+ h2') ->
  h2 = h1' \+ h2' ->
  h1 \+ h2 = h1' \+ h2' \+ h1.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' h1).
  apply~ union_eq_cancel_2'.
Qed.

Lemma union_eq_cancel_4 : forall h1 h1' h2 h2' h3' h4',
  \# h1 ((h1' \+ h2') \+ h3') ->
  h2 = h1' \+ h2' \+ h3' \+ h4' ->
  h1 \+ h2 = h1' \+ h2' \+ h3' \+ h1 \+ h4'.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' (h3' \+ h4')).
  rewrite <- (union_assoc h1' h2' (h3' \+ h1 \+ h4')).
  apply~ union_eq_cancel_3.
Qed.

Lemma union_eq_cancel_4' : forall h1 h1' h2 h2' h3',
  \# h1 (h1' \+ h2' \+ h3') ->
  h2 = h1' \+ h2' \+ h3' ->
  h1 \+ h2 = h1' \+ h2' \+ h3' \+ h1.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h2' h3' h1).
  apply~ union_eq_cancel_3'.
Qed.

End StateEq.

Ltac fmap_eq_step tt :=
  match goal with | |- ?G => match G with
  | ?h1 = ?h1 => apply union_eq_cancel_1'
  | ?h1 \+ ?h2 = ?h1 \+ ?h2' => apply union_eq_cancel_1
  | ?h1 \+ ?h2 = ?h1' \+ ?h1 => apply union_eq_cancel_2'
  | ?h1 \+ ?h2 = ?h1' \+ ?h1 \+ ?h2' => apply union_eq_cancel_2
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h1 => apply union_eq_cancel_3'
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h1 \+ ?h3' => apply union_eq_cancel_3
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h3' \+ ?h1 => apply union_eq_cancel_4'
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h3' \+ ?h1 \+ ?h4' => apply union_eq_cancel_4
  end end.

Tactic Notation "fmap_eq" :=
  subst;
  autorewrite with rew_fmap_for_fmap_eq;
  repeat (fmap_eq_step tt);
  try match goal with
  | |- \# _ _ => fmap_disjoint
  | |- \# _ _ _ => fmap_disjoint
  end.

Tactic Notation "fmap_eq" "~" :=
  fmap_eq; auto_tilde.

Tactic Notation "fmap_eq" "*" :=
  fmap_eq; auto_star.

Lemma fmap_eq_demo : forall A B (h1 h2 h3 h4 h5:fmap A B),
  \# h1 h2 h3 ->
  \# (h1 \+ h2 \+ h3) h4 h5 ->
  h1 = h2 \+ h3 ->
  h4 \+ h1 \+ h5 = h2 \+ h5 \+ h4 \+ h3.
Proof using.
  intros. dup 2.
  { subst. rew_fmap.
    fmap_eq_step tt. fmap_disjoint.
    fmap_eq_step tt.
    fmap_eq_step tt. fmap_disjoint. auto. }
  { fmap_eq. }
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Existence of Fresh Locations *)

(* ########################################################### *)
(** ** Consecutive Locations *)

(** The notion of "consecutive locations" is useful for reasoning about
    records and arrays. *)

Fixpoint conseq (B:Type) (vs:list B) (l:nat) : fmap nat B :=
  match vs with
  | nil => empty
  | v::vs' => (single l v) \+ (conseq vs' (S l))
  end.

Lemma conseq_nil : forall B (l:nat),
  conseq (@nil B) l = empty.
Proof using. auto. Qed.

Lemma conseq_cons : forall B (l:nat) (v:B) (vs:list B),
  conseq (v::vs) l = (single l v) \+ (conseq vs (S l)).
Proof using. auto. Qed.

Lemma conseq_cons' : forall B (l:nat) (v:B) (vs:list B),
  conseq (v::vs) l = (single l v) \+ (conseq vs (l+1)).
Proof using. intros. math_rewrite (l+1 = S l)%nat. applys conseq_cons. Qed.

Global Opaque conseq.

#[global]
Hint Rewrite conseq_nil conseq_cons : rew_listx.


(* ########################################################### *)
(** ** Existence of Fresh Locations *)

Definition loc_fresh_gen (L : list nat) :=
  (1 + fold_right plus O L)%nat.

Lemma loc_fresh_ind : forall l L,
  mem l L ->
  (l < loc_fresh_gen L)%nat.
Proof using.
  intros l L. unfold loc_fresh_gen.
  induction L; introv M; inverts M; rew_listx.
  { math. }
  { forwards~: IHL. math. }
Qed.

Lemma loc_fresh_nat_ge : forall (L:list nat),
  exists (l:nat), forall (i:nat), ~ mem (l+i)%nat L.
Proof using.
  intros L. exists (loc_fresh_gen L). intros i M.
  lets: loc_fresh_ind M. math.
Qed.

(** For any finite list of locations (implemented as [nat]), there exists
    one location not in that list. *)

Lemma loc_fresh_nat : forall (L:list nat),
  exists (l:nat), ~ mem l L.
Proof using.
  intros L. forwards (l&P): loc_fresh_nat_ge L.
  exists l. intros M. applys (P 0%nat). applys_eq M. math.
Qed.

Section FmapFresh.
Variables (B : Type).
Implicit Types h : fmap nat B.

(** For any heap, there exists one (non-null) location not already in the
    domain of that heap. *)

Lemma exists_fresh : forall null h,
  exists l, ~ indom h l /\ l <> null.
Proof using.
  intros null (m&(L&M)). unfold indom, map_indom. simpl.
  lets (l&F): (loc_fresh_nat (null::L)).
  exists l. split.
  { simpl. intros l'. forwards~ E: M l. }
  { intro_subst. applys~ F. }
Qed.

(** For any heap [h], there exists one (non-null) location [l] such that
    the singleton map that binds [l] to a value [v] is disjoint from [h]. *)

Lemma single_fresh : forall null h v,
  exists l, \# (single l v) h /\ l <> null.
Proof using.
  intros. forwards (l&F&N): exists_fresh null h.
  exists l. split~. applys* disjoint_single_of_not_indom.
Qed.

Lemma conseq_fresh : forall null h vs,
  exists l, \# (conseq vs l) h /\ l <> null.
Proof using.
  intros null (m&(L&M)) vs.
  unfold disjoint, map_disjoint. simpl.
  lets (l&F): (loc_fresh_nat_ge (null::L)).
  exists l. split.
  { intros l'. gen l. induction vs as [|v vs']; intros.
    { simple~. }
    { rewrite conseq_cons. destruct (IHvs' (S l)%nat) as [E|?].
      { intros i N. applys F (S i). applys_eq N. math. }
      { simpl. unfold map_union. case_if~.
        { subst. right. applys not_not_inv. intros H. applys F 0%nat.
          constructor. math_rewrite (l'+0 = l')%nat. applys~ M. } }
      { auto. } } }
  { intro_subst. applys~ F 0%nat. rew_nat. auto. }
Qed.

Lemma disjoint_single_conseq : forall B l l' L (v:B),
  (l < l')%nat \/ (l >= l'+length L)%nat ->
  \# (single l v) (conseq L l').
Proof using.
  introv N. gen l'. induction L as [|L']; intros.
  { rewrite~ conseq_nil. }
  { rew_list in N. rewrite conseq_cons. rew_disjoint. split.
    { applys disjoint_single_single. destruct N; math. }
    { applys IHL. destruct N. { left. math. } { right. math. } } }
Qed.


(* ########################################################### *)
(** ** Existence of a Smallest Fresh Locations *)

(** The notion of smallest fresh location is useful for setting up
    deterministic semantics. *)

Definition fresh (null:nat) (h:fmap nat B) (l:nat) : Prop :=
  ~ indom h l /\ l <> null.

Definition smallest_fresh (null:nat) (h:fmap nat B) (l:nat) : Prop :=
  fresh null h l /\ (forall l', l' < l -> ~ fresh null h l').

Lemma exists_smallest_fresh : forall null h,
  exists l, smallest_fresh null h l.
Proof using.
  intros.
  cuts M: (forall l0, fresh null h l0 ->
            exists l, fresh null h l
                   /\ (forall l', l' < l -> ~ fresh null h l')).
  { lets (l0&F&N): exists_fresh null h. applys M l0. split*. }
  intros l0. induction_wf IH: wf_lt l0. intros F.
  tests C: (forall l', l' < l0 -> ~ fresh null h l').
  { exists* l0. }
  { destruct C as (l0'&K). rew_logic in K. destruct K as (L&F').
    applys* IH l0'. }
Qed.


(* ########################################################### *)
(** ** Existence of Nonempty Heaps *)

(** The existence of nonempty (nat-indexed) finite maps is useful
    for constructing counterexamples. *)

Lemma exists_not_empty : forall `{IB:Inhab B},
  exists (h:fmap nat B), h <> empty.
Proof using.
  intros. sets l: 0%nat. sets h: (single l (arbitrary (A:=B))).
  exists h. intros N.
  sets h': (empty:fmap nat B).
  asserts M1: (indom h l).
  { applys indom_single. }
  asserts M2: (~ indom h' l).
  { unfolds @indom, map_indom, @empty. simpls. auto_false. }
  rewrite N in M1. false*.
Qed.

End FmapFresh.
