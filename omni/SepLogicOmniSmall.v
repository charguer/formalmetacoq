(****************************************************************
* Imperative Lambda-calculus                                    *
* Separation Logic on Omni-Small-Step                           *
*****************************************************************)

Set Implicit Arguments.
Require Export SepLogicCommon OmniSmall.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types s : state.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types P : state->trm->Prop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Proof of the Frame Property for the Omni-Small-Step-Based [stepsinto] Relation *)

(** Auxiliary definitions to define [P \*+' (=h)], that is, the
    extension of the postcondition [P] with a piece of heap [h]. *)

Definition swap (A B:Type) (P:A->B->Prop) : B->A->Prop :=
  fun y x => P x y.

Definition pstar (P:state->trm->Prop) (H:hprop) : state->trm->Prop :=
  swap ((swap P) \*+ H).

Notation "P \*+' H" := (pstar P H) (at level 40).

Lemma pstar_intro : forall h1 h2 P t H,
  disjoint h1 h2 ->
  P h1 t ->
  H h2 ->
  (pstar P H) (h1 \u h2) t.
Proof using. introv D M1 M2. unfold pstar, swap. applys* hstar_intro. Qed.

Lemma pstar_inv : forall h P H t,
  (pstar P H) h t ->
  exists h1 h2, disjoint h1 h2 /\ h = h1 \u h2 /\ P h1 t /\ H h2.
Proof using. introv (h1&h2&?&?&?&?). unfolds swap. eauto 8. Qed.

Lemma pstar_intro_same : forall h1 h2 P t,
  disjoint h1 h2 ->
  P h1 t ->
  (pstar P (= h2)) (h1 \u h2) t.
Proof using. introv D M1. applys* pstar_intro. Qed.

Lemma pstar_inv_same : forall h2 h P t,
  (pstar P (= h2)) h t ->
  exists h1, disjoint h1 h2 /\ h = h1 \u h2 /\ P h1 t.
Proof using. introv M. lets (h1&h2'&?&?&?&?): pstar_inv M. subst. eauto. Qed.

Hint Resolve pstar_intro_same.
Hint Constructors step.

(** Frame rule for the [omnismall] judgment *)

Lemma omnismall_frame : forall h1 h2 t P,
  omnismall h1 t P ->
  disjoint h1 h2 ->
  omnismall (h1 \u h2) t (P \*+' (= h2)).
Proof using.
  introv M HD. gen h2. induction M; intros; try solve [ constructors* ].
  { constructors*. introv N. lets (h1&D1&->&K1): pstar_inv_same N.
    applys* pstar_intro_same. }
  { constructors*. intros p Hp. rewrite indom_union_eq in Hp. rew_logic in Hp.
    forwards: H Hp. hint disjoint_update_not_r. rewrite* update_union_not_r. }
  { constructors*. { rewrite* indom_union_eq. }
    { rewrite* read_union_l. } }
  { constructors*. { rewrite* indom_union_eq. }
    { hint disjoint_update_l. rewrite* update_union_l. } }
  { constructors*. { rewrite* indom_union_eq. }
    { hint disjoint_remove_l. rewrite* remove_disjoint_union_l. } }
Qed.

(** Frame rule for the [omnismall] judgment *)

Lemma eventually_frame : forall h1 h2 t P,
  eventually h1 t P ->
  disjoint h1 h2 ->
  eventually (h1 \u h2) t (P \*+' (= h2)).
Proof using.
  introv M HD. gen h2. induction M using eventually_ind_chained; intros.
  { applys eventually_here. unfolds swap. applys* hstar_intro. }
  { rename H into M, H0 into IH.
    applys eventually_step.
    { applys* omnismall_frame IH. }
    { introv N. lets (h1&D1&->&K1): pstar_inv_same N. applys* K1. } }
Qed.

(** Frame rule for the [ostepsinto] judgment *)

Lemma ostepsinto_frame : forall h1 h2 t Q,
  ostepsinto h1 t Q ->
  disjoint h1 h2 ->
  ostepsinto (h1 \u h2) t (Q \*+ (= h2)).
Proof using.
  introv M HD. unfolds ostepsinto. applys eventually_conseq.
  { applys* eventually_frame M. }
  { introv N. lets (h1'&D1&->&(v'&->&K')): pstar_inv_same (rm N).
    exists v'. splits*. applys* hstar_intro. }
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Construction of Separation Logic *)

(* ########################################################### *)
(** ** Definition of Separation Logic triples *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> ostepsinto s t Q.

(* ########################################################### *)
(** ** Structural Rules *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. unfolds triple. introv M MH MQ HF. applys* ostepsinto_conseq. Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof.
  introv M. intros h HF. lets (h1&h2&M1&M2&MD&MU): (rm HF).
  subst. specializes M M1. applys ostepsinto_conseq.
  { applys ostepsinto_frame M MD. } { xsimpl. intros h' ->. applys M2. }
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  inverts HP. subst. rewrite union_empty_l. applys~ M.
Qed.


(* ########################################################### *)
(** ** Reasoning Rules for Terms *)

Ltac unf := unfolds triple, ostepsinto.

Hint Resolve eventually_val.
Hint Constructors omnismall.

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. unf. introv M Hs. auto. Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using. unf. introv M Hs. applys* eventually_step_chained. Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using. unf. introv M Hs. applys* eventually_step_chained. Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using. unf. introv M1 M2 Hs. applys* eventually_step_chained. Qed.

(** The rule for let-bindings depends on the lemma [eventually_let],
    proved by induction in [OmniSmall.v] *)

Lemma triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using. unf. introv M1 M2 Hs. applys* eventually_let. Qed.


(* ########################################################### *)
(** ** Specification of Primitive Operations *)

Lemma hpure_intro : forall (P:Prop),
  P ->
  \[P] Fmap.empty.
Proof using. introv M. exists M. hnfs*. Qed.

Hint Resolve hpure_intro.

Lemma hempty_inv : forall h,
  \[] h ->
  h = Fmap.empty.
Proof using. introv M. hnfs*. Qed.

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using.
  unf. introv N Hs. lets ->: hempty_inv Hs.
  applys* eventually_step_chained.
Qed.

Lemma triple_rand : forall n,
  n > 0 ->
  triple (val_rand n)
    \[]
    (fun r => \[exists n1, r = val_int n1 /\ 0 <= n1 < n]).
Proof using.
  unf. introv N Hs. lets ->: hempty_inv Hs.
  applys* eventually_step_chained. constructors*.
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof using.
  unf. introv Hs. lets ->: hempty_inv Hs.
  applys* eventually_step_chained. constructors*.
  intros p Hp. applys eventually_val. exists p.
  rewrite hstar_hpure_l. rewrite* update_empty. splits*. hnfs*.
Qed.

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  unf. introv ->. applys* eventually_step_chained. constructors*.
  { applys* indom_single. }
  { rewrite read_single. applys eventually_val.
    rewrite hstar_hpure_l. splits*. hnfs*. }
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun r => (p ~~> v)).
Proof using.
  unf. introv ->. applys* eventually_step_chained. constructors*.
  { applys* indom_single. }
  { rewrite update_single. applys eventually_val. hnfs*. }
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun r => \[]).
Proof using.
  unf. introv ->. applys* eventually_step_chained. constructors*.
  { applys* indom_single. }
  { rewrite remove_single. applys eventually_val. hnfs*. }
Qed.
