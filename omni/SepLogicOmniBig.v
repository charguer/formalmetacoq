(****************************************************************
* Imperative Lambda-calculus                                    *
* Separation Logic on Omni-Big-Step                             *
*****************************************************************)

Set Implicit Arguments.
Require Export SepLogicCommon OmniBig.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types s : state.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Proof of the Frame Property for Omni-Big-Step *)

Lemma omnibig_frame : forall h1 h2 t Q,
  omnibig h1 t Q ->
  Fmap.disjoint h1 h2 ->
  omnibig (h1 \u h2) t (Q \*+ (= h2)).
Proof using.
  introv M HD. gen h2. induction M; intros;
    try solve [ hint hstar_intro; constructors* ].
  { rename M into M1, H into M2, IHM into IH1, H0 into IH2.
    specializes IH1 HD. applys omnibig_let IH1. introv HK.
    lets (h1'&h2'&K1'&K2'&KD&KU): HK. subst. applys* IH2. }
  { rename H into M. applys omnibig_ref. intros p Hp.
    rewrite Fmap.indom_union_eq in Hp. rew_logic in Hp.
    destruct Hp as [Hp1 Hp2].
    rewrite* Fmap.update_union_not_r. applys hstar_intro.
    { applys* M. } { auto. } { applys* Fmap.disjoint_update_not_r. } }
  { applys omnibig_get. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.read_union_l. applys* hstar_intro. } }
  { applys omnibig_set. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.update_union_l. applys hstar_intro.
      { auto. } { auto. } { applys* Fmap.disjoint_update_l. } } }
  { applys omnibig_free. { rewrite* Fmap.indom_union_eq. }
    { rewrite* Fmap.remove_disjoint_union_l. applys hstar_intro.
      { auto. } { auto. } { applys* Fmap.disjoint_remove_l. } } }
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Construction of Separation Logic *)

(* ########################################################### *)
(** ** Definition of Separation Logic triples *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> omnibig s t Q.


(* ########################################################### *)
(** ** Structural Rules *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. unfolds triple. introv M MH MQ HF. applys* omnibig_conseq. Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof.
  introv M. intros h HF. lets (h1&h2&M1&M2&MD&MU): (rm HF).
  subst. specializes M M1. applys omnibig_conseq.
  { applys omnibig_frame M MD. } { xsimpl. intros h' ->. applys M2. }
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
  inverts HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.


(* ########################################################### *)
(** ** Reasoning Rules for Terms *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. introv M Hs. applys* omnibig_val. Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using. introv M Hs. applys* omnibig_fix. Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using. introv M Hs. applys* omnibig_if. Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M Hs. applys* omnibig_app_fix. Qed.

Lemma triple_let : forall x t1 t2 Q1 H Q,
  triple t1 H Q1 ->
  (forall v1, triple (subst x v1 t2) (Q1 v1) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using. introv M1 M2 Hs. applys* omnibig_let. Qed.


(* ########################################################### *)
(** ** Specification of Primitive Operations *)

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using.
  introv Hn2 Hs. applys* omnibig_div. inverts Hs. exists*. hnfs*.
Qed.

Lemma triple_rand : forall n,
  n > 0 ->
  triple (val_rand n)
    \[]
    (fun r => \[exists n1, r = val_int n1 /\ 0 <= n1 < n]).
Proof using.
  introv Hn2 Hs. applys* omnibig_rand. inverts Hs.
  intros n1 Hn1. hnfs. exists*. hnfs*.
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).
Proof using.
  intros. intros s1 K. applys omnibig_ref. intros p D.
  inverts K. rewrite Fmap.update_empty. exists p.
  rewrite hstar_hpure_l. split*. hnfs*.
Qed.

Lemma triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).
Proof using.
  intros. intros s K. inverts K. applys omnibig_get.
  { applys* Fmap.indom_single. }
  { rewrite hstar_hpure_l. split*. rewrite* Fmap.read_single. hnfs*. }
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) v)
    (p ~~> w)
    (fun r => (p ~~> v)).
Proof using.
  intros. intros s1 K. inverts K. applys omnibig_set.
  { applys* Fmap.indom_single. }
  { rewrite Fmap.update_single. hnfs*. }
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun r => \[]).
Proof using.
  intros. intros s1 K. inverts K. applys omnibig_free.
  { applys* Fmap.indom_single. }
  { rewrite* Fmap.remove_single. hnfs*. }
Qed.

(** For example proofs in Separation Logic, see the course:
    Separation Logic Foundations, vol 6 of the Software Foundations series:
    https://softwarefoundations.cis.upenn.edu/slf-current/index.html *)
