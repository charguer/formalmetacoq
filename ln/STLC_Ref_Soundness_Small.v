(***************************************************************************
* Safety for STLC with References - Proofs in Small-Step                   *
* Arthur Chargueraud, July 2007, updated Dec 2023                          *
***************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibLN LibNat.
Require Import STLC_Ref_Definitions STLC_Ref_Infrastructure.


(* ********************************************************************** *)
(** * Statements *)

(** Goal is to prove preservation and progress. Soundness will follow. *)

Definition preservation := forall Y t t' mu mu' T,
  empty ! Y |= t ~: T ->
  (t,mu) --> (t',mu') ->
  Y |== mu ->
  exists Y',
     extends Y Y'
  /\ empty ! Y' |= t' ~: T
  /\ Y' |== mu'.

Definition progress := forall Y t mu T,
  empty ! Y |= t ~: T ->
  Y |== mu ->
     value t
  \/ exists t', exists mu', (t,mu) --> (t',mu').


(* ********************************************************************** *)
(** * Proofs *)

Hint Constructors typing.

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F Y t T,
   (E & G) ! Y |= t ~: T ->
   ok (E & F & G) ->
   (E & F & G) ! Y |= t ~: T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; introv EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as y. apply_ih_bind* H0.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F E Y t T z u U,
  (E & z ~ U & F) ! Y |= t ~: T ->
  E ! Y |= u ~: U ->
  (E & F) ! Y |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; introv Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
  autos*.
Qed.

(** Typing is preserved by an extension of store typing. *)

Lemma typing_stability : forall Y E Y' t T,
  E ! Y |= t ~: T ->
  extends Y Y' ->
  E ! Y' |= t ~: T.
Proof.
  introv Typ Ext. induction* Typ.
Qed.

Hint Resolve typing_stability.

(** Store typing preserved by allocation of a well-typed term. *)

Lemma sto_typing_push : forall Y mu l t T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  l # mu -> l # Y ->
  (Y & l ~ T) |== (mu & l ~ t).
Proof.
  unfold sto_typing. introv [StoOk [Dom Ext]]. splits 3.
    auto.
    intros l0 Fr. simpl_dom. lets: (Dom l0).
      asserts* Fr2: (l <> l0). asserts* Fr3: (l0 # Y). auto.
    intros l' T' Has. binds_cases Has.
      destruct (Ext _ _ B) as [t' [Hast' Typt']].
       exists* t'.
      subst. exists* t.
Qed.

(** A simple short-hand to help clarifying the following proof.
  It simply destruct the induction hypothesis into smaller pieces. *)

Ltac pres H t' mu' :=
  let Y' := fresh "Y'" in
  let Ext := fresh "Ext" in
  let Typt' := fresh "Typt'" in
  let TypSto' := fresh "TypSto'" in
  destruct~ (H (@refl_equal env empty) t' mu')
                  as [Y' [Ext [Typt' TypSto']]].

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t' mu'. gen_eq E: (empty : env).
  induction Typ; intros EQ t' mu' Red TypSto; subst;
   inversions Red. (* todo env_fix.*)
  exists Y. inversions Typ1. splits~ 3.
    pick_fresh x. rewrite* (@subst_intro x).
     apply_empty* typing_subst.
  pres IHTyp1 t1' mu'. exists* Y'.
  pres IHTyp2 t2' mu'. exists* Y'.
  exists (Y & l ~ T).
   asserts Fr: (l # Y). lets: (proj32 TypSto). auto.
   splits~ 3. apply* sto_typing_push.
  pres IHTyp t1' mu'. exists* Y'.
  exists Y. splits~ 3.
    inversions Typ.
     destruct~ ((proj33 TypSto) l T) as [t [Hast Typt]].
     rewrite~ (binds_functional H4 Hast).
  pres IHTyp t1' mu'. exists* Y'.
  exists Y. inversions Typ1. splits~ 3.
    destruct TypSto as [StoOk [Dom Map]]. splits~ 3.
     intros. tests: (l = l0).
       exists t2. split~. rewrite~ (binds_functional H H6).
       destruct (Map _ _ H) as [t [Has Typ]]. exists* t.
  pres IHTyp1 t1' mu'. exists* Y'.
  pres IHTyp2 t2' mu'. exists* Y'.
  exists* Y.
  pres IHTyp t1' mu'. exists* Y'.
Qed.

(** Progression (a well-typed term is either a value or it can
  take a step of reduction). *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (empty : env). lets Typ': Typ.
  induction Typ; intros; subst.
  false* binds_empty_inv.
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' [mu' Red1]]].
    destruct~ IHTyp2 as [Val2 | [t2' [mu' Red2]]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2) mu.
      exists* (trm_app t1 t2') mu'.
    exists* (trm_app t1' t2).
  left*.
  left*.
  left*.
  right. destruct~ IHTyp as [Val1 | [t1' [mu' Red1]]].
    destruct (var_fresh (dom mu)) as [l Fr].
     exists* (trm_loc l) (mu & l ~ t1).
    exists* (trm_ref t1') mu'.
  right. destruct~ IHTyp as [Val1 | [t1' [mu' Red1]]].
    inversions Val1; inversions Typ.
     destruct ((proj33 H) _ _ H5) as [t' [Has' Typt']].
     exists* t' mu.
    exists* (trm_get t1') mu'.
  right. destruct~ IHTyp1 as [Val1 | [t1' [mu' Red1]]].
    destruct~ IHTyp2 as [Val2 | [t2' [mu' Red2]]].
      inversions Val1; inversions Typ1.
       destruct ((proj33 H) _ _ H5) as [t' [Has' Typt']].
       exists* trm_unit (mu & l ~ t2).
      exists* (trm_set t1 t2') mu'.
    exists* (trm_set t1' t2) mu'.
  right. destruct~ IHTyp as [Val1 | [t1' [mu' Red1]]].
    inversions Val1; inversions Typ.
     exists* (trm_int 0) mu. constructors*. lia.
    exists* (trm_rand t1') mu'.
Qed.

(** Type soundness (well-typed configurations can only reach
    safe configurations, i.e. configurations that are values
    or can take a reduction step) *)

Lemma soundness_result : soundness.
Proof using.
  intros (t,mu) (Y&T&HT&HS). introv R.
  gen_eq c: (t,mu). gen Y t mu. induction R; intros; subst.
  { intros. lets [Hv|(t'&mu'&Hp)]: progress_result HT HS.
    { left. hnfs*. }
    { right. exists*. } }
  { intros. destruct c2 as (t2,mu2).
    forwards* (Y'&EP'&HT'&HS'): preservation_result HT H. }
Qed.



