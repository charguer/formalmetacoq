(***************************************************************************
* Safety for STLC with References - Proofs in Small-Step                   *
* Arthur Chargueraud, July 2007, updated Dec 2023                          *
***************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibNat.
Require Import STLC_Ref_Soundness_Common.


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

(** A simple short-hand to help clarifying the following proof.
  It simply destruct the induction hypothesis into smaller pieces. *)

Ltac pres H t' mu' :=
  let Y' := fresh "Y'" in
  let Ext := fresh "Ext" in
  let Typt' := fresh "Typt'" in
  let TypSto' := fresh "TypSto'" in
  destruct~ (H (@refl_equal env empty) t' mu')
                  as (Y'&Ext&Typt'&TypSto').

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
     destruct~ ((proj33 TypSto) l T) as (t&Valt&Hast&Typt).
     rewrite~ (binds_functional H4 Hast).
  pres IHTyp t1' mu'. exists* Y'.
  exists Y. inversions Typ1. splits~ 3.
    destruct TypSto as (StoOk&Dom&Map). splits~ 3.
     intros. tests: (l = l0).
       exists t2. split~. rewrite~ (binds_functional H H6).
       destruct (Map _ _ H) as (t&Has&Typ). exists* t.
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
  right. destruct~ IHTyp1 as [Val1 | (t1'&mu'&Red1)].
    destruct~ IHTyp2 as [Val2 | (t2'&mu'&Red2)].
      inversions Typ1; inversions Val1. exists* (t0 ^^ t2) mu.
      exists* (trm_app t1 t2') mu'.
    exists* (trm_app t1' t2).
  left*.
  left*.
  left*.
  right. destruct~ IHTyp as [Val1 | (t1'&mu'&Red1)].
    destruct (var_fresh (dom mu)) as [l Fr].
     exists* (trm_loc l) (mu & l ~ t1).
    exists* (trm_ref t1') mu'.
  right. destruct~ IHTyp as [Val1 | (t1'&mu'&Red1)].
    inversions Val1; inversions Typ.
     destruct ((proj33 H) _ _ H5) as (t'&Has'&Typt').
     exists* t' mu.
    exists* (trm_get t1') mu'.
  right. destruct~ IHTyp1 as [Val1 | (t1'&mu'&Red1)].
    destruct~ IHTyp2 as [Val2 | [t2' [mu' Red2]]].
      inversions Val1; inversions Typ1.
       destruct ((proj33 H) _ _ H5) as (t'&Has'&Typt').
       exists* trm_unit (mu & l ~ t2).
      exists* (trm_set t1 t2') mu'.
    exists* (trm_set t1' t2) mu'.
  right. destruct~ IHTyp as [Val1 | (t1'&mu'&Red1)].
    inversions Val1; inversions Typ.
     exists* (trm_int 0) mu. constructors*.
       unfold max. case_if; nat_math.
    exists* (trm_rand t1') mu'.
Qed.


(* ********************************************************************** *)
(** * Generic result: type soundness follows from preservation and progress *)

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



