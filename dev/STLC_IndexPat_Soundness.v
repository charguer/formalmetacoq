(***************************************************************************
* Safety for STLC with Patterns - Proofs                                  *
* Extented from "Type Safety for STLC" by                                  *
* Arthur Charguéraud, July 2007, Coq v8.1                                  *
***************************************************************************)

Set Implicit Arguments.
Require Import List Metatheory 
  STLC_Pat_Definitions 
  STLC_Pat_Infrastructure.

(* ********************************************************************** *)
(** * Proofs *)

(** Typing is preserved by weakening. *)

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. inductions Typ with gen_eq H:(E & G) 
   and gen G, introv end; introv Ok.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs. 
   do_rew* concat_assoc (apply* H0).
  apply_fresh* typing_let as xs. 
    do_rew* concat_assoc (apply* H1).
  autos*.
  autos*.
Qed.

(** Typing is preserved by substitution. *)

Lemma typing_subst : forall F U E t T z u,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. inductions Typt with gen_eq G:(E & z ~ U & F)
   and gen F, introv end; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs. 
   rewrite* subst_open_vars.
   do_rew concat_assoc (apply* H0).
  apply_fresh* typing_let as xs.
   rewrite* subst_open_vars.
   do_rew* concat_assoc (apply* H1).
  autos*.
  autos*.
Qed.

(** Typing is preserved by iterated substitution. *)

Lemma typing_substs : forall Us E xs ts t T,
   length xs = length ts ->
   typings E ts Us ->
   E & (iter_push xs Us) |= t ~: T ->
   E |= substs xs ts t ~: T.
Proof.
  intros Us E xs. inductions xs with gen Us E end; 
   simpl; introv Le Typts Typt. auto.
  destruct ts; simpls; inversions Le. inversions Typts. 
  rewrite iter_push_cons in Typt. 
  rewrite <- concat_assoc in Typt.
  apply* (@IHxs Us0).
  apply* typing_subst.
Qed.

(** Typing the result of pattern matching. *)

Lemma typing_pattern_match : forall p t T E ts Us,
  Some ts = pat_match p t ->
  E |= t ~: T ->
  Us \= p ~: T ->
  typings E ts Us.
Proof.
  induction p; introv EQ Typt Typp; destruct t; 
   inversion Typp; inversion EQ; auto; subst; inversions Typt; autos*.
  remember (pat_match p1 t1) as K1. 
   remember (pat_match p2 t2) as K2. 
   destruct K1 as [ts1|]; destruct K2 as [ts2|]; try discriminate.
   inversions H6. apply* typings_concat.
Qed.

(** Preservation (typing is preserved by reduction). *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; inversions Red.
  pick_freshes (pat_arity p1) xs.
   forwards~ K: (@pat_match_terms p1 t1 ts).
   rewrite (fresh_length _ _ _ Fr) in K.
   rewrite* (@substs_intro xs).
   apply~ (@typing_substs Us). unfolds terms. auto. 
   apply~ (@typing_pattern_match p1 t1 T).
  autos*.
  inversions Typ1. pick_fresh x.
    rewrite* (@substs_intro (x::nil)). unfolds substs.
    apply_empty* typing_subst.
  autos*.
  autos*.
  autos*.
  autos*.
Qed.

(** Lemma : well-typed pattern matching never fails. *)

Lemma matching_successful : forall p Us v T,
  empty |= v ~: T ->
  value v ->
  Us \= p ~: T ->
  exists vs, pat_match p v = Some vs.
Proof.
  introv Typ. inductions Typ with gen_eq E:(empty:env) 
   and gen p Us, introv Us' end; introv Val Pat;
   inversions Val; inversions Pat; simpl; eauto.
  forwards~ [vs1 Eq1]: (@IHTyp1 p1 Us1). clear IHTyp1.
   forwards~  [vs2 Eq2]: (@IHTyp2 p2 Us2). clear IHTyp2.
   exists (vs1 ++ vs2). rewrite Eq1. rewrite* Eq2.
Qed.

(** Progress (a well-typed term is either a value or it can 
  take a step of reduction). *)
Lemma progress_result : progress.
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ with gen_eq E:(empty:env).
  false. 
  left*. 
  right. destruct~ IHTyp as [Val1 | [t1' Red1]].
    destruct~ (@matching_successful p1 Us _ _ Typ) as [vs Eq].
     exists* (t2 ^^ vs).
    exists* (trm_let p1 t1' t2).
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1.
       exists* (t0 ^^ (t2::nil)). 
      exists* (trm_app t1 t2'). 
    exists* (trm_app t1' t2).
  destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
     right. exists* (trm_pair t1 t2').
     right. exists* (trm_pair t1' t2).
Qed.


