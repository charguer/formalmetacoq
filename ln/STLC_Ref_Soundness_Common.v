(***************************************************************************
* Safety for STLC with References - Common Parts of Type Soundness Proofs  *
* Arthur Chargueraud, Dec 2023                                             *
***************************************************************************)

Set Implicit Arguments.
Require Export STLC_Ref_Definitions STLC_Ref_Infrastructure.

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
  value t ->
  empty ! Y |= t ~: T ->
  l # mu -> l # Y ->
  (Y & l ~ T) |== (mu & l ~ t).
Proof.
  unfold sto_typing. introv (StoOk&Dom&Ext). splits 3.
    auto.
    intros l0 Fr. simpl_dom. lets: (Dom l0).
      asserts* Fr2: (l <> l0). asserts* Fr3: (l0 # Y). auto.
    intros l' T' Has. binds_cases Has.
      destruct (Ext _ _ B) as (t'&Hast'&Typt').
       exists* t'.
      subst. exists* t.
Qed.
