(************************************************************
* Lambda-calculus,                                          *
* Type soundness proof                                      *
* using combined pretty-big-step semantics with error rules *
*************************************************************)

Set Implicit Arguments.
Require Import Lambda_CombiErr Lambda_Typing LibLN LibInt.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Proof of type soundness *)

(** Hints *)

Hint Constructors one typing.
Hint Extern 1 (_ < _) => math.
Hint Extern 1 (~ one _ -> exists _, _) => 
  let H := fresh in intros H; false H.

(** Regularity lemma *)

Lemma typing_ok : forall E t T,
  typing E t T -> ok E.
Proof. introv H. induction* H. Qed.

(** Weakening for values *)

Lemma typing_val_weaken : forall E v T,
  typing empty v T -> ok E -> typing E v T.
Proof. introv H. inverts* H. Qed.

(** Substitution lemma *)

Lemma typing_subst : forall E x T U t v,
  typing empty v U ->
  typing (empty & single x U & E) t T ->
  typing E (subst x v t) T.
Proof.
  introv Tv Tt. inductions Tt; simpl.
  constructors*.
  constructors*.
  case_if. 
    binds_cases H0.
      false* binds_empty_inv. 
      subst. applys* typing_val_weaken.
      lets (?&?): (ok_middle_inv H).
       false~ (binds_fresh_inv B0).
    binds_cases H0.
      false* binds_empty_inv.
      constructors~.
  case_if.
    false. lets: typing_ok Tt.
     rewrite <- concat_assoc in H.
     lets (?&M): (ok_middle_inv H).
     simpl_dom. notin_false.
    forwards*: IHTt. rewrite* concat_assoc. 
  constructors*.
Qed.

(** Soundness lemma, by induction on the height
    of a derivation that ends up in an error *)

Lemma soundness_ind : forall n t b T,
  cred t (out_ter n b) -> typing empty t T -> 
  exists v, b = beh_ret v /\ typing empty v T.
Proof.
  induction n using peano_induction.
  introv R M. inverts~ R as.
  exists* v.
  inverts* M.
  introv R1 R2 [L2 L1]. inverts L2. inverts L1.  
   inverts M as M1 M2.
   forwards~ (v1&E1&V1): H R1 M1. inverts E1. 
   inverts V1. inverts R2 as; auto.
   introv R2 R3 [L3 L2]. inverts L3. inverts L2.
   forwards* (v2&E2&V2): H R2.
   inverts E2. inverts~ R3 as.
   introv R3 L3. inverts L3.
   applys* H R3. apply_empty* typing_subst.
  introv N. false (rm N). destruct~ t.
    inverts M. false* binds_empty_inv.
Qed.

(** Soundness theorem: 
    Well-typed terms don't end up in an error *)

Lemma soundness : forall t T, 
  typing empty t T -> ~ cstuck t.
Proof. introv M (n&R). false soundness_ind R M. Qed.


