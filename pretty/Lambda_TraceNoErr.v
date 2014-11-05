(************************************************************
* Lambda-calculus,                                          *
* Pretty-big-step trace semantics                           *
*************************************************************)

Set Implicit Arguments.
Require Export Lambda_Syntax LibStream Common.

Implicit Types v : val.
Implicit Types t : trm.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Semantics *)

(** Grammar of actions *)

Inductive act := 
  | act_epsilon : act.

(** Grammar of traces *)

Definition ftrace := list act.
Definition itrace := stream act.

Implicit Types f : ftrace.
Implicit Types i : itrace.

(** Grammar of outcomes *)

Inductive out :=
  | out_ter : ftrace -> val -> out
  | out_div : itrace -> out.

Implicit Types o : out.

Definition out_prepend f o :=
  match o with
  | out_ter f' v => out_ter (f ++ f') v
  | out_div i => out_div (stream_prepend f i)
  end.

Notation "f ^^ o" := (out_prepend f o) (at level 60, right associativity).


Definition one_step := act_epsilon::nil.

Definition step o := 
  one_step ^^ o.

(** Grammar of extended terms *)

Inductive ext : Type :=
  | ext_trm : trm -> ext
  | ext_app_1 : out -> trm -> ext
  | ext_app_2 : val -> out -> ext.

Coercion ext_trm : trm >-> ext.
Implicit Types e : ext.

(** Evaluation judgment *)

Inductive red : ext -> out -> Prop :=
  | red_val : forall v,
      red v (out_ter one_step v)
  | red_abs : forall x t,
      red (trm_abs x t) (out_ter one_step (val_clo x t))
  | red_app : forall o1 t1 t2 o2,
      red t1 o1 ->
      red (ext_app_1 o1 t2) o2 ->
      red (trm_app t1 t2) (step o2)
  | red_app_1_abort : forall t2 i,
      red (ext_app_1 (out_div i) t2) (step (out_div i))
  | red_app_1 : forall o2 v1 t2 o f,
      red t2 o2 ->
      red (ext_app_2 v1 o2) o ->
      red (ext_app_1 (out_ter f v1) t2) (step (f ^^ o))
  | red_app_2_abort : forall v1 i,
      red (ext_app_2 v1 (out_div i)) (step (out_div i))
  | red_app_2 : forall x t3 v2 o f,
      red (subst x v2 t3) o ->
      red (ext_app_2 (val_clo x t3) (out_ter f v2)) (step (f ^^ o)).

(** Co-evaluation judgment: copy-paste of the above
    definition, where [red] is replaced with [cored]
    and where [Inductive] becomes [CoInductive]. *)

CoInductive cored : ext -> out -> Prop :=
  | cored_val : forall v,
      cored v (out_ter one_step v)
  | cored_abs : forall x t,
      cored (trm_abs x t) (out_ter one_step (val_clo x t))
  | cored_app : forall o1 t1 t2 o2,
      cored t1 o1 ->
      cored (ext_app_1 o1 t2) o2 ->
      cored (trm_app t1 t2) (step o2)
  | cored_app_1_abort : forall t2 i,
      cored (ext_app_1 (out_div i) t2) (step (out_div i))
  | cored_app_1 : forall o2 v1 t2 o f,
      cored t2 o2 ->
      cored (ext_app_2 v1 o2) o ->
      cored (ext_app_1 (out_ter f v1) t2) (step (f ^^ o))
  | cored_app_2_abort : forall v1 i,
      cored (ext_app_2 v1 (out_div i)) (step (out_div i))
  | cored_app_2 : forall x t3 v2 o f,
      cored (subst x v2 t3) o ->
      cored (ext_app_2 (val_clo x t3) (out_ter f v2)) (step (f ^^ o)).


(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Basic properties of the semantics *)


Hint Constructors red cored.
Hint Extern 1 (_ <> _) => congruence.

(** Proof that [cored] contains [red] *)

Theorem red_cored : forall e o,
  red e o -> cored e o.
Proof. introv H. induction* H. Qed.

(** Proof that [cored] on a finite trace implies [red] *)

Hint Extern 1 (length _ < length _) =>
   unfold one_step; rew_length; math.


Theorem cored_ter_red : forall f e v,
  cored e (out_ter f v) -> red e (out_ter f v).
Proof.  
  intros f. gen_eq n: (length f). gen f.
  induction n using peano_induction.
  introv E R. subst. 
  asserts IH: (forall e v f', cored e (out_ter f' v) -> 
    length f' < length f -> red e (out_ter f' v)).
    introv M L. applys* H. clear H. 
  inverts R as.
  auto.
  auto.
  introv R1 R2 E. destruct o2; simpls; inverts E.
   forwards~ M1: IH R2. inverts M1 as R3 R4 F.
   destruct o; simpls; inverts F.
   forwards~ M2: IH R1. applys_eq* red_app 1.
  introv R1 R2 E. destruct o; simpls; inverts E.
   forwards~ M1: IH R2. inverts M1 as R3 F.
   destruct o; simpls; inverts F.
   forwards~ M2: IH R1. applys_eq* red_app_1 1.
  introv R1 E. destruct o; simpls; inverts E.
   forwards~ M1: IH R1. applys_eq* red_app_2 1.
Qed.


(************************************************************)
(* ** Basic properties of the semantics *)














Hint Resolve bisimilar_mod_equiv.

(*
Lemma stream_prepend_bisimilar_inv : forall f i1 i2',
  stream_prepend f i1 === i2' ->
  exists i2, i1 === i2 /\ stream_prepend f i2 = i2'.
Proof.
  intros f. induction f; introv E; simpls.
  exists* i2'.
  destruct i2' as [b i2']. inverts E.
  forwards (i3&?&?): IHf.
  skip.
  exists i3. split*. fequals.
Qed.

*)


Lemma equates_1 : forall A0,
  forall (P:A0->Prop) x1 y1,
  P y1 -> x1 = y1 -> P x1.
Proof. intros. subst. auto. Defined.


Ltac equates_lemma n ::=
  match nat_from_number n with
  | 0%nat => constr:(equates_0)
  | 1%nat => constr:(equates_1)
  | 2%nat => constr:(equates_2)
  | 3%nat => constr:(equates_3)
  | 4%nat => constr:(equates_4)
  | 5%nat => constr:(equates_5)
  | 6%nat => constr:(equates_6)
  end.  


Hint Extern 1 (_ === _) =>
  apply equiv_refl; apply bisimilar_mod_equiv.

Theorem cored_div_bisim : forall t i i',
  cored t (out_div i) -> bisimilar i i' -> cored t (out_div i').
Proof.
  cofix IH. introv R B. inverts R as.
  introv R1 R2 E. destruct o2; simpls; tryfalse.
   destruct i as [x i1]. destruct i' as [x' i1']. inverts B as B.
   inverts E. inverts R2 as.
     inverts B. forwards* M1: IH R1. applys_eq* cored_app 1.
     introv R2 R3 E. destruct o; simpls; tryfalse.
      destruct i1 as [x i2]. destruct i1' as [x' i2']. inverts B as B.
      inverts E. lets (i2&B1&B2): stream_prepend_bisimilar_inv B.
      inverts R3 as.
        inverts B1. subst. forwards* M1: IH R2. applys_eq* cored_app 1.
        introv R3 E. destruct o; simpls; tryfalse.
         inverts E. inverts B1 as B1.
          lets (i3&B3&B4): stream_prepend_bisimilar_inv B1.
           forwards* M1: IH R3. subst. applys_eq* cored_app 1.
Qed.



























