(************************************************************
* Lambda-calculus,                                          *
* Pretty-big-step trace semantics                           *
*************************************************************)

Set Implicit Arguments.
Require Export Lambda_Syntax LibStream Common.

Inductive act :=
  | act_epsilon : act
  | act_echo : nat -> act.

Definition itrace := stream act.
Implicit Types i : itrace.

Inductive instr :=
  | instr_skip : instr
  | instr_echo : nat -> instr.

Definition prog := list instr.

CoInductive cored : prog -> prog -> itrace -> Prop :=
  | cored_nil : forall P i,
     cored P P i ->
     cored P nil (act_epsilon:::i)
  | cored_skip : forall P L i,
     cored P L i ->
     cored P (instr_skip::L) (act_epsilon:::i)
  | cored_echo : forall P L i n,
     cored P L i ->
     cored P (instr_echo n::L) ((act_echo n)::: i).

Fixpoint trans L :=
  match L with
  | nil => nil
  | instr_skip::L' => trans L'
  | instr_echo n::L' => (instr_echo n)::(trans L')
  end.

(*
Fixpoint epsilons n :=
  match n with
  | O => nil
  | S n' => act_epsilon::epsilons n'
  end.
*)

Fixpoint epsilons n i :=
  match n with
  | O => i
  | S n' => act_epsilon:::epsilons n' i
  end.


CoInductive sim : binary itrace :=
  | sim_intro : forall n1 n2 w i1 i2,
     sim i1 i2 ->
     sim (epsilons n1 (w:::i1)) (epsilons n2 (w:::i2)).

CoInductive coredn : nat -> prog -> prog -> itrace -> Prop :=
  | coredn_nil : forall P i p q,
     coredn p P P i ->
     coredn q P nil (act_epsilon:::i)
  | coredn_skip : forall P L i p q,
     coredn p P L i ->
     coredn q P (instr_skip::L) (act_epsilon:::i)
  | coredn_echo : forall P L i n p q,
     coredn p P L i ->
     coredn q P (instr_echo n::L) ((act_echo n):::i)
  | coredn_epsilons : forall a b p P L i,
     coredn p P L (epsilons a i) ->
     coredn (S p) P L (epsilons b i).

CoInductive corednT : nat -> prog -> prog -> itrace -> Type :=
  | corednT_nil : forall P i p q,
     corednT p P P i ->
     corednT (S q) P nil (act_epsilon:::i)
  | corednT_skip : forall P L i p q,
     corednT p P L i ->
     corednT (S q) P (instr_skip::L) (act_epsilon:::i)
  | corednT_echo : forall P L i n p q,
     corednT p P L i ->
     corednT (S q) P (instr_echo n::L) ((act_echo n):::i)
  | corednT_epsilons : forall a b p P L i,
     corednT p P L (epsilons a i) ->
     corednT (S p) P L (epsilons b i).

CoFixpoint wit : forall p P L i (H:corednT p P L i), itrace.
Proof.
  cofix IH.
  introv H.
  assert (next : act*itrace).
    gen p L i. fix 1.
    destruct p; introv M.
    inversion M.
    inversion M.
    exact (act_epsilon,IH _ _ _ _ H0).
    exact (act_epsilon,i).
    exact (act_echo n,i).
    exact (wit0 _ _ _ H0).
  destruct next as [a' i'].
  exact (a':::i').
Defined.

Print wit.


(*

CoFixpoint wit : forall p P L i (H:corednT p P L i), itrace.
Proof.
  cofix IH.
  introv H. destruct H.
  exact (act_epsilon:::(IH _ _ _ _ H)).
  exact (act_epsilon:::(IH _ _ _ _ H)).
  exact (act_echo n:::(IH _ _ _ _ H)).
  assert (next : act*itrace).
  gen H. generalize (epsilons a i) as j. clear a i.
  gen p. fix 1.
    destruct p; introv M.
    inversion M.
    exact (act_epsilon,i).
    exact (act_epsilon,i).
    exact (act_echo n,i).
    inversion M.
    exact (act_epsilon,i).
    exact (act_epsilon,i).
    exact (act_echo n,i).
    exact (wit0 _ _ H0).
  destruct next as [w j].
  exact (w:::j).
Defined.
*)


Lemma sim_one : forall w i1 i2,
     sim i1 i2 ->
     sim (w:::i1) (w:::i2).
Proof.
intros. apply* (sim_intro 0 0).
Defined.

Lemma sim_step : forall i1 i2,
  match i1,i2 with
  | x1:::j1, x2:::j2 => x1 = x2 /\ sim j1 j2
  end ->
  sim i1 i2.
Proof.
  introv H. destruct i1. destruct i2. destruct H. subst.
  apply sim_one. auto.
Qed.

Lemma wit_coredn_sim : forall p P L i
  (H:corednT p P L i),
  sim i (wit H).
Proof.
  cofix IH. intros.
  asserts (?&?&?&?&?&?&?): (exists w p' L' i', exists H':corednT p' P L' i',
    i = w:::i' /\ sim (wit H) (w:::wit H')).
  induction p.
    inversion H.
    destruct H.
    exists __ __ __ __ H. split. eauto.
    eapply sim_step. simpl. split. auto. apply IH.



    unfold wit.
  subst. rewrite H1. apply sim_one. apply IH.
Qed.

 /\ cored P L (wit H i')


Lemma coredn_cored : forall n P L i,
  coredn n P L i ->
  exists i', sim i i' /\ cored P L i'.
Proof.

Qed.



Lemma coredn_epsilon : forall p P L i,
  coredn p P L i ->
  coredn (S p) P L (act_epsilon:::i).
Proof. applys coredn_epsilons O (S O). Defined.

Lemma trans_sim_core : forall P L i,
  cored P L i ->
  coredn (length L) (trans P) (trans L) i.
Proof.
  cofix IH. introv H.
  inverts H; rew_list; simpl.
  constructors*.
  applys* coredn_epsilon.
  constructors*.
Qed.

Lemma trans_sim : forall P L i,
  cored P L i ->
  exists i', sim i i' /\ cored (trans P) (trans L) i'.
Proof.
  introv H.
  applys coredn_cored.
  applys* trans_sim_core.
Qed.


















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

Inductive beh :=
  | beh_val : val -> beh
  | beh_err : beh.

Coercion beh_val : val >-> beh.

Inductive out :=
  | out_ter : ftrace -> beh -> out
  | out_div : itrace -> out.

Implicit Types o : out.

Definition out_prepend f o :=
  match o with
  | out_ter f' b => out_ter (f ++ f') b
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


(** Abort behavior *)

Inductive abort : out -> Prop :=
  | abort_err : forall f, abort (out_ter f beh_err)
  | abort_div : forall i, abort (out_div i).



(** "One rule applies" judgment *)

Inductive one : ext -> Prop :=
  | one_val : forall v,
      one v
  | one_abs : forall x t,
      one (trm_abs x t)
  | one_app : forall t1 t2,
      one (trm_app t1 t2)
  | one_app_1_abort : forall o1 t2,
      abort o1 ->
      one (ext_app_1 o1 t2)
  | one_app_1 : forall v1 t2 f,
      one (ext_app_1 (out_ter f v1) t2)
  | one_app_2_abort : forall v1 o2,
      abort o2 ->
      one (ext_app_2 v1 o2)
  | one_app_2 : forall x t3 v2 f,
      one (ext_app_2 (val_clo x t3) (out_ter f v2)).

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
      red (ext_app_2 (val_clo x t3) (out_ter f v2)) (step (f ^^ o))
  | red_err : forall e,
      ~ one e ->
      red e (out_ter one_step beh_err).

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
      cored (ext_app_2 (val_clo x t3) (out_ter f v2)) (step (f ^^ o))
  | cored_err : forall e,
      ~ one e ->
      cored e (out_ter one_step beh_err).


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
   unfold one_step; rew_list; math.

(*
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
*)



(************************************************************)
(* ** Complete coverage *)

Lemma complete : forall e,
  exists o, cored e o.
Proof.
  skip.
Qed.




(************************************************************)
(* ** Determinacy *)

(* when traces contain only act_epsilon, we have: *)
Lemma itrace_bisim : forall i1 i2,
  i1 === i2.
Proof.
  cofix IH. intros. destruct i1 as [[]].
  destruct i2 as [[]]. constructor. apply IH.
Qed.

Hint Resolve itrace_bisim.

Inductive out_sim : binary out :=
  | out_sim_ter : forall f1 f2 b,
     (* sim_epsilon f1 f2 ->*)
     out_sim (out_ter f1 b) (out_ter f2 b)
  | out_sim_div : forall q1 q2,
     (* sim_epsilon q1 q2 ->*)
     out_sim (out_div q1) (out_div q2).

Hint Constructors one.
Hint Constructors abort.


Lemma determinacy_ter : forall f e b o,
  cored e (out_ter f b) -> cored e o ->
  o = out_ter f b.
Proof.
  intros f. gen_eq n: (length f). gen f.
  induction n using peano_induction.
  asserts IH: (forall e f b o,
    cored e (out_ter f b) -> cored e o ->
    length f < n ->
    o = out_ter f b).
    intros. apply* H. clear H.
  introv E R1 R2. subst. inverts R1.
  inverts R2; [|false*H]. eauto.
  inverts R2; [|false*H]. eauto.
Focus 1.
  inverts R2; [|false*H].
    destruct o2; [|false]. inverts H.
    asserts (fa&ba&E&L): (exists ba fa, o1 = out_ter fa ba /\
     length fa < length f0).
      inverts H2.
        exists___. split. eauto. skip.
        destruct o1.
           exists___. split. eauto.
           false* H3.
     subst. forwards* E: (>> IH H0 H4).

      inverts H2. false* H3.


  inverts R2; [|false*H].
    destruct o0; [|false]. inverts H.
    destruct o2.
      inverts H2. skip.
      forwards* E: (>> IH H0 H6).
      inverts H2. false* H3.
  inverts R2; [|false*H].
    destruct o0; [|false]. inverts H.
    rewrites* (>> IH H1 H6).
  inverts R2; try solve [ false* H1 ]. eauto.
Qed.

*)

Lemma determinacy_ter' : forall f e b o,
  cored e (out_ter f b) -> cored e o ->
    exists f', o = out_ter f' b.
Proof.
  intros f. gen_eq n: (length f). gen f.
  induction n using peano_induction.
  asserts IH: (forall e f b o,
    cored e (out_ter f b) -> cored e o ->
    length f < n ->
    exists f', o = out_ter f' b).
    intros. apply* H. clear H.
  introv E R1 R2. subst. inverts R1.
  inverts R2; [|false*H]. eauto.
  inverts R2; [|false*H]. eauto.
  inverts R2; [|false*H]. skip.
  inverts R2; [|false*H].
    destruct o0; [|false]. inverts H.
    destruct o2.
      skip.
      inverts H2. false* H3.
  inverts R2; [|false*H].
    destruct o0; [|false]. inverts H.
    forwards* [f' E]: IH H1 H6. subst. simple*.
  inverts R2; try solve [ false* H1 ]. eauto.
Qed.

Lemma determinacy_div : forall e i1 i2,
  cored e (out_div i1) -> cored e (out_div i2) ->
    i1 === i2.
Proof.
  intros. apply itrace_bisim.
Qed.

Lemma determinacy : forall e o1 o2,
  cored e o1 -> cored e o2 -> out_sim o1 o2.
Proof.
  intros.
  destruct o1 as [f1 b|i1].
    forwards* [f' E]: determinacy_ter H. subst.
     constructor.
    destruct o2 as [f2 b|i2].
      forwards* [f' E]: determinacy_ter H. false.
      constructor.
Qed.







(************************************************************)
(* ** Interpreter *)

CoInductive phi :=
  | phi_now : beh -> phi
  | phi_later : act -> phi -> phi.


(** Bind-style operators *)

Definition if_success (r:res) (k:val->phi) : phi :=
  match r with
  | res_return (beh_ret v) => k v
  | _ => r
  end.

Definition if_isclo (v:val) (k:var->trm->phi) : phi :=
  match v with
  | val_clo x t => k x t
  | _ => phi_now beh_err
  end.


CoFixpoint run (t:trm) : phi :=
  phi_later (match t with
    | trm_val v => phi_now v
    | trm_abs x t1 => phi_now (val_clo x t1)
    | trm_var x => phi_now beh_err
    | trm_app t1 t2 =>
       if_success (run t1) (fun v1 =>
         if_success (run t2) (fun v2 =>
            if_isclo v1 (fun x t3 =>
              run (subst x v2 t3))))
    end).













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



























