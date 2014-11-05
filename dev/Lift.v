Set Implicit Arguments.
Require Import LibTactics BigStep_Definitions.


Definition terminates t :=
  exists v, reds t v.

Definition returns_of t :=
  { v | reds t v }.


Lemma reds_deterministic : forall v v' t,
  reds t v -> reds t v' -> v = v'.
Proof.
  introv R1 R2. gen v'. induction R1; intros.
  inversions R2.
    auto.
    false_inv.
  inversions R2.
    false_inv.
    lets E: IHR1_1 H1. inversions E.
    lets E: IHR1_2 H2. inversions E.
    lets E: IHR1_3 H4. inversions E.
    auto.
Defined.

Lemma terminates_bvar_not : forall i,
  ~ terminates (trm_bvar i).
Proof.
  introv H. inversions H. inversions H0. false_inv. 
Defined.

Lemma terminates_fvar_not : forall x,
  ~ terminates (trm_fvar x).
Proof.
  introv H. inversions H. inversions H0. false_inv. 
Defined.

Lemma terminates_abs : forall t, 
  terminates (trm_abs t) ->
  reds (trm_abs t) (trm_abs t).
Proof.
  introv H. inversions H. inversions H0. apply~ reds_val.
Defined.

Lemma terminates_app_1 : forall t2 t1, 
  terminates (trm_app t1 t2) ->
  terminates t1.
Proof.
  introv [v H]. inversions H. false_inv. exists_*.   
Defined.

Lemma terminates_app_2 : forall t1 t2, 
  terminates (trm_app t1 t2) ->
  terminates t2.
Proof.
  introv [v H]. inversions H. false_inv. exists_*.   
Defined.

Lemma terminates_app_3 : forall t3 v2 t1 t2, 
  terminates (trm_app t1 t2) ->
  reds t1 (trm_abs t3) -> 
  reds t2 v2 ->
  terminates (t3 ^^ v2).
Proof.
  introv [v H] R1' R2'. inverts H as R1 R2 R3.
  false_inv.
  lets E: (reds_deterministic R1' R1). inversions E.
  lets E: (reds_deterministic R2 R2'). inversions E.
  exists_*.   
Defined.

Lemma terminates_app_bvar_not : forall t1 t2 i,
  terminates (trm_app t1 t2) -> 
  reds t1 (trm_bvar i) -> False.
Proof.
  introv [v T] R. inversions T.
  inversions R; false_inv.
  lets E: (reds_deterministic R H1). inversions E.
Defined.

Lemma terminates_app_fvar_not : forall t1 t2 x,
  terminates (trm_app t1 t2) -> 
  reds t1 (trm_fvar x) -> False.
Proof.
  introv [v T] R. inversions T.
  inversions R; false_inv.
  lets E: (reds_deterministic R H1). inversions E.
Defined.

Lemma terminates_app_app_not : forall t1 t2 v1 v2,
  terminates (trm_app t1 t2) -> 
  reds t1 (trm_app v1 v2) -> False.
Proof.
  introv [v T] R. inversions T.
  inversions R; false_inv.
  lets E: (reds_deterministic R H1). inversions E.
Defined.

Inductive ends (t:trm) : Prop :=
  | ends_intro : 
     (forall t1 t2, t = trm_app t1 t2 -> ends t1) ->
     (forall t1 t2, t = trm_app t1 t2 -> ends t2) ->
     (forall t1 t2 t3 v2, t = trm_app t1 t2 -> 
        reds t1 (trm_abs t3) ->
        reds t2 v2 ->
        ends (t3 ^^ v2)) ->
     ends t.

Lemma terminates_ends : forall t,
  terminates t -> ends t.
Proof. 
  introv [v H]. induction H.
  inversions H. constructor; introv Eq; inversions Eq.
  constructor; introv Eq; inversions Eq.
  auto.
  auto.
  introv R2 R3.
  lets E: (reds_deterministic R2 H). inversions E.
  lets E: (reds_deterministic R3 H0). inversions E.
  auto.
Defined.

Definition eval_core : 
  forall (t:trm) (H:terminates t), (returns_of t).
Proof.
introv H.
lets H': (terminates_ends H). gen H.
induction H' as [t H1 IH1 H2 IH2 H3 IH3].
introv H. destruct t.
false* terminates_bvar_not. 
false* terminates_fvar_not.
constructors. apply~ terminates_abs.
destruct~ (IH1 t1 t2) as [v1 R1]. apply* terminates_app_1.
destruct~ (IH2 t1 t2) as [v2 R2]. apply* terminates_app_2.
destruct v1. 
  false* terminates_app_bvar_not.
  false* terminates_app_fvar_not.
  destruct~ (IH3 t1 t2 v1 v2) as [v3 R3].
   apply* terminates_app_3.
   constructors. apply* reds_red.
    false* terminates_app_app_not.
Defined.

Print eval_core.

Definition eval (t:trm) (H:terminates t) :=
  proj1_sig (eval_core H).

Require Import Metatheory.

Hint Constructors term.

Definition test := 
  trm_app (trm_abs (trm_bvar 0)) (trm_abs (trm_bvar 0)).

Lemma terminates_test : terminates test.
Proof.
  exists (trm_abs (trm_bvar 0)).
  unfold test.
  constructors.
  apply reds_val. apply value_abs. apply (@term_abs {}). 
   intros. unfold open. simple~.
  apply reds_val. apply value_abs. apply (@term_abs {}). 
   intros. unfold open. simple~.
  unfold open. simpl. apply reds_val.
  apply value_abs. apply (@term_abs {}). 
   intros. unfold open. simple~.
Defined.

Eval compute in (eval terminates_test).
(* It works !! *)


Notation "'returns' t" := (exist _ t _) (at level 67).

Program Fixpoint Eval
  (t:trm) (H:ends t) {struct H} : (terminates t -> returns_of t) :=
  fun T => match t with 
  | trm_app t1 t2 => 
     let (t1',H1) := @Eval t1 _ _ in
     let (t2',H2) := @Eval t2 _ _ in
     match t1' with
     | trm_abs t3 => 
         let (t',H3) := @Eval (t3 ^^ t2') _ _ in 
         returns t'
     | _ => returns (trm_app t1' t2')
     end 
  | _ => returns t
  end.
Next Obligation.
apply terminates_ends. apply* terminates_app_1.
Defined.
Next Obligation.
apply* terminates_app_1.
Defined.
Next Obligation.
apply terminates_ends. apply* terminates_app_2.
Defined.
Next Obligation.
apply* terminates_app_2.
Defined.
Next Obligation.
apply terminates_ends. apply* terminates_app_3.
Defined.
Next Obligation.
apply* terminates_app_3.
Defined.
Next Obligation.
apply* reds_red.
Defined.
Next Obligation.
destruct t1'.
false* terminates_app_bvar_not.
false* terminates_app_fvar_not.
false*.
false* terminates_app_app_not.
Defined.
Next Obligation.
destruct t.
false* terminates_bvar_not. 
false* terminates_fvar_not.
apply* terminates_abs.
false*.
Defined.

(*
Error:
Recursive definition of Eval is ill-formed.
In environment
Eval : forall t : trm, ends t -> terminates t -> returns_of t
t : trm
H : ends t
T : terminates t
t1 : trm
t2 : trm
Heq_t : trm_app t1 t2 = t
Recursive call to Eval has principal argument equal to
"Eval_obligation_1 H T Heq_t"
instead of a subterm of H.
*)



(*  let eval t' := @Eval t' _ _ in
  puis appeler "eval t1" ça ne marche pas .. *)

Proof.
introv H.
lets H': (terminates_ends H). gen H.
induction H' as [t H0 H1 IH1 H2 IH2 H3 IH3].
introv H. destruct t.
false* terminates_bvar_not. 
false* terminates_fvar_not.
constructors. apply~ terminates_abs.
destruct~ (IH1 t1 t2) as [v1 R1]. apply* terminates_app_1.
destruct~ (IH2 t1 t2) as [v2 R2]. apply* terminates_app_2.
destruct v1. 
  false* terminates_app_bvar_not.
  false* terminates_app_fvar_not.
  destruct~ (IH3 t1 t2 v1 v2) as [v3 R3].
   apply* terminates_app_3.
   constructors. apply* reds_red.
    false* terminates_app_app_not.
Defined.




