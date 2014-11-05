(***************************************************************************
* A lambda-term evaluator for terminating terms, defined in Coq            *
* Arthur Charguéraud, March 2009                                           *
***************************************************************************)

Set Implicit Arguments.
Require Import LibTactics.


(* ********************************************************************** *)
(** ** Grammar of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_app  : trm -> trm -> trm.


(* ********************************************************************** *)
(** ** Operation to open up abstractions. *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => if k === i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x 
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1    => trm_abs (open_rec (S k) u t1) 
  end.

Definition open t u := open_rec 0 u t.

Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).


(* ********************************************************************** *)
(** ** Definition of well-formedness of a term *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> term (trm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1). 


(* ********************************************************************** *)
(** ** Definition of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).


(* ********************************************************************** *)
(** ** Definition of the small-step semantics *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1, 
      term (trm_abs t1) -> value (trm_abs t1).

Inductive beta : trm -> trm -> Prop :=
  | beta_red : forall t1 t2,
      body t1 -> 
      value t2 ->
      beta (trm_app (trm_abs t1) t2) (t1 ^^ t2) 
  | beta_app1 : forall t1 t1' t2, 
      term t2 ->
      beta t1 t1' -> 
      beta (trm_app t1 t2) (trm_app t1' t2) 
  | beta_app2 : forall t1 t2 t2',
      value t1 ->
      beta t2 t2' ->
      beta (trm_app t1 t2) (trm_app t1 t2').

Inductive beta_star : trm -> trm -> Prop :=
  | beta_star_refl : forall t,
      term t ->
      beta_star t t
  | beta_star_step : forall t2 t1 t3,
      beta t1 t2 -> 
      beta_star t2 t3 -> 
      beta_star t1 t3.


(* ********************************************************************** *)
(** ** Definition of the big-step semantics *)

Inductive reds : trm -> trm -> Prop :=
  | reds_val : forall t1, 
      value t1 ->
      reds t1 t1
  | reds_red : forall t3 v2 v3 t1 t2,
      reds t1 (trm_abs t3) ->
      reds t2 v2 -> 
      reds (t3 ^^ v2) v3 ->
      reds (trm_app t1 t2) v3.


(* ********************************************************************** *)
(** ** Definition of the big-step semantics *)

Definition equivalence := forall t v,
  reds t v <-> beta_star t v /\ value v.












Set Implicit Arguments.
Require Import LibTactics BigStep LibClosure.


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
    inverts_false.
  inversions R2.
    inverts_false.
    lets E: IHR1_1 H1. inversions E.
    lets E: IHR1_2 H2. inversions E.
    lets E: IHR1_3 H4. inversions E.
    auto.
Defined.

Lemma terminates_bvar_not : forall i,
  ~ terminates (trm_bvar i).
Proof.
  introv H. inversions H. inversions H0. inverts_false. 
Defined.

Lemma terminates_fvar_not : forall x,
  ~ terminates (trm_fvar x).
Proof.
  introv H. inversions H. inversions H0. inverts_false. 
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
  introv [v H]. inversions H. inverts_false. exists__*.   
Defined.

Lemma terminates_app_2 : forall t1 t2, 
  terminates (trm_app t1 t2) ->
  terminates t2.
Proof.
  introv [v H]. inversions H. inverts_false. exists__*.   
Defined.

Lemma terminates_app_3 : forall t3 v2 t1 t2, 
  terminates (trm_app t1 t2) ->
  reds t1 (trm_abs t3) -> 
  reds t2 v2 ->
  terminates (t3 ^^ v2).
Proof.
  introv [v H] R1' R2'. inverts H as R1 R2 R3.
  inverts_false.
  lets E: (reds_deterministic R1' R1). inversions E.
  lets E: (reds_deterministic R2 R2'). inversions E.
  exists__*.   
Defined.

Lemma terminates_app_bvar_not : forall t1 t2 i,
  terminates (trm_app t1 t2) -> 
  reds t1 (trm_bvar i) -> False.
Proof.
  introv [v T] R. inversions T.
  inversions R; inverts_false.
  lets E: (reds_deterministic R H1). inversions E.
Defined.

Lemma terminates_app_fvar_not : forall t1 t2 x,
  terminates (trm_app t1 t2) -> 
  reds t1 (trm_fvar x) -> False.
Proof.
  introv [v T] R. inversions T.
  inversions R; inverts_false.
  lets E: (reds_deterministic R H1). inversions E.
Defined.

Lemma terminates_app_app_not : forall t1 t2 v1 v2,
  terminates (trm_app t1 t2) -> 
  reds t1 (trm_app v1 v2) -> False.
Proof.
  introv [v T] R. inversions T.
  inversions R; inverts_false.
  lets E: (reds_deterministic R H1). inversions E.
Defined.

Inductive ends (t:trm) : Prop :=
  | ends_intro : 
     (forall t1, t = trm_abs t1 -> True) ->
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
   auto.
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


