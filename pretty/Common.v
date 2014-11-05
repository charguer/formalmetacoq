(************************************************************
* Wrapper around the library TLC                            *
*************************************************************)


Set Implicit Arguments.
Require Export LibTactics LibCore LibVar LibEnv.
Generalizable Variables A B.

(** Formalization of [max] on natural numbers *)

Definition max (n m:nat) :=
  If n < m then m else n.

Lemma max_cases : forall n m, 
  (n <= m /\ max n m = m) \/
  (m <= n /\ max n m = n).
Proof.
  intros. unfold max. case_if. 
  left. math.
  right. math.
Qed.
















(* todo: liblist *)
Fixpoint assoc_option A B k (l:list (A*B)) : option B :=
  match l with 
  | nil => None
  | (x,v)::l' => If x = k then Some v else assoc_option k l' 
  end.

(* todo move *)

CoInductive colist (A:Type) : Type :=
  | colist_nil : colist A
  | colist_cons : A -> colist A -> colist A.

Implicit Arguments colist_nil [[A]].

Notation "x :::: s" := (colist_cons x s) (at level 30, right associativity).

Definition colist_one A (x:A) :=
  x :::: colist_nil.





CoFixpoint colist_append A (s1 s2 : colist A) :=
  match s1 with
  | colist_nil => s2
  | colist_cons x s1' => colist_cons x (colist_append s1' s2)
  end.

Notation "s1 +++ s2" := (colist_append s1 s2) (at level 31).

Definition step_eq A (s1 s2 : colist A) :=
  match s1,s2 with 
  | colist_nil, colist_nil => True
  | colist_cons x1 s1', colist_cons x2 s2' => x1 = x2 /\ s1' = s2'
  | _ , _ => False
  end.

Lemma step_eq_inj : forall A (s1 s2 : colist A),
  step_eq s1 s2 -> s1 = s2.
Proof.
  introv H. destruct s1; destruct s2; simpls; inverts~ H.
Qed.

Definition step_eq_left A (s1 s2 : colist A) :=
  match s1 with 
  | colist_nil => s2 = colist_nil
  | colist_cons x1 s1' => s2 = colist_cons x1 s1'
  end.

Lemma step_eq_left_inj : forall A (s1 s2 : colist A),
  step_eq_left s1 s2 -> s1 = s2.
Proof.
  introv H. destruct s1; simpls; inverts~ H.
Qed.

Definition colist_step A (s : colist A) : colist A :=
  match s with
  | colist_nil => colist_nil
  | colist_cons x s' => colist_cons x s' 
  end.

Theorem colist_step_eq : forall A (s : colist A), 
  s = colist_step s.
Proof. intros. destruct s; reflexivity. Qed.


Lemma colist_append_nil : forall A (s : colist A),
  colist_append colist_nil s = s.
Proof.
  intros. rewrite (colist_step_eq (colist_append colist_nil s)).
  simpl. destruct~ s.
Qed.

Lemma colist_append_cons : forall A x (s1 s2 : colist A),
  colist_append (colist_cons x s1) s2 = colist_cons x (colist_append s1 s2).
Proof.
  intros. rewrite (colist_step_eq (colist_append (colist_cons x s1) s2)).
  simpl. auto.
Qed.

Inductive colist_finite (A:Type) : colist A -> Prop :=
  | colist_finite_nil : 
      colist_finite colist_nil
  | colist_finite_cons : forall x s,
      colist_finite s ->
      colist_finite (x::::s).

Implicit Arguments colist_finite [[A]].

CoInductive colist_infinite (A:Type) : colist A -> Prop :=
  | colist_infinite_cons : forall x s,
      colist_infinite s ->
      colist_infinite (x::::s).

Implicit Arguments colist_infinite [[A]].

Hint Constructors colist_finite.

Lemma colist_finite_one : forall A (x:A),
  colist_finite (colist_one x).
Proof. unfolds~ colist_one. Qed.

Hint Resolve colist_finite_one.

Implicit Arguments colist_append [A].

Notation "'cnil'" := (colist_nil).

Lemma colist_append_nil_l : forall A (s:colist A),
  cnil +++ s = s.
Proof.
  intros. rewrite (colist_step_eq (cnil +++ s)).
  destruct~ s.
Qed.

(*
Lemma colist_append_nil_r : forall A (s:colist A),
  s +++ cnil = s.
*)

Hint Rewrite colist_append_nil colist_append_cons 
  colist_append_nil_l : rew_colist.

Tactic Notation "rew_colist" := autorewrite with rew_colist.
Tactic Notation "rew_colist" "~" := rew_colist; auto_tilde.
Tactic Notation "rew_colist" "*" := rew_colist; auto_star.
Tactic Notation "rew_colist" "in" hyp(H) := autorewrite with rew_colist in H.
Tactic Notation "rew_colist" "~" "in" hyp(H) := rew_colist in H; auto_tilde.
Tactic Notation "rew_colist" "*" "in" hyp(H) := rew_colist in H; auto_star.
Tactic Notation "rew_colist" "in" "*" := autorewrite with rew_colist in *.
Tactic Notation "rew_colist" "~" "in" "*" := rew_colist in *; auto_tilde.
Tactic Notation "rew_colist" "*" "in" "*" := rew_colist in *; auto_star.


Lemma colist_append_assoc_finite : forall A (s1 s2 s3 : colist A),
  colist_finite s1 ->
  (s1 +++ s2) +++ s3 = s1 +++ (s2 +++ s3).
Proof.
  introv F1. induction F1; rew_colist~. fequals.
Qed.

Lemma colist_finite_append : forall A (s1 s2 : colist A),
  colist_finite s1 ->
  colist_finite s2 ->
  colist_finite (s1 +++ s2).
Proof. introv F1 F2. induction F1; rew_colist~. Qed.

Hint Resolve colist_finite_append.

Lemma colist_one_not_nil : forall A (x:A),
  colist_one x <> colist_nil.
Proof. intros_all. false. Qed.

Lemma colist_append_to_not_nil : forall A (s1 s2 : colist A),
  s2 <> colist_nil -> (colist_append s1 s2) <> colist_nil.
Proof. intros. destruct s1; rew_colist; auto_false. Qed.

(*
Lemma colist_append_infinite : forall A (s1 s2 : colist A),
  colist_infinite s2 ->
  colist_infinite (s1 +++ s2).
Proof.
  introv H. induction s1; rew_colist~.

Lemma colist_append_infinite_prod : forall A (s1 s2 : colist A),
  s1 <> colist_nil ->
  colist_infinite s2 ->
  colist_infinite (s1 +++ s2).
Proof.
  introv N F.

Defined.
*)


(*
*)
Require Import LibStream.

CoFixpoint colist_of_stream (A:Type) (s:stream A) : colist A :=
  match s with stream_intro x s' => colist_cons x (colist_of_stream s') end.

Fixpoint colist_of_list (A:Type) (l:list A) : colist A :=
  match l with 
  | nil => colist_nil
  | x :: l' => colist_cons x (colist_of_list l') 
   end.

Fixpoint colist_prepend (A:Type) (l:list A) (s:colist A) : colist A :=
  match l with
  | nil => s
  | x::l' => colist_cons x (colist_prepend l' s)
  end.

Fixpoint stream_prepend (A:Type) (l:list A) (s:stream A) : stream A :=
  match l with
  | nil => s
  | x::l' => stream_intro x (stream_prepend l' s)
  end.



(** Bisimilarity  *)

CoInductive bisimilar (A:Type) : binary (stream A) :=
  | bisimilar_intro : forall x s1 s2,
      bisimilar s1 s2 ->   
      bisimilar (x:::s1) (x:::s2).

(** Bisimilarity modulo Leibnitz *)

Notation "x === y" := (bisimilar x y) (at level 68).

(** Bisimilarity is an equivalence *)

Lemma bisimilar_mod_equiv : forall A,
  equiv (@bisimilar A).
Proof.
  constructor.
  unfolds. cofix IH. destruct x. constructor*.
  unfolds. cofix IH. destruct x; destruct y; introv M.
   inversions M. constructor*.
  unfolds. cofix IH. destruct x; destruct y; destruct z; introv M1 M2.
   inversions M1. inversions M2. constructor*.
Qed.

