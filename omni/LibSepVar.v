(****************************************************************
* Representation of Variables as Strings                        *
* Utility Functions                                             *
****************************************************************)

Set Implicit Arguments.
From TLC Require Export LibString LibList LibCore.
Open Scope string_scope.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Representation of Program Variables *)

(** This file contains definitions, lemmas, tactics and notations for
    manipulating program variables and list of program variables. *)


(* ########################################################### *)
(** ** Representation of Variables *)

(** Variables are represented as strings *)

Definition var : Type := string.

(** The boolean function [var_eq s1 s2] compares two variables. *)

Definition var_eq (s1:var) (s2:var) : bool :=
  if String.string_dec s1 s2 then true else false.

(** The boolean function [var_eq s1 s2] returns [true] iff the
    equality [v1 = v2] holds. *)

Lemma var_eq_spec : forall s1 s2,
  var_eq s1 s2 = isTrue (s1 = s2).
Proof using.
  intros. unfold var_eq. case_if; rew_bool_eq~.
Qed.

Global Opaque var.


(* ########################################################### *)
(** ** Tactic [case_var] *)

(** The tactic [case_var] performs case analysis on expressions of the
    form [if var_eq x y then .. else ..] that appear in the goal. *)

Tactic Notation "case_var" :=
  repeat rewrite var_eq_spec in *; repeat case_if.

Tactic Notation "case_var" "~" :=
  case_var; auto_tilde.

Tactic Notation "case_var" "*" :=
  case_var; auto_star.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Representation of List of Variables *)

(* ########################################################### *)
(** ** Definition of Distinct Variables *)

(** [vars] is the type of a list of variables *)

Definition vars : Type := list var.

(** [var_fresh y xs] asserts that [y] does not belong to the list [xs] *)

Definition var_fresh (y:var) (xs:vars) : Prop :=
  ~ mem y xs.

(** The following lemma asserts that if [x] is a variable in the list [xs],
    and [y] is fresh from this list [xs], then [y] is not equal to [x]. *)

Lemma var_fresh_mem_inv : forall y x xs,
  var_fresh x xs ->
  mem y xs ->
  x <> y.
Proof using. introv H M N. unfolds var_fresh. subst*. Qed.


(* ########################################################### *)
(** ** Generation of [n] Distinct Variables *)

(** [nat_to_var n] converts [nat] values into distinct [name] values. *)

(* LATER: make the implementation more optimized by using more than one
   character. *)

Definition dummy_char :=
  Ascii.ascii_of_nat 0%nat.

Fixpoint nat_to_var (n:nat) : var :=
  match n with
  | O => String.EmptyString
  | S n' => String.String dummy_char (nat_to_var n')
  end.

Lemma injective_nat_to_var :
  injective nat_to_var.
Proof using.
  intros n. induction n as [|n']; intros m E; destruct m as [|m']; tryfalse.
  { auto. }
  { inverts E. fequals~. }
Qed.

(** [var_seq i n] generates a list of variables [x1;x2;..;xn] with [x1=i] and
    [xn=i+n-1]. The ability to start at a given offset is sometimes useful. *)

Fixpoint var_seq (start:nat) (nb:nat) : vars :=
  match nb with
  | O => nil
  | S nb' => (nat_to_var start) :: var_seq (S start) nb'
  end.

(** The properties of [var_seq] are stated next. They assert that this
    function produce the expected number of variables, that the variables
    are pairwise distinct *)

Section Var_seq.
Implicit Types start nb : nat.

Lemma var_fresh_var_seq_lt : forall (x:nat) start nb,
  (x < start)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. unfold var_fresh. gen start. induction nb; simpl; introv N; rew_listx.
  { auto. }
  { simpl. case_var. rew_logic. split.
    { intros E. lets: injective_nat_to_var E. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_fresh_var_seq_ge : forall (x:nat) start nb,
  (x >= start+nb)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. unfold var_fresh. gen start. induction nb; simpl; introv N; rew_listx.
  { auto. }
  { simpl. case_var. rew_logic. split.
    { intros E. lets: injective_nat_to_var E. math. }
    { applys IHnb. math. } }
Qed.

Lemma noduplicates_var_seq : forall start nb,
  LibList.noduplicates (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros; simpl; rew_listx.
  { auto. }
  { split.
    { applys var_fresh_var_seq_lt. math. }
    { auto. } }
Qed.

Lemma length_var_seq : forall start nb,
  length (var_seq start nb) = nb.
Proof using.
  intros. gen start. induction nb; simpl; intros.
  { auto. } { rew_list. rewrite~ IHnb. }
Qed.

End Var_seq.

