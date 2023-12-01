(************************************************************
* Lambda-calculus with exceptions                           *
* Interpreter in combined pretty-big-step with error rules  *
*************************************************************)

Set Implicit Arguments.
Require Import LambdaExn_Interp LambdaExn_CombiErr.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types e : ext.
Implicit Types o : out.
Implicit Types b : beh.
Implicit Types r : res.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Statement of the theorem *)

(** [result n r o] asserts that it is correct for
    the interpreter to return the result [r] when
    run with max-recursion depth [n] for a term
    whose real behavior is [o]. *)

Definition result n r o :=
  match o with
  | out_ter m b => r = b \/ (r = res_bottom /\ n <= m)
  | out_div => r = res_bottom
  end.

Definition correct_and_complete :=
  forall n t r o,
    run n t = r -> cred t o -> result n r o.


(*==========================================================*)
(* * Proofs *)

Hint Unfold result.
Hint Extern 1 (_ <= _) => math.
Hint Constructors isclo.


(************************************************************)
(* ** Properties of monadic operators *)

(** Monotonicity of [result] *)

Lemma result_before : forall n r o1 o2,
  result n r o1 -> before o1 o2 -> result (S n) r o2.
Proof.
  unfold result. introv R B.
  destruct o1; inverts B.
  destruct R as [?|[? ?]]; eauto.
  auto.
Qed.

(** Partial specification for [if_isclo] *)

Lemma if_isclo_not : forall v k,
  ~ isclo v -> if_isclo v k = beh_err.
Proof.
  introv V. destruct~ v. false~ V.
Qed.

(** Combined specification for
        [if_success] when taking [i=true],
    and [if_fault]   when taking [i=false] *)

Lemma if_result : forall (i:bool) n r o1 r1 o k,
  result n r1 o1 ->
  (if i then if_success else if_fault) r1 k = r ->
  faster o1 o ->
  (match o1 with
   | out_ter _ (beh_ret v1) =>
      if i then result (S n) (k v1) o else before o1 o
   | out_ter _ (beh_exn v1) =>
      if i then before o1 o else result (S n) (k v1) o
   | out_ter _ _ => before o1 o
   | out_div => o = out_div
   end) ->
  result (S n) r o.
Proof.
  introv R I F M. unfold result in R. unfolds if_success.
  destruct o1.
  destruct R as [E|[E L]].
    subst r1. destruct b.
      destruct i. subst~. inverts M. unfolds. left~.
      destruct i. inverts M. unfolds. left~. subst~.
      inverts M. unfolds. left. destruct~ i.
    subst r1 r. unfolds. destruct i;
     (destruct o; [ inverts~ F | auto ]).
  subst o r1 r. unfolds. destruct~ i.
Qed.

Definition if_success_result := @if_result true.
Definition if_fault_result := @if_result false.


(************************************************************)
(* ** Correctness and completeness of the interpreter *)

Lemma specification : correct_and_complete.
Proof.
  unfolds. induction n using peano_induction. introv U R.
  destruct n; simpl in U. destruct~ o.
  lets~ IH: (rm H) n __. destruct t.
  inverts* R.
  inverts* R.
  inverts* R.
  inverts R as R1 R2 [L2 L1]. forwards~ M1: IH R1.
   applys~ if_success_result M1 U. inverts R2 as.
     introv A B. inverts A; inverts B; inverts L2; inverts~ L1.
     introv R3 R4 [L4 L3]. forwards~ M2: IH R3.
     applys if_success_result M2. auto.
       destruct o0; inverts L3; inverts~ L2.
     inverts R4 as.
       introv A B. inverts A; inverts B;
        inverts L4; inverts L2; inverts~ L1.
       introv R5 L5. simpl. forwards~ M3: IH R5.
        applys result_before M3.
        destruct o1; inverts L5; inverts L4; inverts~ L2.
       introv C. rewrite~ if_isclo_not.
        inverts L4; inverts~ L2.
  inverts R as R1 R2 [L2 L1]. forwards~ M1: IH R1.
   applys~ if_fault_result M1 U. inverts R2 as.
     inverts L2. inverts~ L1.
     introv R5 L5. forwards~ M2: IH R5.
      applys~ result_before M2.
       destruct o0; inverts L5; inverts~ L2.
     inverts~ L2.
     inverts L2. inverts~ L1.
  inverts R as R1 R2 [L2 L1]. forwards~ M1: IH R1.
   applys~ if_success_result M1 U. inverts R2 as.
     introv A B. inverts A; inverts B; inverts L2; inverts~ L1.
     inverts L2. inverts~ L1.
  inverts* R.
Qed.


(************************************************************)
(* ** Corollaries, formulated as implications *)

Corollary correct_ter : forall n t b,
  run n t = b -> credbeh t b.
Proof.
  introv U. lets (o&R): (cred_full t).
  forwards M: specification U R.
  destruct o; tryfalse.
  destruct M as [E|[? ?]]; tryfalse.
  unfolds credbeh. inverts* E.
Qed.

Corollary complete_ter : forall t b,
  credbeh t b -> exists m, forall n, n > m -> run n t = b.
Proof.
  introv (m&R). exists m. introv G.
  forwards~ [?|[? ?]]: specification (run n t) R.
  math.
Qed.

Corollary correct_div : forall t,
  (forall n, run n t = res_bottom) -> cdiverge t.
Proof.
  introv H. unfold cdiverge.
  lets (o&R): (cred_full t).
  destruct o as [n b|]; [false|auto].
  forwards [E|[? ?]]: specification (H (S n)) R.
    false.
    math.
Qed.

Corollary complete_div : forall t n,
  cdiverge t -> run n t = res_bottom.
Proof.
  introv H. forwards~: specification (run n t) H.
Qed.


(************************************************************)
(* ** Corollaries, formulated as equivalences *)

Corollary specification_ter : forall t b,
     (exists m, forall n, n > m -> run n t = b)
  <-> credbeh t b.
Proof.
  iff (n&?).
  applys* correct_ter (S n). applys* H. math.
  applys* complete_ter. exists* n.
Qed.

Corollary specification_div : forall t,
      (forall n, run n t = res_bottom)
  <-> cdiverge t.
Proof.
  iff.
  applys* correct_div.
  intros. applys* complete_div.
Qed.

