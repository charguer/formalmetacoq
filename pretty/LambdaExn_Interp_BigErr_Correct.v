(************************************************************
* Lambda-calculus with exceptions                           *
* Interpreter in combined pretty-big-step with error rules  *
*************************************************************)

Set Implicit Arguments.
Require Import LambdaExn_Interp LambdaExn_BigErr.

Implicit Types v : val.
Implicit Types t : trm.
Implicit Types b : beh.
Implicit Types r : res.


(*==========================================================*)
(* * Proofs *)

Hint Extern 1 (_ < _) => math.
Hint Constructors isclo abort bigred.


(************************************************************)
(* ** Properties of monadic operators *)

Lemma if_success_abort : forall b k,
  abort b -> if_success b k = b.
Proof. introv A. inverts* A. Qed.

Lemma if_isclo_not_isclo : forall v k,
  ~ isclo v -> if_isclo v k = beh_err.
Proof. introv N. destruct v; auto_false. Qed.


(************************************************************)
(* ** Correctness and completeness of the interpreter *)

(** Correctness *)

Lemma run_correct_red : forall n t b,
  bigredh n t b -> forall k, k >= n -> run k t = b.
Proof.
  induction n using peano_induction.
  introv R. destruct n. inverts R.
  introv K. destruct k. math.
  asserts IH: (forall t b, bigredh n t b -> run k t = b).
    introv M. applys H M; math. clear H K.
  inverts R as; simpl.
  auto.
  auto.
  auto.
  introv R1 R2 R3. rewrites~ (>> IH R1). simpl.
   rewrites~ (>> IH R2). simple*.
  introv A R1. rewrites~ (>> IH R1). rewrite~ if_success_abort.
  introv A R1 R2. rewrites~ (>> IH R1). simpl.
   rewrites~ (>> IH R2). rewrite~ if_success_abort.
  introv N R1 R2. rewrites~ (>> IH R1). simpl.
   rewrites~ (>> IH R2). simpl. rewrite~ if_isclo_not_isclo.
  introv R1. rewrites~ (>> IH R1).
  introv R1 R2. rewrites~ (>> IH R1). simple*.
  introv R1. rewrites~ (>> IH R1).
  introv R1. rewrites~ (>> IH R1).
  introv A R1. rewrites~ (>> IH R1). rewrite~ if_success_abort.
  introv E. rewrite* E. rewrite~ Deterministic.
Qed.

(** Completeness *)

Ltac runs b :=
  match goal with HR: context [ run ?n ?t ] |- _ =>
    let r := fresh "r" in let E := fresh "E" in
    sets_eq <- r E: (run n t);
    destruct r as [ b | ]; [ | inverts HR ];
    match goal with IH: (forall _ _, run _ _ = _ -> bigred _ _) |- _ =>
      let M := fresh "M" in lets M: IH E; clear E end end.

Lemma run_complete_red : forall n t b,
  run n t = b -> bigred t b.
Proof.
  induction n using peano_induction.
  introv R. destruct n; simpl in R. inverts R.
  lets~ IH: (rm H) n __. destruct t.
  inverts~ R.
  inverts~ R.
  inverts~ R.
  runs b1. destruct b1; inverts R as R; auto.
   runs b2. destruct b2; inverts R as R; autos*.
   tests C: (isclo v).
     inverts C. simpls. runs b3. inverts* R.
     rewrite~ if_isclo_not_isclo in R. inverts* R.
  runs b1. destruct b1; inverts R as R; auto.
   runs b2. inverts* R.
  runs b1. destruct b1; inverts~ R.
  inverts~ R.
Qed.


(************************************************************)
(* ** Corollaries, formulated as implications *)

Corollary correct_ter : forall n t b,
  run n t = b -> bigred t b.
Proof. applys run_complete_red. Qed.

Corollary complete_ter : forall t b,
  bigred t b -> exists m, forall n, n > m -> run n t = b.
Proof.
  introv H. lets (n&R): bigred_bigredh H. exists n.
  introv L. applys* run_correct_red. math.
Qed.

Corollary correct_div : forall t,
  (forall n, run n t = res_bottom) -> bigdiv t.
Proof.
  introv H. tests (b&B) C: (terminates t).
  lets (n&R): bigred_bigredh B.
   specializes H n. forwards: (run_correct_red R) n.
   math. false.
  applys* not_terminates_bigdiv.
Qed.

Corollary complete_div : forall t n,
  bigdiv t -> run n t = res_bottom.
Proof.
  introv H. cases (run n t) as C; [ false | auto ].
  lets H': correct_ter C.
  applys* bigred_bigdiv_exclusive H' H.
Qed.


(************************************************************)
(* ** Corollaries, formulated as equivalences *)

Corollary specification_ter : forall t b,
     (exists m, forall n, n > m -> run n t = b)
  <-> bigred t b.
Proof.
  iff (n&?) ?.
  applys* correct_ter (S n). applys* H. math.
  applys* complete_ter.
Qed.

Corollary specification_div : forall t,
      (forall n, run n t = res_bottom)
  <-> bigdiv t.
Proof.
  iff.
  applys* correct_div.
  intros. applys* complete_div.
Qed.

