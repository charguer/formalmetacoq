Set Implicit Arguments.
From TLC Require Import LibTactics.


(*****************************************************)
(** * Stream *)

(** Definition *)

CoInductive stream : Type :=
  | stream_cons : nat -> stream -> stream.

Notation "x ::: s" := (stream_cons x s) (at level 60).


(*****************************************************)
(** * Definition of concrete streams *)

(** Simple definition *)

CoFixpoint nat_stream_1 n :=
  n ::: (nat_stream_1 (S n)).

(** Definition with [let] *)

CoFixpoint nat_stream_2 n :=
  let s' := nat_stream_2 (S n) in
  n ::: s'.

(** Definition with [bind] *)

Definition bind (P Q:Type) (x:P) (f:P->Q) : Q := f x.

CoFixpoint nat_stream_3 n :=
  bind (nat_stream_3 (S n)) (fun s' => n ::: s').

(** Definition with [bind'] *)

Definition bind' (P Q:Type) (x:P) (f:P->Q) : Q.
Proof. exact (f x). Defined.

CoFixpoint nat_stream_4 n :=
  bind' (nat_stream_4 (S n)) (fun s' => n ::: s').

(** Definition with [bind''] *)

Definition bind'' (P Q:Type) (x:P) (f:P->Q) : Q.
Proof. exact (f x). Qed.

(*
CoFixpoint nat_stream_5 n :=
  bind'' (nat_stream_5 (S n)) (fun s' => n ::: s').

  Error:
  Sub-expression "bind'' (nat_stream_5 (S n)) (fun s' : stream => n ::: s')"
  not in guarded form
*)



(*****************************************************)
(** * Bisimilarity *)


(** Definition of bisimiarity *)

CoInductive bisim : stream -> stream -> Prop :=
  | bisim_cons : forall x s s',
     bisim s s' -> bisim (x:::s) (x:::s').




(** Proof of reflexivity via tactic *)

Lemma bisim_refl_0 : forall s, bisim s s.
Proof.
  cofix IH. intros [x s']. constructor. apply IH.
Qed.

(* Print bisim_refl_0. *)

Lemma bisim_refl_0a : forall s, bisim s s.
Proof.
  cofix IH. intros [x s']. apply IH.
  (* Guarded.
     Unguarded recursive call in "IH (x ::: s')". *)
Admitted.

(** Associated proof term *)

CoFixpoint bisim_refl_1 s : bisim s s :=
  match s with x ::: s' =>
    bisim_cons x (bisim_refl_1 s')
  end.

(** Another proof term with [let] *)

CoFixpoint bisim_refl_2 s : bisim s s :=
  match s with x ::: s' =>
    let H := bisim_refl_2 s' in
    bisim_cons x H
  end.

(** Another proof term with [let_lemma_prop] *)

Lemma let_lemma_prop : forall (P Q : Prop),
  P -> (P -> Q) -> Q.
Proof. auto. Defined.

CoFixpoint bisim_refl_3 s : bisim s s :=
  match s with x ::: s' =>
    let_lemma_prop (bisim_refl_3 s') (fun H => bisim_cons x H)
  end.

(** Another proof term with [let_lemma_prop'] *)

Lemma let_lemma_prop' : forall (P Q : Prop),
  P -> (P -> Q) -> Q.
Proof. auto. Qed.

(*
CoFixpoint bisim_refl_4 s : bisim s s :=
  match s with x ::: s' =>
    let_lemma_prop' (bisim_refl_4 s') (fun H => bisim_cons x H)
  end.

  Error:
  Sub-expression
    "let_lemma_prop (bisim_refl_4 s')
     (fun H : bisim s' s' => bisim_cons x H)"
  not in guarded form
*)


(** Proof of reflexivity via tactic, using rewrite *)

Lemma add_zero : forall n, 0 + n = n.
Proof. auto. Qed.

Lemma bisim_refl_5 : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  rewrite <- (add_zero x). rewrite (add_zero x).
  constructor. apply IH.
Qed.
(*Print bisim_refl_5.*)

Lemma bisim_refl_5a : forall s, bisim s s.
Proof.
  cofix IH. intros [x s']. constructor.
  sets_eq s'': s'. subst s''.
  apply IH.
Qed.
(*Print bisim_refl_5a.*)


(** Proof of reflexivity via tactic, using [eq_rect] *)

Definition eq_rect' : forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, x = y -> P y.
Proof.
exact(
  fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
  match e in (_ = y0) return (P y0) with
  | eq_refl => f
  end).
Defined.

Arguments eq_rect' [A].

CoFixpoint bisim_refl_5' s : bisim s s :=
  match s as s0 return (bisim s0 s0) with
  | x ::: s' =>
      eq_rect' (0 + x) (fun x0 : nat => bisim (x0 ::: s') (x0 ::: s'))
        (eq_ind_r (fun n : nat => bisim (n ::: s') (n ::: s'))
           (bisim_cons x (bisim_refl_5' s')) (add_zero x)) x (add_zero x)
  end.


(** Proof of reflexivity via tactic, using [eq_rect''] *)

Definition eq_rect'' : forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, x = y -> P y.
Proof.
exact(
  fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
  match e in (_ = y0) return (P y0) with
  | eq_refl => f
  end).
Qed.

Arguments eq_rect'' [A].

(* Not guarded
CoFixpoint bisim_refl_5'' s : bisim s s :=
  match s as s0 return (bisim s0 s0) with
  | x ::: s' =>
      eq_rect'' (0 + x) (fun x0 : nat => bisim (x0 ::: s') (x0 ::: s'))
        (eq_ind_r (fun n : nat => bisim (n ::: s') (n ::: s'))
           (bisim_cons x (bisim_refl_5'' s')) (add_zero x)) x (add_zero x)
  end.
*)


(*****************************************************)
(** * Debugging guardedness *)


Lemma bisim_refl_6 : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  apply (@let_lemma_prop' (bisim s' s')).
    apply IH.
    (* Guarded. *)
(* Sub-expression "let_lemma_prop' (IH s') (?1 IH x s')" not in guarded form *)
Admitted.


Lemma bisim_refl_7 : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  apply (@let_lemma_prop' True).
    auto. intros.
  (* Guarded. *)
  constructor.
  (* Guarded. *)
  apply IH.
  (* Guarded.
    Sub-expression "let_lemma_prop' I (fun _ : True => bisim_cons x (IH s'))" not
    in guarded form
  *)
Admitted.

Lemma bisim_refl_8 : forall s, bisim s s.
Proof.
  cofix IH. intros [x s']. constructor.
  apply (@let_lemma_prop' True).
    auto. intros.
    (* Guarded. *)
   (* Guarded. *)
   apply IH.
  (* Guarded.
    Sub-expression "let_lemma_prop' I (fun _ : True => bisim_cons x (IH s'))" not
    in guarded form
  *)
Admitted.

Lemma bisim_refl_8b : forall s, bisim s s.
Proof.
  cofix IH. intros [x s']. constructor.
  forwards: True. apply IH.
Qed.

Lemma bisim_refl_8c : forall s, bisim s s.
Proof.
  cofix IH. intros [x s']. constructor.
  specializes IH s'. apply IH.
  (* or one of:
  lets H: (IH s'). apply H.
  forwards H: (IH s'). apply H.
  forwards H: (IH s'). apply IH.
  *)
Qed.



Lemma refl_reproduce_1 : (forall s, bisim s s) -> (forall s, bisim s s).
Proof.
  intros IH. apply IH.
Defined.

Lemma bisim_refl_9 : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  apply refl_reproduce_1. apply IH.
  (*
  Unguarded recursive call in
  "refl_reproduce IH (x ::: s')".
  Recursive definition is:
  "fun s : stream =>
   match s as s0 return (bisim s0 s0) with
   | x ::: s' => refl_reproduce IH (x ::: s')
   end".
*)
Admitted.

Lemma bisim_refl_9a : forall s, bisim s s.
Proof.
  cofix IH. intros [x s']. constructor.
  apply refl_reproduce_1. apply IH.
Qed.



Lemma refl_reproduce_2 : (forall s, bisim s s) -> (forall s, bisim s s).
Proof.
  intros IH. intros [x s']. constructor. apply IH.
Defined.

Lemma bisim_refl_10 : forall s, bisim s s.
Proof.
  cofix IH. intros s. apply refl_reproduce_2. apply IH.
Qed.

Lemma refl_reproduce_3 : (forall s, bisim s s) -> (forall s, bisim s s).
Proof.
  skip.
Defined.

Lemma bisim_refl_10a : forall s, bisim s s.
Proof.
  cofix IH. intros s. apply refl_reproduce_3. apply IH.
(*
  Guarded.
Recursive call in a branch of
"match
   skip_axiom
   return ((forall s : stream, bisim s s) -> forall s : stream, bisim s s)
 with
 end".

Recursive definition is:
  "fun s : stream => refl_reproduce_3 IH s".

*)
Admitted.


Lemma bisim_refl_10b : forall s, bisim s s.
Proof.
  cofix IH. intros s. apply refl_reproduce_3. skip.
Qed.

Lemma refl_reproduce_4 : (forall s, bisim s s).
Proof.
  skip.
Defined.

Lemma bisim_refl_10c : forall s, bisim s s.
Proof.
  cofix IH. intros s. apply refl_reproduce_4.
  (* or: cofix IH. intros [x s']. constructor. apply refl_reproduce_4.*)
Qed.



Lemma bisim_refl_11 : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  assert (x = x). apply eq_refl.
  constructor. apply IH.
Qed.

Lemma bisim_refl_11a : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  assert (x = x). abstract apply eq_refl.
  constructor. apply IH.
Qed.

Lemma bisim_refl_11b : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  assert (x = 0 + x). apply eq_refl.
  rewrite H.
  constructor. apply IH.
Qed.

Lemma bisim_refl_11c : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  assert (x = 0 + x). skip.
  rewrite H.
  constructor. apply IH.
Qed.

Lemma bisim_refl_11d : forall s, bisim s s.
Proof.
  cofix IH. intros [x s'].
  assert (x = 0 + x). abstract apply eq_refl.
  rewrite H.
  constructor. apply IH.
(* Guarded.

Recursive call in the argument of cases in
"match
   match bisim_refl_11b_subproof IH x s' in (_ = y) return (y = x) with
   | eq_refl => eq_refl
   end in (_ = y)
   return
     ((fun y0 : nat => (fun x : nat => bisim (x ::: s') (x ::: s')) y0) y)
 with
 | eq_refl => bisim_cons (0 + x) (IH s')
 end".

Recursive definition is:
"fun s : stream =>
 match s as s0 return (bisim s0 s0) with
 | x ::: s' =>
     let H := bisim_refl_11b_subproof IH x s' in
     eq_ind_r (fun x0 : nat => bisim (x0 ::: s') (x0 ::: s'))
       (bisim_cons (0 + x) (IH s')) H
 end".

*)
Admitted.














(*

*)