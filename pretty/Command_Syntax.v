(************************************************************
* Language of commands                                      *
* Syntax                                                    *
*************************************************************)

Set Implicit Arguments.
Require Export Common LibHeap.
Module Heap := LibHeap.HeapList.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Syntax of the language *)

(** Definition of words of unbounded size *)

Definition word := int.

Typeclasses Transparent word.

(** Variables used as keys to the stack *)

Definition var := nat.

(** Representation of the stack *)

Definition stack := Heap.heap var word.

(** Initial stack *)

Definition stack_init : stack := Heap.empty.

(** Representation of the heap as a finite map from words 
    to words -- the heap is of unbounded size *)

Definition heap := Heap.heap word word.

(** Initial heap *)

Definition heap_init : heap := Heap.empty.

(** Grammar of pure expressions *)

Inductive exp :=
  | exp_var : var -> exp
  | exp_cst : int -> exp
  | exp_add : exp -> exp -> exp
  | exp_neg : exp -> exp
  | exp_pos : exp -> exp
  | exp_not : exp -> exp.

Coercion exp_var : var >-> exp.
Coercion exp_cst : Z >-> exp.

(** Grammar of effectful expressions *)

Inductive act :=
  | act_comp : exp -> act
  | act_load : exp -> act
  | act_store : exp -> exp -> act
  | act_cas : exp -> exp -> exp -> act
  | act_fence : act.

(** Grammar of commands *)

Inductive cmd :=
  | cmd_bind : var -> act -> cmd
  | cmd_seq : cmd -> cmd -> cmd
  | cmd_if : exp -> cmd -> cmd -> cmd
  | cmd_while : exp -> cmd -> cmd.

(** Grammar of programs (list of processes) *)

Definition prog := list cmd.


(************************************************************)
(* ** Evaluation of pure expressions *)

Definition int_of_prop (P:Prop) :=
  If P then 1 else 0.

Fixpoint eval (s:stack) (e:exp) : word :=
  let r := eval s in
  match e with
  | exp_var x => Heap.read s x
  | exp_cst n => n
  | exp_add e1 e2 => (r e1) + (r e2) 
  | exp_neg e1 => - (r e1)
  | exp_pos e1 => int_of_prop ((r e1) > 0)
  | exp_not e1 => int_of_prop ((r e1) = 0)
  end.



