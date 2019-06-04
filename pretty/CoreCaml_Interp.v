(************************************************************
* Core Caml                                                 *
* Interpreter                                               *
*************************************************************)

Set Implicit Arguments.
Require Export String CoreCaml_Syntax CoreCaml_Pretty.

Implicit Types x : var.
Implicit Types c : cst.
Implicit Types f : prim.
Implicit Types k : constr.
Implicit Types v : val.
Implicit Types t : trm.
Implicit Types m : mem.
Implicit Types B : beh.
Implicit Types a : lab.
Implicit Types l : loc.
Implicit Types i: inst.
Implicit Types n : int.
Implicit Types z : bool.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Results *)

(** Grammar of results of the interpreter *)

Inductive res :=
  | res_out : out -> res
  | res_bottom : res
  | res_stuck : res
  | res_unimplem : res.

Coercion res_out : out >-> res.
Implicit Types r : res.


(************************************************************)
(* ** Debugging operators *)

Definition stuck (s:string) :=
  (* print s; *) res_stuck.



(*==========================================================*)
(* * Signature of deterministic/non-deterministic monad *)

Module Type MonadSig.

Parameter result : Type.
Parameter returns : res -> result.
Parameter binds : result -> (res -> result) -> result.
Parameter picks : forall A, list A -> (A -> result) -> result.

End MonadSig. 

(*==========================================================*)
(* * Implementation of deterministic monad *)

Module MonadDeterministic : MonadSig.

Definition result := res.

Definition returns (r:res) := r.

Definition binds (r:result) (K:res->result) := K r.

Definition picks (A:Type) (xs:list A) K : result :=
  match xs with 
  | nil => returns res_stuck
  | x::xs' => K x
  end.

End MonadDeterministic. 

(*==========================================================*)
(* * Implementation of non-deterministic monad *)

Module MonadNonDeterministic : MonadSig.

Inductive bag (A:Type) : Type :=
  | bag_empty : bag A
  | bag_one : A -> bag A
  | bag_concat : bag A -> bag A -> bag A.

Arguments bag_empty {A}.

Fixpoint bag_fold (A B:Type) (f:B->A->B) (i:B) (b:bag A) : B :=
  match b with
  | bag_empty => i
  | bag_one x => f i x
  | bag_concat b1 b2 => bag_fold f (bag_fold f i b1) b2
  end.

Definition bag_map_concat (A B:Type) (f:A->bag B) (b:bag A) : bag B :=
  bag_fold (fun acc (x:A) => bag_concat acc (f x)) bag_empty b.

Definition bag_to_list (A:Type) (b:bag A) : list A :=
  LibList.rev (bag_fold (fun acc (x:A) => x::acc) nil b).

Definition result := bag res.

Definition returns (r:res) := bag_one r.

Definition binds (r:result) (K:res->result) := bag_map_concat K r.

Definition picks (A:Type) (xs:list A) K : result :=
  LibList.fold_left (fun (x:A) acc => bag_concat acc (K x)) bag_empty xs.

End MonadNonDeterministic. 


(*==========================================================*)
(* * Functor for deterministic/non-deterministic monad *)

Module Interpreter (Monad : MonadSig).
Export Monad.

Coercion returns : res >-> result.


(************************************************************)
(* ** Monadic operators *)

(** Operators for values *)

Definition if_bool (v:val) (K:bool->result) : result :=
  match v with
  | val_cst (cst_bool z) => K z
  | _ => stuck "boolean value was expected"
  end.

Definition if_int (v:val) (K:int->result) : result :=
  match v with
  | val_cst (cst_int n) => K n
  | _ => stuck "int value was expected"
  end.

Definition if_abs (v:val) (K:option var->pat->trm->result) : result :=
  match v with
  | val_abs oy p t => K oy p t
  | _ => stuck "function was expected"
  end.

(** Operators for results *)

Definition if_ter (re:result) (K:mem->beh->result) : result :=
  binds re (fun r =>
    match r with
    | res_out (out_ter m B) => K m B
    | _ => r
    end).

Definition if_success (re:result) (K:mem->val->result) : result :=
  if_ter re (fun m B => 
    match B with
    | beh_ret v => K m v
    | _ => out_ter m B
    end).

Definition if_success_bool_cases (re:result) (K1:mem->result) (K2:mem->result) : result :=
  if_success re (fun m v =>
    if_bool v (fun z => 
      match z with
      | true => K1 m
      | false => K2 m
      end)).



(************************************************************)
(* ** Interpreter *)

(** Definition of the interpreter methods *)

Record runs := runs_intro {
  runs_trm : mem -> trm -> result;
  runs_branches : mem -> beh -> val -> branches -> result;
  runs_list : mem -> trms -> vals -> (mem -> vals -> result) -> result }.

(** Definition of pattern matching *)

Definition run_primitive_eq m v1 v2 : result :=
  res_unimplem.

Parameter run_primitive_eq_spec : forall m m' v1 v2 z,
  run_primitive_eq m v1 v2 = out_ter m z ->
  primitive_eq v1 v2 z.

(** Definition of pattern matching *)

Definition run_matching (v:val) (p:pat) : option inst := 
  None. (* TODO *)

Parameter run_matching_spec : forall v p,
  match run_matching v p with
  | None => mismatching v p
  | Some i => matching i v p
  end.

(** Definition of function call *)

Definition run_call R m oy p t v : result :=
  match run_matching v p with
  | None => out_ter m (beh_exn constr_matching_failure)
  | Some i =>
     let t1 := substs i t in
     let t2 := 
       match oy with 
       | None => t1
       | Some y => subst y (val_abs oy p t) t1
       end in
     runs_trm R m t2
  end.

(** Definition of execution of list of terms *)

Definition run_list R m ts vs F : result :=
  match ts with
  | nil => F m vs
  | t::ts' => 
      if_success (runs_trm R m t) (fun m v =>
        runs_list R m ts' (vs++v::nil) F)
  end.

(** Definition of execution of terms *)

Definition run_trm R m t : result := 
  let run_trm := runs_trm R in
  match t with
  | trm_var x => res_stuck
  | trm_cst c => out_ter m c
  | trm_abs oy p t1 => 
      out_ter m (val_abs oy p t1)
  | trm_constr k ts => 
      runs_list R m ts nil (fun m vs => 
        out_ter m (val_constr k vs))
  | trm_tuple ts => res_unimplem
  | trm_record ats => res_unimplem
  | trm_unary f t1 => 
      if_success (run_trm m t1) (fun m v1 =>
        let ret v := out_ter m v in
        match f with
        | prim_neg => if_bool v1 (fun z => ret (neg z))
        | prim_not => if_int v1 (fun n => ret (-n))
        | prim_raise => out_ter m (beh_exn v1)
        | _ => stuck "invalid unary operator"
        end)
  | trm_binary f t1 t2 => 
      if_success (run_trm m t1) (fun m v1 =>
        if_success (run_trm m t2) (fun m v2 =>
          let ret v := out_ter m v in
          let op_int F :=
            if_int v1 (fun n1 => if_int v2 (fun n2 => F n1 n2)) in
          match f with
          | prim_eq => run_primitive_eq m v1 v2
          | prim_add => op_int (fun n1 n2 => ret (n1+n2))
          | prim_sub => op_int (fun n1 n2 => ret (n1-n2))
          | prim_mul => op_int (fun n1 n2 => ret (n1*n2))
          | prim_div => op_int (fun n1 n2 =>
               If n2 <> 0 
                 then ret (Zdiv n1 n2) 
                 else (out_ter m (beh_exn constr_div_by_zero)))
          | _ => stuck "invalid binary operator"
          end))
  | trm_lazy_binary _ _ _ => res_unimplem
  | trm_app t1 t2 =>
     if_success (run_trm m t1) (fun m v1 =>
       if_success (run_trm m t2) (fun m v2 =>
         if_abs v1 (fun oy p t => 
           run_call R m oy p t v2)))
  | trm_seq t1 t2 =>
     if_success (run_trm m t1) (fun m v1 =>
       If v1 = val_unit 
         then (run_trm m t2)
         else stuck "sequence with LHS that is not unit")
  | trm_let p t1 t2 => 
     if_success (run_trm m t1) (fun m v1 =>
       match run_matching v1 p with
       | None => out_ter m (beh_exn constr_matching_failure)
       | Some i => run_trm m (substs i t2)
       end)
  | trm_get t1 a => res_unimplem
  | trm_set t1 a t2 => res_unimplem
  | trm_if t1 t2 t3o => 
     if_success_bool_cases (run_trm m t1)
       (fun m => run_trm m t2)
       (fun m =>
           match t3o with
           | None => out_ter m val_unit
           | Some t3 => run_trm m t3
           end)
  | trm_while t1 t2 => res_unimplem
  | trm_for x d t1 t2 t3 => res_unimplem
  | trm_match t1 bs => 
     if_success (run_trm m t1) (fun m v1 =>
       let B := (beh_exn constr_matching_failure) in
       runs_branches R m B v1 bs)
  | trm_try t1 bs =>
      if_ter (run_trm m t1) (fun m B => 
        match B with
        | beh_exn v => runs_branches R m B v bs
        | _ => out_ter m B
        end)
  | trm_assert t1 =>
      if_success_bool_cases (run_trm m t1) 
        (fun m => out_ter m val_unit)
        (fun m => out_ter m (beh_exn constr_assert_failure))
  | trm_rand => 
      picks (true::false::nil) (fun z =>
        out_ter m (val_cst z))
  end.


Fixpoint run_branches R m B v bs : result := 
  match bs with
  | nil => out_ter m B
  | (branch_intro p g t)::bs' =>
      let next m := run_branches R m B v bs' in
      match run_matching v p with
      | None => next m
      | Some i => 
         let here m := runs_trm R m (substs i t) in
         match g with
         | None => here m
         | Some tg => 
             if_success_bool_cases (runs_trm R m (substs i tg)) 
                (fun m => here m)
                (fun m => next m)
         end
      end
  end.

(** Definition of the interpreter *)

Fixpoint runs_for (n:nat) : runs :=
  match n with 
  | O => 
      {| runs_trm := (fun _ _ => res_bottom);
         runs_branches := (fun _ _ _ _ => res_bottom);
         runs_list := (fun _ _ _ _ => res_bottom) |}
  | S n' => 
      let build {A} (F:runs->mem->A) := (fun m => F (runs_for n') m) in
      {| runs_trm := build run_trm;
         runs_branches := build run_branches;
         runs_list := build run_list |}
  end.

Definition runs_many := runs_trm (runs_for 100).


End Interpreter.


(*==========================================================*)
(* * Demo for the deterministic interpreter *)

Module DemoDeterministic.

Module Import Interp := Interpreter(MonadDeterministic).

Definition demo_mem : mem := Heap.empty.

Definition demo_prog := 
  trm_if (trm_cst false)
     (trm_cst 1) (Some (trm_cst 2)).

Definition demo_result :=
  runs_many demo_mem demo_prog.

(* pb
Lemma test : True.
set (x := runs_trm runs_many demo_mem demo_prog).
 compute in x.
Print MonadDeterministic.binds.
unfold binds in x.
Eval compute in runs_trm runs_many demo_mem demo_prog.
*)

End DemoDeterministic.


(*==========================================================*)
(* * Demo for the deterministic interpreter *)

Module DemoNonDeterministic.

Module Import Interp := Interpreter(MonadNonDeterministic).

Definition demo_mem : mem := Heap.empty.

Definition demo_prog := 
  trm_if trm_rand
     (trm_if trm_rand (trm_cst 1) (Some (trm_cst 2)))
     (Some (trm_if trm_rand (trm_cst 3) (Some (trm_cst 4)))).

Definition demo_result :=
  runs_many demo_mem demo_prog.

(*Eval compute in (bag_to_list (runs_trm runs_many demo_mem demo_prog)).
*)

End DemoNonDeterministic.


(*==========================================================*)
(* * Demo Extraction *)

Extraction Language Ocaml.
Extract Constant constr_unit => "O".
Extract Constant constr_div_by_zero => "S(O)".
Extract Constant constr_matching_failure => "S(S(O))".
Extract Constant constr_assert_failure => "S(S(S(O)))".

Extract Constant arbitrary => "(fun _ -> failwith ""arbitrary"")".
(*Extract Constant epsilon_def => "(fun _ -> failwith ""epsilon"")".*)
Extract Constant classicT => "Left".

Extract Constant indefinite_description => 
  "fun x -> raise Not_found".
Extract Constant subst => 
  "fun x -> raise Not_found".
Extract Constant substs => 
  "fun x -> raise Not_found".
(*
Extract Constant DemoDeterministic.Interp.run_matching => 
  "fun x => raise Not_found".
*)
Extraction "test1.ml" 
  DemoDeterministic.demo_result 
  DemoNonDeterministic.demo_result.


(*==========================================================*)
(* * Proofs for the deterministic interpreter *)


(************************************************************)
(* ** Correctness definitions *)

(** Characterization of correctness *)

Definition correct_runs_trm_def run := forall m t o,
  run m t = res_out o -> 
  red m t o.

Definition correct_runs_branches_def run := forall bs m B v o,
  run m B v bs = res_out o -> 
  red m (ext_branches_1 B v bs) o.

Definition correct_runs_list_def run := forall m ts vs F o,
  run m ts vs F = res_out o -> forall K,
  (forall m' vs', F m' vs' = o -> red m' (K vs') o) ->
  red m (ext_list_1 ts vs K) o.

Record correct_runs (R:runs) := correct_runs_intro {
  correct_runs_trm : correct_runs_trm_def (runs_trm R);
  correct_runs_branches : correct_runs_branches_def (runs_branches R);
  correct_runs_list : correct_runs_list_def (runs_list R)
  }.


(************************************************************)
(* ** Correctness lemmas *)


Hint Constructors abort. 

Definition if_success_bool_bases_post o1 K1 K2 o :=
    (o = o1 /\ abort o)
 \/ (exists m z, o1 = out_ter m z /\
       (   (z = true /\ K1 m = res_out o)
        \/ (z = false) /\ K2 m = res_out o)).

Lemma if_success_bool_cases_out : forall r K1 K2 o,
  if_success_bool_cases r K1 K2 = res_out o ->
  exists o1, r = res_out o1 /\
  if_success_bool_bases_post o1 K1 K2 o.
Proof.
  introv H. destruct r as [o1 | | | ]; simpls; tryfalse.
  exists o1. splits~. unfolds.
  destruct o1 as [m [v|v]| ].
  destruct v; simpls; tryfalse.
  destruct c; simpls; tryfalse.
  right. destruct b; simpls; exists___*.
  inverts* H. 
  inverts* H.
Qed.

Definition if_ter_post o1 K o :=
     (o = o1 /\ o = out_div)
  \/ (exists m B, o1 = out_ter m B /\ K m B = res_out o).

Lemma if_ter_out : forall r K o,
  if_ter r K = res_out o ->
  exists o1, r = res_out o1 /\
  if_ter_post o1 K o.
Proof.
  introv H. destruct r as [o1 | | | ]; simpls; tryfalse.
  exists o1. splits~. unfolds.
  destruct o1 as [m b| ].
  jauto. 
  inverts* H. 
Qed.

Definition if_success_post o1 K o :=
    (o = o1 /\ abort o)
 \/ (exists m v, o1 = out_ter m (beh_ret v) /\ K m v = res_out o).

Lemma if_success_out : forall r K o,
  if_success r K = res_out o ->
  exists o1, r = res_out o1 /\
  if_success_post o1 K o.
Proof.
  introv H. destruct r as [o1 | | | ]; simpls; tryfalse.
  exists o1. splits~. unfolds.
  destruct o1 as [m [v|v]| ].
  jauto.
  inverts* H.
  inverts* H.
Qed.

Lemma if_int_out : forall (v:val) K o,
  if_int v K = res_out o ->
  exists n, v = cst_int n /\ K n = res_out o.
Proof.
  introv H. destruct v; simpls; tryfalse.
  destruct c; simpls; tryfalse. eauto.
Qed.

Lemma if_bool_out : forall (v:val) K o,
  if_bool v K = res_out o ->
  exists z, v = cst_bool z /\ K z = res_out o.
Proof.
  introv H. destruct v; simpls; tryfalse.
  destruct c; simpls; tryfalse. eauto.
Qed.

Lemma if_abs_out : forall (v:val) K o,
  if_abs v K = res_out o ->
  exists oy p t, v = val_abs oy p t /\ K oy p t = res_out o.
Proof.
  introv H. destruct v; simpls; tryfalse. eauto.
Qed.


(************************************************************)
(* ** Correctness tactics *)

(** [prove_not_intercept] proves a goal of
    the form "~ intercept _" *)

Ltac prove_not_intercept :=
  let H := fresh in intros H; try solve [ inversion H ].

Hint Extern 1 (~ intercept _) => prove_not_intercept.
  
(** [run_abort] proves a reduction using the abort rule *)

Ltac run_abort :=
  applys red_abort; 
  [ simpl; congruence 
  | try prove_not_intercept
  | try solve [ assumption | constructor ] ].

(** [run_ifres_select] selects the appropriate "out" lemma *)

Ltac run_ifres_select H :=
  match type of H with 
  | context [ if_ter ] => constr:(if_ter_out)
  | context [ if_success ] => constr:(if_success_out)
  | context [ if_success_bool_cases ] => constr:(if_success_bool_cases_out)
  end.

(* [run_hyp H] exploits the induction hypothesis
   on [correct_runs] to the hypothesis [H] *)

Ltac run_hyp_select_proj H :=
  match type of H with
  | runs_trm _ _ _ = _ => constr:(correct_runs_trm)
  | runs_branches _ _ _ _ _ = _ => constr:(correct_runs_branches)
  | runs_list _ _ _ _ _ = _ => constr:(correct_runs_list)
  end.

Ltac run_hyp_select_ind tt :=
  match goal with IH: correct_runs _ |- _ => constr:(IH) end.

Tactic Notation "run_hyp" hyp(H) "as" ident(R) :=
  let IH := run_hyp_select_ind tt in
  let Proj := run_hyp_select_proj H in
  lets R: Proj IH (rm H).

Tactic Notation "run_hyp" hyp(H) :=
  let T := fresh in rename H into T;
  run_hyp T as H.

(* [run_pre] exploits the "out" lemma and 
   the induction hypothesis, forwarding the
   lemma given by [run_ifres_select] and running [run_hyp] *)

Ltac run_pre_forward H o1 O1 K :=
  let L := run_ifres_select H in
  lets (o1&O1&K): L (rm H).

Ltac run_pre_core H o1 R1 K :=
  let O1 := fresh "O1" in
  run_pre_forward H o1 O1 K;
  try run_hyp O1 as R1.

Tactic Notation "run_pre" hyp(H) "as" ident(o1) ident(R1) ident(K) :=
  let T := fresh in rename H into T;
  run_pre_core T o1 R1 K.

Tactic Notation "run_pre" "as" ident(o1) ident(R1) :=
  match goal with H: _ = res_out _ |- _ =>
    let T := fresh in rename H into T;
    run_pre_core T o1 R1 H end.

Tactic Notation "run_pre" "as" ident(o1) :=
  let R1 := fresh "R1" o1 in
  run_pre as o1 R1.

Tactic Notation "run_pre" :=
  let o1 := fresh "o1" in let R1 := fresh "R1" in
  run_pre as o1 R1.

(** [run_step Red o1 R1] applys a reduction rule on a given 
    [o1] or reduction reaching [o1]. *)

Tactic Notation "run_step" constr(Red) constr(o1orR1) :=
  applys Red o1orR1.

Tactic Notation "run_step" constr(Red) constr(o1) constr(R1) :=
  first [ applys Red (rm R1) 
        | applys Red o1 ].

(** [run_post] decomposes the conclusion of the "out" 
    lemma *)

Tactic Notation "run_post" :=
  let Er := fresh "Er" in let Ab := fresh "Ab" in
  let m := fresh "m" in let v := fresh "v" in 
  let O1 := fresh "O1" in 
  let subst_or_clear O1 :=  
    first [ subst_hyp O1 | (*clear O1*) idtac ] in
  match goal with
  | H: if_ter_post _ _ _ |- _ => 
    let B := fresh "B" in 
    destruct H as [(Er&Ab)|(m&B&O1&H)];
    [ try subst_hyp Er | ]
  | H: if_success_post _ _ _ |- _ => 
    destruct H as [(Er&Ab)|(m&v&O1&H)];
    [ try run_abort | subst_or_clear O1 ]
  | H: if_success_bool_bases_post _ _ _ _ |- _ =>
    let z := fresh "z" in let Ez := fresh "Ez" in 
    destruct H as [(Er&Ab)|(m&z&O1&[(Ez&H)|(Ez&H)])];
    [ try run_abort | subst_or_clear O1 | subst_or_clear O1 ]
  end.

(** [run_inv] simplifies equalities in goals 
    by performing inversions on equalities. *) 

Ltac run_inv := 
  repeat 
  match goal with
  | H: res_out ?o = res_out ?o |- _ => clear H
  | H: res_out _ = res_out _ |- _ => inverts H 
  | H: out_ter ?m ?b = out_ter ?m ?b |- _ => clear H
  | H: out_ter _ _ = out_ter _ _ |- _ => inverts H
  | H: beh_ret ?v = beh_ret ?v |- _ => clear H 
  | H: beh_ret _ = beh_ret _ |- _ => inverts H 
  | H: beh_exn ?v = beh_exn ?v |- _ => clear H 
  | H: beh_exn _ = beh_exn _ |- _ => inverts H 
  end.

(** [runs_inv] is the same as [run_inv] followed by subst. *)

Ltac runs_inv := 
  run_inv; subst.

(** Auxiliary tactics to select/check the current "out" *)

Ltac run_get_current_out tt := 
  match goal with |- red _ _ ?o => o end.

Ltac run_check_current_out o :=
  match goal with |- red _ _ o => idtac end.

(** [run_ifres L] combines [run_pre], [run_step L] and calls
    [run_post] on the main reduction subgoal, followed
    with a cleanup using [run_inv] *)

Ltac run_ifres Red :=
  let o1 := fresh "o1" in let R1 := fresh "R1" in
  run_pre as o1 R1;
  let o := run_get_current_out tt in
  run_step Red o1 R1;
  try (run_check_current_out o; run_post);
  run_inv.

(** [run_if] is intended for simplyfing simple monads
    that do not match over a result, then run
    [run_inv] to clean up the goal. *)

Ltac run_if_core H K :=
  let E := fresh "E" in 
  match type of H with   
  | context [ if_int ] => 
     let n := fresh "n" in
     lets (n&E&K): if_int_out (rm H)
  | context [ if_bool ] => 
     let z := fresh "z" in
     lets (z&E&K): if_bool_out (rm H)
  | context [ if_abs ] => 
     let oy := fresh "oy" in let p := fresh "p" in 
     let t := fresh "t" in
     lets (oy&p&t&E&K): if_abs_out (rm H)
  end.

Tactic Notation "run_if" constr(H) "as" ident(K) :=  
  run_if_core H K; 
  run_inv.

Tactic Notation "run_if" :=  
  match goal with H: _ = res_out _ |- _ =>
    let T := fresh in rename H into T;  
    run_if T as H
  end.

(** [run Red] is the same as [run_ifres Red].
    [run] without arguments is the same as [run_if].
    [runs] is same as [run] followed with [subst]. *)

Tactic Notation "run" constr(Red) :=
  run_ifres Red.

Tactic Notation "run" "*" constr(Red) :=
  run Red; autos*.

Tactic Notation "runs" constr(Red) :=
  run Red; subst.

Tactic Notation "runs" "*" constr(Red) :=
  run Red; subst; autos*.

Tactic Notation "run" :=
  run_if.

Tactic Notation "run" "*" :=
  run; autos*.

Tactic Notation "runs" :=
  run; subst.

Tactic Notation "runs" "*" :=
  runs; autos*.


(************************************************************)
(* ** Correctness proofs *)

Hint Constructors binary_red binary_pure unary_red unary_pure.


(** Proof of correctness of auxiliary definitions *)

Lemma correct_run_list : forall R, 
  correct_runs R ->  
  correct_runs_list_def (run_list R).
Proof.
  introv IH. 
  introv M HF. simpls. unfolds run_list. destruct ts.
  (* nil *)
  inverts M. applys red_list_1_nil. applys* HF. 
  (* cons *)
  run red_list_1_cons. applys* red_list_2.
  applys* (correct_runs_list IH). 
Qed. 

Lemma correct_run_trm : forall R, 
  correct_runs R ->  
  correct_runs_trm_def (run_trm R).
Proof. 
  introv IH. lets IHt: (correct_runs_trm IH). introv K.
  destruct t; simpl in K; tryfalse.
  (* cst *)
  inverts K. applys red_cst.
  (* abs *)
  inverts K. applys red_abs.  
  (* constr *)
  apply red_constr. run_hyp K. applys (rm K). 
  introv M. subst. applys red_build_1.
  (* unary *)
    (* ALTERNATIVE for testing: 
    run_pre.
    run_pre as o1 R1.
    run_pre K as o1 R1 K.
    run_pre K as o1 R1 K'.
    *)
    (* DETAILS 
    run_pre as o1 R1.
    run_step red_unary o1 R1.
    run_check_current_out o. run_post.
    *)
  run red_unary. applys red_unary_1.
  destruct p; tryfalse; run_inv.
    applys* unary_red_raise.
    runs*. 
    runs*. 
  (* binary *)
  run red_binary. run red_binary_1. 
  applys red_binary_2. destruct p; tryfalse.
  runs. runs*.
  runs. runs*. 
  runs. runs*. 
  runs. runs. case_if; run_inv; subst; autos*.
  (* app *)
  run red_app. run red_app_1. destruct v; tryfalse.
  unfolds run_call. run. inverts E.
  rename v0 into v, p0 into p.
  forwards M: ching_spec v p.
  destruct (run_matching v p).
    applys* red_app_2_match.
    inverts K. apply* red_app_2_mismatch.
  (* seq *)
  run red_seq. case_if. applys* red_seq_1. 
  (* let *)
  run red_let. forwards M: run_matching_spec v p.
  destruct (run_matching v p).
    applys* red_let_1_match.
    run_inv. applys* red_let_1_mismatch.
  (* if *)
  runs red_if.
    applys* red_if_1_true.
    destruct o0.
      applys* red_if_1_false_some.
      inverts K. applys* red_if_1_false_none.
  (* match *)
  run red_match. run_hyp K. applys* red_match_1.
  (* try *)
  run red_try.
    subst. run_abort.
    destruct B; runs_inv.
     applys* red_try_1_val. 
     run_hyp K. applys* red_try_1_exn.
  (* assert *)
  runs red_assert.
    applys red_assert_1_true.
    applys red_assert_1_false.
Admitted. (*faster*)


Lemma correct_run_branches : forall R, 
  correct_runs R ->  
  correct_runs_branches_def (run_branches R).
Proof.
  introv IH. lets IHt: (correct_runs_trm IH).
  intros bs. induction bs; introv K; simpl in K.
  (* nil *)
  inverts K. applys* red_branches_1_nil.
  (* cons *)
  destruct a as [p g t].
  forwards M: run_matching_spec v p.
  destruct (run_matching v p).
  (* match *)
  destruct g as [tg|]. 
  (* match guarded *)
  run* red_branches_1_cons_match_guarded.
    (* ALTERNATIVE
    run_pre K as o1 R1. 
    run_step red_branches_1_cons_match_guarded o1 R1.
    auto.
    run_post.
    *)
    (* ALTERNATIVE
    lets (o1&O1&M1): if_success_bool_cases_out (rm K).
    applys* red_branches_1_cons_match_guarded o1.
    destruct M1 as [(Er&Ab)|(m1&z1&Er&[(Ez1&K2)|(Ez1&K2)])].
    subst. applys* red_abort.
    *)
  (* match guarded true *)
  subst. applys* red_branches_2_true.
  (* match guarded false *)
  subst. applys* red_branches_2_false.
  (* match unguarded *)
  applys* red_branches_1_cons_match_unguarded.
  (* mismatch *)
  applys* red_branches_1_cons_mismatch.
Qed.


(** Proof of correctness for the main function *)

Lemma correct_runs_for : forall (n:nat), 
  correct_runs (runs_for n).
Proof.
  induction n.
  constructor; introv K; simpls; discriminate.
  simpl. constructor; introv K; simpls.
    apply* correct_run_trm.
    apply* correct_run_branches.
    apply* correct_run_list.
Qed.








(*--------------------------------------*)

(** Not used *)

Ltac name_runs o :=
  match goal with HR: ?H = res_out _ |- _ =>
  match H with 
  | context [ runs_trm ?R ?m ?t ] => 
      sets_eq o: (runs_trm R m t)
  | context [ runs_branches ?R ?m ?B ?v ?bs ] => 
      sets_eq o: (run_branches R m B v bs)
  end
  end.