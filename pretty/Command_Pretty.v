(************************************************************
* Language of commands                                      *
* Pretty-big-step semantics                                 *
*************************************************************)

Set Implicit Arguments.
Require Export Command_Syntax.

Implicit Types h : heap.
Implicit Types s : stack.
Implicit Types n : int.
Implicit Types v : word.
Implicit Types e : exp.
Implicit Types a : act.
Implicit Types c : cmd.
Implicit Types p : prog.

Definition novar := O.


(*==========================================================*)
(* * Definitions *)

(************************************************************)
(* ** Trace semantics *)

(** Grammar of observable effects *)

Inductive obs :=
  | obs_none : obs
  | obs_load : word -> word -> obs
  | obs_store : word -> word -> obs
  | obs_cas : word -> word -> word -> word -> obs
  | obs_fence : obs.

Implicit Types k : obs.

(** Grammar of traces *)

Definition fintrace := list obs.
Definition inftrace := stream obs.
Definition trace := colist obs.
Definition traces := list trace.

Implicit Types f : fintrace.
Implicit Types i : inftrace.
Implicit Types t : trace.

(** Grammar of outcomes *)

Inductive out :=
  | out_ter : stack -> fintrace -> out
  | out_div : inftrace -> out.

Implicit Types o : out.

(** Prefixing of an outcome with a trace *)

Definition out_prepend f o :=
  match o with
  | out_ter s f' => out_ter s (f ++ f')
  | out_div i => out_div (stream_prepend f i)
  end.

(** Outcomes that abort *)

Inductive abort : out -> Prop :=
  | abort_div : forall i, abort (out_div i).

(** Grammar of extended commands *)

Inductive ext :=
  | ext_cmd : cmd -> ext
  | ext_seq_1 : out -> cmd -> ext.

Implicit Types d : ext.
Coercion ext_cmd : cmd >-> ext.

(** Evaluation of effectful actions *)

Inductive exec : stack -> act -> word -> obs -> Prop :=
  | exec_comp : forall e v s a,
      eval s e = v ->
      exec s (act_comp e) v obs_none 
  | exec_load : forall v1 v2 s e,
      eval s e = v1 ->
      exec s (act_load e) v2 (obs_load v1 v2)
  | exec_store : forall v1 v2 s e1 e2,
      eval s e1 = v1 ->
      eval s e2 = v2 ->
      exec s (act_store e1 e2) v2 (obs_store v1 v2)
  | exec_cas : forall v1 v2 v3 v4 s e1 e2 e3,
      eval s e1 = v1 ->
      eval s e2 = v2 ->
      eval s e3 = v3 ->
      exec s (act_cas e1 e2 e3) v4 (obs_cas v1 v2 v3 v4)
  | exec_fence : forall s,
      exec s (act_fence) 0 obs_fence.

(** Prefixing the trace with a [obs_none] *)

Definition step o :=
  out_prepend (obs_none::nil) o.

(** Evaluation of commands *)

Inductive red : stack -> ext -> out -> Prop :=
  | red_bind : forall v k s' s x a,
      exec s a v k ->
      s' = (If x = novar then s else Heap.write s x v) ->
      red s (cmd_bind x a) (out_ter s' (k::nil))
  | red_seq : forall o1 s c1 c2 o,
      red s c1 o1 ->
      red s (ext_seq_1 o1 c2) o ->
      red s (cmd_seq c1 c2) (step o)
  | red_seq_1_abort : forall s o c2,
      abort o ->
      red s (ext_seq_1 o c2) (step o)
  | red_seq_1 : forall s s' f o c2,
      red s c2 o ->
      red s' (ext_seq_1 (out_ter s f) c2) (step (out_prepend f o))
  | red_if : forall c3 s e o c1 c2,
      c3 = (If (eval s e = 0) then c1 else c2) ->
      red s c3 o ->
      red s (cmd_if e c1 c2) (step o)
  | red_while_exit : forall s e c1,
      eval s e = 0 ->
      red s (cmd_while e c1) (out_ter s (obs_none::nil))
  | red_while_step : forall s e c1 o,
      red s (cmd_seq c1 (cmd_while e c1)) o ->
      red s (cmd_while e c1) (step o). 

(** Same as above, except co-inductive *)

CoInductive cored : stack -> ext -> out -> Prop :=
  | cored_bind : forall v k s' s x a,
      exec s a v k ->
      s' = (If x = novar then s else Heap.write s x v) ->
      cored s (cmd_bind x a) (out_ter s' (k::nil))
  | cored_seq : forall o1 s c1 c2 o,
      cored s c1 o1 ->
      cored s (ext_seq_1 o1 c2) o ->
      cored s (cmd_seq c1 c2) (step o)
  | cored_seq_1_abort : forall s o c2,
      abort o ->
      cored s (ext_seq_1 o c2) (step o)
  | cored_seq_1 : forall s s' f o c2,
      cored s c2 o ->
      cored s' (ext_seq_1 (out_ter s f) c2) (step (out_prepend f o))
  | cored_if : forall c3 s e o c1 c2,
      c3 = (If (eval s e = 0) then c1 else c2) ->
      cored s c3 o ->
      cored s (cmd_if e c1 c2) (step o)
  | cored_while_exit : forall s e c1,
      eval s e = 0 ->
      cored s (cmd_while e c1) (out_ter s (obs_none::nil))
  | cored_while_step : forall s e c1 o,
      cored s (cmd_seq c1 (cmd_while e c1)) o ->
      cored s (cmd_while e c1) (step o). 

(** Same as above, except in Type *)

CoInductive tcored : stack -> ext -> out -> Type :=
  | tcored_bind : forall v k s' s x a,
      exec s a v k ->
      s' = (If x = novar then s else Heap.write s x v) ->
      tcored s (cmd_bind x a) (out_ter s' (k::nil))
  | tcored_seq : forall o1 s c1 c2 o,
      tcored s c1 o1 ->
      tcored s (ext_seq_1 o1 c2) o ->
      tcored s (cmd_seq c1 c2) (step o)
  | tcored_seq_1_abort : forall s o c2,
      abort o ->
      tcored s (ext_seq_1 o c2) (step o)
  | tcored_seq_1 : forall s s' f o c2,
      tcored s c2 o ->
      tcored s' (ext_seq_1 (out_ter s f) c2) (step (out_prepend f o))
  | tcored_if : forall c3 s e o c1 c2,
      c3 = (If (eval s e = 0) then c1 else c2) ->
      tcored s c3 o ->
      tcored s (cmd_if e c1 c2) (step o)
  | tcored_while_exit : forall s e c1,
      eval s e = 0 ->
      tcored s (cmd_while e c1) (out_ter s (obs_none::nil))
  | tcored_while_step : forall s e c1 o,
      tcored s (cmd_seq c1 (cmd_while e c1)) o ->
      tcored s (cmd_while e c1) (step o). 

(** should be generated by coq *)

Inductive branches (A : Type) (P : A -> Prop) : Type := 
  | branches_witness : sig P -> branches P
  | branches_none : (forall x, ~ P x) -> branches P.

Lemma branches_intro : forall A (P:A->Prop), branches P.
Proof. 
  intros. destruct (classicT (ex P)) as [C|C].
  applys branches_witness. applys~ indefinite_description.
  applys branches_none. rewrite <- not_exists. intros [x M].
   applys C. applys ex_intro M.
Qed.

Lemma cored_tcored : forall s d o,
  cored s d o -> tcored s d o.
Proof.
  cofix IH. introv H. destruct d as [ [x a|c1 c2|e c1 c2|e c1] |o1 c2].
  destruct (branches_intro (fun z => let '(s',v,k) := z in
    exec s a v k /\ s' = (If x = novar then s else Heap.write s x v)
    /\  o = out_ter s' (k::nil)))
  as [[[[s' v'] k] (?&?&?)]|N]. 
   subst. constructors*.
   false. invert H. intros. applys N (s',v,k). subst. splits*.
  destruct (branches_intro (fun z => let '(o1,o') := z in
    cored s c1 o1 /\ cored s (ext_seq_1 o1 c2) o' /\ o = step o'))
  as [[[o1 o'] (?&?&?)]|N]. 
   subst. constructors*.
   false. inverts H. applys* N (o1,o0).
  destruct (branches_intro (fun z => let '(c3,o') := z in
      c3 = (If (eval s e = 0) then c1 else c2) /\
      cored s c3 o' /\ o = step o'))
  as [[[c4 o'] (?&?&?)]|N]. 
   subst. constructors*.
   false. invert H. intros. applys* N (c3,o0).
  destruct (branches_intro (fun z:unit => 
      eval s e = 0 /\ o = (out_ter s (obs_none::nil))))
  as [[[] (?&?)]|N]. 
   subst. constructors*.
    destruct (branches_intro (fun o' => 
      cored s (cmd_seq c1 (cmd_while e c1)) o' /\ o = step o'))
    as [[o' (?&?)]|N2]. 
      subst. constructors*.
   false. inverts H; intros. applys* N tt. applys* N2 o0.
  destruct (branches_intro (fun o' => 
      o1 = o' /\ abort o' /\ o = step o'))
  as [[o' (?&?&?)]|N]. 
   subst. constructors*.
    destruct (branches_intro (fun z => let '(s0,f,o') := z in
      cored s0 c2 o' /\
      o1 = out_ter s0 f /\
      o = step (out_prepend f o')))
    as [[[[s0 f] o'] (?&?&?)]|N2]. 
      subst. constructors*.
   false. inverts H; intros. applys* N. applys* N2 (s0,f,o0).
Qed.

Hint Constructors cored.

Theorem red_cored : forall s d o,
  red s d o -> cored s d o.
Proof. introv H. induction* H. Qed.

CoFixpoint dummy := obs_none ::: dummy.

Definition stream_step_eq A (s1 s2 : stream A) :=
  match s1,s2 with 
  | stream_intro x1 s1', stream_intro x2 s2' => x1 = x2 /\ s1' = s2'
  end.

Lemma stream_step_eq_inj : forall A (s1 s2 : stream A),
  stream_step_eq s1 s2 -> s1 = s2.
Proof.
  introv H. destruct s1; destruct s2; simpls; inverts~ H.
Qed.


Lemma dummy_unfold : dummy = obs_none ::: dummy.
Proof. 
  applys stream_step_eq_inj. simpl. auto.
Qed.

Definition get_out_trace o :=
  match o with
  | out_ter _ _ => dummy
  | out_div i => i
  end.

Ltac testi H :=
  match type of H with tcored ?s ?d ?o => tests: (red s d o) end.

Hint Constructors  red abort.

Lemma get_out_trace_step : forall o,
  out_div (get_out_trace (step o)) = step (out_div (get_out_trace o)).
Proof.
  intros. destruct~ o. simpl. rewrite dummy_unfold at 1. auto.
Qed.

(*
Lemma get_out_trace_self : forall o,
  out_div (get_out_trace o) = o.
Proof.
  intros. destruct~ o. simpl. rewrite dummy_unfold at 1. auto.
Qed.
*)

Definition cored_not_red_trace : forall s d o,
  tcored s d o -> ~ red s d o -> inftrace.
Proof.
  cofix IH. introv R N. inverts R as.
  introv E. false* N.
  introv R1 R2. testi R1.
     forwards i2: IH R2. eauto. exact (obs_none:::i2).
     forwards i2: IH R1. eauto. exact (obs_none:::i2).
  skip.
  skip.
  skip.
  skip.
  skip.
Defined.

Lemma cored_not_red_not_ter' : forall s d o
  (R:tcored s d o) (N: ~ red s d o),
  cored s d (out_div (cored_not_red_trace R N)).
Proof.
  cofix IH. intros. destruct R.
  skip.
  skip.

  skip.
  skip.
  skip.
  skip.
  skip.
Qed.



Lemma cored_not_red_not_ter : forall s d o,
  cored s d o -> ~ red s d o -> exists i, cored s d (out_div i).
Proof.
  introv R N. exists (cored_not_red_trace (cored_tcored R) N).
  applys cored_not_red_not_ter'.
Qed.


Lemma cored_red_or_div : forall s d o,
  cored s d o -> red s d o \/ exists i, cored s d (out_div i). 
Proof.
  introv C. applys classic_right. intros N.
  applys* cored_not_red_not_ter.
Qed.


(************************************************************)
(* ** Auxiliary definition for the semantics of a program *)

(** Grammar of the results of a program *)

Inductive res :=
  | res_ter : heap -> res
  | res_div.

Implicit Types r : res.

(** Trace of a process execution *)

Inductive process_trace : cmd -> trace -> Prop :=
  | process_trace_ter : forall s c f,
      red stack_init c (out_ter s f) ->
      process_trace c (colist_of_list f)
  | process_trace_div : forall c i,
      cored stack_init c (out_div i) ->
      process_trace c (colist_of_stream i).

(** Extracting one observation from a list of traces *)

Inductive extract_obs : nat -> obs -> traces -> traces -> Prop :=
  | extract_obs_here : forall k t ts ts', 
      extract_obs 0 k ((k::::t)::ts) (t::ts')
  | extract_obs_next : forall id k t ts ts', 
      extract_obs id k ts ts' ->
      extract_obs (S id) k (t::ts) (t::ts').


(************************************************************)
(* ** Semantics w.r.t. sequential consistency *)

(** Transition of an observation over the heap *)

Inductive sc_heap_update : obs -> heap -> heap -> Prop :=
  | sc_heap_update_none : forall h,
      sc_heap_update obs_none h h
  | sc_heap_update_load : forall h v1 v2,
      Heap.binds h v1 v2 ->
      sc_heap_update (obs_load v1 v2) h h
  | sc_heap_update_store : forall h h' v1 v2,
      h' = Heap.write h v1 v2 ->
      sc_heap_update (obs_store v1 v2) h h'
  | sc_heap_update_cas : forall E h' v2' h v1 v2 v3 v4,
      Heap.binds h v1 v2' ->
      E = (v2 = v2') ->
      h' = (If E then (Heap.write h v1 v3) else h) ->
      v4 = int_of_prop E ->
      sc_heap_update (obs_cas v1 v2 v3 v4) h h'
  | sc_heap_update_fence : forall h,
      sc_heap_update obs_fence h h.

(** Interleaving of traces *)

CoInductive sc_observable : heap -> traces -> res -> Prop :=
  | sc_observable_nil : forall h ts,
      Forall (eq colist_nil) ts ->
      sc_observable h ts (res_ter h)
  | sc_observable_cons : forall id h' ts' k h ts r,
      extract_obs id k ts ts' ->
      sc_heap_update k h h' ->
      sc_observable h' ts' r ->
      sc_observable h ts r.

(** Possible behavior of a program *)

Definition sc_behavior p r :=
  exists ts, Forall2 process_trace p ts
    /\ sc_observable heap_init ts r
    /\ (r <> res_div -> Forall colist_finite ts).

(** More direct definitions for behaviros *)

Definition sc_returns p h := sc_behavior p (res_ter h).
Definition sc_diverge p := sc_behavior p res_div.



(************************************************************)
(* ** Semantics w.r.t. x86-TSO memory model *)

(** Write buffer *)

Definition buffer := list (word*word).

Implicit Types b : buffer.

Definition buffers := list buffer.

Definition buffers_init p : buffers := 
  LibList.map (fun _ => nil) p.

(** Updating a given buffer inside a list of buffers *)

Inductive buffers_replace : nat -> buffer -> buffer -> buffers -> buffers -> Prop :=
  | buffers_replace_here : forall b b' bs,
      buffers_replace O b b' (b::bs) (b'::bs)
  | buffers_replace_next : forall id b b' bs bs' b0,
      buffers_replace id b b' bs bs' ->
      buffers_replace (S id) b b' (b0::bs) (b0::bs').

(** Reading from the buffer then the store *)

Definition x86tso_lookup h b v1 v2 :=
  match assoc_option v1 b with
  | Some v => v = v2
  | None => Heap.binds h v1 v2 
  end.

(** Transition of an observation over the heap *)

Inductive x86tso_heap_update : obs -> heap -> heap -> buffer -> buffer -> Prop :=
  | x86tso_heap_update_none : forall h b,
      x86tso_heap_update obs_none h h b b
  | x86tso_heap_update_load_buffer : forall h b v1 v2,
      x86tso_lookup h b v1 v2 ->
      x86tso_heap_update (obs_load v1 v2) h h b b
  | x86tso_heap_update_store : forall h h' v1 v2 b b',
      b' = b ++ ((v1,v2)::nil) ->
      x86tso_heap_update (obs_store v1 v2) h h b b'
  | x86tso_heap_update_cas : forall E h' v2' h v1 v2 v3 v4,
      Heap.binds h v1 v2' ->
      E = (v2 = v2') ->
      h' = (If E then (Heap.write h v1 v3) else h) ->
      v4 = int_of_prop E ->
      x86tso_heap_update (obs_cas v1 v2 v3 v4) h h' nil nil
  | x86tso_heap_update_fence : forall h,
      x86tso_heap_update obs_fence h h nil nil.

(** Interleaving of traces *)

CoInductive x86tso_observable : heap -> buffers -> traces -> res -> Prop :=
  | x86tso_observable_nil : forall h bs ts,
      Forall (eq nil) bs ->
      Forall (eq colist_nil) ts ->
      x86tso_observable h bs ts (res_ter h)
  | x86tso_observable_cons : forall id h' b b' bs' ts' k h ts bs r,
      extract_obs id k ts ts' ->
      buffers_replace id b b' bs bs' ->
      x86tso_heap_update k h h' b b' ->
      x86tso_observable h' bs' ts' r ->
      x86tso_observable h bs ts r
  | x86tso_observable_write : forall id b h' bs bs' v1 v2 h ts r,
      buffers_replace id ((v1,v2)::b) b bs bs' ->
      h' = Heap.write h v1 v2 ->
      x86tso_observable h' bs' ts r ->
      x86tso_observable h bs ts r.

(** Possible behavior of a program *)

Definition x86tso_behavior p r :=
  exists ts, Forall2 process_trace p ts
    /\ x86tso_observable heap_init (buffers_init p) ts r
    /\ (r <> res_div -> Forall colist_finite ts).

(** More direct definitions for behaviros *)

Definition x86tso_returns p h := x86tso_behavior p (res_ter h).
Definition x86tso_diverge p := x86tso_behavior p res_div.




(*==========================================================*)
(* * Proofs *)

(************************************************************)
(* ** Permutations *)

Inductive is_cmd_fence : cmd -> Prop :=
  | is_cmd_fence_intro : is_cmd_fence (cmd_bind novar act_fence).

Inductive is_cmd_cas : cmd -> Prop :=
  | is_cmd_cas_intro : forall x e1 e2 e3,
      is_cmd_cas (cmd_bind x (act_cas e1 e2 e3)).

Inductive is_cmd_load : cmd -> exp -> Prop :=
  | is_cmd_load_intro : forall x e,
      is_cmd_load (cmd_bind x (act_load e)) e.

Inductive is_cmd_store : cmd -> exp -> Prop :=
  | is_cmd_store_intro : forall x e1 e2,
      is_cmd_store (cmd_bind x (act_store e1 e2)) e1.

Definition is_cmd_load_or_store c e :=
  is_cmd_load c e \/ is_cmd_store c e.


Inductive cmd_permut : cmd -> cmd -> Prop :=
  | cmd_permut_refl : forall c,
      cmd_permut c c
  | cmd_permut_ctx_seq_1 : forall c1 c2 c1',
      cmd_permut c1 c1' ->
      cmd_permut (cmd_seq c1 c2) (cmd_seq c1' c2)
(*
  | cmd_permut_ctx_seq_2 : forall c1 c2 c2',
      cmd_permut c2 c2' ->
      cmd_permut (cmd_seq c1 c2) (cmd_seq c1 c2')
  | cmd_permut_ctx_if_1 : forall e c1 c2 c1',
      cmd_permut c1 c1' ->
      cmd_permut (cmd_if e c1 c2) (cmd_if e c1' c2)
  | cmd_permut_ctx_if_2 : forall e c1 c2 c2',
      cmd_permut c2 c2' ->
      cmd_permut (cmd_if e c1 c2) (cmd_if e c1 c2')
  | cmd_permut_ctx_while : forall e c1 c1',
      cmd_permut c1 c1' ->
      cmd_permut (cmd_while e c1) (cmd_while e c1')
*)
  | cmd_permut_seq_assoc_1 : forall c1 c2 c3,
      cmd_permut (cmd_seq c1 (cmd_seq c2 c3)) (cmd_seq (cmd_seq c1 c2) c3)
(*
  | cmd_permut_seq_assoc_2 : forall c1 c2 c3,
      cmd_permut (cmd_seq (cmd_seq c1 c2) c3) (cmd_seq c1 (cmd_seq c2 c3)) 
*)
  | cmd_permut_fence_fence : forall c1 c2,
      is_cmd_fence c1 ->
      is_cmd_fence c2 ->
      cmd_permut (cmd_seq c1 c2) c1
(*
  | cmd_permut_fence_cas : forall c1 c2,
      is_cmd_fence c1 ->
      is_cmd_cas c2 ->
      cmd_permut (cmd_seq c1 c2) c2
  | cmd_permut_cas_fence : forall c1 c2,
      is_cmd_cas c1 ->
      is_cmd_fence c2 ->
      cmd_permut (cmd_seq c1 c2) c1
  | cmd_permut_load_load :forall x1 e1 x2 e2,
      is_cmd_load c1 e1 ->
      is_cmd_load c2 e2 ->
      cmd_permut (cmd_seq c1 c2) (cmd_seq c2 c1)
  | cmd_permut_neq : forall c1 c2,
      is_cmd_load_or_store c1 e1 ->
      is_cmd_load_or_store c2 e2 ->
      (forall s, eval s e1 <> eval s e2) ->
      cmd_permut (cmd_seq c1 c2) (cmd_seq c2 c1)
  *)
  .

Definition is_obs_cas k :=
  match k with obs_cas _ _ _ _ => True | _ => False end.

Definition is_obs_load k v :=
  match k with obs_load v _ => True | _ => False end.

Definition is_obs_store k v :=
  match k with obs_load v _ => True | _ => False end.

Definition is_obs_load_or_store k v :=
  is_obs_load k v \/ is_obs_store k v.



Inductive trace_permut : trace -> trace -> Prop :=
  | trace_permut_refl : forall t,
      trace_permut t t
  | trace_permut_append_l : forall t1 t2 t,
      trace_permut t1 t2 ->
      trace_permut (t+++t1) (t+++t2) 
  | trace_permut_append_r : forall t1 t2 t,
      trace_permut t1 t2 ->
      trace_permut (t1+++t) (t2+++t) 
  | trace_permut_none_l : forall t1 t2, 
      trace_permut t1 t2 ->
      trace_permut (obs_none::::t1) t2
  | trace_permut_none_r : forall t1 t2, 
      trace_permut t1 t2 ->
      trace_permut t1 (obs_none::::t2) 
  | trace_permut_fence_fence : 
      trace_permut (obs_fence::::obs_fence::::cnil) (obs_fence::::cnil)
(*
  | trace_permut_fence_cas : forall k,
      is_obs_cas k ->
      trace_permut (obs_fence::::obs_none::::k::::cnil) k
  | trace_permut_cas_fence : forall k,
      is_obs_cas k ->
      trace_permut (k::::obs_none::::obs_fence::::cnil) k
  | trace_permut_load_load :forall x1 e1 x2 e2,
      is_obs_load k1 v1 ->
      is_obs_load k2 v2 ->
      trace_permut (k1::::obs_none::::k2::::cnil) (k2::::obs_none::::k1::::cnil)
  | trace_permut_neq : forall v1 v2,
      is_obs_load_or_store k1 v1 ->
      is_obs_load_or_store k2 v2 ->
      v1 <> v2 ->
      trace_permut (k1::::obs_none::::k2::::cnil) (k2::::obs_none::::k1::::cnil)
*)
      .


Hint Constructors trace_permut.

Lemma trace_permut_cons : forall k t1 t2,
  trace_permut t1 t2 ->
  trace_permut (k::::t1) (k::::t2).
Proof. 
  introv H. forwards M: trace_permut_append_l (k::::cnil) H.
  rew_colist~ in M.
Qed.

Hint Resolve trace_permut_cons.

Lemma trace_permut_prepend : forall f t1 t2,
  trace_permut t1 t2 ->
  trace_permut (colist_prepend f t1) (colist_prepend f t2).
Proof. introv H. induction f; simple*. Qed.

(*
Lemma trace_permut_append : forall t t1 t2,
  trace_permut t1 t2 ->
  colist_finite t1 ->
  trace_permut (t1 +++ t) (t2 +++ t).
Proof.
  introv P. induction P; introv T.
  auto.
  inverts T. rew_colist*.
  inverts T. rew_colist*.
  rew_colist*.
  rew_colist*.
  inverts~ P. rew_colist. 

trace_permut (colist_of_list f +++ colist_of_list f0)
  (colist_of_list t2' +++ colist_of_list f0)

*)
(*

Proof.
  Qed.

  | trace_permut_append : forall t t1 t2, eauto.

      trace_permut t1 t2 ->
      trace_permut (t1 +++ t) (t2 +++ t) 
*)

Lemma colist_finite_append_inv : forall A (s1 s2 : colist A),
  colist_finite (s1 +++ s2) ->
  colist_finite s1 /\ colist_finite s2.
Proof.
  introv H. inductions H.
  destruct s1; destruct s2; rew_colist in *; auto_false.
  destruct s1.
    rew_colist in *. destruct s2; tryfalse. inverts~ x. 
    rew_colist in *. inverts x. forwards*: IHcolist_finite.
Qed.

Lemma trace_permut_finite : forall t1 t2,
  trace_permut t1 t2 ->
  colist_finite t1 ->
  colist_finite t2.
Proof.
  introv P. induction P; introv F.
  auto.
  lets* (?&?): colist_finite_append_inv F.
  lets* (?&?): colist_finite_append_inv F.
  inverts~ F.
  auto.
  auto.
Qed.

Lemma colist_prove_eq : forall A (s1 s2 : colist A),
  colist_step s1 = colist_step s2 -> s1 = s2.
Proof. intros. destruct s1; destruct~ s2. Qed.

(* bin
Lemma trace_simpl : forall s f1 f2,
    step (out_prepend f1 (out_ter s f2))
  = out_ter s (obs_none :: f1 ++ f2).
Proof. auto. Qed.
*)
(*
  intros. auto. unfold step, colist_one, out_prepend.
  fequals. rew_colist~.
*)

Lemma colist_of_list_append : forall A (l1 l2 : list A),
   colist_of_list (l1 ++ l2) 
 = colist_append (colist_of_list l1) (colist_of_list l2).
Proof. 
  intros. induction l1; rew_list; simpl; rew_colist; fequals.
Qed.

Hint Rewrite colist_of_list_append : rew_colist.

Ltac trace_simpl_base :=
  simpl; idtac.
Tactic Notation "trace_simpl" :=
  trace_simpl_base; rew_colist.
Tactic Notation "trace_simpl" "in" hyp(H) :=
  trace_simpl_base; rew_colist in H.
Tactic Notation "trace_simpl" "in" "*" :=
  trace_simpl_base; rew_colist in *.

Hint Constructors exec.

Lemma red_bind_novar : forall v k s a,
  exec s a v k ->
  red s (cmd_bind novar a) (out_ter s (k::nil)).
Proof. introv H. constructors*. case_if*. Qed.

Lemma cored_bind_novar : forall v k s a,
  exec s a v k ->
  cored s (cmd_bind novar a) (out_ter s (k::nil)).
Proof. introv H. constructors*. case_if*. Qed. (* or red_cored *)

Hint Constructors trace_permut.

(* bin
Axiom red_trace_finite : forall s c o,
  red s c o -> 
  exists s t, o = out_ter s t /\ colist_finite t /\ t <> colist_nil.

Lemma red_cmd_trace_finite : forall s c t s',
  red s c (out_ter s' t) -> colist_finite t.
Proof. introv R. lets (?&?&E&?&?): red_trace_finite R. inverts~ E. Qed.
Hint Resolve red_cmd_trace_finite.
*)

Lemma red_cmd_permut_trace_permut : forall c1 c2 f1 s s',
  cmd_permut c1 c2 ->
  red s c1 (out_ter s' f1) ->
  exists f2, red s c2 (out_ter s' f2) 
          /\ trace_permut (colist_of_list f1) (colist_of_list f2).
Proof.
  introv P. gen f1 s s'. induction P; introv R.
  (* refl *)
  eauto.
  (* ctx_seq_1 *)
  inverts R as R1 R2 M. inverts R2 as. 
  introv A. inverts A. trace_simpl in M. false.
  introv R2. destruct o0; trace_simpl in M; [| false ].
  inverts M. forwards* (t2'&S1&E1): IHP R1.
  esplit. split. applys_eq red_seq 1. eauto.
  applys* red_seq_1. simpl. fequals.
  trace_simpl. eauto.
  (* seq_assoc_1 *)
  inverts R as R1 R2 M. inverts R2 as.
  introv A. inverts A. trace_simpl in M. false.
  introv R2. destruct o0; trace_simpl in M; [| false ].
  inverts M. inverts R2 as R2 R3 M. inverts R3 as.
  introv A. inverts A. trace_simpl in M. false.
  introv R3. destruct o0; trace_simpl in M; [| false ].
  inverts M. esplit. split. applys_eq red_seq 1.
  applys* red_seq. simpl. applys* red_seq_1.
  trace_simpl. fequals.
  rew_list. trace_simpl. 
  repeat applys trace_permut_none_l.
  repeat applys trace_permut_none_r.
  applys trace_permut_append_l.
  trace_simpl. eauto.
  (* fence_fence *)
  inverts H. inverts H0. inverts R as R1 R2 M.
  inverts R1 as R1. inverts R1.
  inverts R2 as R2 R3. inverts R2. inverts R2 as R2. inverts R2.
  case_if. trace_simpl in M. inverts M.
  esplit. split. applys* red_bind_novar.
  rew_list. trace_simpl. eauto.
Qed.

Lemma colist_of_stream_cons : forall A x (s : stream A),
   colist_of_stream (x:::s) = x::::(colist_of_stream s).
Proof. intros. applys~ colist_prove_eq. Qed.

Hint Rewrite colist_of_stream_cons : rew_colist.



Hint Constructors cored.
Hint Constructors abort.

Lemma cored_cmd_permut_trace_permut : forall c1 c2 i1 s,
  cmd_permut c1 c2 ->
  cored s c1 (out_div i1) ->
  exists i2, cored s c2 (out_div i2) 
          /\ trace_permut (colist_of_stream i1) (colist_of_stream i2).
Proof.
  introv P. gen i1 s. induction P; introv R.
  (* refl *)
  eauto.
  (* ctx_seq_1 *)
(*
Focus 1.
  inverts R as R1 R2 M. inverts R2 as. 
  introv A. inverts A. inverts M.
   forwards* (i2&?&?): IHP. exists (obs_none:::(obs_none:::i2)). splits*.
   applys* cored_seq (out_div (obs_none:::i2)).
   applys* cored_seq_1_abort (out_div i2). 
   trace_simpl. eauto. 
  introv R2. destruct o0; trace_simpl in M; [false|].
  inverts M. forwards [M1|(i1&M1)]: (cored_red_or_div R1).
  applys red_cored.

 exists (obs_none:::i). splits.

  cored s d o -> red s d o \/ exists i, cored s d (out_div i). 
*)
skip.
skip.
(*
   applys_eq cored_seq 1. 

  applys* cored_seq_1. simpl. fequals.
  trace_simpl. eauto.
  (* seq_assoc_1 *)
  inverts R as R1 R2 M. inverts R2 as.
  introv A. inverts A. trace_simpl in M. false.
  introv R2. destruct o0; trace_simpl in M; [| false ].
  inverts M. inverts R2 as R2 R3 M. inverts R3 as.
  introv A. inverts A. trace_simpl in M. false.
  introv R3. destruct o0; trace_simpl in M; [| false ].
  inverts M. esplit. split. applys_eq cored_seq 1.
  applys* cored_seq. simpl. applys* cored_seq_1.
  trace_simpl. fequals.
  rew_list. trace_simpl. 
  repeat applys trace_permut_none_l.
  repeat applys trace_permut_none_r.
  applys trace_permut_append_l.
  trace_simpl. eauto.
*)
  (* fence_fence *)
  inverts H. inverts H0. inverts R as R1 R2 M.
  inverts R1 as R1. inverts R1.
  inverts R2 as R2 R3. inverts R2. inverts R2 as R2. inverts R2.
  case_if.
Qed.






Hint Constructors process_trace. 

Lemma process_cmd_permut_trace_permut : forall c1 c2 t1,
  cmd_permut c1 c2 ->
  process_trace c1 t1 ->
  exists t2, process_trace c2 t2 
          /\ trace_permut t1 t2.
Proof.
  introv P T. inverts T as R.    
  forwards* (f2&?&?): red_cmd_permut_trace_permut.
    exists* (colist_of_list f2).
  forwards* (i2&?&?): cored_cmd_permut_trace_permut.
    exists* (colist_of_stream i2).
Qed.

Lemma trace_permut_keep_x86tso_behavior : forall h bs ts1 ts2 r,
  Forall2 trace_permut ts1 ts2 ->
  x86tso_observable h bs ts1 r ->
  x86tso_observable h bs ts2 r.
Proof.
  cofix IH. introv P M. inverts P. skip.

Qed.
(* process_cmd_permut_trace_permut *)

Lemma cmd_permut_keep_x86tso_behavior : forall p1 p2 r,
  Forall2 cmd_permut p1 p2 ->
  x86tso_behavior p1 r ->
  x86tso_behavior p2 r.
Proof.
  introv F (ts&TS&OS&FS). 
  asserts (ts'&M): (exists ts',
    Forall3 (fun c t t' => process_trace c t' /\ trace_permut t t') p2 ts ts').
    clear OS FS. gen p2. induction TS; intros; inverts F.
    esplit. applys Forall3_nil.
    forwards* (t'&?&?): process_cmd_permut_trace_permut.
    forwards* (?&?): IHTS.
     esplit. applys* Forall3_cons. 
  exists ts'. splits.
  gen M. clears_all. introv M. induction M; constructors*.
  applys trace_permut_keep_x86tso_behavior ts.
    gen M. clears_all. introv M. induction M; constructors*.
    applys_eq OS 3. gen F. clears_all. introv F.
     unfold buffers_init. induction F; intros; rew_list; fequals.
  gen M F FS. clears_all. introv M. gen p1. induction M; introv P FS N.
    constructors.
    forwards~ FS': FS. inverts~ FS'.  inverts H as N1 N2. inverts P.
     constructors.
       applys~ trace_permut_finite N2.
       applys* IHM.
Qed.
  

