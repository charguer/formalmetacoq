


----------------


Definition eval : 
  forall (t:trm) (H:terminates t), (returns_of t).
Proof.
skip_goal IH.

introv H. destruct t.
false* terminates_bvar_not. 
false* terminates_fvar_not.
econstructor. apply~ terminates_abs.

destruct (IH t1) as [v1 IH1]. apply* terminates_app_1.
destruct (IH t2) as [v2 IH2]. apply* terminates_app_2.
destruct v1; [ skip | skip | | skip ]. (* false *)
destruct (IH (v1 ^^ v2)) as [v3 IH3]. apply* terminates_app_3.
econstructor. apply* reds_red.
Defined.






 

Definition future v t := reds v t.
Lemma reds_wf : well_founded reds.
Proof.
  intros t. constructor. introv H.
  induction H.
  constructor. introv M.
Qed.


(*
Inductive sub : trm -> trm -> Prop :=
  | sub_1 : forall t1 t2,
            sub t1 (trm_app t1 t2)
  | sub_2 : forall t1 t2,
            sub t2 (trm_app t1 t2)
  | sub_3 : forall t1 t3 t2 v2,
            reds t1 (trm_abs t3) ->
            reds t2 v2 ->
            sub (t3 ^^ v2) (trm_app t1 t2).

Definition terminating := { t | terminates t }.

Definition subs (t1 t2 : terminating) :=
  sub (proj1_sig t1) (proj1_sig t2).

Lemma sub_wf : well_founded subs.
Proof.
  intros m. sets_eq m': m. destruct m as [t [v R]].
  gen m'. 
  intros [t [v R]].
*)





 reds_val : forall t1 : trm, value t1 -> reds t1 t1

Lemma terminates_rec :
  forall P : trm -> Type,
  (forall t1, P (trm_abs t1)) ->
  (forall t3 v2 t1 t2,
    reds t1 (trm_abs t3) ->
    reds t2 v2 ->
    P t1 ->
    P t2 ->
    P (t3 ^^ v2) -> 
    P (trm_app t1 t2)) ->
   forall t, terminates t -> P t.
Proof.
  introv H1 H2 T. 

Qed.


Print reds_ind.

Inductive Reds : rel :=
 | Reds_intros : forall t1 : trm, value t1 -> reds t1 t1
 | reds_red : forall t3 v2 v3 t1 t2 : trm,
               reds t1 (trm_abs t3) ->
               reds t2 v2 -> reds (t3 ^^ v2) v3 -> reds (trm_app t1 t2) v3


(*
Definition relation_sym (A:Type) (R:A->A->Prop) :=
  fun x y => R y x.
*)



Inductive subterm: trm->trm->Prop :=
  | subterm_1 : forall t1 t2, 
      subterm t1 (trm_app t1 t2)
  | subterm_2 : forall t1 t2, 
      subterm t2 (trm_app t1 t2).

Inductive terminates (t : trm) : Prop :=
  | step : (forall t', beta t t' -> terminates t') ->
           (forall t', subterm t' t -> terminates t') -> 
           terminates t.

Lemma betas_to_subterm : forall t t' t1,
  betas t t' -> subterm t1 t -> 



Definition reducible t :=
  exists t', beta t t'.




Definition irreducible t :=
  forall t', beta t t' -> False.

Lemma not_irreducible :
  forall t t', beta t t' -> ~ irreducible t.
Proof.
  introv B H. applys* H. 
Qed.

Definition dec (P:Prop) := {P}+{~P}.

Lemma value_dec : forall t, dec (value t).
Proof.
  destruct t.
  right. introv H. inversion H.
  right. introv H. inversion H.
  left. constructor. skip. (* todo: term t *)
  right. introv H. inversion H.
Qed.

Hint Constructors beta.
Hint Extern 1 (term _) => skip.
Hint Extern 1 (body _) => skip.

Lemma irreducible_dec : forall t, dec (irreducible t).
(*  
Proof.
  induction t.
  left. introv H. inversion H.
  left. introv H. inversion H.
  left. introv H. inversion H.
  destruct (value_dec t1).    
    destruct t1; try solve [ false; inversion v ].
     destruct (value_dec t2).
       right. applys* not_irreducible.
       destruct IHt2. 
       left. introv H. inversions H.
         tryfalse*.
         inversions H4.
         tryfalse*.
; tryfalse*.
left. introv H. inversions H; tryfalse*.

  destruct IHt1.

   
     
Defined.
*)
Admitted.

Lemma reducible_dec : forall t, dec (reducible t).
Admitted.


Lemma terminates_irreducible : forall t,
  ~ reducible t -> terminates t.
Proof.
  introv H. constructor. introv R.
  false. applys H. exists* t'. skip.
Qed.

Lemma deterministic : forall t'1 t'2 t,
  beta t t'1 -> beta t t'2 -> t'1 = t'2.
Admitted.

Lemma terminates_app1 : forall t1 t2, 
  terminates (trm_app t1 t2) -> terminates t1.
Proof.
(* 
  introv H. inductions H gen t1 t2 end; introv.
  destruct (reducible_dec t1) as [[t' B]|NB].
  constructor. introv B'.
   applys H0. rewrite (deterministic B' B).
   apply beta_app1. eauto. eauto. eauto.
  apply~ terminates_irreducible.
Qed.
*)
Admitted.

Lemma terminates_app2_gen : forall t1 t2, 
  terminates (trm_app t1 t2) ->
  ~ reducible t1 ->
  terminates t2.
Proof. skip.
(*
  introv T. inductions T gen t1 t2 end; introv Ir.
  destruct (reducible_dec t2) as [[t' B]|NB].
  constructor. introv B'.
    applys H0. apply beta_app2.
   rewrite (deterministic B' B).

  apply~ terminates_irreducible.
*)
Qed.

Lemma terminates_app2 : forall t1 t2 v1, 
  ~ reducible v1 -> betas t1 v1 -> 
  terminates (trm_app t1 t2) -> 
  terminates t2.
Proof.
  introv Ir B. induction B; introv Te.
  apply* terminates_app2_gen.
  apply~ IHB. inversions Te. applys~ H0.
Qed.  
    
Definition eval : forall (t:trm) (H:terminates t), 
  {t':trm| betas t t'}.
introv H. induction H.
assert (terminates t). constructor~.
sets_eq t': t.
let go := 
  apply (@Specif.exist _ _ t'); (apply star_refl) in
(destruct t; [ go | go | go | ]).
subst t'.
destruct (H2 t1) as [t1' IH1]. constructor.
destruct (H2 t2) as [t2' IH2]. constructor.



let (t1',H1) := eval t1 _ in
     let (t2',H2) := eval t2 _ in
     match t1' with
     | trm_abs t3 => let (t',H3) := eval (t3 ^^ t2') _ in 
                     @Specif.exist _ _ t' _
     | _ => @Specif.exist _ _ (trm_app t1' t2') _ 
     end
Defined.
Print eval.
go



--pb manque des hypothèses !
Definition eval : forall (t:trm) (H:terminates t), 
  {t':trm| betas t t'}.
refine (fix eval (t:trm) (H:terminates t) {struct H} 
        : {t':trm | betas t t'} :=
  match H with step H' => 
  match t with 
  | trm_app t1 t2 =>  
     let (t1',H1) := eval t1 _ in
     let (t2',H2) := eval t2 _ in
     match t1' with
     | trm_abs t3 => let (t',H3) := eval (t3 ^^ t2') _ in 
                     @Specif.exist _ _ t' _
     | _ => @Specif.exist _ _ (trm_app t1' t2') _ 
     end
  | _ => @Specif.exist _ _ t _
  end end).




Inductive terminates (t : trm) : Prop :=
  | step : (forall t', betas t t' -> terminates t') -> terminates t.

Axiom terminates_value : forall v,
  value v -> terminates v.
Axiom terminates_app1 : forall t1 t2,
  terminates (trm_app t1 t2) ->
  terminates t1 /\ exists v1, value v1 /\ terminates (trm_app v1 t2).
Axiom terminates_app2 : forall v1 t2,
  value v1 ->
  terminates (trm_app v1 t2) ->
  terminates t2 /\ exists v2, value v2 /\ terminates (trm_app v1 v2).


Definition eval : forall (t:trm) (H:terminates t), trm.
introv H. induction H.
sets_eq t': t.
destruct t; [ exact t' | exact t' | | exact t'].
assert (terminates t'). constructor~.
subst t'.



Definition eval : forall (t:trm) (H:terminates t), trm.
refine (fix eval (t:trm) (H:terminates t) {struct H} : trm :=
  match H with step H' => 
  match t with 
  | trm_app t1 t2 =>  
     let t1' := eval t1 _ in
     let t2' := eval t2 _ in
     match t1' with
     | trm_abs t3 => eval (t3 ^^ t2') _
     | _ => trm_app t1' t2' 
     end
  | _ => t
  end end).
(* pb: dep hyp ... *)







(*Program Fixpoint eval (t:trm) (H:terminates t) {struct H} : trm :=
  match H with step _ H' => 
  match t with _ =>  t
  end end.

    Require Import Sumbool LibData.
Definition fixwf' (A:Type) (B:obj) (F:(A->B)->(A->B)) 
  (R:A->A->bool) (W:well_founded R) (x:A) :=
  (fix fixwf_rec (x:A) (K:Acc R x) {struct K} : B :=
     match K with Acc_intro K' =>
     let f y := match sumbool_of_bool (R y x) with 
                | left H => fixwf_rec y (K' y H)
                | _ => arbitrary end in
     F f x end)
  x (W x).
*)




Variable skip : False. 
Ltac skip :=
  assert False; [ apply skip | contradiction ].



(*
Axiom unifier_types : forall (A B:Type) (x : A) (y : B),
   A = B -> True.

Lemma demo_unifier : forall (S : Type) 
  (x: forall a:S, a=a), (forall a:S, a=a).
introv x (T: Type).
evar (y: forall a:T, a=a). subst T.
assert (True).
eapply unifier_types. apply x. apply y. reflexivity.
refine (unifier x y).
apply y.

instantiate (1:=x) in (Value of y).
*)


Hint Extern 1 (_ \in _ -> False) =>
  repeat match goal with
  | H: context [?x \in ?E -> False] |- _ => 
    fold (not (x \in E)) in H 
  | |- context [?x \in ?E -> False] => 
    fold (not (x \in E)) end.

(***************************************************************************)
(* BIN 

Ltac notin_simpl_hyps := (* forward-chaining *)
  try match goal with
  | H: _ \notin {} |- _ =>
     clear H; notin_simpl_hyps
  | H: ?x \notin {{?y}} |- _ =>
     lets: (@notin_singleton_r x y);
     clear H; notin_simpl_hyps
   | H: ?x \notin (?E \u ?F) |- _ =>
     let H1 := fresh "Fr" in let H2 := fresh "Fr" in
     destruct (@notin_union_r x E F H) as [H1 H2];
     clear H; notin_simpl_hyps
  end.

Ltac notin_simpls :=
  notin_simpl_hyps; notin_simpl.
*)


Ltac notin_neq_solve :=

  apply notin_singleton_r; notin_solve.


(*
Tactic Notation "counter_incr" := 
  let n := _get in _rem; _put (S n).

Ltac counter_add_nb_to_mark :=
  match goal with 
  | |- (mark_type -> _) => intros _
  | _ => counter_incr; intro; counter_add_nb_to_mark
  end.

Tactic Notation "count_generalized_in" tactic(T) :=
  generalize mark; T;
  lets: mark; _put 0;
  counter_add_nb_to_mark;
  gen_until_mark.

Tactic Notation "inductions" constr(E) tactic(GEN) :=
  induction E; count_generalized_in GEN; 
  induction 
let n := _get in _rem; 
*)



Tactic Notation "inductions" constr(E) 
  "," tactic(INTROS) :=
  inductions E, (idtac), INTROS.

Tactic Notation "inductions" constr(E) 
  "gen_eq" ident(X1) ":" constr(E1) ","
  tactic(INTROS) :=
  inductions E gen_eq X1: E1, (idtac), INTROS.

Tactic Notation "inductions" constr(E) 
  "gen_eq" ident(X1) ":" constr(E1) "," 
           ident(X2) ":" constr(E2) ","
  tactic(INTROS) :=
  inductions E gen_eq X1: E1, X2:E2, (idtac), INTROS.


Axiom typing_subst' : forall U E t T z u,
  (E & z ~ U) |= t ~: T ->
  E |= u ~: U ->
  E |= [z ~> u]t ~: T.

Lemma preservation_result' : preservation.
proof.
  let E, t, _t':trm, T be such that 
     Typ:(E |= t ~: T). 
  suffices Ind:(forall t', t --> t' -> E |= t' ~: T) 
   to show thesis by Ind. (* should clear t' here *)
  per induction on Typ.
  suppose it is (typing_var E0 x T0 Ok Binds).
    let t' be such that R:(trm_fvar x --> t').
    hence thesis using inversion R.
  suppose it is (typing_abs L E0 U1 T1 t1 Bod).
    let t' be such that R:(trm_abs t1 --> t').
    hence thesis using inversion R.
  suppose it is (typing_app S0 T0 E0 t1 t2 Typ1 Typ2) 
   and IH1 : thesis for Typ1 and IH2 : thesis for Typ2.
    define u as (trm_app t1 t2).
    let t' be such that R:(u --> t').
    suffices K:(trm_app t1 t2 = u -> E0 |= t' ~: T0) 
     to show thesis by K,refl_equal.
    per cases on R.
    suppose it is (red_app_1 t10 t1'0 t20 WFt20 Red1).
      assume EQ:(trm_app t1 t2 = trm_app t10 t20).
      (* escape. inversion EQ. subst t10. subst t20. return. wish *)
      suffices K:(E0 |= trm_app t1'0 t2 ~: T0) to show thesis by K,EQ.
      have Red1':(t1 --> t1'0) by EQ,Red1.
      have (E0 |= t1'0 ~: typ_arrow S0 T0) by IH1,Red1'.
      hence thesis by typing_app,Typ2.
    suppose it is (red_app_2 t10 t20 t2'0 ValT1 Red2).
      assume EQ:(trm_app t1 t2 = trm_app t10 t20).
      suffices K:(E0 |= trm_app t1 t2'0 ~: T0) to show thesis by K,EQ.
      have Red2':(t2 --> t2'0) by EQ,Red2.
      have (E0 |= t2'0 ~: S0) by IH2,Red2'.
      hence thesis by typing_app,Typ1.
    suppose it is (red_beta fct arg Wf1 Val2). 
      assume EQ:(trm_app t1 t2 = trm_app (trm_abs fct) arg).
      then Typ1':(E0 |= trm_abs fct ~: typ_arrow S0 T0) by Typ1,EQ.
      then Typ2':(E0 |= arg ~: S0) by Typ2,EQ.
      define v as (trm_abs fct). 
      define V as (typ_arrow S0 T0). 
      define F as E0.
      reconsider Typ1' as (F |= v ~: V).
      suffices K:(F = E0 -> v = trm_abs fct -> V = typ_arrow S0 T0 -> 
        E0 |= fct ^^ arg ~: T0) 
       to show thesis by K,refl_equal.
      per cases on Typ1'.
      suppose it is (typing_abs L E1 U1 T1 fct1 Body).
      assume
        EQ1:(E1 = E0) and
        EQ2:(trm_abs fct1 = trm_abs fct) and
        EQ3:(typ_arrow U1 T1 = typ_arrow S0 T0).
      consider x such that Fr:(x \notin L \u fv t2) 
       from (var_fresh (L \u fv t2)).
      have (x \notin L) by Fr using notin_solve.
      then (E0 & x ~ S0 |= fct ^ x ~: T0) by Body,EQ1,EQ2,EQ3.
      then K:(E0 |= [x ~> arg](fct ^ x) ~: T0) by
        typing_subst',Typ2'. 

(@subst_intro x). .

      suppose it is (typing_var _ _ _ _ _). thus thesis.
      suppose it is (typing_app _ _ _ _ _ _ _). thus thesis.
      end cases.
Qed.


(* temp *)
Axiom concat_empty_l : forall (E:env),
  empty & E = E.
Hint Rewrite concat_empty_l : rew_env


(** The matching function returns a list of terms of the expected length. *)

Lemma pat_match_terms : forall p t ts,
  (pat_match p t is) -> term t -> 
  terms (pat_arity p) ts.
Proof.
  induction p; simpl; introv EQ TT;
   try solve [ inversions EQ; auto ]; 
   destruct t; inversions EQ; inversions TT; autos*.
  remember (pat_match p1 t1) as K1. symmetry in HeqK1.
   remember (pat_match p2 t2) as K2. symmetry in HeqK2. 
   destruct K1 as [ts1|]; destruct K2 as [ts2|]; try discriminate.
   inversions H0. unfolds terms. apply* list_for_n_concat.
Qed.



Lemma pat_match_regular : forall p v i,
  pat_match p v i -> term v.
Proof.
  induction 1; autos*.
Qed.

Lemma pat_match_regular_has : forall p v i,
  pat_match p v i -> 
  forall x t, binds x t i -> term t.
Proof.
  induction 1; introv B.
  binds_single B. subst~.
  inversion B.
  binds_cases B; autos*.
Qed.




(*todo*)

Axiom iter_push_inv_empty : forall (A:Set) xs (vs:list A),
  empty = xs ~* vs -> xs = nil /\ vs = nil.
Axiom iter_push_inv_single : forall (A:Set) x v xs (vs:list A),
  x ~ v = xs ~* vs -> xs = x::nil /\ vs = v::nil.
Axiom iter_push_inv_concat : forall (A:Set) xs (vs:list A) i1 i2,
  i1 & i2 = xs ~* vs -> 
  exist xs1 xs2 vs1 vs2,
  i1 = xs1 ~* vs1 /\ i2 = xs2 ~* vs2 /\
  xs = xs1 ++ xs2 /\ vs = vs1 ++ vs2.
Axiom iter_push_concats : forall (A:Set) xs1 xs2 (vs1 vs2:list A),
 (xs1 ++ xs1) ~* (vs1 ++ vs2) = (xs1 ~* vs1) & (xs2 ~* vs2).





Inductive pattern : pat -> Prop :=
  | pattern_var : forall x,
      pattern (pat_fvar x)
  | pattern_wild : 
      pattern (pat_wild)
  | pattern_pair : forall p1 p2,
      pattern p1 -> 
      pattern p2 -> 
      pattern (pat_pair p1 p2).
      
Inductive typings (E : env) : list trm -> list typ -> Prop :=
  | typings_nil : typings E nil nil 
  | typings_cons : forall ts Us t U,
      typings E ts Us ->
      typing E t U ->
      typings E (t::ts) (U::Us).


Module Env.
End Env.
Export Env.

Tactic Notation "simple" :=
  simpl.
Tactic Notation "simple" "~" :=
  simpl; auto_tilde.
Tactic Notation "simple" "*" :=
  simpl; auto_star.



  (* | forall _, (_ \in ?L -> False) -> _ => go L --inutile*)
  dans inst_notin

  Lemma fresh_empty : forall L n xs,
  fresh L n xs -> fresh {} n xs.
Proof.
  intros. rewrite <- (@union_empty_r L) in H.
  destruct* (fresh_union_r _ _ _ _ H).
Qed.
(** Proposition capturing the idea that a proposition P holds on all 
  values containted in the environment. *)

Definition env_prop (P : A -> Prop) (E : env A) := 
  forall x a, binds x a E -> P a.


(*temp: utile?
Parameter env_ind_union : forall (P : env A -> Prop),
  (P empty) ->
  (forall k v, P (x ~ l)) ->
  (forall E F, P E -> P F -> P (E \u F)) ->
  (forall E, P E).
*)



Lemma empty_single : forall x v,
  empty = x ~ v -> False.
Proof. intros. false. Qed.
Lemma empty_concat : forall E F,
  empty = E & F -> empty = E /\ empty = F.
Proof. intros. induction F. auto. false. Qed.



Hint Extern 1 (ok (?E & ?G)) =>
  match goal with H: context [E & ?F & G] |- _ =>
    apply (@ok_remove _ F) end.

Hint Extern 1 (ok (?E)) =>
  match goal with H: context [E & _ ~ _] |- _ =>
    eapply ok_push end.

Hint Extern 1 (ok (?E)) =>
  match goal with H: context [E & _] |- _ =>
    eapply ok_concat_inv_l end.

Hint Extern 1 (ok (?E)) =>
  match goal with H: context [_ & E] |- _ =>
    eapply ok_concat_inv_r end.



Lemma binds_subst : forall x1 v1 x2 v2 E1 E2,
  ok (E1 & x1 ~ v1 & E2) ->
  binds x1 v1 (E1 & x2 ~ v2 & E2) ->
     (x2 = x1 /\ v1 = v2 /\ x1 # E2)
  \/ (binds x1 v1 (E1 & E2)).
Proof. skip. Qed.


(*
Record Pat : Set := make_Pat {
  pat_pattern :> pat; 
  pat_arity : nat }.
*)



(** Substitution for names 

Fixpoint pat_subst (z : var) (u : pat) (p : pat) {struct p} : pat :=
  match p with
  | pat_fvar x     => if x == z then u else (pat_fvar x)
  | pat_bvar n     => pat_bvar n 
  | pat_wild       => pat_wild
  | pat_pair p1 p2 => pat_pair (pat_subst z u p1) (pat_subst z u p2)
  end.

Fixpoint pat_substs (zs : list var) (us : list pat) (p : pat)
   {struct zs} : pat :=
  match zs, us with
  | z::zs', u::us' => pat_substs zs' us' (pat_subst z u p)
  | _, _ => p
  end.    

Lemma pat_match_anyname : forall p xs ys vsx vsy T,  
   pat_match (open_pat xs p) T (xs ~* vsx) ->
   pat_match (open_pat ys p) T (ys ~* vsy) ->
   vsx = vsy.
Proof.
  induction p; introv P1 P2;
   inversions P1; inversions P2. 
  skip.
  skip.
  skip.
  skip.
Qed.

*)
Ltac unfolds_base :=
  match goal with |- ?G => 
  let E := 

  | |- ?P => unfold P
  | |- ?P _ => unfold P
  | |- ?P _ _ => unfold P
  | |- ?P _ _ _ => unfold P
  | |- ?P _ _ _ _ => unfold P
  | |- ?P _ _ _ _ _ => unfold P
  | |- ?P _ _ _ _ _ _ => unfold P
  | |- ?P _ _ _ _ _ _ _ => unfold P
  | |- ?P _ _ _ _ _ _ _ _ => unfold P
  | _ => intro; unfolds_base
  end. 
Ltac is_metavar_or_name H E :=
  let go := 
     let X := fresh "X" in
     gen_eq_in_base H E X in
  match E with
  | ?P ?X1 => go; gen X1
  | ?P ?X1 ?X2 => go; gen X1 X2
  | ?P ?X1 ?X2 ?X3 => go; gen X1 X2 X3
  | ?P ?X1 ?X2 ?X3 ?X4 => go; gen X1 X2 X3 X4
  | ?P ?X1 ?X2 ?X3 ?X4 ?X5 => go; gen X1 X2 X3 X4 X5
  | ?P ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 => go; gen X1 X2 X3 X4 X6
  | ?P ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 => go; gen X1 X2 X3 X4 X4
  | ?P => constr:(true)
  end.
Ltac gen_eq_in_base H E X :=
  let HX := fresh "H" X in
  set (X := E) in H |-;
  (assert (HX : X = E) by reflexivity; clearbody X);
  generalizes HX.




(** injections on tuples *)

Ltac injection_base H :=
  let go :=
    let H1 := fresh in let H2 := fresh in
    injection H; intros H1 H2; 
    generalize H1; injection_base H2 
    in
  match type of H with
  | (_,_,_) = (_,_,_) => go
  | (_,_,_,_) = (_,_,_,_) => go
  | (_,_,_,_,_) = (_,_,_,_,_) => go
  | (_,_,_,_,_,_) = (_,_,_,_,_,_) => go
  | _ => injection H
  end.


(*
Notation "v '>>>' v1" :=
  (v, >>> v1)
  (v1 at level 0)
  : ltac_scope.
Notation "'>>>' v1 v2" :=
  (v, >>> v1 v2)
  (v1 at level 0, v2 at level 0)
  : ltac_scope.
Notation "'>>>' v1 v2 v3" :=
  (v, >>> v1 v2 v3)
  (v1 at level 0, v2 at level 0, v3 at level 0)
  : ltac_scope.
*)



(* ********************************************************************** *)
(** * Tactique générique pour l'induction avec generalize;
      je ne suis pas sûr que je vais garder ça ... *)

Tactic Notation "inductions" constr(E) "with" tactic(GEN) "," tactic(INTROS) :=
  GEN; induction E; INTROS.
Tactic Notation "inductions" constr(E) "with" "," tactic(INTROS) :=
  induction E; INTROS.

Tactic Notation "intro_subst" :=
  let H := fresh in intros H; 
  match type of H with
  | ?x = ?y => first [ subst x | subst y ] 
  | _ => fail 1 ">- you probably forgot to perform some introductions" 
  end.

Tactic Notation "inductions" constr(E) "with"
  tactic(GEN) "," tactic(INTROS) "end" :=
  GEN; induction E; INTROS.

Tactic Notation "inductions" constr(E) "with"
  "gen_eq" ident(X1) ":" constr(E1) "and" tactic(GEN) "," tactic(INTROS) "end" :=
  gen_eq X1: E1; GEN; induction E; INTROS; try intro_subst.

Tactic Notation "inductions" constr(E) "with"
  "gen_eq" ident(X1) ":" constr(E1) ","
           ident(X2) ":" constr(E2) "and"
  tactic(GEN) "," tactic(INTROS) "end" :=
  gen_eq X2: E2; gen_eq X1: E1; GEN; induction E; INTROS; 
   try (do 2 intro_subst).


Tactic Notation "inductions" constr(E) "with"
  tactic(GEN) "end" :=
  inductions E with (GEN), (idtac).

Tactic Notation "inductions" constr(E) "with"
  "gen_eq" ident(X1) ":" constr(E1) "and"
  tactic(GEN) "end" :=
  inductions E with gen_eq X1: E1 and (GEN), (idtac) end.

Tactic Notation "inductions" constr(E)  "with"
  "gen_eq" ident(X1) ":" constr(E1) ","
           ident(X2) ":" constr(E2) "and"
  tactic(GEN) "end" :=
  inductions E with gen_eq X1: E1, X2:E2 and (GEN), (idtac) end.


Tactic Notation "inductions" constr(E) :=
  inductions E with (idtac), (idtac).

Tactic Notation "inductions" constr(E) "with"
  "gen_eq" ident(X1) ":" constr(E1) :=
  inductions E with gen_eq X1: E1 and (idtac), (idtac) end.

Tactic Notation "inductions" constr(E) "with" 
  "gen_eq" ident(X1) ":" constr(E1) "," 
           ident(X2) ":" constr(E2) :=
  inductions E with gen_eq X1: E1, X2:E2 and (idtac), (idtac) end.

(*  in stlc_core
Lemma demo_inductions : forall G E F t T,
   (E & G) |= t ~: T -> 
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ. dup 3.
  gen_eq H: (E & G). induction Typ; introv EQ; subst; skip.
  inductions Typ with gen_eq H:(E&G); skip.
  inductions Typ with gen_eq H:(E&G) and gen F, introv end; skip.
Qed.
*)



(** Underlying implementation of forward *) 

Ltac forwards_tactic I E :=
  match type of E with
  | ?A -> ?B =>
    let HYPA := fresh in 
    assert (HYPA : A); 
    [| forwards_tactic I (E HYPA); clear HYPA ]
  | forall _:?T,_ => 
    let XVAR := fresh in 
    evar (XVAR : T); 
    let HYPB1 := constr:(E XVAR) in
    let HYPB2 := eval unfold XVAR in HYPB1 in 
    forwards_tactic I HYPB2; subst XVAR
  | _ => lets I: E
  end.

Ltac forwards_depth I E N :=
  match N with
  | 0 => lets I: E
  | S ?N' => 
    match type of E with
    | ?A -> ?B =>
      let HYPA := fresh in 
      assert (HYPA : A); 
      [| forwards_depth I (E HYPA) N'; clear HYPA ]
    | forall _:?T,_ => 
      let XVAR := fresh in 
      evar (XVAR : T); 
      let HYPB1 := constr:(E XVAR) in
      let HYPB2 := eval unfold XVAR in HYPB1 in 
      forwards_depth I HYPB2 N'; subst XVAR
    end
  end.

(** [forwards H: E] applied to an expression [E] of type 
    [forall (x1:P1)...(xN:PN).Q] adds the assumption [H:Q] to the 
    context. The variables [xi] are introduced as uninstanciated
    variables if dependent and as subgoals if non-dependent.
    Note that [H] may be a structured introduction pattern. *)

Tactic Notation "forwards" simple_intropattern(I) ":" constr(E) :=  
  forwards_tactic I E.

(** [forwards: E as I] is another syntax for [forwards I: E] *) 

Tactic Notation "forwards" ":" constr(E) "as" simple_intropattern(I) :=  
  forwards_tactic I E.

(** [forwards: E] is same as [forwards H: E] with
    [H] being chosen automatically. *)

Tactic Notation "forwards" ":" constr(E) :=  
  let H := fresh in forwards H: E.

(** [forwards H: E depth N] is similar to [forwards H E] except
    that it ensures that only the [N] first arguments of the 
    proposition [E] will be instantiated. *)

Tactic Notation "forwards" simple_intropattern(I) ":" constr(E) 
 "depth" constr(N) :=  
  forwards_depth I E N.

(** [forwards: E depth N as H] is another syntax for 
    [forwards H: E depth N]. *) 

Tactic Notation "forwards" ":" constr(E) "depth" constr(N)
 "as" simple_intropattern(I) :=  
  forwards_depth I E N.

(** [forwards: E depth N] is same as [forwards H: E depth N] 
    with [H] being chosen automatically. *)

Tactic Notation "forwards" ":" constr(E) "depth" constr(N) :=  
  let H := fresh in forwards H: E depth N.


(*
Inductive Carriers : Type :=
  | carriers_nil : Carriers
  | carriers_cons : forall A x, Carrier x -> Carriers.
Notation "'~~'" := carriers_nil : ltac_scope.
Notation "v1 '~~'" := (carriers_cons v1 carriers_nil) : ltac_scope.
Notation "v1 ~~ vs" := (carriers_cons v1 vs) : ltac_scope.
*)


(** [puts E] adds an hypothesis whose type is the type of [E]. Another syntax is [puts E]. *)

Ltac puts E := 
  generalize E; intro.

Tactic Notation "put" constr(E) :=
  puts E.



    (* --
Tactic Notation "introv" :=
  let rec go _ := match goal with
  | |- (ltac_tag_subst (?x = ?y) -> ?Q) =>
     let H := fresh "Aux" in 
     intro H; unfold ltac_tag_subst in H;
     try subst x; try go tt
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; try go tt
  end in first [ go tt | intro; go tt ].

 Note: this tactic could also be implemented using as follows: 
      Tactic Notation "introv" := 
        first [ progress (intros until 0) 
              | intro; intros until 0 ].
  *) 

(*
Lemma cps_rename : forall y x t t', 
  cps (t ^ y) (t' ^ y) ->
  y \notin fv t \u fv t' ->
  cps (t ^ x) (t' ^ x). 
Admitted.
*)




Definition f_body f_rec n :=
  match n with
  | 0 => f_rec 2
  | 1 => f_rec 0
  | 2 => 2
  | _ => f_rec (n-1)
  end.

Definition d := 0.
Definition mu n := 1 + max (2-n) (n-2).
Definition f := fixmu d f_body mu.

Ltac math := skip.

Lemma fix_f_ind : forall m n x, 
  (mu x < n) -> (n <= S m) -> 
  fixn d f_body n x = f_body (fixn d f_body m) x.
Proof.
  induction n; introv Lt Le.
  inverts Lt.
  unfold fixn at 1. fold (fixn d f_body).
  sets_eq f1: (fixn d f_body n).
  sets_eq f2: (fixn d f_body m).
  unfold f_body.
  destruct x.
  subst.
skip. skip.
Qed.

Lemma fix_f : forall x, f x = f_body f x.
Proof.
  intros.
 unfold f, fixmu. 
  forwards: (@fix_f_ind (mu x) (mu x)). skip. skip.
  f_equal. apply extensionality. intros. 

Qed.



---
Lemma fixF_ind : forall n x, 
  S (mu x) = n ->
  fixn d f n x = f F x.
Proof.
  induction n using peano_induction; introv Lt.
  destruct n. inverts Lt.
  unfold_fix (fixn d f). sets f': (fixn d f n).
  unfold f. destruct x.
  auto.
  subst f'. rewrite H.
  unfold F at 2. unfold fixmu. rewrite H. auto.
  measure. omega. omega. measure.
Qed.


Lemma fixF : forall x, 
  F x = f F x.
Proof.
  intros. unfold F at 1. unfold fixmu.
  sets_eq n E: (1 + mu x). asserts H: (mu x < n). omega. clear E.
  gen x. induction n using peano_induction; introv Lt.
  destruct n. inverts Lt.
  unfold_fix (fixn d f). sets f': (fixn d f n). 
  asserts IH: (forall y, mu y < mu x -> f' y = F y).
    introv Sm. subst f'. rewrite H; try omega.
    unfold F at 2. unfolds fixmu. rewrite H; try omega.
    clearbody f'. clears n.
  
  unfold f. destruct x.
  auto.
  apply IH. unfold mu. omega.
Qed.


Lemma fixF : forall x, 
  F x = f F x.
Proof.
  intros. unfold F at 1. unfold fixmu.
  sets_eq n E: (1 + mu x). asserts H: (mu x < n). omega. clear E.
  gen x. induction n using peano_induction; introv Lt.
  destruct n. inverts Lt.
  unfold_fix (fixn d f). sets f': (fixn d f n). 
  asserts IH: (forall y, mu y < mu x -> f' y = F y).
    introv Sm. subst f'. rewrite H; try omega.
    unfold F at 2. unfolds fixmu. rewrite H; try omega.
    clearbody f'. clears n.
  
  unfold f. destruct x.
  auto.
  apply IH. unfold mu. omega.
Qed.

(*
Axiom extensionality : forall (A B : Type) (f f' : A -> B),
  (forall x, f x = f' x) -> f = f'.
*)







(*
Lemma cps_fv : forall t,
  term t ->
  fv (cps t) = fv t.
Proof. 
  intros t. gen_eq n:(trm_size t). gen t.
  induction n using peano_induction; introv EQ T; subst n.
  destruct t; simplfix cps; simpl.
  calc_set*.
  calc_set*.
  calc_set*.
  calc_set. 
   lets H1: H of_vars (>>> __ t1 ___); eauto. simpl; omega.
   lets H2: H of_vars (>>> __ t2 ___); eauto. simpl; omega.
   congruence.
  calc_set. sets x: (var_gen (fv t)).
   skip_rewrite (forall t, fv (close_var x t) = (fv t \rem {{x}})).
   applys_in H of_vars (>>> __ (t^x) ___); eauto.
    rewrite~ trm_size_open.
   rewrite H. 
   skip. (* fset fact *)
Qed.
*)
(* ********************************************************************** *)
(** ** Notation for fresh variables *)

(** The notation [x \notin E] is overloaded so that [x] be typed
    with type [var] and not type [Var_as_OT.t]. *)

Notation "x \notin E" := (notin (x:var) E)
 (at level 69, only parsing) : var_scope.
Open Scope var_scope.



(* ********************************************************************** *)
(** TEMP *)

Lemma open_lc : forall t u,
  term t -> t ^^ u = t.
Proof. intros. unfold open. rewrite~ open_rec_term. Qed.
Lemma open_rec_app : forall u t1 t2,
  (trm_app t1 t2) ^^ u = trm_app (t1^^u) (t2^^u).
Proof. auto. Qed.
Lemma open_rec_bvar : forall u,
  (trm_bvar 0) ^^ u = u.
Proof. auto. Qed.
Lemma open_rec_abs : forall u t1,
  body t1 ->
  (trm_abs t1) ^^ u = (trm_abs t1).
Proof. 
 introv B. unfold open. rewrite~ open_rec_term.
Qed.

Hint Rewrite open_rec_app open_rec_bvar open_rec_abs : open2.
Ltac opens := autorewrite with open.
Ltac calc_open2 :=
  autorewrite with open2; rewrite_all open_lc.
Hint Extern 1 (body _) => exists_fresh; calc_open.
Hint Extern 1 (term (trm_abs _)) =>
  apply_fresh term_abs; calc_open.
Hint Extern 1 (term (trm_abs _)) =>
  apply_fresh term_abs; calc_open2.



(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Bin *)

(* move
Hint Rewrite
 union_empty_r
 union_empty_l
 union_assoc
 union_same : set.
Tactic Notation "calc_set" :=
  autorewrite with set.
Tactic Notation "calc_set" "*" := 
  calc_set; autos*.
 *)

(* useful ??
Lemma rename_open : forall y x t,
  y \notin fv t ->
  t ^ x = [[y ~> x]](t ^ y).
Proof.
  intros. rewrite~ (@subst_intro y).
Qed.
*)

(*
Definition rename_open' y t x := @subst_intro y t (trm_fvar x). 
Check rename_open'.
*)




(*
Fixpoint term_hole (k:nat) (t:trm) {struct t} : Prop :=
  match t with 
  | trm_bvar i    => i = k
  | trm_fvar x    => True
  | trm_app t1 t2 => term'_rec k t1 /\ term'_rec k t2
  | trm_abs t1    => term'_rec (S k) t1
  end.

Fact f1: forall t,
  term'_rec 1 t -> term_hole 
*)
(*
Inductive term_rec : nat -> nat -> trm -> Prop :=
  | term_rec_bvar : forall i j k,
      i <= k < j ->
      term_rec i j (trm_bvar k)
  | term_rec_fvar : forall i j x, 
      term_rec i j (trm_fvar x)
  | term_rec_app : forall i j t1 t2,
      term_rec i j t1 -> 
      term_rec i j t2 -> 
      term_rec i j (trm_app t1 t2)
  | term_rec_abs : forall i j t1,
      term_rec i j t1 -> 
      term_rec i j (trm_abs t1). 
*)


(*
Require Import List.
Definition var_default := var_gen {}.
Fixpoint lazy_open (k:nat) (xs:list var) (t:trm) {struct t} : trm :=
  match t with 
  | trm_bvar i    => if le_lt_dec k i then t else 
                        trm_fvar (nth k xs var_default)
  | trm_fvar x    => t
  | trm_app t1 t2 => trm_app (lazy_open k xs t1) (lazy_open k xs t2)
  | trm_abs t1    => trm_abs (lazy_open (S k) xs t1)
  end.

Fact open_var_lazy_open : forall x xs t k i j,
  k < i -> j = S i ->
  (open_var_rec k x (lazy_open i xs t)) 
  = lazy_open j (x::xs) t.
Proof.
  induction t; introv Lt Eq. simpl.
  destruct (le_lt_dec i n); destruct (le_lt_dec j n); simpl.
    case_nat~. false. omega.
    case_nat~. fequals. destruct~ j. false. omega.
    false. omega.

Qed.

Fact test : forall t xs k,
  term'_rec k t -> term (lazy_open k xs t).
Proof.
  induction t; simpl; introv H; autos*.
  destruct~ (le_lt_dec k n). false. omega.
  apply_fresh term_abs. apply IHt. 
Qed.

Fact term'_rec_1_to_hole_rec : forall t,
  term'_rec 1 t -> hole_rec 0 t.
Proof.
  introv. generalize 0. induction t; simpl; introv H; autos*.
  omega.
Qed.
*)

(*
Fact test : forall x t n,
  term'_rec (S n) t -> term (open_var_rec n x t).
Proof.
  induction t; simpl; introv H.
  case_nat~.
Qed.
*)


Lemma fixeq' : forall mu f F,
  F = fixmu f mu ->
  (forall x f',   
    (forall y, mu y < mu x -> f' y = F y) ->
    f f' x = f F x) ->
  (forall x, F x = f F x).
Proof.
  unfold fixmu. introv EqF IH. introv. 
  pattern F at 1. rewrite EqF.
  sets_eq n E: (1 + mu x). asserts H: (mu x < n). omega. clear E.
  gen x. induction n using peano_induction; introv Lt.
  destruct n. inverts Lt.
  unfold_fix (fixn f). apply IH. introv Sm.
  rewrite EqF. do 2 (rewrite H; try omega). auto.
Qed.


Lemma fixeq_pre_post : forall (P:A->Prop)(Q:A->B->Prop) mu f F,
  F = fixmu f mu ->
  (forall x F',
    P x ->  
    (forall y, P y -> mu y < mu x -> 
       F y = F' y /\ Q y (F y)) ->
    f F' x = f F x /\ Q x (f F x)) ->
  (forall x, P x -> F x = f F x /\ Q x (F x)).
Proof.
  unfold fixmu. introv EqF IH. introv Px. 
  pattern F at 1. rewrite EqF.
  sets n: (1 + (mu x)). asserts~ H: (mu x < n). clearbody n.
  gen n. induction x using (@measure_induction _ mu).
  introv Lt. destruct n. inverts Lt.
  simpl. apply~ IH. introv Py Sm.
  lets K1 K2: H of_vars (>>> y n ___); auto; try omega.
  lets K3 _: H of_vars (>>> y (1+(mu y)) ___); auto; try omega.
  split~. rewrite EqF. rewrite~ K1. 
Qed.
let M := fresh "M" in
  lets M: (@typing_substitution U empty).
  specializes_vars M.
  clean_empty M.
   first [ apply M | eapply M | apply M ]; 
  clear M.


(*

Axiom tester : forall (A:Type),
  EnvList.env A -> True.

match goal with |- context [?R] => 
  let t := constr:(tester R) in
  pose R end.
rewrite <- (@concat_empty_r _ E).
*)
lets M: (@typing_substitution U empty).
specializes M __ __ __ __ __.
rewrite concat_empty_r in M.
rewrite map_empty in M.
rewrite concat_empty_r in M.
apply M; try rewrite concat_empty_r; autos*.
(*   apply_empty* (@typing_substitution U). todo *)