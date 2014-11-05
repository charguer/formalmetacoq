


(** Note: proof irrelevance also entails "the uniqueness of identity
    proofs" as well as "Streicher's axiom K", which are two immediate
    consequences of proof irrelevance. *)  


Axiom func_choice : forall A B (R:A->B->Prop),
  (forall x, exists y, R x y) ->
  (exists f, forall x, R x (f x)).

Definition A := sig (fun P:bool->Prop => ex P).
Definition newA P H :=
  @exist _ (fun P:bool->Prop => ex P) P H.

(*
Inductive R : A -> bool -> Prop :=
  | R_intro : forall (P:bool->Prop) b (H:P b),
   let H':= ex_intro P b H in
      R (newA H') b.
*)

Lemma eq_to_eq_sig :
  forall (A : Type) (P : A->Prop) (x y : A) (p : P x) (q : P y),
    x = y -> exist P x p = exist P y q.
Proof. intros. destruct H. f_equal. apply proof_irrelevance. Qed.

Instance bool_Inhab : Inhab bool.
Proof. apply (prove_Inhab true). Qed.


Inductive R : A -> bool -> Prop :=
  | R_intro : forall (P:bool->Prop) (H:ex P) b,  
     P b -> R (newA H) b.

Lemma ertest : forall P:Prop, P \/ ~ P.
  assert (H: (forall x : A, exists y : bool, R x y)).
  intros [P [b M]]. exists b. constructor. auto.
  generalize (@func_choice A bool R H). intros [f F].
  assert (Z : (forall P:bool -> Prop, forall (H: ex P), P (f (newA H)))).
    intros P IP. generalize (F (newA IP)). intros M. inversion M. subst. auto.
  intros P.
  set (B1 := fun b => P \/ b = true).
  set (B2 := fun b => P \/ b = false).
  assert (H1 : ex B1). exists true. right. auto.
  assert (H2 : ex B2). exists false. right. auto.
  destruct (Z B1 H1) as [|E1]. auto.
  destruct (Z B2 H2) as [|E2]. auto.
  right. intros HP.
  cut (f (newA H1) = f (newA H2)). intros EQ. congruence.
  clear E1 E2.
  assert (EB : B1 = B2).
    apply pred_ext. intros b. split; intros _; left; auto.
  clear HP. f_equal. unfold newA. 
  destruct EB. f_equal. apply proof_irrelevance.
Qed.

Notation Local eps := (@epsilon bool _) (only parsing).

Lemma classic_derivable' : forall P:Prop, P \/ ~ P.
Proof.
  intro P.
  pose (B := fun y => y=false \/ P).
  pose (C := fun y => y=true  \/ P).
  assert (B (eps B)) as [Hfalse|HP].
    apply epsilon_spec_exists. exists false. left. reflexivity.
    assert (C (eps C)) as [Htrue|HP].
      apply epsilon_spec_exists. exists true. left. reflexivity.
      right; intro HP.
       assert (forall y, B y <-> C y).
         intro y. split; intro; right; assumption.
       rewrite epsilon_eq with (1:=H) in Hfalse.
       congruence.
    auto.
  auto.
Qed.

Axiom proof_irrelevance : forall (P : Prop) (u v : P), u = v. 

Lemma test : forall A (P1 P2 : A->Prop) (s1 : sig P1) (s2 : sig P2) (E : P1 = P2),
  s2 = @eq_rect _ _ (fun P => sig P) s1 _ E ->
  @proj1_sig _ P1 s1 = @proj1_sig _ P2 s2.
Proof.
  intros. rewrite H. clear H. destruct s1. destruct s2. subst P1. auto.
Qed.

Lemma f_eq_all : 
  forall (f : forall (A : Type) (P : A -> Prop), ex P -> sig P),
  forall (A : Type) (P1 P2 : A->Prop), 
  forall (E: P1 = P2) (H1 : ex P1) (H2 : ex P2),
  (f A P2 H2) =
    (@eq_rect _ _ (fun P => sig P) (f A P1 H1) _ E).
Proof. 
  intros.
  generalize (@proof_irrelevance (ex P2) H2 (@eq_rect _ _ (fun P => ex P) H1 _ E)).
   intros M. rewrite M. clear M. subst P1. auto.
Qed.

Lemma f_eq_all' : 
  forall (f : forall (A : Type) (P : A -> Prop), (ex P) -> sig P),
  forall (A : Type) (P1 P2 : A->Prop), 
  forall (E: P1 = P2) (H1 : ex P1) (H2 : ex P2),
  (f A P2 H2) =
    (@eq_rect _ _ (fun P => sig P) (f A P1 H1) _ E).
Proof. 
  intros.
  generalize (@proof_irrelevance (ex P2) H2 (@eq_rect _ _ (fun P => ex P) H1 _ E)).
   intros M. rewrite M. clear M. subst P1. auto.
Qed.

Lemma indefinite_description_eq_proofs : forall (A : Type) (P : A->Prop), 
  forall (H1 H2 : ex P),
  indefinite_description P H1 = indefinite_description P H2.
Proof.
  intros. generalize (proof_irrelevance H1 H2). intros E.
  rewrite E. auto.
Qed.

Lemma indefinite_description_eq_pred : forall (A : Type) (P1 P2 : A->Prop), 
  forall (E: P1 = P2),
  (indefinite_description P2) =
    @eq_rect _ _ (fun P:A->Prop => ex P -> sig P) (indefinite_description P1)  _ E.
Proof. intros. rewrite E. auto. Qed.


Lemma indefinite_description_eq_pred' : forall (A : Type) (P1 P2 : A->Prop), 
  forall (E: P1 = P2) (H1: ex P2),
  (indefinite_description P2 H1) =
    (@eq_rect _ _ (fun P:A->Prop => ex P -> sig P) (indefinite_description P1)  _ E) H1.
Proof. intros. rewrite E. auto. Qed.

Axiom eq_rect_eq : 
  forall (A : Type) (p : A) (Q : A -> Type) (x : Q p) (h : p = p),
  eq_rect p Q x p h = x.



Lemma indefinite_description_eq_pred_proofs' : forall (A : Type) (P1 P2 : A->Prop), 
  forall (E: P1 = P2) (H1 : ex P2) (H2 : ex P2),
  (indefinite_description P2 H2) =
    (@eq_rect _ _ (fun P:A->Prop => ex P -> sig P) (indefinite_description P1) _ E)
     (@eq_rect _ _ (fun _ => ex P2) H1 _ (proof_irrelevance H1 H2)).
Proof. intros. rewrite E. rewrite eq_rect_eq. f_equal. apply proof_irrelevance. Qed.

Lemma indefinite_description_eq_all' : forall (A : Type) (P1 P2 : A->Prop), 
  forall (E: P1 = P2) (H1 : ex P1) (H2 : ex P2),
   let H1' := @eq_rect _ _  (fun P:A->Prop => ex P) H1 _ E in
  (indefinite_description P2 H2) =
    (@eq_rect _ _ (fun P:A->Prop => ex P -> sig P) (indefinite_description P1) _ E)
     (@eq_rect _ _ (fun _ => ex P2) H1' _ (proof_irrelevance H1' H2)).
Proof. intros. rewrite E. rewrite eq_rect_eq. f_equal. apply proof_irrelevance. Qed.


Require Import ProofIrrelevance.

(** [pi_rewrite E] replaces [E] of type [Prop] with a fresh 
    unification variable, and is thus a practical way to
    exploit proof irrelevance, without writing explicitly
    [rewrite (proof_irrelevance E E')]. Particularly useful
    when [E'] is a big expression. *)

Ltac pi_rewrite_base E rewrite_tac :=
  let E' := fresh in let T := type of E in evar (E':T);
  rewrite_tac (@proof_irrelevance _ E E'); subst E'.

Tactic Notation "pi_rewrite" constr(E) :=
  pi_rewrite_base E ltac:(fun X => rewrite X).
Tactic Notation "pi_rewrite" constr(E) "in" hyp(H) :=
  pi_rewrite_base E ltac:(fun X => rewrite X in H).

Axiom t : forall (P:Prop), P.


(*intros. pi_rewrite H1.
 rewrite E. 
 pose (@eq_rect_eq).

 pi_rewrite E.
Check eq_rect_eq.
rewrite <- eq_rect_eq.
  f_equal. apply proof_irrelevance. Qed.


   let H1' := @eq_rect _ _  (fun P:A->Prop => exists x, P x) H1 _ E in
*)

(** Contrary to the value [x] in [ exists x, P x ], the value [x] inside 
    the dependent pair [ { x : A | P x } ] can be subject to case analysis 
    from within any definition. In technical words, indefinite description
    is reifying existence proofs to the computational level.
*)


(** Assuming that we have predicate extensionality, the indefinite 
    description axiom entails the excluded middle.

*)
(* 

Require Import JMeq.
Axiom JMeq_eq : forall (A : Type) (x y : A), 
  JMeq x y -> x = y.
*)

Require Import Eqdep.



Ltac def_to_eq X HX E :=
  assert (HX : X = E) by reflexivity; clearbody X.
Ltac def_to_eq_sym X HX E :=
  assert (HX : E = X) by reflexivity; clearbody X.

(** [set_eq X H: E] generates the equality [H: X = E],
    for a fresh name [X], and replaces [E] by [X] in the
    current goal. Syntaxes [set_eq X: E] and
    [set_eq: E] are also available. Similarly,
    [set_eq <- X H: E] generates the equality [H: E = X]. 

    [sets_eq X HX: E] does the same but replaces [E] by [X]
    everywhere in the goal. [sets_eq X HX: E in H] replaces in [H].
    [set_eq X HX: E in |-] performs no substitution at all. *)

Tactic Notation "set_eq" ident(X) ident(HX) ":" constr(E) :=
  set (X := E); def_to_eq X HX E.
Tactic Notation "set_eq" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in set_eq X HX: E.
Tactic Notation "set_eq" ":" constr(E) :=
  let X := fresh "X" in set_eq X: E.

Tactic Notation "set_eq" "<-" ident(X) ident(HX) ":" constr(E) :=
  set (X := E); def_to_eq_sym X HX E.
Tactic Notation "set_eq" "<-" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in set_eq <- X HX: E.
Tactic Notation "set_eq" "<-" ":" constr(E) :=
  let X := fresh "X" in set_eq <- X: E.

Tactic Notation "sets_eq" ident(X) ident(HX) ":" constr(E) :=
  set (X := E) in *; def_to_eq X HX E.
Tactic Notation "sets_eq" ident(X) ":" constr(E) :=
  let HX := fresh "EQ" X in sets_eq X HX: E.
Tactic Notation "sets_eq" ":" constr(E) :=
  let X := fresh "X" in sets_eq X: E.

Implicit Arguments proj1_sig [].
Implicit Arguments eq_rect [].
Implicit Arguments sig [A].

Print sigT.










Lemma rew_logic_demo_3 : forall (P : nat -> Prop), 
  ~ (forall n, n <> 0 -> exists m, m <> n /\ ~ P m) ->
    (exists n, n <> 0 /\ forall m, m = n \/ P m).
Proof.
  intros P H. up M. down H. intros n N.
  rewrite not_exists in M. specialize (M n).
  rew_logic. destruct M. congruence.
  rewrite not_forall in H.  destruct H as [x H].
  rew_logic.



Lemma not_exists : forall A (P:A->Prop),
  (~ (exists x, P x)) = (forall x, ~ P x).
Proof.
  intros. rewrite <- not_not. rewrite not_forall.
  f_equal. apply prop_ext. split; intros [x H].
  exists x. rewrite not_not.
 

Section Distribute.
Variables P Q : Prop.
Local Ltac bruteforce :=
  try apply prop_ext;
  destruct (classic P);
  destruct (classic Q);
  try solve [ intuition (first [ auto | elimtype False; auto ]) ].


==================
ok

Definition dyn_val := { A : Type & A }.

Definition new_dyn_val (T:Type) (v:T) : dyn_val :=
  existT Type (fun A => A) T v.

Definition dyn_pred := { A : Type & (A -> Prop) }.

Definition new_dyn_pred (T:Type) (P:T->Prop) : dyn_pred :=
  existT Type (fun A => A->Prop) T P.

Inductive dyn_satisfy : dyn_val -> dyn_pred -> Prop :=
  | dyn_satisfy_intro : forall A (P:A->Prop) (v:A),
      P v -> dyn_satisfy (new_dyn_val v) (new_dyn_pred P).

Lemma test : forall (dv:dyn_val),
  dyn_satisfy dv (new_dyn_pred (fun n:nat => n > 0)) -> 
  exists m, dv = new_dyn_val m /\ m > 0.
Proof.
  intros. inversion H as [A P v Pv EQv EQA]. clear H.
  unfold new_dyn_val in EQv.
  generalize (inj_pairT2 H0). clear H0.
  intros. subst. exists v0. auto.
Qed.

==================




Definition dyn_val := { A : Type & A }.

Definition new_dyn_val (T:Type) (v:T) : dyn_val :=
  existT Type (fun A => A) T v.

Inductive dyn_satisfy : forall A, (A->Prop) -> dyn_val -> Prop :=
  | dyn_satisfy_intro : forall A (P:A->Prop) (v:A),
      P v -> dyn_satisfy P (new_dyn_val v).

Lemma test : forall (dv:dyn_val),
  dyn_satisfy (fun n:nat => n > 0) dv -> 
  exists m, dv = new_dyn_val m /\ m > 0.
Proof.
  intros. destruct H.   exists m, dv = new_dyn_val m /\ m > 0. inversion H.


