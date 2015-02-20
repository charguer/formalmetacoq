Set Implicit Arguments.
Require Import LibCore LibNat LibClosure.


Lemma list_last_inv : forall (A:Type) (l:list A), 
  l = nil \/ exist a l', l = l' & a.
Proof.
  intros. sets_eq l': l. gen l'.
  induction l; intros.
  left. auto.
  right. destruct~ (IHl l) as [|[r [h E]]]; subst.
    exists~ a (@nil A).
    exists r (a::h). calc_app~.
Qed.


Lemma nth_last : forall (A:obj) (x:A) l k,
  k < length l ->
  nth k (l & x) = nth k l.
Proof.
  induction l; introv Lt.
  inversions Lt.
  calc_length in Lt. calc_app. destruct k; simpl.
    auto.
    rewrite~ IHl.
Qed.

Lemma nth_last_one : forall (A:obj) (x:A) l,
  nth (length l) (l & x) = x.
Proof. induction l; auto. Qed.

Lemma nth_last_one_eq : forall (A:obj) (x:A) n l,
  n = (length l) ->
  nth n (l & x) = x.
Proof. intros. subst. apply nth_last_one. Qed.

Lemma list_ind_rev
     : forall (A : Type) (P : list A -> Prop),
       P nil ->
       (forall (a : A) (l : list A), P l -> P (l & a)) ->
       forall l : list A, P l.
Proof.
  introv Hnil Hcons. intros l.
  induction_wf: (measure_wf (@length A)) l.
  destruct (list_last_inv l) as [Eq|[a [l' Eq]]]; subst.
  auto. apply Hcons. apply IH. calc_length. skip. (* math *)
Qed.


(*==================================================================*)
(** Definitions *)

(********************************************************************)
(** Syntax of lambda-terms (with de Bruijn indices) *)

Inductive term : Set :=
  | var : nat -> term
  | app : term -> term -> term
  | lam : term -> term.

Fixpoint apps (t:term) (us:list term) {struct us} : term :=
  match us with
  | nil => t
  | u::us' => apps (app t u) us'
  end.

Fixpoint lams (n:nat) (t:term) {struct n} : term :=
  match n with
  | 0 => t
  | S n' => lam (lams n' t)
  end.

Fixpoint shifts (n:nat) (t:term) {struct t} : term :=
  match t with
  | var i => if i < n then t 
             else var (i+1)
  | app t1 t2 => app (shifts n t1) (shifts n t2)
  | lam t1 => lam (shifts (n+1) t1)
  end.

Definition shift := shifts 0.

Fixpoint substs (n:nat) (u:term) (t:term) {struct t} :=
  match t with
  | var i => if i == n then u 
             else if i < n then t 
             else var (i-1)
  | app t1 t2 => app (substs n u t1) (substs n u t2)
  | lam t1 => lam (substs (n+1) (shift u) t1)
  end.

Definition subst := substs 0.

Fixpoint degree (n:nat) (t:term) {struct t} : Prop :=
  match t with
  | var i => i < n
  | app t1 t2 => degree n t1 /\ degree n t2
  | lam t1 => degree (n+1) t1
  end.

Definition closed := degree 0.


(********************************************************************)
(** Beta-reduction and eta-equivalence on lambda-terms *)

Inductive beta : term -> term -> Prop :=
  | beta_step : forall t1 t2,
      beta (app (lam t1) t2) (subst t2 t1)
  | beta_app1 : forall t11 t12 t2,
      beta t11 t12 ->
      beta (app t11 t2) (app t12 t2)
  | beta_app2 : forall t1 t21 t22,
      beta t21 t22 ->
      beta (app t1 t21) (app t1 t22)
  | beta_lam : forall t11 t12,
      beta t11 t12 ->
      beta (lam t11) (lam t12).

Notation "t1 --> t2" := (beta t1 t2)
  (at level 69).

Definition beta_star := star beta.

Notation "t1 -->* t2" := (beta_star t1 t2)
  (at level 69).

Definition normal t :=
  forall t', ~ (t --> t').

Definition eta_of t :=
  lam (app (shift t) (var 0)).

Inductive eta_equiv : term -> term -> Prop :=
  | eta_equiv_eta : forall t,
      eta_equiv t (eta_of t)
  | eta_equiv_refl : forall t,
      eta_equiv t t
  | eta_equiv_sym : forall t1 t2,
      eta_equiv t1 t2 ->
      eta_equiv t2 t1
  | eta_equiv_trans : forall t2 t1 t3,
      eta_equiv t1 t2 ->
      eta_equiv t2 t3 ->
      eta_equiv t1 t3 
  | eta_equiv_app1 : forall t11 t12 t2,
      eta_equiv t11 t12 ->
      eta_equiv (app t11 t2) (app t12 t2)
  | eta_equiv_app2 : forall t1 t21 t22,
      eta_equiv t21 t22 ->
      eta_equiv (app t1 t21) (app t1 t22)
  | eta_equiv_lam : forall t11 t12,
      eta_equiv t11 t12 ->
      eta_equiv (lam t11) (lam t12).


(********************************************************************)
(** Statement of Böhm's theorem on separability *)

Definition cst_false := lam (lam (var 0)).
Definition cst_true  := lam (lam (var 1)).

Definition separable t1 t2 := 
  exists us, apps t1 us -->* cst_true
          /\ apps t2 us -->* cst_false.

Definition bohm_theorem := forall t1 t2,
  closed t1 -> normal t1 ->
  closed t2 -> normal t2 ->
  eta_equiv t1 t2 \/ separable t1 t2.


(*==================================================================*)
(** Auxiliary definitions *)

(********************************************************************)
(** Canonical equality and inhabitant for terms *)

Section TermObj.

Fixpoint beq (x y : term) {struct x} : bool := 
   match x,y with
   | var i, var j => i == j
   | app x1 x2, app y1 y2 => beq x1 y1 && beq x2 y2
   | lam x1, lam y1 => beq x1 y1
   | _,_ => false
   end.

Lemma req : R_eq beq. 
Proof.
  constructor; gen y; induction x; destruct y; simpl; 
   intros; tryfalse.
  rewriteb* H.
  destructb H. rewrite~ (IHx1 y1). rewrite~ (IHx2 y2).
  rewrite~ (IHx y).
  inversions~ H.
  inversions~ H.
  inversions~ H.
Qed.

Canonical Structure Term := make_obj (var 0) req.

End TermObj.


(********************************************************************)
(** Alternative definition for normal forms and eta-expansion *)

Definition not_a_lam t :=
  match t with
  | lam _ => False
  | _ => True
  end.

Inductive noredex : term -> Prop :=
  | noredex_var : forall i, 
      noredex (var i)
  | noredex_lam : forall t1,
      noredex t1 ->
      noredex (lam t1)
  | noredex_app : forall t1 t2,
      noredex t1 ->
      noredex t2 ->
      not_a_lam t1 ->
      noredex (app t1 t2).

Inductive eta_exp : term -> term -> Prop :=
  | eta_exp_eta : forall t1 t2,
      eta_exp t1 t2 ->
      eta_exp t1 (eta_of t2)
  | eta_exp_refl : forall t,
      eta_exp t t
  | eta_exp_app : forall t11 t12 t21 t22,
      eta_exp t11 t12 ->
      eta_exp t21 t22 ->
      eta_exp (app t11 t21) (app t12 t22)
  | eta_exp_lam : forall t11 t12,
      eta_exp t11 t12 ->
      eta_exp (lam t11) (lam t12).


(********************************************************************)
(** Useful lambda-terms *)

Definition cst_erase n t := lams n t.
Definition cst_select n k := lams n (var k).
Definition cst_id := lam (var 0).

Fixpoint var_decr_from n :=
  match n with
  | 0 => nil
  | S n' => (var n)::(var_decr_from n')
  end.
Definition cst_tuple n := lams (n+1) (apps (var 0) (var_decr_from n)).


(********************************************************************)
(** Paths in head-normal-form terms and disimilarity *)

Definition hnf n us i := lams n (apps (var i) us).

Inductive path : Set :=
  | path_nil (n p1 p2 i1 i2 : nat)
  | path_cons (n p i k : nat) (P' : path).

Fixpoint path_length (P:path) {struct P} : nat :=
  match P with
  | path_nil n p1 p2 i1 i2 => 0
  | path_cons n p i k P' => 1 + path_length P'
  end.

Fixpoint no_binding_to (j:nat) (P:path) {struct P} : Prop :=
  match P with
  | path_nil n p1 p2 i1 i2 => i1 != j /\ i2 != j
  | path_cons n p i k P' => (i != j+n) /\ no_binding_to (j+n) P'
  end.

Fixpoint no_arity_above (m:nat) (P:path) {struct P} : Prop :=
  match P with
  | path_nil n p1 p2 i1 i2 => p1 <= m /\ p2 <= m
  | path_cons n p i k P' => p <= m /\ no_arity_above m P'
  end.

Inductive disimilar : path -> term -> term -> Prop :=
  | disimilar_nil : forall n p1 p2 a1 a2 i1 i2,
      p1 = length a1 -> p2 = length a2 -> ((p1 != p2) || (i1 != i2)) ->
      disimilar (path_nil n p1 p2 i1 i2) (hnf n a1 i1) (hnf n a2 i2)
  | disimilar_cons : forall n p i k P' a1 a2,
      p = length a1 -> p = length a2 -> k < p ->
      disimilar P' (nth k a1) (nth k a2) ->
      disimilar (path_cons n p i k P') (hnf n a1 i) (hnf n a2 i).

Definition eta_confluent t1 t2 :=
  exist t, eta_exp t1 t
        /\ eta_exp t2 t.

Definition eta_disimilar t1 t2 :=
  exist t1' t2' P, eta_exp t1 t1'
                /\ eta_exp t2 t2'
                /\ disimilar P t1' t2'.


(*==================================================================*)
(** Auxiliary lemmas *)

Hint Constructors noredex beta eta_exp.
Hint Resolve eta_equiv_eta eta_equiv_refl 
  eta_equiv_app1 eta_equiv_app2 eta_equiv_lam.


(********************************************************************)
(** Structure of terms *)

Lemma apps_last : forall u us t,
  apps t (us & u) = app (apps t us) u.
Proof.
  induction us; intros. auto.
  calc_app. simpl. rewrite~ IHus. 
Qed.

Lemma get_hnf_form : forall t, noredex t ->
  exist n a i, t = hnf n a i 
            /\ noredex (apps (var i) a).
Proof.
  induction t; introv N; inversions N.
  exists 0 (@nil term) n. simple~.
  skip.
  lets n a i H E: (IHt H0).
  exists (S n) a i. split~. unfold hnf. simpl. fequals~.
Qed. 


(********************************************************************)
(** Normal forms *)

Lemma normal_app_inv : forall t1 t2,
  normal (app t1 t2) -> normal t1 /\ normal t2.
Proof. introv H. split; intros t R; apply* H. Qed.

Lemma normal_lam_inv : forall t1,
  normal (lam t1) -> normal t1.
Proof. introv H. intros t R; apply* H. Qed.

Lemma normal_to_noredex : forall t,
  normal t -> noredex t.
Proof.
  induction t; intros N.
  auto.
  asserts C: (not_a_lam t1 \/ exists t11, t1 = lam t11).
    destruct t1; simpl; eauto.
   destruct C as [NL | [t11 Eq]].
    lets ? ?: (normal_app_inv N); auto.
    subst. false. apply* N.
  lets~: (normal_lam_inv N).
Qed.


(********************************************************************)
(** Eta-expansion *)

Lemma eta_exp_to_eta_equiv : forall t1 t2,
  eta_exp t1 t2 -> eta_equiv t1 t2.
Proof.
  induction 1; auto.
  apply* (@eta_equiv_trans t2) .
  apply* (@eta_equiv_trans (app t12 t21)).
Qed.

Lemma eta_exp_apps : forall us t1 t2,
  eta_exp t1 t2 ->
  eta_exp (apps t1 us) (apps t2 us).
Proof.
  induction us using list_ind_rev; introv E; simple.
  auto.
  rewrite_all apps_last. 
   apply eta_exp_app. auto. apply eta_exp_refl.
Qed.

Lemma eta_exp_lams : forall n t1 t2,
  eta_exp t1 t2 ->
  eta_exp (lams n t1) (lams n t2).
Proof. induction n; introv E; simple~. Qed.


(********************************************************************)
(** Beta and beta-star *)

Lemma beta_apps : forall us t1 t2,
  t1 --> t2 ->
  apps t1 us --> apps t2 us.
Proof. induction us; introv R; simple~. Qed.

Section Star.
Hint Resolve star_refl star_once star_step.

Lemma beta_star_lam : forall t1 t2,
  star beta t1 t2 ->
  star beta (lam t1) (lam t2).
Proof. induction 1; autos*. Qed.

Lemma beta_star_app1 : forall t11 t12 t2,
  star beta t11 t12 ->
  star beta (app t11 t2) (app t12 t2).
Proof. induction 1; autos*. Qed.

Lemma beta_star_app2 : forall t1 t21 t22,
  star beta t21 t22 ->
  star beta (app t1 t21) (app t1 t22).
Proof. induction 1; autos*. Qed.

Lemma beta_star_apps : forall t1 t2 us,
  t1 -->* t2 ->
  apps t1 us -->* apps t2 us.
Proof.
  introv R. gen us. unfolds beta_star. 
  inductions R; introv. lets: star_refl.
  induction us; simple~.
    apply~ (@star_step _ beta (apps y us)).
     apply~ beta_apps. 
Qed.

End Star.


(********************************************************************)
(** Separability *)

Lemma separable_app : forall u t1' t2' t1 t2,
  app t1 u -->* t1' ->
  app t2 u -->* t2' ->
  separable t1' t2' ->
  separable t1 t2.
Proof.
  introv R1 R2 [us [S1 S2]].
  exists (u::us). simpl. split.
  apply~ (@star_trans _ beta (apps t1' us)). 
   apply~ beta_star_apps.
  apply~ (@star_trans _ beta (apps t2' us)). 
   apply~ beta_star_apps.
Qed.


(********************************************************************)
(** Eta-confluence *)

Lemma eta_confluent_app : forall t1 t2 u1 u2,
  eta_confluent t1 t2 ->
  eta_confluent u1 u2 ->
  eta_confluent (app t1 u1) (app t2 u2).
Proof.
  introv [t [E1 E2]] [u [F1 F2]]. exists~ (app t u). 
Qed.

Lemma eta_confluent_lams : forall n t1 t2,
  eta_confluent t1 t2 ->
  eta_confluent (lams n t1) (lams n t2).
Proof.
  induction n; introv R; simpl. auto.
  destruct (IHn _ _ R) as [t [E1 E2]]. exists~ (lam t).
Qed.



(*==================================================================*)
(** Main lemmas *)

(********************************************************************)
(** Eta-equivalent or disimilar *)

Axiom eta_exp_or_disimilar_ih : forall t1 t2,
  noredex t1 -> noredex t2 -> 
  eta_confluent t1 t2 \/ eta_disimilar t1 t2.

Axiom nat_symmetric_diff : forall n1 n2,
  exist n r1 r2, n1+r1 = n /\ n2+r2 = n.

Fixpoint iter (A:Type) (f:A->A) (n:nat) (x:A) {struct n} : A :=
  match n with 
  | 0 => x
  | S n' => iter f n' (f x)
  end.

Definition shiftn := iter shift.

Definition etas_list r a :=
  (map (shiftn r) a) ++ (var_decr_from r).

Definition hnf_etas r n a i :=
  hnf (n+r) (etas_list r a) (i+r).

Axiom etas_list_length : forall r a,
  length (etas_list r a) = r + length a.

Axiom eta_exp_hnf_etas : forall r n a i,
  eta_exp (hnf n a i) (hnf_etas r n a i).

Axiom eta_exp_hnf : forall n a a' i r,
  Forall2 eta_exp (etas_list r a) a' ->
  eta_exp (hnf n a i) (hnf_etas r n a i).

Section List.
Variables (A B : Type) (P : A -> B -> Prop) .
Axiom Forall2_last : forall l1 l2 x1 x2, 
      Forall2 P l1 l2 -> P x1 x2 ->
      Forall2 P (l1 & x1) (l2 & x2).
End List.

Lemma eta_exp_or_disimilar_arguments : 
  forall a1 a2 i t1 t2,
  t1 = apps (var i) a1 ->
  t2 = apps (var i) a2 ->
  noredex t1 ->
  noredex t2 ->
  length a1 = length a2 ->
     (Forall2 eta_confluent a1 a2)
  \/ (exist k, k < length a1 
            /\ eta_disimilar (nth k a1) (nth k a2)).
Proof.
  skip_goal. introv T1 T2 N1 N2 Len.
  destruct (list_last_inv a1) as [ | [x1 [b1 Eq1]]]; subst a1;
  destruct (list_last_inv a2) as [ | [x2 [b2 Eq2]]]; subst a2;
  calc_length in Len; invert Len.
  left. constructor.
  intros Len. rewrite apps_last in T1,T2.
   subst t1 t2. inversions N1. inversions N2.
   forwards H: (@IH b1 b2); eauto. clear IH.
   destruct H as [Ht | [k [Len' Dis]]]. 
     destruct~ (@eta_exp_or_disimilar_ih x1 x2) as [Hx|Hx].
       left. apply~ Forall2_last.
       right. exists (length b1). split. 
         calc_length~. skip. (*math*)
         lets_simpl Q: (@nth_last_one_eq Term). do 2 rewrite~ Q.
     right. exists k. split.
       calc_length~. skip. (*math*)
       lets_simpl Q: (@nth_last Term). do 2 rewrite~ Q. congruence.    
Qed.

Section replace.
Variable A : Type.
Implicit Types l : list A.

Fixpoint replace (n:nat) (y:A) (l:list A) {struct l} : list A :=
  match l with
  | nil => nil 
  | x::l' => 
     match n with
     | 0 => y::l'
     | S n' => replace n' y l'
     end
  end.

End replace.

Lemma eta_exp_or_disimilar : forall t1 t2,
  noredex t1 -> noredex t2 -> 
  eta_confluent t1 t2 \/ eta_disimilar t1 t2.
Proof.
  introv N1 N2.
  lets n1 a1 i1 H1 M1: (get_hnf_form N1).
  lets n2 a2 i2 H2 M2: (get_hnf_form N2).
  lets n r1 r2 D1 D2: (nat_symmetric_diff n1 n2).
  sets_eq p1: (r1+length a1).
  sets_eq p2: (r2+length a2).
  sets_eq i1': (i1+r1).
  sets_eq i2': (i2+r2).
  sets_eq a1': (etas_list r1 a1).
  sets_eq a2': (etas_list r2 a2).
  testsb R: ((p1 != p2) || (i1' != i2')).
    right.
     exists (hnf_etas r1 n1 a1 i1) (hnf_etas r2 n2 a2 i2).
     exists (path_nil n p1 p2 i1' i2'). subst t1 t2. splits 3.
       apply~ eta_exp_hnf_etas.
       apply~ eta_exp_hnf_etas.
       unfold hnf_etas. rewrite D1. rewrite D2. subst i1' i2'.
        apply~ disimilar_nil; rewrite~ etas_list_length.
    calc_bool in R. destructb R. subst t1 t2. 
    forwards C: (@eta_exp_or_disimilar_arguments a1' a2'); eauto.
      skip. skip. (*noredex etas_list*)
      subst. do 2 rewrite etas_list_length. rewriteb~ H.
    destruct C as [E | [k [Len [x1' [x2' [P [E1 [E2 D]]]]]]]].
      left. skip. (*etaexp with confluence*)
      right. 
       exists (hnf n (replace k x1' a1') i1').
       exists (hnf n (replace k x2' a2') i2').
       exists (path_cons n p1 i1' k P). splits 3.
         skip. skip. (* etaexp with replace *)
         rewriteb H0. apply~ disimilar_cons.
           skip. skip. skip. (* length_replace, length etas_list *)
           skip_rewrite (nth (A:=Term) k (replace k x1' a1') = x1').
           skip_rewrite (nth (A:=Term) k (replace k x2' a2') = x2').
           auto. 
Admitted.


(********************************************************************)
(** Reduction of an eta-expansion is an eta-expansion *)

Section BetaEta.

Hint Resolve star_refl star_once star_step.
Hint Resolve beta_star_lam beta_star_app1 beta_star_app2.

Lemma eta_exp_subst : forall t11 t12 t21 t22,
  eta_exp t11 t12 ->
  eta_exp t21 t22 ->
  eta_exp (subst t11 t21) (subst t12 t22).
Admitted.

Hint Resolve eta_exp_subst.

Lemma beta_on_eta_exp : forall t1 t2 t2',
  eta_exp t1 t2 -> t2 --> t2' ->
  exists t1', eta_exp t1' t2' /\ t1 -->* t1'.
Proof.
  unfold beta_star. introv E R. gen t1. 
  induction R; introv E.
  (* case: beta *)
  inversions E.
  exists~ (subst t2 t1).
  inversions H2.
    exists (app t11 t21). 
     skip_rewrite (subst t2 (app (shift t3) (var 0)) = app t3 t2).
     auto.
    subst. exists~ (subst t21 t1).
    subst. exists~ (subst t21 t0). 
  (* case: app1 *)
  inversions E.
  exists~ (app t12 t2).
  lets t11' ? ?: (IHR _ H2). exists~ (app t11' t21).
  (* case: app2 *)
  inversions E. 
  exists~ (app t1 t22).
  lets t21' ? ?: (IHR _ H3). exists~ (app t11 t21').
  (* case: lam *)
  inversion E. subst t0. subst t11.
   inversion R. 
     subst. exists t1. split~.
      rewrite <- H0 in E.
      skip [t21 Eq]: (exists t21, t2 = lam t21). subst.
      skip H0': (t0 = shifts 1 t21). subst t0.
      skip_rewrite (subst (var 0) (shifts 1 t21) = t21).
      auto.
     subst t3. skip [t0' Eq]: (exists t0', t0 = shift t0'). subst t0.
      skip H3': (t2 --> t0'). 
      skip [t1' [IH1 IH2]]: (exists t1', eta_exp t1' t0' /\ star beta t1 t1').
      exists t1'. split~. rapply~ eta_exp_eta. 
     inversion H3.
  exists (lam t12). split~.
  lets t11' ? ?: (IHR _ H1). exists~ (lam t11').
Qed.

Lemma beta_star_on_eta_exp : forall t1 t2 t2',
  eta_exp t1 t2 -> t2 -->* t2' ->
  exists t1', eta_exp t1' t2' /\ t1 -->* t1'.
Proof.
  unfold beta_star. introv E Red. gen t1.
  induction Red as [t2 | t2' t2 t2'' R]; introv E.
  exists t1. auto~ star_refl.
  lets t1' E' R': (beta_on_eta_exp E R).
   lets t1'' E'' R'': (IHRed _ E').
   exists t1''. autos* star_trans.
Qed.

End BetaEta.


(********************************************************************)
(** Separable eta-expansions is sufficient *)

Lemma select_not_an_app : forall t1 t2 n k,
  app t1 t2 <> cst_select n k.
Proof. 
  unfold cst_select. destruct n; simpl; intros R; fequals. 
Qed.

Implicit Arguments select_not_an_app [t1 t2 n k].

Lemma select_not_eta_of : forall t n k,
  eta_of t <> cst_select n k.
Proof.
  unfold eta_of, cst_select. intros.
  destruct n as [|[|]]; simpl; fequals.
Qed.

Implicit Arguments select_not_eta_of [t n k].

Lemma eta_exp_to_select : forall n k t1 t2,
  eta_exp t1 t2 ->
  t2 = cst_select n k ->
  t1 = t2.
Proof.
  introv H. gen n k. induction H; introv Eq.
  false (select_not_eta_of Eq).
  auto.
  false (select_not_an_app Eq).
  unfolds cst_select. destruct n; simpls; inversions Eq.
  fequals*.
Qed.

Lemma beta_star_and_exp_to_select : forall n k t2 t1 t2',
  eta_exp t1 t2 ->
  beta_star t2 t2' ->
  t2' = cst_select n k ->
  beta_star t1 t2'.
Proof.
  introv E R Eq.
  lets t' E' S': (beta_star_on_eta_exp E R).
  rewrite~ <- (eta_exp_to_select n k E' Eq).
Qed.

Hint Resolve eta_exp_apps.

Lemma separable_eta_exp : forall t1' t2' t1 t2,
  eta_exp t1 t1' ->
  eta_exp t2 t2' ->
  separable t1' t2' ->
  separable t1 t2.
Proof.
  introv E1 E2 [us [S1 S2]]. exists us. split.
  apply* (@beta_star_and_exp_to_select 2 1 (apps t1' us)).
  apply* (@beta_star_and_exp_to_select 2 0 (apps t2' us)).
Qed.


(********************************************************************)
(** Disimilar separable *)

Definition separable_at_depth n :=
  forall P t1 t2, path_length P = n ->
  disimilar P t1 t2 -> separable t1 t2.

Lemma separability_neq_i : forall n a1 a2 i1 i2,
  i1 != i2 -> i1 < n -> i2 < n ->
  separable (hnf n a1 i1) (hnf n a2 i2).
Admitted.

Lemma separability_neq_p : forall n a1 a2 i,
  length a1 != length a2 -> i < n ->
  separable (hnf n a1 i) (hnf n a2 i).
Admitted.

Lemma separability_cons_0 : forall n a1 a2 k P,
  no_binding_to 0 P ->
  length a1 = length a2 -> 
  disimilar P (nth k a1) (nth k a2) ->
  separable_at_depth (path_length P) ->
  separable (hnf n a1 0) (hnf n a2 0).
Admitted.

Lemma separability_cons_i : forall n (a1 a2 : list term) i k P,
  length a1 = length a2 -> 
  disimilar P (nth k a1) (nth k a2) ->
  separable_at_depth (path_length P) ->
  separable (hnf n a1 i) (hnf n a2 i).
Admitted.

Lemma disimilar_separable : forall P t1 t2,
  disimilar P t1 t2 -> separable t1 t2.
Proof.
  cuts H: (forall n, separable_at_depth n).
    intros. rapply* H.
  induction n; introv Len Dis;
   destruct P; inversions Len.
  (* case: path_nil *)
  inverts Dis as C. testsb H: (i1 != i2).
    apply~ separability_neq_i. skip. skip.
    calc_bool in C. apply~ separability_neq_p. skip.
  (* case: path_cons *)
  inverts Dis as Eq Lt Dis.
  apply* separability_cons_i. 
Qed.


(********************************************************************)
(** Conclusion *)

Lemma bohm : bohm_theorem.
Proof.
  introv C1 N1 C2 N2.
  apply_to N1 normal_to_noredex.
  apply_to N2 normal_to_noredex.
  destruct~ (@eta_exp_or_disimilar t1 t2) 
   as [[t [E1 E2]] | [t1' [t2' [P [E1 [E2 D]]]]]];
   [left | right].
  (* case: eta-equivalent *)
  apply (@eta_equiv_trans t).
  apply~ eta_exp_to_eta_equiv.
  apply eta_equiv_sym.
  apply~ eta_exp_to_eta_equiv.
  (* case: disimilar *)
  apply* (@separable_eta_exp t1' t2').
  apply* disimilar_separable.
Qed.

