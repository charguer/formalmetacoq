(**************************************************************************
* Extensionality, Classical logic and Non-construtivism                   *
* Arthur Charguéraud                                                      *
**************************************************************************)

Set Implicit Arguments.
Require Import Plus Omega.

(** By default, Coq features a constructive logic and provides a 
    relatively weak notion of equality. This contrasts with most
    other well-known theorem provers (e.g., Isabelle/HOL), which
    are based on classical logic, offer non-constructive operators,
    and feature an extensional equality. These features can allow for
    dramatic simplifications in formal developments compared with what
    can be achieved in a constructive logic with a weak equality.
   
    Fortunately, it is straightforward to extend the logic Coq with 
    a few axioms in order to recover these features. In fact, three
    axioms suffice to add support for extensionality, classical logic 
    and non-constructive operators. Note that these axioms do not break 
    the soundness of Coq because they are compatible with the boolean 
    model in which every proposition is either true or false. 
    
    The three axioms that we need are called "functional extensionality",
    "propositional extensionality" and "indefinite description". From
    these, other well-known axioms can be derived, including "predicate
    extensionality", "proof irrelevance", the "excluded middle", the
    "strong excluded middle", as well various forms of the "axiom of choice".
    
    There are two interests to adding these axioms to Coq. First, it 
    allows proving some mathematical theorems that otherwise could not
    be proved at all. Second, it allows simplifying some developments,
    for example by replacing equivalence relations by equalities, or by 
    saving the need to carry around evidence of the decidability of 
    particular predicates. 
   
    Of course, there is some interest to constructive developments:
    the use of non-constructive axioms in definitions can prevent one
    from running computations in Coq and may disable the possibility of
    extracting code. However, if you are not running computations in Coq 
    and are not interested in code extraction, then there is no reason to
    refrain yourself from using non-constructive features. And, even
    if you are interested in code extraction and need to be constructive
    for your definitions, you may still be interested in exploiting non-
    constructive features in some of your proofs.

    In this chapter, we will explain the meaning of each of the axioms 
    mentioned above, and we will present concrete examples illustrating
    the benefits of making these axioms available. *)

   
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Functional extensionality *)

(** The notion of equality between two functions in Coq is definitely
    not satisfying. For example, [fun n => 1 + n] is equal to
    [fun n => S n] but is not equal to [fun n => n + 1]. The reason is
    that two Coq functions can be proved equal if their body are two
    convertible Coq terms, but cannot be proved equal if their body are
    only equal. *)

Definition succ_1 n := S n.
Definition succ_2 n := 1 + n.
Definition succ_3 n := n + 1.

Lemma succ_1_eq_succ_2 : succ_1 = succ_2.
Proof.
  reflexivity. (* works because [S n] and [1 + n] are convertible *)
Qed.

Lemma succ_1_eq_succ_3_fails : succ_1 = succ_3.
Proof.
  (* [n + 1] and [1 + n] are equal but not convertible *)
  try reflexivity.   
  (* rewriting [n + 1 = 1 + n] is not possible because it is not
     possible to perform rewriting involving bound names *)
  unfold succ_3. try rewrite plus_comm.
Admitted.

(** Even though we cannot prove [succ_1] and [succ_3] equal, we can
    prove them extensionaly equal: for any argument [n], the applications
    [succ_1 n] and [succ_3 n] yields equal results. *)

Lemma succ_1_eq_succ_3_ext : 
  forall n, succ_1 n = succ_3 n.
Proof. intros. unfold succ_1, succ_3. rewrite plus_comm. reflexivity. Qed.

(** From this lemma, it is possible to derive the equality [succ_1 = succ_3] 
    by using the axiom of "functional extensionality". This axioms states
    that if two functions agree on all arguments, then they are equal in the
    sense of [=]. This axiom can be stated in Coq as shown below. *)

Axiom func_ext : forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.

(** Let us check that we can indeed derive [succ_1 = succ_3] using
    functional extensionality. *)

Lemma succ_1_eq_succ_3 : succ_1 = succ_3.
Proof. apply func_ext. apply succ_1_eq_succ_3_ext. Qed.

(** So, one interest of functional extensionality is that it allows
    to more elegantly state that a function matches another. We will
    see another interest of functional extensionality later on, when
    discussing predicate extensionality. *)

(** The functional extensionality axiom only describes equality between
    two functions of arity one. What about functions of arity two or more?
    Functional extensional for functions of higher arities can be derived
    from the basic functional extensionality axiom that we have seen.
    Intuitively, it suffices to iterate applications of [func_ext]. As an
    exercise, prove the extensionality for functions of two arguments by
    filling in the proof below. *)

Lemma func_ext_2 : forall A1 A2 B (f g : A1 -> A2 -> B),
  (forall x1 x2, f x1 x2 = g x1 x2) -> f = g.
Proof.
  (* BEGIN SOLUTION *)
  intros. apply func_ext. intros. apply func_ext. auto. 
  (* END SOLUTION *)
Qed.

(** As another direct application of functional extensionality, prove that
    a function is equal to an eta-expansion of itself, i.e., that [f] is
    always equal to [fun x => f x]. *)

Lemma func_eta : forall A B (f : A -> B),
  (fun x => f x) = f.
Proof.
  (* BEGIN SOLUTION *)
  intros. apply func_ext. auto.
  (* END SOLUTION *)
Qed.

(** The functional extensionality axiom [func_ext] that we have introduced
    above is actually not quite general enough, because it only accomodates
    function with a simple arrow type but not functions with a dependent
    type. It is straightforward to generalize [func_ext] into a version
    that supports functions with a type of the form [forall x:A, B x]. *)

Axiom func_ext_dep : forall (A:Type) (B:A->Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.

(** Note that the axiom [func_ext_dep] is strictly more general than
    [func_ext]. This fact is established next. *)

Lemma func_ext_derivable : forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.
Proof. intros. apply func_ext_dep. auto. Qed. 

(** So, in practice we only take functional extensionality for dependently-
    typed functions as axiom. From this one axiom, we can derive extensionality
    for simply-typed functions as well as extensionality for functions of 
    several arguments (even for dependently-typed functions). *) 


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Propositional extensionality *)

(** Propositional extensionality is another axiom that strengthens 
    the meaning of equality. This axiom asserts that when two propositions
    are equivalent, in the sense that they are related by "if and only if",
    then these two propositions can be considered to be "equal", in the sense
    of [=]. *)

Axiom prop_ext : forall (P Q : Prop), 
  (P <-> Q) -> P = Q.

(** For example, using propositional equality, one can prove that [~ True] 
    is equal to [False] and that [~ False] is equal to [True]. *)

Lemma not_True : (~ True) = False.
Proof. intros. apply prop_ext. split; intros H; auto. Qed.

Lemma not_False : (~ False) = True.
Proof. intros. apply prop_ext. split; intros H; auto. Qed.

(** Having such equalities makes it easy to simplify logical expressions
    through rewriting operations. Moreover, such rewriting operations 
    can be automated, as we will see soon afterwards. *)

(** Combining propositional extensionality with functional extensionality,
    we can derive a result called "predicate extensionality". Predicate
    extensionality states that if two predicate yield equivalent propositions 
    (in the sense of [<->]) on all arguments, then these two predicates 
    can be considered to be equal (in the sense of [=]). The formal
    statement appears next. *)

Lemma pred_ext : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x <-> Q x) -> P = Q.
Proof.
  (* use [prop_ext] and [func_ext_dep] to complete the proof *)
  (* BEGIN SOLUTION *)
  intros. apply func_ext_dep. intros. apply prop_ext. auto.
  (* END SOLUTION *) 
Qed.

(** Like functional extensionality, predicate extensionality allows for
    more concise statements of lemmas. To get some practice with using
    [pred_ext], prove that the two definitions of the predicate "is equal 
    to zero" shown below are equal. *)

Definition zero_1 n := (n = 0).

Definition zero_2 n := (forall m, n <> S m).

Lemma zero_1_eq_zero_2 : zero_1 = zero_2.
Proof.
  (* BEGIN SOLUTION *)
  apply pred_ext. intros n.
  unfold zero_1, zero_2. split; intros H.
    intros m E. congruence.
    destruct n. auto. destruct (H n). auto.
  (* END SOLUTION *) 
Qed.

(** Note that, like other extensionality results, predicate extensionality 
    can be easily generalized to support higher arities. *)

(** A major application of predicate extensionality is the
    construction of a general-purpose set library that features
    a proper double-inclusion lemma [subset E F -> subset F E -> E F].
    In Coq, a (possibly-infinite) set of values of type [A] can be 
    represented as a predicate of type [A->Prop]. *)

Definition set (A:Type) := A -> Prop.

(** The idea underlying this representation of sets is that a set [E]
    contains a value [x] if and only if [E x] holds. We write [mem x E]
    to describe membership of [x] to the set [E]. It is defined as follows. *)

Definition mem (A : Type) (x : A) (E : set A) : Prop := 
  E x.

(** We can define the basic operations on sets, such as union, intersection,
    empty sets and singleton sets, by constructing the appropriate functions. *)

Section SetOperations.
Variables A : Type.

Definition empty : set A := 
  fun _ => False.

Definition singleton (v : A) : set A :=
  fun x => x = v.

Definition union (E F : set A) : set A :=
  fun x => mem x E \/ mem x F.

Definition inter (E F : set A) : set A :=
  fun x => mem x E /\ mem x F.

(** We can define inclusion in terms of logical implication: [E] is a subset
    of [F] set if all the members of [E] are also members of [F], that is,
    if for any [x], the proposition [mem x E] implies [mem x F]. *)

Definition subset (E F : set A) : Prop :=
  forall x, mem x E -> mem x F.

(** Now that we have defined inclusion, we can state the double inclusion
    result: if two sets are subsets of each other, then they are equal.
    This statement appears next. *)

Lemma double_inclusion : forall (E F : set A), 
  subset E F -> subset F E -> E = F.
Proof. 
  (* Complete the proof using predicate extensionality ([pred_ext]). *)
  (* BEGIN SOLUTION *)
  intros E F H1 H2. apply pred_ext. intros. split. apply H1. apply H2.
  (* END SOLUTION *)
Qed.

End SetOperations.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Classical logic *)

(** A "classical logic" is a logic where any given proposition is either
    "true" or "false". This property is also known as the "excluded middle",
    capturing the idea that there is no such thing as being half-way 
    between "true" and "false". The logic of Coq can be safely extended 
    into a classical logic by including the excluded middle axiom. *)

Axiom classic : forall (P : Prop), P \/ ~ P.

(** The above statement states that, for any proposition [P], we can 
    assume that either there exists a proof of [P], or there exists a
    proof of the negation of [P]. Using the axiom of propositional
    extensionality that we have introduced earlier on, we can reformulate
    this result is a slightly different way: any proposition [P] is
    either equal to [True] or equal to [False]. This alternative 
    formulation, known as "propositional degeneracy" is formally stated
    and proved below. *)

Lemma prop_degeneracy : forall (P : Prop),
   P = True \/ P = False.
Proof.
  intros. destruct (classic P).
    left. apply prop_ext. tauto.
    right. apply prop_ext. tauto.
Qed.

(** There are some mathematical results that cannot be established 
    without classical logic. For example, if we want to show that
    a program diverges in small-step semantics if and only if it
    diverges in a (co-inductive) big-step semantics, then we cannot
    complete our proof without using the excluded middle property.
    (Intuitively, the reason is that the halting problem is undecidable.
    For more details, read "Coinductive big-step operational semantics",
    by Xavier Leroy and Hervé Grall.) *)

(** Beyond the fact that the excluded middle is sometimes necessary,
    it is sometimes also very convenient. It means that, at any time
    in a proof, we can perform a case analysis on whether a given
    proposition is true or not. The tactic [test] helps exploiting
    the excluded middle in such a way. [test P] applies to any goal
    and produces two copies of this goal: a first one containing the
    hypothesis [P], and a second one containing the hypothesis [~P]. *)

Tactic Notation "test" constr(P) :=
  destruct (classic P).
Tactic Notation "test" constr(P) "as" ident(H) :=
  destruct (classic P) as [H|H].

(** The excluded middle is also often exploited indirectly through
    the introduction of a double negation, which allows to replace
    a goal [P] with [False] and to add [~P] as hypothesis. The double
    negation property is captured by the following lemma. *)

Lemma not_not_elim : forall (P : Prop), 
  ~ ~ P -> P.
Proof. 
  (* complete the proof usint the tactic [test]; at some point in
     the proof, you need to invoke [elimtype False] in order to
     discard one absurd subgoal *)
  (* BEGIN SOLUTION *) 
   intros P N. test P.
      auto.
      elimtype False. apply N. auto.
  (* END SOLUTION *)
Qed.

(** Another formulation of the double negation is known as 
   "Peirce's result". It says that to prove [P], it is sufficient
   to prove [P] under the assumption that [~P] holds. *)

Lemma peirce : forall (P : Prop), 
  (~ P -> P) -> P.
Proof. intros P N. test P. auto. auto. Qed.

(** Classical reasoning is particularly useful to prove disjunction.
    For example, to prove the disjunction [P \/ Q], it suffices to
    prove that [P] is true under the assumption that [Q] is false,
    or, symmetrically, to prove that [Q] is true under the assumption
    that [P] is false. Prove this result formally. *)

Lemma classic_or : forall (P Q : Prop), 
  ((~ Q -> P) \/ (~ P -> Q)) -> (P \/ Q).
Proof.
  (* BEGIN SOLUTION *) 
  intros P Q H. destruct H.
    test Q. auto. auto.
    test P. auto. auto.
  (* END SOLUTION *)
Qed.

(** Many of the consequences of classical logic are best stated in
    the form of rewriting rules. For example, the elimination of
    double negation can be written [(~ ~ P) = P]. Similarly, the
    distribution of negation over disjunction takes the form of an
    equality [(~ (P \/ Q)) = (~ P /\ ~ Q)]. Negation also distributes
    over quantifiers, for example the negation of an existential is
    a universal: [(~ (exists x, P x)) = (forall x, ~ P x)].

    In what follows, we show how to derive equalities of this form
    and how to set up a tactic that exploits these equalities in order
    to automate the simplification of logical expressions. Let us
    start with the equality for double negation. *)

Lemma not_not : forall P : Prop,
   (~ ~ P) = P.
Proof. 
  intros. apply prop_ext. split.
    apply not_not_elim.
    intros M N. apply N. apply M.
Qed.

(** To prove the distribution of negation over logical conjunction,
    we follow a more brute-force approach that consists in considering
    all four possible cases (P true and Q true, P true and Q false, 
    (P false and Q true, and P false and Q false). For each case, 
    we call the decision procedure [tauto] to handle the goal. *)

Lemma not_and : forall P Q : Prop,
  (~ (P /\ Q)) = (~ P \/ ~ Q).
Proof.
  intros. apply prop_ext.
  destruct (classic P); destruct (classic Q); tauto.
Qed.

(** In a similar way, we can show how negation distributes over
    disjunctions, implications and equivalences. The proofs all follow
    the exact same pattern, so we use a tactic to factorize them. *)

Ltac classic_bruteforce_2 := 
  intros P Q; apply prop_ext;
  destruct (classic P); destruct (classic Q); tauto.

Lemma not_or : forall (P Q : Prop),
  (~ (P \/ Q)) = (~ P /\ ~ Q).
Proof. classic_bruteforce_2. Qed.

Lemma not_impl : forall (P Q : Prop),
  (~ (P -> Q)) = (P /\ ~ Q).
Proof. classic_bruteforce_2. Qed.

Lemma not_iff : forall (P Q : Prop),
  (~ (P <-> Q)) = ((P /\ ~ Q) \/ (~ P /\ Q)).
Proof. classic_bruteforce_2. Qed.

(** At this point, we are almost ready to set up the tactic that
    automates the simplification of logical expressions. We only
    need to prove a few additional lemmas describing how [True]
    and [False] behave in front of conjunctions and disjunctions. *)

Lemma and_True_l : forall P, (True /\ P) = P.
Proof. intros. apply prop_ext; tauto. Qed.
Lemma and_True_r : forall P, (P /\ True) = P.
Proof. intros. apply prop_ext; tauto. Qed.
Lemma and_False_l : forall P, (False /\ P) = False.
Proof. intros. apply prop_ext; tauto. Qed.
Lemma and_False_r : forall P, (P /\ False) = False.
Proof. intros. apply prop_ext; tauto. Qed.
Lemma or_True_l : forall P, (True \/ P) = True.
Proof. intros. apply prop_ext; tauto. Qed.
Lemma or_True_r : forall P, (P \/ True) = True.
Proof. intros. apply prop_ext; tauto. Qed.
Lemma or_False_l : forall P, (False \/ P) = P.
Proof. intros. apply prop_ext; tauto. Qed.
Lemma or_False_r : forall P, (P \/ False) = P.
Proof. intros. apply prop_ext; tauto. Qed.

(** The tactic [rew_logic] is defined in such a way that it 
    automatically tries to perform rewriting using all the 
    equalities that we have proved. The tactic is implemented 
    using the [autorewrite] mechanism. *)

Hint Rewrite not_True not_False not_not not_and not_or
  and_True_l and_True_r and_False_l and_False_r
  or_True_l or_True_r or_False_l or_False_r 
  not_impl not_iff : rew_logic.

Ltac rew_logic := autorewrite with rew_logic in *.

(** The following example illustrates the behavior of [rew_logic]. *)

Lemma rew_logic_demo_1 : forall (P Q R : Prop) (n : nat),
  ~ ((P \/ ~ ((~ Q /\ R) /\ (n <> 3)) -> ~ ~ Q) /\ (~ R /\ ~ Q)).
Proof.
  intros.
  (* first we can simplify the expression *)
  rew_logic.
  (* to simplify further, we need to perform case analyses;
     for example, let's do a case analysis on proposition [Q] *)
  destruct (prop_degeneracy Q) as [H|H]; rewrite H; clear H.
    (* in the first subgoal, [Q] has been replaced with [True]; *)
    (* this subgoal can be simplified further *)
    rew_logic. auto.
    (* in the second subgoal [Q] has been replaced with [False]; *)
    (* this subgoal can also be simplified further *)
    rew_logic.
      (* let's perform a second case analysis, on [R] this time *)
      destruct (prop_degeneracy R) as [H|H]; rewrite H; clear H.
        rew_logic. auto.
        rew_logic. auto.
  (* Note: it was also possible to first test [Q] and then test [P] *) 
Qed.

(** We still need to explain how negation distributes over existential
    and universal quantifiers. These results can be very useful in practice.
    Interestingly, the simplification of [~ (exists ..)] does not require
    classical logic. Only the simplification of [~ (forall ..)] does. 
    The two proofs appear below. *)

Lemma not_exists : forall A (P:A->Prop),
  (~ (exists x, P x)) = (forall x, ~ P x).
Proof.
  intros. apply prop_ext. split; intros H.
    intros x M. apply H. exists x. auto.
    intros [x M]. apply (H x). auto.
Qed.

Lemma not_forall : forall A (P:A->Prop),
  (~ (forall x, P x)) = (exists x, ~ P x).
Proof.
  intros. apply prop_ext. split; intros H.
    (* here, without classical logic, we would be completely
       stuck because we have absolutely no witness to provide *)
    apply not_not_elim. intros M. apply H.
     intros. apply not_not_elim. intros N.
     apply M. exists x. apply N.
    intros M. destruct H as [x H]. apply H. apply M.
Qed.

(** The following example shows how to distribute negation over
    universal and existential quantifiers. *)

Lemma rew_logic_demo_2 : forall (P : nat -> Prop), 
  ~ (forall n, n <> 0 -> exists m, m <> n /\ ~ P m) ->
    (exists n, n <> 0 /\ forall m, m = n \/ P m).
Proof.
  intros P H.
  (* distribute [not] over [forall] *)
  rewrite not_forall in H. 
  destruct H as [n H]. exists n.
  (* simplify a logical expression *)
  rew_logic.
  destruct H as [H1 H2]. split. auto. intros m.
  (* distribute [not] over [exists] *)
  rewrite not_exists in H2. 
  specialize (H2 m).
  (* simplify a logical expression *)
  rew_logic. auto.
Qed.
  
(** Note: for technical reasons, we cannot extend our simplification tactic
    [rew_logic] with the lemmas [not_forall]. Indeed, because Coq internally
    represents implication as a universal quantification, the pattern
    [~ (forall x, P x)] would match any proposition of the form [~ (P -> Q)],
    leading to unwanted rewriting operations being performed. *)

(** When working in a classical logic, facts can be very easily moved
    from the goal to the context and reciprocally by taking the negation.
    We set up two new tactics to assist in this process. The tactic [up]
    applies to an arbitrary goal [P], replaces the goal with [False] and 
    adds [~ P] as assumption. The tactic [down H] replaces the current
    goal with [~ H] and adds the negation of the current goal as hypothesis.     
    Below, we implement the two tactics and then give a demo. *)

Ltac up H :=
  apply not_not_elim; intros H; 
  autorewrite with rew_logic in H.

Lemma down_lemma : forall (P Q : Prop), P -> ~ P -> Q.
Proof. tauto. Qed.

Ltac down H :=
  match goal with
  | |- False => idtac
  | _ => let G := fresh "G" in up G
  end;
  apply (@down_lemma _ _ H);
  clear H; autorewrite with rew_logic.
  
(** A demo follows. This demo shows in particular that reasoning
    by contraposition is made very simple. *)

Lemma up_demo : forall (P : nat->Prop) (n m : nat),
  (n <> m -> ~ P n) -> P n -> n = m.
Proof.
  intros P n m U V. up W. apply U. auto. auto.
Qed.

(** The same lemma can also be proved by applying the tactic [down] to
    the first hypothesis, thereby computing the negation of an implication. *)

Lemma down_demo : forall (P : nat->Prop) (n m : nat),
  (n <> m -> ~ P n) -> P n -> n = m.
Proof.
  intros P n m U V. down U. auto.
Qed.

(** Note that, without classical logic, the proof of the above lemma would
    need to invoke the lemma [eq_dec_nat] in order to perform a case analysis
    on whether [n = m] or [n <> m]. With classical logic, all predicates are
    decidabile by default, so proofs can be much simpler. *)


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Non-constructivism *)

(** The "excluded middle" property captures the fact that, inside a proof,
    we can make a case analysis on whether a proposition is true or false.
    The "strong excluded middle" property states that we can make a case
    analysis on whether a proposition is true or false not just inside a 
    proof, but even inside any definition. For example, with the strong
    excluded middle we can define the min function simply as 
    [fun n m => If n < m then n else m], without having to worry about
    whether comparison is decidable. We are only saying "if the property
    [n < m] is true, then [min n m] should be equal to [n], otherwise it
    should be equal to [m]". However, we are not providing any concrete way 
    of computing whether [n] is less than [m]. This is why such a definition
    of [min] is said to be "non-constructive".

    The excluded middle was stated using a normal disjunction, [P \/ ~P]. 
    The strong excluded middle is similar except that it uses a strong sum,
    of the form [{P} + {~P}]. Its statement is thus as follows.
*)

Axiom classicT : forall (P : Prop), {P} + {~ P}.

(** If [P] is a proposition, then [classicT P] is an term of type
    [{P} + {~ P}] which can be examined using a Coq if-statement.
    For example, in the definition of the minimum function, the argument 
    of the if-statement is [classicT (n < m)], as shown below. *)

Definition min' n m := 
  if classicT (n < m) then n else m.

(** In a non-constructive logic, the pattern [if classicT P then .. else ..] 
    is very common. So, we introduce a specific notation for it, in order
    to simply write [If P then v1 else v2] (starting with a capital "i"). *)

Notation "'If' P 'then' v1 'else' v2" := 
  (if (classicT P) then v1 else v2)
  (at level 200, right associativity) : type_scope.

(** For example, we can re-define [min] using this notation *)

Definition min n m :=
  If n < m then n else m.

(** At this point, we know how to write non-constructive definitions.
    Let's now see how to prove properties about non-constructive 
    definitions. For example, let's prove that [min] is associative. 
    Whenever we see a pattern of the form [If P then v1 else v2], we
    can perform a case analysis on [P] using [destruct (classictT P)]. *)

Lemma min_assoc_1 : forall n m p,
  min n (min m p) = min (min n m) p.
Proof.
  intros. unfold min.
  destruct (classicT (m < p)).
    destruct (classicT (n < m)). 
      destruct (classicT (n < p)). omega. omega. 
      destruct (classicT (m < p)). omega. omega.
    destruct (classicT (n < m)).
      auto.
      destruct (classicT (n < p)).
        omega.
      destruct (classicT (m < p)). omega. omega.
Qed.

(** Testing whether the condition of a if-statement is true or false
    is something that we keep repeating over and over in the proof above.
    More generally, it is very common that we want to perform a case
    analysis on the condition from an if-statement. So, we introduce a
    tactic, called [case_if], that looks in the goal for the first if-
    statement that it finds and perform a case analysis on its condition. *)

Ltac case_if :=
  let go P := destruct P; try solve [elimtype False; congruence] in
  match goal with 
  | |- context [if ?P then _ else _] => go P
  | K: context [if ?P then _ else _] |- _ => go P
  end.

(** Using [case_if], we can now revisit the proof of associativity of 
    the mininum function. By using [repeat case_if], the proof script
    now fits on a single line! *)

Lemma min_assoc_2 : forall n m p,
  min n (min m p) = min (min n m) p.
Proof. intros. unfold min. repeat case_if; omega. Qed.

(** Sometimes we have in the goal an expression of the form
    [If P then v1 else v2] yet we know that [P] is true. So, rather
    than performing a case analysis on [P] and having to prove that
    [~P] is absurd, we could directly simplify [If P then v1 else v2]
    into [v1] and have [P] appear as a new subgoal. This can be 
    achieved by using the following lemma. *)

Lemma If_l : forall (A:Type) (P:Prop) (x y : A), 
  P -> (If P then x else y) = x.
Proof. intros. case_if. auto. Qed.

(** For example, if we have [If K 3 then True else False] and we
    know that [K n] holds for all [n], then we can perform a rewrite
    step using the lemma [If_l] to simplify the goal into [True]. *)

Lemma If_l_demo : forall (K : nat->Prop),
  (forall n, K n) -> If K 3 then True else False.
Proof. intros. rewrite If_l. auto. auto. Qed.

(** Symmetrically, if our goal contains an expression of the form
    [If P then v1 else v2] and we know that [~P] is true, then we
    may simplify the expression into [v2] directly, using the following
    lemma. *)

Lemma If_r : forall (A:Type) (P:Prop) (x y : A), 
  ~ P -> (If P then x else y) = y.
Proof. intros. case_if. auto. Qed.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Indefinite description *)

(** The strong excluded middle introduces non-constructivism by allowing 
    to test in a program whether a proposition is true or false. The
    indefinite description axiom takes non-constructivism one step further
    by allowing to "pick" a value that satisfies some given property.
    In other words, we can write in a definition "let [x] be a value 
    satisfying the predicate [P]" without having to explicitly say how
    the value [x] can be constructed.

    Technically, if one can prove that the assertion [exists y, P y],
    then applying the indefinite description axiom to [P] returns one
    arbitrary value [x] satisfying [P x]. 

    Indefinite description is a very strong axiom. It is so strong that
    it entails the strong excluded middle, it entails all the version of
    the axiom of choice, and it allows defining Hilbert's epsilon operator
    (which we will describe soon afterwards). The statement of indefinite
    description, shown below, is certainly a bit mysterious at first sight. *)

Axiom indefinite_description : forall (A : Type) (P : A->Prop), 
   ex P -> sig P. 

(** On the one hand, [ex P] is by definition equivalent to [exists x, P x]
    (because the later is a notation for [ex (fun x => P x)]). On the 
    other hand [sig P] is by definition the same as [ { x | P x } ].
    Both [ex P] and [sig P] describe dependent pairs made of a value and
    a proposition. The only difference is that [ex P] is of type [Prop],
    whereas [sig P] is of type [Type]. 

[[
    Inductive ex  (A : Type) (P : A -> Prop) : Prop :=
      ex_intro : forall x, P x -> ex P.
  
    Inductive sig (A : Type) (P : A -> Prop) : Type :=
      exist    : forall x, P x -> sig P.
]]
  
    So, whereas a pair of type [ex P] can only be deconstructed 
    inside a proof to obtain a particular witness [x] satisfying [P],
    a pair type [sigP] can be deconstructed anywhere in order to
    obtain such a witness, and not just in proofs.

    The indefinite description axiom simply says that if we are able
    to build a dependent pair in the sort [Prop], then we can assume
    that we would have been able to build a similar dependent pair
    in the sort [Type]. In technical words, we are "reifying" objects
    from the proof level into objects from the computational level. *)

(** A first consequence of the indefinite description axiom is the
    axiom of choice. The axiom of choice is required for proving
    certain mathematical results, in particular results from topology
    or from category theory. One classic such result is Tychonoff's
    theorem, which states that the product of any collection of
    compact spaces is itself compact.
 
    The axiom of choice can take many forms. All of them are derivable
    from indefinite description. Here, we consider a particular version
    called "functional choice". Functional choice states that if we
    have a binary relation that maps every input to at least one output, 
    then we can build a function that implements this relation in the
    sense that this input and output values of this function are related
    by the relation. More precisely, if [R] is a relation such that for
    any [x] there exists at least one [y] satisfying [R x y], then there
    exists a function [f] such that for any [x] we have [R x (f x)]. *)

Lemma func_choice : forall A B (R:A->B->Prop),
  (forall x, exists y, R x y) ->
  (exists f, forall x, R x (f x)).

(** Remark: if for a given [x] we have several values [y] such that
    [R x y] holds, then [f x] can be equal to any of these values.

    To prove functional choice, we invoke, for each [x], the indefinite 
    description axiom on the predicate [exists y, R x y]. This allows us
    to pick one particular value [y] that is related to [x]. We use this
    value to define the result produced by [f x]. *) 

Proof.
  intros. exists (fun x => proj1_sig (indefinite_description (H x))).
  intros x. apply proj2_sig.
Qed.

(** A second consequence of indefinite description it that it entails
    the excluded middle and even the strong excluded middle (under the
    assumption that we have the propositional extensionality axiom).  
    The proofs are out of the scope of this tutorial. They can be found
    in the TLC library. *)

Lemma classic_derivable : forall (P : Prop), P \/ ~ P.
Admitted.

Lemma classicT_derivable : forall (P : Prop), {P} + {~ P}.
Admitted.

(** A third and very useful application of indefinite description
    is the construction of Hilbert's epsilon operator, which can
    be used to non-constructively "pick" values satisfying some
    predicate. Consider an inhabited type [A] (i.e. such that there
    exists at least one [x] of type [A]). Then, for any predicate [P] 
    of type [A -> Prop], the expression [epsilon P] denotes a term 
    of type [A]. If, on the one hand, there exists at least one [x] 
    satisfying [P], then [epsilon P] also satisfies [P]. If, on the
    other hand, there exists no value satisfying [P], then [epsilon P] 
    could be any abitrary value of type [A].

    Before we can show the definition of [epsilon], we need to
    introduce a proper definition of "inhabited types". Passing 
    around an arbitrary value of type [A] directly as witness is 
    not appropriate because we do not want the result of [epsilon]
    to depend on the witness given. So, in order to capture the
    fact that a type is inhabited without depending on the particular
    witness provided, we introduce a type-class called [Inhab]. If
    you have never used type-classes in Coq, don't worry, we are 
    only going to use type-classes in a very straightforward way. *)

(** A value of type [Inhab A] is a proof that the type [A] is 
    inhabited. By declaring this as a [Class], we will have Coq
    automatically pass around proofs of the form [Inhab A] without
    having to be explicit about thes proofs. The definition of the
    class is as follows. *)

Class Inhab (A:Type) : Prop := 
  { Inhab_intro : exists x:A, True }.

(** To work with type classes, we need to declare the variables
    that are eligible for automatic generalization. So we write: *)

Generalizable Variables A B.

(** The auxiliary lemma [prove_Inhab] helps building a proof of
    [Inhab A] from a given value of type [A]: if [x] is a value
    of type [A], then [prove_Inhab x] is a proof of [Inhab A]. *)

Lemma prove_Inhab : forall (A:Type), A -> Inhab A.
Proof. intros A x. constructor. exists x. auto. Qed. 

(** For example, we can prove that the type [nat] is inhabited.
    By using the word [Instance] instead of [Lemma], we register
    the corresponding statement in a database, making it possible
    for Coq to automatically refer to this result when it is looking
    for some evidence that [nat] is inhabited. *)

Instance bool_Inhab : Inhab nat.
Proof. apply (prove_Inhab 0). Qed.

(** When we have an inhabited type, we can ask for an arbitrary
    value of that type. We will need to do so in the definition
    of [epsilon]. So, let's introduce the definition [arbitrary].
    Below, the argument [`{Inhab A}] indicates that [arbitrary] 
    expects a type [A] and of proof that this type is inhabited.
    Moreover, it indicates that these arguments will be passed
    automatically so we need not be explicit about them. *)

Definition arbitrary `{Inhab A} : A :=
  proj1_sig (@indefinite_description A _ Inhab_intro).

(** For example, we can define the function [pred] using [arbitrary]. *)

Definition pred n :=
  match n with
  | O => arbitrary
  | S m => m
  end.

(** We are now ready to present the epsilon operator. Before we look
    at the definition of [epsilon] in terms of [indefinite_description], 
    let us first look at the interface that the epsilon operator
    satisfies. *)

Module Type EpsilonInterface.

(** If [A] is inhabited, then [epsilon P] is a value of type [A]. *)

Parameter epsilon : forall `{Inhab A} (P : A -> Prop), A.

(** If there exists a value [x] satisfying [P], then [epsilon P]
    satisfies [P]. This result captures the fact that [epsilon]
    not only knows in advance whether [P] is satisfiable, but it
    is even able to pick one value satisfying [P] when there
    exists one. *)

Parameter epsilon_spec : forall `{Inhab A} (P : A->Prop),
  (exists x, P x) -> P (epsilon P).

(** If [P] and [Q] are two equivalent predicates, then [epsilon P]
    is equal to [epsilon Q]. This result follows directly
    from predicate extensionality: if [P] and [Q] are equivalent
    then [P = Q], hence [epsilon P = epsilon Q]. 

    This result means that when [epsilon] returns a value [x] 
    for one given predicate [P], it has commited itself to 
    returning the exact same value for any other predicate logically
    equivalent to [P]. *)

Parameter epsilon_eq : forall `{Inhab A} (P Q : A->Prop),
  (forall x, P x <-> Q x) -> epsilon P = epsilon Q.

End EpsilonInterface.

(** Let's now investigate the definition of the epsilon operator. The 
    idea is to apply indefinite description for picking a value [x]
    satisfying [(exists y, P y) -> P x]. In other words, if there
    exists at least one value satisfying [P], then epsilon should pick
    one such value. Otherwise, it does not matter what value [epsilon] 
    picks. 

    In order to invoke the indefinite description axiom on the
    predicate [fun x => (exists y, P y) -> P x], we need to show
    that there always exists a value [x] satisfying this predicate,
    that is, [exists x, (exists y, P y) -> P x]. Proving this 
    statement involves classic reasoning. On the one hand, if
    [exists y, P y] is true, then we instantiate [x] with one
    such value [y] and we have [P x]. On the other hand, if
    [exists y, P y] is false, then we instantiate [x] with an 
    arbitrary value of type [A], and the implication 
    [(exists y, P y) -> P arbitrary] holds because [exists y, P y] 
    is false. The following lemma formalizes this piece of reasoning. *)

Lemma epsilon_aux : forall `{Inhab A} (P : A->Prop),  
  ex (fun x => (exists y, P y) -> P x).
Proof.
  intros. destruct (classic (exists y, P y)) as [[y Py]|M].
    exists y. intros _. auto.
    exists arbitrary. intros N. elimtype False. auto.
Qed. 

(** We can now define [epsilon] by applying indefinite description
    to the above result and returning the witness produced by 
    indefinite description. *)

Definition epsilon `{Inhab A} (P : A -> Prop) : A := 
  proj1_sig (indefinite_description (epsilon_aux P)).

(** The specification of the epsilon operator follows directly
    from the definition of indefinite description. *)

Lemma epsilon_spec : forall `{Inhab A} (P : A->Prop),
  (exists x, P x) -> P (epsilon P).
Proof.
  intros A IA P. unfold epsilon. 
  apply (proj2_sig (indefinite_description (epsilon_aux P))).
Qed.

(** The second property of the epsilon operator follows directly 
    from extensionality, as mentioned earlier on. *)

Lemma epsilon_eq : forall `{Inhab A} (P Q : A->Prop),
  (forall x, P x <-> Q x) -> epsilon P = epsilon Q.
Proof. intros. f_equal. apply pred_ext. auto. Qed.

(** We are going to illustrate the interest of the epsilon operator
    on two particular applications. First, we prove the "omniscient
    functional choice", a result slightly stronger than "functional
    choice". Later on, we will show how the epsilon operator can be
    used to build general quotient structures. *)

(** Recall the statement of functional choice. *)

Parameter func_choice' : forall A B (R:A->B->Prop),
  (forall x, exists y, R x y) ->
  (exists f, forall x, R x (f x)).

(** "Omniscient functional choice" is similar to "functional choice" 
    except that it does not require the user to provide up-front a
    proof that the relation [R] maps every input to at least one output. 
    Instead, the omniscient choice produces a function [f] right away, 
    and then, if the user wants to derive [R x (f x)] for a particular
    input value [x], then he needs to prove that there exists at least 
    one value [y] such that [R x y] holds. *)

Lemma omniscient_func_choice : forall A `{Inhab B} (R : A->B->Prop),
  exists f, forall x, (exists y, R x y) -> R x (f x).

(** Omnicient functional choice is stronger than functional choice 
    because it only requires proving [exists y, R x y] for the values
    [x] of interest, and not for all the possible values [x]. 

    The result can be easily proved using the epsilon operator. 
    We build [f] as a function that maps each [x] to the value
    [epsilon (fun y => R x y)]. Using this value for [f x] ensures
    that, if we can prove that there exists at least one [y] satisfying
    [R x y], then we have [R x (f x)], as required. *)

Proof.
  intros A B IB R. exists (fun x => epsilon (fun y => R x y)).
  intros x Hx. apply epsilon_spec. apply Hx.
Qed.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Proof irrelevance *)

(** From propositional extensionality, we can derive "proof irrelevance",
    which is a very interesting logical property. It captures the fact
    that two proofs of a same proposition can be considered to be equal. 
    More precisely, if [u] and [v] are two proof terms for a same
    proposition [P], in the sense that [u : P] and [v : P], then we have
    the equality [u = v]. *)

Parameter proof_irrelevance : forall (P : Prop) (u v : P), u = v. 

(** Intuitively, the reason why proof irrelevance makes sense is because
    Coq forbids to perform case analysis on values of sort [Prop] for
    building values whose type does not have the sort [Prop]. As a result,
    one cannot exploit the fact that the proof terms [u] and [v] have
    been built differently for disproving [u = v]. Because it is not 
    possible to disprove [u = v], it does not hurt the logic to consider
    that [u = v] is true. 

    The proof showing that irrelevance follows from propositional 
    extensionality is quite technical. It can be found in the Coq library
    or in the TLC library. Remark: proof irrelevance also follows from
    the excluded middle. *)

(** Proof irrelevance is crucial for reasoning about dependent pairs,
    and more generally for working with dependent types. To illustrate
    this, assume that we have defined the type [pos] as the subtype
    of natural numbers that are strictly greater than zero. *)

Definition pos := { n:nat | n > 0 }.

(** Recall that this notation stands for:
    [Definition pos := sig (fun n:nat => n > 0)].
    and that [sig] is defined as follows:
    [[
    Inductive sig (A : Type) (P : A -> Prop) : Type :=
      exist : forall x, P x -> sig P.
    ]] *)

(** We can build a value of type [pos] by providing a natural
    number [n] and a proof of [n > 0]. The auxiliary function
    [new_pos], defined below, helps building values of type [pos]. *)

Definition new_pos (n:nat) (H:n>0) : pos :=
  exist (fun n => n > 0) n H.

Implicit Arguments new_pos []. 

(** If we want to prove two values of type [pos] equal, then we need
    to show not only that the two underlying natural numbers are equal, 
    but also that the that the two proofs showing that these numbers
    are nonzero are equal. That's where proof irrelevance is useful.
    Without it, we would not be able to prove that the two proofs are
    equal in general. The use of proof irrelevance appears below. *)

Lemma new_pos_eq : forall (n1 n2 : nat) (H1 : n1>0) (H2 : n2>0), 
  n1 = n2 -> new_pos n1 H1 = new_pos n2 H2.
Proof.
  intros. unfold new_pos.
  (* note that [rewrite] does not work for substituting [n1] with [n2]
     because there are dependencies on [n1] and [n2] *)
  try rewrite H. 
  (* however, [destruct] works here (it does not always work though) *)
  destruct H.  
  (* at this point it only remains to prove [H1] equal to [H2] *)
  f_equal. apply proof_irrelevance.
Qed.

(** Having to prove an equality of the form [exist P x p = exist P y q]
    is a common pattern when working with dependent types. We can
    encapsulate this pattern in the following convenient lemma. *)

Lemma exist_eq :
  forall (A : Type) (P : A->Prop) (x1 x2 : A) (H1 : P x1) (H2 : P x2),
    x1 = x2 -> exist P x1 H1 = exist P x2 H2.
Proof. intros. destruct H. f_equal. apply proof_irrelevance. Qed.

(** For example, we can use this lemma to simplify our proof *)

Lemma new_pos_eq' : forall (n1 n2 : nat) (H1 : n1>0) (H2 : n2>0), 
  n1 = n2 -> new_pos n1 H1 = new_pos n2 H2.
Proof. intros. apply exist_eq. auto. Qed.

(** In summary, proof irrelevance is critical for working with
    dependent types, because when we manipulate pairs made of a 
    value and a proof, we need to reason about equalities between
    proofs. Proof irrelevance allows us to consider that two proofs
    of a same proposition are always equal. *)
    
(** We end this section with one remark that will be useful to those
    working with dependently-typed values. When working with dependent
    pairs that do have computation content, i.e., values of the form
    [existT P x q] and type [sigT P], we need a lemma for extracting
    information about equalities between two such objects. This lemma,
    called "injectivity of dependent pairs" is as follows: *)

Lemma inj_pairT2 : 
  forall (A : Type) (P : A -> Type) (x : A) (H1 H2 : P x),
  existT P x H1 = existT P x H2 -> H1 = H2.
Admitted. (* the proof uses proof irrelevance *)


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Quotient structures *)

(** Coq does not support quotient structures very well. Indeed, given
    a type [A] and an equivalence relation [R], the quotient type
    [A/R] can only be built and used in a constructive logic if there
    exists a computable "normalization function" [f] of type [A -> A] 
    that takes each element [x] to the elements that represents the class 
    of [x], i.e., such that [f x = f y <-> R x y]. Even though there
    are many cases where we can find such a computable function [f],
    there are also many cases where there is no such function and thus
    no way of building the quotient type.

    In a non-constructive logic, things are much simpler. Whenever we
    have a type [A] and an equivalence relation [R], we can define a
    (non-constructive) normalization function with help of the epsilon
    operator, and use this function to define the quotient type [A/R]. *) 

Module Quotient.
Require Import Equivalence.

Parameter A : Type.
Parameter IA : Inhab A. Existing Instance IA.
Parameter R : A -> A -> Prop.
Parameter E : Equivalence R.

(** First, we use the epsilon operator to define a function called
    [repr], of type [A -> A], such that [repr x = repr y] if and
    only if [R x y] holds. Intuitively, [repr] maps very element of
    type [x] onto the element that represents the equivalence class 
    of [x].
 
    We define [repr x] as the result of picking a value [y] that is
    related to [x] i.e., a value satisfying the predicate
    [fun y => R x y]. *)

Definition repr x := epsilon (R x).

(** Because [R] is a reflexive relation, [repr x] satisfies [R x].
    This means that [repr x] is, as expected, in the same equivalence
    class as [x]. *)

Lemma repr_elim : forall x,
  R x (repr x).
Proof.
  intros. unfold repr. apply epsilon_spec. 
  exists x. destruct E as [R _ _]. apply R.
Qed.

(** Furthermore, [repr] uniquely characterizes the equivalent classes
    in the sense that [repr x] and [repr y] are equal if and only if
    [x] and [y] belong to the same equivalence class. *)

Lemma repr_spec : forall x y, 
  repr x = repr y <-> R x y.
Proof.
  intros. destruct E as [_ S T].
  generalize (repr_elim x). generalize (repr_elim y). intros Ry Rx.
  split; intros M.
    rewrite M in Rx. eauto.
    unfold repr. apply epsilon_eq. intuition eauto.
Qed.

(** We are now going to define the quotient type [Q] as a subtype of the
    type [A] made of the values that represent an equivalence class,
    i.e., of the values [x] satisfying [x = repr x]. To define the type
    [Q] in Coq, we first define a predicate of the form [is_repr x],
    which captures the fact that the equality [x = repr x] holds. *)

Definition is_repr x := (x = repr x).

(** We define [Q] as [ { x : A | is_repr x } ], which can be formulated
    more concisely as [ sig is_repr ]. *)

Definition Q : Type := sig is_repr.

(** In order to justify that we can use [repr] to map each value of
    type [A] onto its corresponding value in the quotient type [Q],
    we need to prove that [repr] behaves as the identity functions on
    values that are representing an equivalence class. More precisely,
    we need to show that for any [x], [repr x] satisfies the predicate
    [is_repr] (i.e., that we have [repr x = repr (repr x)]). *)

Lemma is_repr_repr : forall x, 
  is_repr (repr x).   
Proof. intros. unfold is_repr. apply repr_spec. apply repr_elim. Qed.

(** Using this property, we can view the function [repr] of type 
    [A->A] as a function of type [A->Q] that takes a value of type 
    [A] and returns the corresponding value in the quotient type [Q].
    This function is called [proj]. *)

Definition proj : A -> Q :=
  fun x => exist is_repr (repr x) (is_repr_repr x).

(** The fact that [repr] characterizes equivalence classes implies
    that [proj] also characterizes equivalence classes: [proj x] 
    and [proj y] are equal values of type [Q] if and only if [x] 
    and [y] belong to the equivalence class. *)

Lemma proj_spec : forall x y,
  proj x = proj y <-> R x y.
Proof.
  intros. unfold proj. split; intros H.
    inversion H. apply repr_spec. auto.
    generalize (proj2 (repr_spec x y) H).
     intros. apply exist_eq. auto.
Qed. 

(** It may also be useful to define a function that takes values
    from the quotient type [Q] back to the original type [A].
    Because [Q] is a subtype of [A], this function is implemented
    simply by returning the first projection. *)

Definition unproj : Q -> A :=
  fun q => proj1_sig q.

(** The function [unproj] can be used for example to transport 
    a function into the quotient structure, that is, to transform
    a function [f] of type [A->A] into a corresponding function [g]
    of type [Q->Q]. The function [g] can be defined using [f],
    [proj] and [unproj]. The idea is to take an argument [q] of
    type [Q], convert it into an value of type [A] using [unproj], 
    then applying [f] to that value, and finally using [proj] to 
    convert the result back into a value form the quotient type [Q].
    The formal definition appears below. *)
    
Parameter f : A -> A.

Definition g : Q -> Q := 
  fun q => proj (f (unproj q)).

(** In order to translate properties about the function [f] into
    properties about the function [g], one usually need to argue
    at some point in the proof that [f] "respects" the relation [R]. 
    This property is typically stated in the following form: *)

Parameter f_resp : forall x y, R x y -> R (f x) (f y).

(** How to establish and to use such a property is specific to
    the equivalence relation and to the function being considered.
    Going through a complete example would be out of the scope of this
    tutorial, so we end this section here. In summary, the epsilon
    operator offers a general technique for building quotient structures.
    The central idea is that for any equivalence relation [R] the
    function [fun x => epsilon (R x)] is a normalization function that,
    for each equivalence class of [R], picks one particular element to
    represent this equivalence class. *)

End Quotient.



(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Recursive functions *)

Module FixedPoints.
Require Import Even.

(** The epsilon operator can be used to define the "optimal fixed
    point combinator". This combinator can be used to define (partial)
    recursive functions for which termination is nontrivial to justify.
    More precisely, the optimal fixed point combinator allows one to
    construct the fixed point of any functional, without having to 
    justify termination; then, subsequently, one can derive a fixed point
    equation that holds on the domain of definition of the function.

    This approach has two benefits compared to what can be done in a
    constructive logic. First, one is able to completely separate the
    definition of the function from the justification of why the definition
    actually admits a fixed point. In particular, the domain of the 
    function and the termination relation used to argue for termination
    need not be provided at the time of defining the function. Second,
    one is able to justify the termination of the function through
    interactive proofs that need not involve dependently-typed values.
    This makes the definition of nontrivial partial recursive function
    accessible to those who do not master programming with dependent types.

    The optimal fixed point combinator takes as argument a functional and
    returns its fixed point, of type [A->B]. The only restriction is that 
    the return type [B] must be inhabited. Note: in this tutorial, we do 
    not discuss the implementation of the fixed point combinator but only
    explain how to use it. *)

Parameter FixFun : forall A `{Inhab B} (F:(A->B)->(A->B)), (A->B).

(** We will illustrate the working of the optimal fixed point combinator
    on three examples: a recursive function that terminates only on even
    numbers, a function implementing division (this function does not
    terminate if its second argument is zero), and the Ackerman function
    (whose termination relation involves a lexicographical order).

    To start with, consider the following ML function [f]. It is defined
    in such a way that [f 0] is equal to 1, [f 1] diverges, and [f n] is 
    equal to 2 + [f (n-2)]. This is quite an artificial example, but it
    will very clearly illustrate the working of the optimal fixed point.

[[
let rec f n =
  if n = 0 then 1 else 
  if n = 1 then 1 + f 1 else
  2 + f (n - 2).
]]

    Because this function is not total (it does not terminate odd arguments),
    it cannot be translated into a Coq fixpoint. So, we are going to describe
    this recursive function in the form of a functional, that is, a function
    that is like the function [f] that we want to define except that it takes
    as argument an extra argument representing the function that should be 
    used to make recursive calls. Here, the functional is named [F] and its
    extra argument is named [f]. *)

Definition F f n :=
  If n = 0 then 1 else 
  If n = 1 then 1 + f 1 else
  2 + f (n - 2).

(** We now want to build the fixed point of this functional [F]. That is,
    a function [f] such that we have [f n = F f n] for any [n] in the
    domain of definition [f]. We can obtain such a fixed point simply
    by applying the optimal fixed point combinator [FixFun] to the 
    functional [F]. Note that we do not need to provide the domain of the
    recursive function at this point. *)

Definition f := FixFun F.

(** At this point, we have build one function [f]. For the time being,
    we know nothing about the properties of [f]. We are now going to
    prove that we have [f n = F f n] whenever [n] is even. Using this
    result, whenever we see an application of the form [f n] for some
    even number [n], we are able to "unfold" the definition of [f] and
    rewrite [f n] into:

[[
  If n = 0 then 1 else 
  If n = 1 then 1 + f 1 else
  2 + f (n - 2).
]]

    The fixed point equation is formally stated as follows. *)

Parameter F_fix_statement : forall n, even n ->
  f n = F f n.

(** In order to prove this fixed point equation, it suffices to
    establish that the functional [F] is "contractive" with respect
    to some well-founded relation [R] on the domain of [f], which
    is the set of even values. The definition of contractiveness is
    the one nontrivial notion involved here. To present it, we first
    state its definition in the particular case of a total function,
    we will then generalize it to the case of a partial function, and 
    then we will see how we prove functions contractive in practice.

    A functional [F] describing a non-partial recursive function is
    "contractive" if, for any two functions [f1] and [f2] and for any
    argument [x], we can prove the equality [F f1 x = F f2 x] under the
    assumption that [f1] and [f2] agree on all values strictly smaller 
    than [x]. Formally, [F] is contractive if:

    [[ forall f1 f2 x, 
       (forall y, R y x -> f1 y = f2 y) ->
        F f1 x = F f2 x.
    ]]

    Basically, [F f1 x] and [F f2 x] correspond to two copies of the
    body of the function [f], where in the first copy the recursive
    calls are made using an abstract function called [f1] and where in 
    the second copy the recursive calls are made using another abstract
    function [f2]. To prove the two copies equal, we need to argue that
    for each recursive call made on a value [y] we have [f1 y = f2 y].   
    Because the only assumption that we have about [f1] and [f2] is 
    that they agree on arguments strictly smaller than [x] (here [R y x]
    should be read [y] smaller than [x] w.r.t. [R]), we will be forced
    to giving some evidence that if a recursive call made on a value [y]
    then this value is smaller than [x].

    It turns out that establishing that a functional is contractive
    suffices to prove the existence of a unique fixed point and to
    derive a fixed point equation for the functional considered.

    The formal definition of the contraction condition appears next.
    It generalizes our previous definition to include a domain [P].
    On the one hand, we can assume that our current argument [x] is in 
    the domain. On the other hand, we have to prove that recursive calls
    are made to values [y] that are also in the domain. *)

Definition contractive A B (P:A->Prop) 
    (F:(A->B)->(A->B)) (R:A->A->Prop) :=
  forall f1 f2 x, P x -> 
  (forall y, P y -> R y x -> f1 y = f2 y) ->
  F f1 x = F f2 x.

(** The specification of the optimal fixed point combinator states that
    if [f] has been built as the optimal fixed point of a functional [F]
    and if [F] is contractive on some domain [P] with respect to some 
    well-founded [R], then the function [f] satisfies the fixed point 
    equation [f x = F f x] on the domain [P]. *)

Parameter FixFun_fix : forall A (R:A->A->Prop) (P:A->Prop)
  `{Inhab B} (F:(A->B)->(A->B)) (f:A->B),
  f = FixFun F -> well_founded R -> contractive P F R ->
  (forall x, P x -> f x = F f x).

Implicit Arguments FixFun_fix [A B F f].

(** Using this property, we can prove that [f n = F f n] holds for
    any even [n]. To achieve this, we instantiate the well-founded 
    relation [R] as [<] and we instantiate [P] as [even]. 

    In order to carry out the proof, we will use an auxiliary tactic
    called [math] to help us discard arithmetic goals that contain
    a contradiction in their hypotheses. We also use an auxiliary lemma
    for reasoning about the fact that [even n] implies [even (n-2)] when
    [n] is not 0 nor 1. The tactic and the lemma appear below. *)

Ltac math := first [ simpl; omega | elimtype False; omega ].

Lemma even_minus_2 : forall n, 
  even n -> n <> 0 -> n <> 1 -> even (n - 2).
Proof.
  intros. inversion H. math. inversion H2.
  simpl. rewrite <- minus_n_O. auto.
Qed.

(** The proof of the fixed point equation is then as follows. It 
    starts with an application of the specification of the optimal
    fixed point combinator ([FixFun_fix]). It then establishes the
    "contraction condition", i.e., the fact that [F] is contractive. *)

Lemma f_fix : forall n, even n ->
  f n = F f n.
Proof.
  (* first, we apply the specification of the combinator *)
  eapply (FixFun_fix lt). reflexivity. apply lt_wf.
  (* then we prove the contraction condition *)
  intros f1 f2 n Pn IH. unfold F.
  (* we have two copies of the body, one with [f1] and one with [f2] *)
  (* we case-analyse until we reach the recursive calls *)
  case_if. auto.
  case_if.
    (* the case where the function diverge cannot happen because 
       [n = 1] is not possible when we have [even n] *)
    subst. inversion Pn. inversion H0.
    (* in the general case, we simplify the two bodies *)
    f_equal.
    (* until the point where we reach a recursive call, in which
       situation we invoke the assumption relating [f1] and [f2] *)
    apply IH. 
      (* first, we need to prove that the recursive call is made
         inside the domain: we have [even n] and we know that [n] 
         is not 0 nor 1, so we can deduce [even (n-2)] *)
      apply even_minus_2; auto.
      (* second, we have to show that recursive call was made on
         a strictly smaller value than the current argument *)
      math.
Qed.

(** Once we have the fixed point equation, we can use it to prove
    concrete properties about the recursive function. For example,
    we can prove that for any even [n], the value [f n] is equal
    to [n + 1]. We can prove this property by induction on [n]. *)

Lemma f_spec : forall n, even n -> f n = 1 + n.
Proof.
  (* first we set up the induction *)
  intros n. pattern n. apply (well_founded_ind lt_wf). clear n.
  intros n IH E. 
  (* then we unfold the definition of [f] *)
  rewrite f_fix; [| assumption ]. unfold F.
  (* now we can analyse the body of [f] *)
  case_if. math.
  case_if. subst. inversion E. inversion H0.
  (* on the recursive call, we invoke the induction hypothesis *)
  rewrite IH. math. math. apply even_minus_2; auto.
Qed.

(** In summary, our development was three-step:

    - define the functional and build its fixed point,
    
    - derive the fixed point equation by proving the functional 
      to be contractive,

    - prove properties of the function by rewriting with the 
      fixed point equation in order to unfold the definition.

    Observe that, for reasoning about the function [f], we were
    required to set up a proof by induction on the termination
    relation [<] and we had to justify again that the recursive
    calls were made to smaller values. We thereby had to duplicate
    some of the arguments already given in the proof of the fixed
    point equation (in [f_fix]). This situation is a bit unsatisfying
    because it duplicates some material, however it does not seem
    to be possible to do better without some tool support. In the 
    future, we can hope some support for automatically generating
    reasoning principles for recursive functions, in the same
    style as done by the implementation of the [Program Fixpoint]
    feature of Coq. We could thereby get the same convenient features 
    as in [Program Fixpoint], yet without having to be manipulating
    dependently-typed values. Nevertheless, despites the fact that 
    there might be some duplicated arguments, this duplication can
    be largely avoided by introducing the appropriate auxiliary
    lemmas, like we did for example by introducing [even_minus_2]. 
    So, even without specific tool support, the optimal fixed point
    combinator can be very useful in practice. *)

(** We now show a slightly more interesting example which consists in
    formalizing the division function. This function has two arguments,
    so we use a version of the fixed point combinator, called [FixFun2]
    that accomodates two arguments. (Remark: [FixFun2] is defined in
    terms of [FixFun] by packing the two arguments into a pair. *)

Parameter FixFun2 :
  forall A1 A2 `{Inhab B} (F:(A1->A2->B)->(A1->A2->B)), (A1->A2->B).

(** The division function that we consider returns a pair made of
    the quotient and the remainder. Because the result type needs
    to be proved inhabited, we need a lemma to establish that pairs
    are inhabited when both their components are inhabited. *)

Instance prod_Inhab : forall `{Inhab A} `{Inhab B}, Inhab (A*B).
Proof. intros. apply (prove_Inhab (arbitrary,arbitrary)). Qed.

(** The functional associated with the division function [div] is
    defined below. The intention is that [div n m] returns a pair
    [(q,r)] such that [n = q*m + r] and [r < m]. Observe that the
    recursion is non-structural (recursive calls are of the form
    [div (n-m) m], and that the recursive function does not terminate
    when [m = 0]. *)

Definition Div div n m :=
  If n < m then (0,n) 
  else let '(q,r) := div (n-m) m in 
       (q+1,r).

(** We now build the optimal fixed point. *)

Definition div := FixFun2 Div.

(** For reasoning about the function, we use a generalization of
    the lemma [FixFun_fix] that accomodates two arguments. Observe
    that the well-founded relation involved is now a binary 
    relation over pairs of arguments. *)

Parameter FixFun2_fix : forall A1 A2 (R:A1*A2->A1*A2->Prop)
    (P:A1->A2->Prop) `{IB:Inhab B} F (f:A1->A2->B), 
  f = FixFun2 F -> well_founded R -> 
  (forall x1 x2 f1 f2, P x1 x2 ->   
    (forall y1 y2, P y1 y2 -> R (y1,y2) (x1,x2) -> f1 y1 y2 = f2 y1 y2) ->
     F f1 x1 x2 = F f2 x1 x2) ->
  (forall x1 x2, P x1 x2 -> f x1 x2 = F f x1 x2).

Implicit Arguments FixFun2_fix [A1 A2 B IB F f].

(** The function [div] terminates when [m <> 0] because the
    first argument strictly decreases on each recursive call.
    We could define the termination relation [R] as 
    [fun (n1,m1) (n2,m2) => n1 < n2] and prove this particular
    relation well-founded. However, it saves some effort to use
    a "measure", because a measure is always well-founded.

    If [m] is a function that "measures" the size of the arguments,
    and if the measure decreases on every recursive calls, then
    [fun y x => m y < m x] is a well-founded binary relation that 
    can be used to prove termination. We define the predicate
    [measure] in such a way that it turns a measure [m] into a
    well-founded binary relation, as shown below. *)

Definition measure (A:Type) (m:A->nat) : A->A->Prop :=
  fun y x => m y < m x.

Lemma measure_wf : forall A (f:A->nat), well_founded (measure f).
Proof.
  intros A g. intros a. set (n := g a). assert (n = g a). auto.
  clearbody n. revert a H. pattern n. apply (well_founded_ind lt_wf).
  clear n. intros n IH a E. constructor. intros b M. subst.
  apply (IH (g b)); auto.
Qed.

(** Moreover, we extend the tactic [math] so that it is able to 
    automatically unfold the definition of [measure]. *)

Ltac math ::= 
  unfold measure in *; first [ simpl; omega | elimtype False; omega ].

(** For our division function [div] takes two arguments. As explained
    earlier, our termination relation needs to be a binary relation
    over pairs of natural numbers. Since the first argument decreases
    strictly on each recursive calls, [measure fst] denotes the
    relation [fun (n1,m1) (n2,m2) => n1 < n2] that we want to use.

    By applying [FixFun2_fix] to the measure [measure fst], we are
    able to prove a fixed point equation for [div]. *)

Lemma div_fix : forall n m, m <> 0 -> 
  div n m = Div div n m.
Proof.
  eapply (FixFun2_fix (measure (@fst nat nat))). 
  reflexivity. apply measure_wf.
  intros * Posm IH. unfold Div. case_if. auto.
  rewrite IH; auto. math.
Qed.

(** As a third example, we consider the Ackermann function.
    Termination of this function involves a lexicographical
    relation. Let us recall the definition of lexicographical
    relation and the fact that they are well-founded. *)

Definition lexico2 {A1 A2} (R1:A1->A1->Prop) (R2:A2->A2->Prop)
    : (A1*A2)->(A1*A2)->Prop :=
  fun p1 p2 => let '(x1,x2) := p1 in let '(y1,y2) := p2 in
  (R1 x1 y1) \/ (x1 = y1) /\ (R2 x2 y2).

Parameter lexico2_wf : forall {A1 A2} 
    (R1:A1->A1->Prop) (R2:A2->A2->Prop),
  well_founded R1 -> well_founded R2 -> well_founded (lexico2 R1 R2).

(** The Ackermann function is defined as shown next. *)

Definition Ack ack m n :=
  If m = 0 then n+1 else 
  If n = 0 then ack (m-1) 1 else
  ack (m-1) (ack m (n-1)).

Definition ack := FixFun2 Ack.

(** We can prove the fixed point equation using [FixFun2_fix]. 
    This time, our function is total, so we use [fun _ _ => True]
    to describe its domain. *)

Lemma ack_fix : forall m n, 
  ack m n = Ack ack m n.
Proof.
  intros. eapply (FixFun2_fix (lexico2 lt lt) (fun _ _ => True));
   auto. apply lexico2_wf; apply lt_wf.
  intros * _ IH. unfold Ack. case_if. auto. case_if.
  rewrite IH; auto. math.
  rewrite IH; auto. rewrite IH; auto. math. math.
Qed.

(** Exercise: following the pattern of the Ackermann function, 
    define a greatest common denominator (GCD) function based on
    Euclide's algorithm, and then state and prove a fixed point
    for it. In ML, this [gcd] function would be defined as follows.
[[
    let rec gcd x m =
       if n = 0 then m else
       if m = 0 then n else
       if n <= m then gcd n (m-n) 
                 else gcd (n-m) m
]]
    For the termination measure, you should use the sum of the
    two arguments. So, in the proof of the fixed point equation, 
    you will need to provide [measure (fun p => fst p + snd p)]
    as first argument to [FixFun2_fix], and use the lemma
    [measure_wf] to prove this measure well-founded. *)

(* BEGIN SOLUTION *)

Definition Gcd gcd n m :=
  If n = 0 then m else
  If m = 0 then n else
  If n <= m then gcd n (m-n) else gcd (n-m) m.

Definition gcd := FixFun2 Gcd.

Lemma gcd_fix : forall n m, 
  gcd n m = Gcd gcd n m.
Proof.
  intros. eapply (FixFun2_fix (measure (fun p => fst p + snd p)) 
   (fun _ _ => True)); auto. apply measure_wf.
  intros * _ IH. unfold Gcd. 
  case_if. auto. 
  case_if. auto.
  case_if. rewrite IH; auto. math. rewrite IH; auto. math.
Qed.

(* END SOLUTION *)

(** Follow-up exercise: prove that [gcd n (k*n)] is equal to [n]
    for any [n] and [k]. The proof starts with and induction on [k]. 
    In both cases ([k = 0] and [k = S k']), you will need to invoke
    [rewrite gcd_fix; unfold Gcd] in order to unfold the body of
    the GCD function. 
 
    You will need to use the lemma [rewrite mult_0_r] to prove that
    [S k * 0 = 0], to use the lemma [minus_plus] to prove that
    [n + k*n - n = k*n], and to use the lemma [le_plus_l] to prove
    that [n <= n + k*n].
[[
   Lemma gcd_multiple : forall n k, gcd n (k * n) = n.
]]
*) 

(* BEGIN SOLUTION *)

Lemma gcd_multiple : forall n k, gcd n (k * n) = n.
Proof.
  intros. induction k. simpl. 
  rewrite gcd_fix; unfold Gcd. case_if. auto. case_if. auto.
  rewrite gcd_fix; unfold Gcd. case_if. 
    subst. rewrite mult_0_r. auto.
    simpl. case_if. auto. rewrite If_l.
      rewrite minus_plus. auto.
      apply le_plus_l.
Qed.

(* END SOLUTION *)


(** This concludes our little presentation of the optimal fixed point
    combinator, whose existence is made possible by the epsilon
    operator. Building recursive functions without giving the domain
    and the termination relation at the time of definition is something
    made possible by the epsilon operator. There is no way to achieve
    such a result in a constructive logic.

    The optimal fixed point combinator can also be used for defining
    co-recursive functions, i.e., recursive functions over co-inductive
    data structures. For such functions, one does not argue for 
    termination but instead for "productivity", which involves a slightly
    different notion of contractivity. Even better, one can build the
    fixed point of functions mixing recursion and co-recursion. Such
    functions are notoriously difficult to define in a constructive way,
    but they can be relatively easily handled with the optimal fixed point
    combinator.

    Note: the notion of the "optimal fixed point of a recursive 
    program" originates in work by Manna and Shammir (1975). The author
    of this tutorial adapted this notion to the definition of fixed
    points in formal logics. Details can be found in the paper:
   
       The Optimal Fixed Point Combinator
       Arthur Charguéraud, 
       Interactive Theorem Proving (ITP), July 2010
*)

End FixedPoints.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Conclusion *)

(** Overall, only three axioms are needed to extend the strength of Coq's
    logic. All the others axioms can be derived from these three axioms.
    The three axioms that we need are:

    - functional extensionality: [(forall x, f x = g x) -> f = g],

    - predicate extensionality: [(P <-> Q) -> (P = Q)],

    - and indefinite description: [ex P -> sig p].


    Adding these axioms to Coq's logic allows to prove mathematical
    theorems that could not be proved otherwise. This includes proofs
    that need to exploit "proof irrelevance" or the "excluded middle" 
    or the "axiom of choice". Moreover, adding these axioms to the logic
    allows for dramatic simplifications in formal developments. In 
    particular, it gives:

    - the ability to [If P then .. else ..] in any definition,

    - tactics for simplifying logical expressions such as [~ (P /\ Q)],

    - equality between provably-equivalent functions and predicates,

    - support for sets with a proper double-inclusion property,

    - the ability to build non-computable quotient structures,

    - the possibility to simplify definitions of nontrivial partial
      recursive and co-recursive functions.


    If you are interested in conducting your own developments using 
    extensionality, the (strong) excluded middle, the epsilon operator,
    the extensional sets and the optimal fixed point combinators,
    you might be interested in using the Coq library TLC, developed by
    the author. This library exports all the lemmas and tactics presented
    in this tutorial, plus many more. Further information about TLC is
    available from http://www.chargueraud.org/softs/tlc .

*)

