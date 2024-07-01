(****************************************************************
* Imperative Lambda-calculus                                    *
* Separation Logic Heap Predicates                              *
*****************************************************************)

Set Implicit Arguments.
Require Export Hprop.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types s : state.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(** [Hprop.v] already contains the definition of [heap], [hprop],
    and of the entailment relations. *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Construction of Separation Logic Predicates *)

(* ########################################################### *)
(** ** Core Heap Predicates *)

(** Core heap predicates, and their associated notations:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [H1 \-* H2] denotes the magic wand
    - [Q1 \--* Q2] denotes the magic wand on postconditions
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential
    - [\forall x, H] denotes a universal. *)

Definition hempty : hprop :=
  fun h => (h = Fmap.empty).

Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single p v).

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Definition hpure (P:Prop) : hprop := (* encoded as [\exists (p:P), \[]] *)
  hexists (fun (p:P) => hempty).

Declare Scope hprop_scope.
Open Scope hprop_scope.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Definition hwand (H1 H2:hprop) : hprop :=
  \exists H0, H0 \* \[ H1 \* H0 ==> H2 ].

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Definition qwand (Q1 Q2:val->hprop) : hprop :=
  \forall v, (Q1 v) \-* (Q2 v).

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.


(* ########################################################### *)
(** ** Automation for Heap Equality and Heap Disjointness *)

(** For goals asserting equalities between heaps, i.e., of the form [h1 = h2],
    we set up automation so that it performs some tidying: substitution,
    removal of empty heaps, normalization with respect to associativity. *)

#[global] Hint Rewrite union_assoc union_empty_l union_empty_r : fmap.
#[global] Hint Extern 1 (_ = _ :> heap) => subst; autorewrite with fmap.

(** For goals asserting disjointness between heaps, i.e., of the form
    [Fmap.disjoint h1 h2], we set up automation to perform simplifications:
    substitution, exploit distributivity of the disjointness predicate over
    unions of heaps, and exploit disjointness with empty heaps. The tactic
    [jauto_set] used here comes from the TLC library; essentially, it destructs
    conjunctions and existentials. *)

#[global] Hint Resolve Fmap.disjoint_empty_l Fmap.disjoint_empty_r.
#[global] Hint Rewrite disjoint_union_eq_l disjoint_union_eq_r : disjoint.
#[global] Hint Extern 1 (Fmap.disjoint _ _) =>
  subst; autorewrite with rew_disjoint in *; jauto_set.


(* ########################################################### *)
(** ** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (Fmap.union h1 h2).
Proof. intros. exists* h1 h2. Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof.
  unfold hprop, hstar. intros H1 H2. applys himpl_antisym.
  { intros h (h1&h2&M1&M2&D&U).
    rewrite* union_comm_of_disjoint in U. exists* h2 h1. }
  { intros h (h1&h2&M1&M2&D&U).
    rewrite* union_comm_of_disjoint in U. exists* h2 h1. }
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits*. { applys* hstar_intro. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits*. { applys* hstar_intro. } }
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D&U). hnf in M1. subst. rewrite* union_empty_l. }
  { intros M. exists (@Fmap.empty loc val) h. splits*. { hnfs*. } }
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists* x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits*. { exists* x. } }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists* h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof. introv W (h1&h2&?). exists* h1 h2. Qed.

(** Additional, symmetric results, useful for tactics *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof.
  applys neutral_r_of_comm_neutral_l. applys* hstar_comm. applys* hstar_hempty_l.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof.
  introv M. do 2 rewrite (@hstar_comm H1). applys* himpl_frame_l.
Qed.


(* ########################################################### *)
(** ** Properties of [hpure] *)

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split*. } { exists* p. }
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof. introv W Hh. rewrite hstar_hpure_l in Hh. applys* W. Qed.


(* ########################################################### *)
(** ** Properties of [hexists] *)

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof. introv W. intros h. exists x. apply* W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.


(* ########################################################### *)
(** ** Properties of [hforall] *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof. introv M. intros h Hh x. apply* M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof. introv M. intros h Hh. apply* M. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.


(* ########################################################### *)
(** ** Basic Tactics for Simplifying Entailments *)

(** [xsimpl] performs immediate simplifications on entailment relations.
    For a more powerful version of [xsimpl], see the course
    Separation Logic Foundations, or the implementation of the CFML tool. *)

#[global] Hint Rewrite hstar_assoc hstar_hempty_l hstar_hempty_r : hstar.

Tactic Notation "xsimpl" :=
  try solve [ apply qimpl_refl ];
  try match goal with |- _ ===> _ => intros ? end;
  autorewrite with hstar; repeat match goal with
  | |- ?H \* _ ==> ?H \* _ => apply himpl_frame_r
  | |- _ \* ?H ==> _ \* ?H => apply himpl_frame_l
  | |- _ \* ?H ==> ?H \* _ => rewrite hstar_comm; apply himpl_frame_r
  | |- ?H \* _ ==> _ \* ?H => rewrite hstar_comm; apply himpl_frame_l
  | |- ?H ==> ?H => apply himpl_refl
  | |- ?H ==> ?H' => is_evar H'; apply himpl_refl end.

Tactic Notation "xsimpl" "*" := xsimpl; auto_star.

(** [xchange] helps rewriting in entailments. *)

Lemma xchange_lemma : forall H1 H1',
  H1 ==> H1' -> forall H H' H2,
  H ==> H1 \* H2 ->
  H1' \* H2 ==> H' ->
  H ==> H'.
Proof.
  introv M1 M2 M3. applys himpl_trans M2. applys himpl_trans; [|applys M3].
  applys himpl_frame_l. applys M1.
Qed.

Tactic Notation "xchange" constr(M) :=
  forwards_nounfold_then M ltac:(fun K =>
    eapply xchange_lemma; [ eapply K | xsimpl | ]).


(* ########################################################### *)
(** ** Properties of [hwand] *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { rewrite hstar_comm. xchange M. rewrite hstar_hexists.
    applys himpl_hexists_l. intros H. rewrite (hstar_comm H).
    rewrite hstar_assoc. applys himpl_hstar_hpure_l. intros N.
    rewrite hstar_comm. auto. }
  { applys himpl_hexists_r H0. rewrite hstar_comm.
    applys* himpl_hstar_hpure_r. }
Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. rewrite* <- hwand_equiv. Qed.

Arguments hwand_cancel : clear implicits.


(* ########################################################### *)
(** ** Properties of [qwand] *)

Lemma qwand_specialize : forall (v:val) (Q1 Q2:val->hprop),
  (Q1 \--* Q2) ==> (Q1 v \-* Q2 v).
Proof using.
  intros. unfold qwand. applys himpl_hforall_l v. xsimpl.
Qed.

Lemma qwand_equiv : forall H Q1 Q2,
      H ==> (Q1 \--* Q2)
  <-> (Q1 \*+ H) ===> Q2.
Proof using.
  intros. iff M.
  { intros x. xchange M. xchange (qwand_specialize x).
    rewrite hstar_comm. applys (hwand_cancel (Q1 x)). }
  { applys himpl_hforall_r. intros x. rewrite* hwand_equiv. }
Qed.


(* ########################################################### *)
(** ** Properties of [hsingle] *)

Lemma hstar_hsingle_same_loc : forall p v1 v2,
  (p ~~> v1) \* (p ~~> v2) ==> \[False].
Proof.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* disjoint_single_single_same_inv.
Qed.
