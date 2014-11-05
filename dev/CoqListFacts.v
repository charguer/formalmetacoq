Require Import List. 

(*****************************************************************************)
(** * Notations*)

(** Notation for "cons at the back of a list" *)

Notation "l & x" := (l ++ (x::nil)) (at level 28) : list_scope.
Open Local Scope list_scope.


(*****************************************************************************)
(** * Lemmas *)

(*****************************************************************************)
(** ** Properties of [append] *)

Section Append.
Variable A B : Type.
Implicit Types x : A.
Implicit Types l : list A.
Lemma app_cons : forall x l1 l2,
  (x::l1) ++ l2 = x::(l1++l2).
Proof. auto. Qed.
Lemma app_nil_l : forall l,
  nil ++ l = l.
Proof. auto. Qed.
Lemma app_nil_r : forall l,
  l ++ nil = l.
Proof. induction l. auto. rewrite app_cons. f_equal. auto. Qed.
Lemma app_assoc : forall l1 l2 L3,
  (l1 ++ l2) ++ L3 = l1 ++ (l2 ++ L3).
Proof. 
  intros. induction l1.
  rewrite ? app_nil_l. auto.
  rewrite ? app_cons. f_equal. auto.
Qed.
Lemma app_last : forall x l1 l2,
  l1 ++ (x::l2) = (l1 & x) ++ l2.
Proof. intros. rewrite app_assoc. auto. Qed.
Lemma app_last_sym : forall x l1 l2,
  (l1 & x) ++ l2 = l1 ++ (x::l2).
Proof. intros. rewrite <- app_last. auto. Qed.
Lemma app_cons_one : forall x l,
  (x::nil) ++ l = x::l.
Proof. auto. Qed.
End Append.

(*****************************************************************************)
(** ** Properties of [fold_right] *)

Section FoldRight.
Variable A B : Type.
Variables (f : A -> B -> B) (i : B).
Lemma fold_right_nil : 
  fold_right f i nil = i.
Proof. auto. Qed.
Lemma fold_right_cons : forall x l,
  fold_right f i (x::l) = f x (fold_right f i l) .
Proof. auto. Qed.
Lemma fold_right_app : forall l1 l2,
  fold_right f i (l1 ++ l2) = fold_right f (fold_right f i l2) l1.
Proof.
  intros. induction l1. auto. 
  rewrite app_cons. simpl. f_equal. auto.
Qed.
Lemma fold_right_last : forall x l,
  fold_right f i (l & x) = fold_right f (f x i) l.
Proof. intros. rewrite fold_right_app. auto. Qed.
End FoldRight.

(*****************************************************************************)
(** ** Properties of [fold_left] *)

Section FoldLeft.
Variable A B : Type.
Variables (f : B -> A -> B) (i : B).
Lemma fold_left_nil : 
  fold_left f nil i = i.
Proof. auto. Qed.
Lemma fold_left_cons : forall x l,
  fold_left f (x::l) i = fold_left f l (f i x).
Proof. auto. Qed.
Lemma fold_left_app : forall l1 l2,
  fold_left f (l1 ++ l2) i = fold_left f l2 (fold_left f l1 i).
Proof.
  intros. generalize i. induction l1; intros. auto. 
  rewrite app_cons. simpl. rewrite IHl1. auto.
Qed.
Lemma fold_left_last : forall x l,
  fold_left f (l & x) i = f (fold_left f l i) x.
Proof. intros. rewrite fold_left_app. auto. Qed.
End FoldLeft.

Implicit Arguments fold_left [A B].
Implicit Arguments fold_right [A B].

(*****************************************************************************)
(** ** Properties of [length] *)

Section Length.
Variable A B : Type.
Implicit Types x : A.
Implicit Types l : list A.
Lemma length_nil : 
  length (@nil A) = 0.
Proof. auto. Qed.
Lemma length_cons : forall x l,
  length (x::l) = 1 + length l.
Proof. auto. Qed.
Lemma length_app : forall l1 l2,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1; simpl; auto.
Qed.
Lemma length_last : forall x l,
  length (l & x) = length l + 1.
Proof. 
  intros. rewrite length_app.
  rewrite length_cons. rewrite length_nil. auto.
Qed.
End Length.

(*****************************************************************************)
(** ** Properties of [rev] *)

Section Rev.
Variable A B : Type.
Implicit Types x : A.
Implicit Types l : list A.
Lemma rev_nil : 
  rev (@nil A) = nil.
Proof. auto. Qed.
Lemma rev_app : forall l1 l2,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. intros. apply distr_rev. Qed. (*uses lib*)
Lemma rev_cons : forall x l,
  rev (x::l) = rev l & x.
Proof. intros. rewrite <- app_cons_one. rewrite rev_app. auto. Qed.
Lemma rev_last : forall x l,
  rev (l & x) = x::(rev l).
Proof. intros. rewrite rev_app. auto. Qed.
Lemma rev_cons_app : forall x l1 l2,
  rev (x :: l1) ++ l2 = rev l1 ++ (x::l2).
Proof. intros. rewrite rev_cons. rewrite <- app_last. auto. Qed.
End Rev.

(*****************************************************************************)
(** ** Properties of [rev] *)

Section Map.
Variables A B : Type.
Variable f : A -> B.
Lemma map_nil : 
  map f nil = nil.
Proof. auto. Qed.
Lemma map_cons : forall x l,
  map f (x::l) = f x :: map f l.
Proof. auto. Qed.
Lemma map_app : forall l1 l2,
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof. intros. apply map_app. Qed.
Lemma map_last : forall x l,
  map f (l & x) = map f l & f x.
Proof. intros. rewrite map_app. auto. Qed.
End Map.



(*****************************************************************************)
(** * Autorewrite facilities *)

(*****************************************************************************)
(** ** Rewrite databases *)

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc app_cons_one 
  : rew_app. (* not used: app_last *)
Hint Rewrite fold_right_nil fold_right_cons fold_right_app fold_right_last 
  : rew_foldr.
Hint Rewrite fold_left_nil fold_left_cons fold_left_app fold_left_last 
  : rew_foldl.
Hint Rewrite length_nil length_cons length_app length_last 
  : rew_length.
Hint Rewrite rev_nil rev_app rev_cons rev_last 
  : rew_rev. (* not used: rev_cons_app *)
Hint Rewrite map_nil map_cons map_app map_last 
  : rew_map.
Hint Rewrite 
  app_cons app_nil_l app_nil_r app_assoc app_cons_one 
  fold_right_nil fold_right_cons fold_right_app fold_right_last 
  fold_left_nil fold_left_cons fold_left_app fold_left_last 
  length_nil length_cons length_app length_last 
  rev_nil rev_app rev_cons rev_last 
  map_nil map_cons map_app map_last
  : rew_list.

(*****************************************************************************)
(** ** Tactic notations *)

Tactic Notation "calc_app" :=
  autorewrite with rew_app.
Tactic Notation "calc_app" "in" hyp(H) :=
  autorewrite with rew_app in H.
Tactic Notation "calc_app" "in" "*" :=
  autorewrite with rew_app in *.

Tactic Notation "calc_length" :=
  autorewrite with rew_length.
Tactic Notation "calc_length" "in" hyp(H) :=
  autorewrite with rew_length in H.
Tactic Notation "calc_length" "in" "*" :=
  autorewrite with rew_length in *.

Tactic Notation "calc_map" :=
  autorewrite with rew_map rew_app.
Tactic Notation "calc_map" "in" hyp(H) :=
  autorewrite with rew_map rew_app in H.
Tactic Notation "calc_map" "in" "*" :=
  autorewrite with rew_map rew_app in *.

Tactic Notation "calc_foldr" :=
  autorewrite with rew_foldr rew_app.
Tactic Notation "calc_foldr" "in" hyp(H) :=
  autorewrite with rew_foldr rew_app in H.
Tactic Notation "calc_foldr" "in" "*" :=
  autorewrite with rew_foldr rew_app in *.

Tactic Notation "calc_foldl" :=
  autorewrite with rew_foldl rew_app.
Tactic Notation "calc_foldl" "in" hyp(H) :=
  autorewrite with rew_foldl rew_app in H.
Tactic Notation "calc_foldl" "in" "*" :=
  autorewrite with rew_foldl rew_app in *.
Tactic Notation "calc_rev" :=
  autorewrite with rew_rev rew_app.
Tactic Notation "calc_rev" "in" hyp(H) :=
  autorewrite with rew_rev rew_app in H.
Tactic Notation "calc_rev" "in" "*" :=
  autorewrite with rew_rev rew_app in *.

Tactic Notation "calc_map" :=
  autorewrite with rew_map rew_app.
Tactic Notation "calc_map" "in" hyp(H) :=
  autorewrite with rew_map rew_app in H.
Tactic Notation "calc_map" "in" "*" :=
  autorewrite with rew_map rew_app in *.

Tactic Notation "calc_list" :=
  autorewrite with rew_list.
Tactic Notation "calc_list" "in" hyp(H) :=
  autorewrite with rew_list in H.
Tactic Notation "calc_list" "in" "*" :=
  autorewrite with rew_list in *.


(*****************************************************************************)
(** * Demos *)

Lemma demo_length : forall (A:Type) a b c d x y (z:A),
  length ((((a ++ b) & x) ++ (c ++ d) & y) & z) > 0 -> 
  length (x::nil) > 0.
Proof.
  intros. calc_length in *. auto.
Qed.

Lemma demo_map : forall (A B:Type) (f:A->B) a b c d x y z,
  map f (((a ++ b) & x) ++ (c ++ d) & y) = z -> True.
Proof.
  intros. calc_map in H. auto.
Qed.

Lemma demo_list : forall (A B:Type) (f:A->B) a b x,
  map f (rev ((a ++ b) & x)) =
  f x :: map f (rev b) ++ map f (rev a).
Proof.
  intros. calc_list. reflexivity.
Qed.


