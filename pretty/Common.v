(************************************************************
* Wrapper around the library TLC                            *
*************************************************************)

Set Implicit Arguments.
From TLC Require Export LibTactics LibCore LibVar LibEnv.
Generalizable Variables A B.

(** Extension to [LibNat] *)

Definition max (n m:nat) :=
  If n < m then m else n.

Lemma max_cases : forall n m,
  (n <= m /\ max n m = m) \/
  (m <= n /\ max n m = n).
Proof.
  intros. unfold max. case_if.
  left. math.
  right. math.
Qed.

(** Extension to [LibRelation *)

CoInductive infclosure A (R:binary A) : A -> Prop :=
  | infclosure_step : forall y x,
      R x y -> infclosure R y -> infclosure R x.
