(***************************************************************************
* Safety for STLC with References - Definitions                            *
* Arthur Chargueraud, July 2007                                            *
***************************************************************************)

Set Implicit Arguments.
From TLC Require Export LibLN.


(* ********************************************************************** *)

(** Grammar of types. *)

Parameter atm : Set.

Inductive typ : Set :=
  | typ_var   : var -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_ref   : typ -> typ
  | typ_int   : typ
  | typ_unit  : typ.

(** Grammar of pre-terms. For simplicity, integers are restricted to naturals. *)

Definition int := nat.

Definition loc := var.

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_unit : trm
  | trm_int : int -> trm
  | trm_loc : loc -> trm
  | trm_ref : trm -> trm
  | trm_get : trm -> trm
  | trm_set : trm -> trm -> trm
  | trm_rand : trm -> trm.

(** Opening up abstractions *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs t1    => trm_abs (open_rec (S k) u t1)
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_unit      => trm_unit
  | trm_int n     => trm_int n
  | trm_loc l     => trm_loc l
  | trm_ref t1    => trm_ref (open_rec k u t1)
  | trm_get t1    => trm_get (open_rec k u t1)
  | trm_set t1 t2 => trm_set (open_rec k u t1) (open_rec k u t2)
  | trm_rand t1   => trm_rand (open_rec k u t1)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).

(** Terms are locally-closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (trm_abs t1)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> term (trm_app t1 t2)
  | term_trm_unit :
      term trm_unit
  | term_int : forall n,
      term (trm_int n)
  | term_loc : forall l,
      term (trm_loc l)
  | term_ref : forall t1,
      term t1 ->
      term (trm_ref t1)
  | term_get : forall t1,
      term t1 ->
      term (trm_get t1)
  | term_set : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_set t1 t2)
  | term_rand : forall t1,
      term t1 ->
      term (trm_rand t1).

(** Store maps (sto) locations to values, and
    Store typing (phi) maps locations to type. *)

Definition sto := LibEnv.env trm.
Definition phi := LibEnv.env typ.

Inductive sto_ok : sto -> Prop :=
  | sto_ok_empty : sto_ok empty
  | sto_ok_push : forall mu l t,
      sto_ok mu -> term t ->
      sto_ok (mu & l ~ t).

(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env typ.


(* ********************************************************************** *)

(** Typing relation *)

Reserved Notation "E ! Y |= t ~: T" (at level 69).

Inductive typing : env -> phi -> trm -> typ -> Prop :=
  | typing_var : forall E Y x T,
      ok E ->
      binds x T E ->
      E ! Y |= (trm_fvar x) ~: T
  | typing_abs : forall L E Y U T t1,
      (forall x, x \notin L -> (E & x ~ U) ! Y  |= t1 ^ x ~: T) ->
      E ! Y |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_app : forall T1 T2 E Y t1 t2,
      E ! Y |= t1 ~: (typ_arrow T1 T2) -> E ! Y  |= t2 ~: T1 ->
      E ! Y  |= (trm_app t1 t2) ~: T2
  | typing_unit : forall E Y,
      ok E ->
      E ! Y |= trm_unit ~: typ_unit
  | typing_int : forall E Y n,
      ok E ->
      E ! Y |= (trm_int n) ~: typ_int
  | typing_loc : forall E Y l T,
      ok E ->
      binds l T Y ->
      E ! Y |= (trm_loc l) ~: (typ_ref T)
  | typing_ref : forall E Y t1 T,
      E ! Y |= t1 ~: T ->
      E ! Y |= (trm_ref t1) ~: (typ_ref T)
  | typing_get : forall E Y t1 T,
      E ! Y |= t1 ~: (typ_ref T) ->
      E ! Y |= (trm_get t1) ~: T
  | typing_set : forall E Y t1 t2 T,
      E ! Y |= t1 ~: (typ_ref T) ->
      E ! Y |= t2 ~: T ->
      E ! Y |= (trm_set t1 t2) ~: typ_unit
  | typing_rand : forall E Y t1,
      E ! Y |= t1 ~: typ_int ->
      E ! Y |= (trm_rand t1) ~: typ_int

where "E ! Y |= t ~: T" := (typing E Y t T).

(** Typing store *)

Definition sto_typing Y mu :=
     sto_ok mu
  /\ (forall l, l # mu -> l # Y)
  /\ (forall l T, binds l T Y ->
        exists t, binds l t mu
               /\ empty ! Y |= t ~: T).

Notation "Y |== mu" := (sto_typing Y mu) (at level 68).

(** Definition of values *)

Inductive value : trm -> Prop :=
  | value_abs : forall t1,
      term (trm_abs t1) ->
      value (trm_abs t1)
  | value_unit :
      value trm_unit
  | value_int : forall n,
      value (trm_int n)
  | value_loc : forall l,
      value (trm_loc l).

(** Reduction relation - one step in call-by-value *)

Definition conf := (trm * sto)%type.

Inductive red : conf -> conf -> Prop :=

  | red_beta : forall mu t1 t2,
      sto_ok mu ->
      term (trm_abs t1) ->
      value t2 ->
      red (trm_app (trm_abs t1) t2, mu) (t1 ^^ t2, mu)
  | red_ref : forall mu t1 l,
      sto_ok mu ->
      value t1 ->
      l # mu ->
      red (trm_ref t1, mu) (trm_loc l, (mu & l ~ t1))
  | red_get : forall mu l t,
      sto_ok mu ->
      binds l t mu ->
      red (trm_get (trm_loc l), mu) (t, mu)
  | red_set : forall mu l t2,
      sto_ok mu ->
      value t2 ->
      red (trm_set (trm_loc l) t2, mu) (trm_unit, mu & l ~ t2)

  | red_app_1 : forall mu mu' t1 t1' t2,
      term t2 ->
      red (t1, mu) (t1', mu') ->
      red (trm_app t1 t2, mu) (trm_app t1' t2, mu')
  | red_app_2 : forall mu mu' t1 t2 t2',
      value t1 ->
      red (t2, mu) (t2', mu') ->
      red (trm_app t1 t2, mu) (trm_app t1 t2', mu')
  | red_ref_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_ref t1, mu) (trm_ref t1', mu')
  | red_get_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_get t1, mu) (trm_get t1', mu')
  | red_set_1 : forall mu mu' t1 t1' t2,
      red (t1, mu) (t1', mu') ->
      term t2 ->
      red (trm_set t1 t2, mu) (trm_set t1' t2, mu')
  | red_set_2 : forall mu mu' t1 t2 t2',
      value t1 ->
      red (t2, mu) (t2', mu') ->
      red (trm_set t1 t2, mu) (trm_set t1 t2', mu')
  | red_rand : forall mu n m,
      sto_ok mu ->
      (0 <= m < max 1 n) ->
      red (trm_rand (trm_int n), mu) ((trm_int m), mu)
  | red_rand_1 : forall mu mu' t1 t1',
      red (t1, mu) (t1', mu') ->
      red (trm_rand t1, mu) (trm_rand t1', mu').

Notation "c --> c'" := (red c c') (at level 68).

(** The goal is to prove type soundness *)

(** [reds c c'] is the reflexive-transitive closure of [red] *)

Inductive reds : conf -> conf -> Prop :=
  | reds_here : forall c,
      term (fst c) ->
      reds c c
  | reds_step : forall c1 c2 c3,
      red c1 c2 ->
      reds c2 c3 ->
      reds c1 c3.

(** Terminal configuration *)

Definition terminal_conf (c:conf) : Prop :=
  value (fst c).

(** Reducible configuration *)

Definition reducible_conf (c:conf) : Prop :=
  exists c', c --> c'.

(** Safety of a configuration *)

Definition safe_conf (c:conf) : Prop :=
  forall c', reds c c' -> terminal_conf c' \/ reducible_conf c'.

(** Well-typed configuration *)

Definition typed_conf (c:conf) : Prop :=
  let '(t,mu) := c in
  exists Y T,
     empty ! Y |= t ~: T
  /\ Y |== mu.

(** Type soundness: starting from a well-typed configuration,
    all accessible configurations are safe *)

Definition soundness : Prop :=
  forall c, typed_conf c -> safe_conf c.

