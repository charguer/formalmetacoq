(***************************************************************************
* Functional Translation of a Calculus of Capabilities - Definitions       *
* Arthur Charguéraud, January 2009, Coq v8.1                               *
***************************************************************************)

Set Implicit Arguments.
Require Export Metatheory.
Implicit Types x : var.

(* --todo: replace k with j in open *)

(* ********************************************************************** *)
(** ** Source language *)

(** Locations *)

Definition loc := var.
Implicit Types l : loc.

(** Grammar of primitive, values and terms *)

Inductive prm : Set :=
  | prm_new  : prm
  | prm_get  : prm
  | prm_set  : prm.

Inductive val : Set :=
  | val_bvar : nat -> val
  | val_fvar : var -> val
  | val_unit : val
  | val_cst  : nat -> val
  | val_loc  : loc -> val
  | val_prm  : prm -> val
  | val_pair : val -> val -> val
  | val_abs  : trm -> val

with trm : Set :=
  | trm_val  : val -> trm
  | trm_app  : val -> trm -> trm.


Notation "'\' v" := (trm_val v) (at level 69).
Coercion trm_val : val >-> trm.
Coercion val_prm : prm >-> val.
Implicit Types v : val.


(** Open on terms *)

Fixpoint trm_open_rec (k : nat) (u : val) (t : trm) {struct t} : trm :=
  match t with
  | trm_val v1    => trm_val (val_open_rec k u v1)
  | trm_app v1 t2 => trm_app (val_open_rec k u v1) (trm_open_rec k u t2)
  end 
with val_open_rec (k : nat) (u : val) (v : val) {struct v} : val :=
  match v with
  | val_bvar i  => if k === i then u else v
  | val_fvar x  => v
  | val_unit    => v
  | val_cst c   => v
  | val_loc l   => v
  | val_prm p   => v
  | val_pair v1 v2 => val_pair (val_open_rec k u v1) (val_open_rec k u v2)
  | val_abs t1  => val_abs (trm_open_rec (S k) u t1)
  end.

Definition trm_open t u := trm_open_rec 0 u t.
Definition trm_open_var t x := trm_open t (val_fvar x).

(* temp
Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).
*)

(** Locally-closed terms *)

Inductive term : trm -> Prop :=
  | term_val : forall v,
      value v ->
      term (trm_val v)
  | term_app : forall v1 t2,
      value v1 -> 
      term t2 -> 
      term (trm_app v1 t2)
with value : val -> Prop :=
  | value_var : forall x,
      value (val_fvar x)
  | value_unit : 
      value val_unit
  | value_cst : forall c,
      value (val_cst c)
  | value_loc : forall l,
      value (val_loc l)
  | value_prm : forall p,
      value (val_prm p)
  | value_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (val_pair v1 v2)
  | value_abs : forall L t1,
      (forall x, x \notin L -> term (trm_open_var t1 x)) ->
      value (val_abs t1).

(** Store *)

Definition sto := env val.

Inductive sto_ok : sto -> Prop :=
  | sto_ok_empty : sto_ok empty
  | sto_ok_push : forall mu l v,
      sto_ok mu -> value v -> 
      sto_ok (mu & l ~ v).

(** Semantics *)

Definition conf := (trm * sto)%type.

Inductive red : conf -> conf -> Prop :=

  | red_beta : forall m t1 v2,
      sto_ok m ->
      value (val_abs t1) -> 
      red (trm_app (val_abs t1) v2, m) (trm_open t1 v2, m)
  | red_new : forall m v1 l,
      sto_ok m ->
      value v1 ->
      l # m ->
      red (trm_app prm_new v1, m) (\(val_loc l), (m & l ~ v1))
  | red_get : forall m l v,
      sto_ok m ->
      binds l v m ->
      red (trm_app prm_get (val_loc l), m) (\v, m)
  | red_set : forall m l v2,
      sto_ok m ->
      value v2 ->
      red (trm_app prm_set (val_pair (val_loc l) v2), m) (\val_unit, m & l ~ v2)
  | red_app_2 : forall m m' v1 t2 t2',
      value v1 ->
      red (t2, m) (t2', m') ->
      red (trm_app v1 t2, m) (trm_app v1 t2', m').


(* ********************************************************************** *)
(** ** Target language *)

(** Grammar of Values and Terms *)

Inductive Prm : Set :=
  | Prm_fst  : Prm
  | Prm_snd  : Prm.

Inductive Val : Set :=
  | Val_bvar : nat -> Val
  | Val_fvar : var -> Val
  | Val_prm  : Prm -> Val
  | Val_unit : Val
  | Val_cst  : nat -> Val
  | Val_pair : Val -> Val -> Val
  | Val_abs  : Trm -> Val

with Trm : Set :=
  | Trm_val  : Val -> Trm
  | Trm_app  : Val -> Trm -> Trm.

Coercion Val_prm : Prm >-> Val.
Coercion Trm_val : Val >-> Trm.
Implicit Types V : Val.

Definition Trm_apps T1 T2 :=
  Trm_app (Val_abs (Trm_app (Val_bvar 0) T2)) T1.  
Definition Val_pairs T1 V2 :=
  Trm_app (Val_abs (Val_pair (Val_bvar 0) V2)) T1.  
Definition Trm_lets2 T x:=
  Trm_apps (Trm_app (Val_abs (Val_abs T)) 
     (Trm_app Prm_fst (Val_fvar x)))
     (Trm_app Prm_snd (Val_fvar x)). 


(** Open on Terms *)

Fixpoint Trm_open_rec (K : nat) (U : Val) (T : Trm) {struct T} : Trm :=
  match T with
  | Trm_val V1    => Trm_val (Val_open_rec K U V1)
  | Trm_app V1 T2 => Trm_app (Val_open_rec K U V1) (Trm_open_rec K U T2)
  end 
with Val_open_rec (K : nat) (U : Val) (V : Val) {struct V} : Val :=
  match V with
  | Val_bvar i  => if K === i then U else V
  | Val_fvar X  => V
  | Val_prm P   => V
  | Val_unit    => V
  | Val_cst C   => V
  | Val_pair V1 V2 => Val_pair (Val_open_rec K U V1) (Val_open_rec K U V2)
  | Val_abs T1  => Val_abs (Trm_open_rec (S K) U T1)
  end.

Definition Trm_open T U := Trm_open_rec 0 U T.
Definition Trm_open_var T X := Trm_open T (Val_fvar X).

(** Locally-closed Terms *)

Inductive Term : Trm -> Prop :=
  | Term_Val : forall V,
      Value V ->
      Term (Trm_val V)
  | Term_app : forall V1 T2,
      Value V1 -> 
      Term T2 -> 
      Term (Trm_app V1 T2)
with Value : Val -> Prop :=
  | Value_var : forall X,
      Value (Val_fvar X)
  | Value_prm : forall P,
      Value (Val_prm P)
  | Value_unit : 
      Value Val_unit
  | Value_cst : forall C,
      Value (Val_cst C)
  | Value_pair : forall V1 V2,
      Value V1 ->
      Value V2 ->
      Value (Val_pair V1 V2)
  | Value_abs : forall L T1,
      (forall X, X \notin L -> Term (Trm_open_var T1 X)) ->
      Value (Val_abs T1).

(** Semantics *)

Inductive Red : Trm -> Trm -> Prop :=
  | Red_beta : forall T1 V2,
      Value (Val_abs T1) ->
      Value V2 ->
      Red (Trm_app (Val_abs T1) V2) (Trm_open T1 V2)
  | Red_app_2 : forall V1 T2 T2',
      Value V1 ->
      Red T2 T2' ->
      Red (Trm_app V1 T2) (Trm_app V1 T2').


(* ********************************************************************** *)
(** ** Typing entities *)

(** Grammar of kinds *)

Inductive kind : Set :=
  | kind_val : kind
  | kind_cmp : kind
  | kind_mem : kind 
  | kind_cap : kind
  | kind_sng : kind.

(*   | kind_grp : kind *)

(** Grammar of syntactic types objects *)

Inductive obj : Set :=
  | obj_bvar   : kind -> nat -> obj
  | obj_fvar   : kind -> var -> obj
  | obj_top    : obj
  | obj_unit   : obj
  | obj_arrow  : obj -> obj -> obj
  | obj_star   : obj -> obj -> obj
  | obj_prod   : obj -> obj -> obj
  | obj_ref    : obj -> obj
  | obj_at     : obj -> obj
  | obj_nocap  : obj
  | obj_sng    : obj -> obj -> obj
  | obj_exists : kind -> obj -> obj.
(* 
  | obj_prod
  | obj:
  | obj_grp    : obj -> obj 
  | obj_bot    : obj
  | obj_forall : obj -> obj
*)

(** Open on objects *)

Fixpoint obj_open_rec (j : nat) (u : obj) (o : obj) {struct o} : obj :=
  match o with
  | obj_bvar k i => if j === i then u else o
  | obj_fvar k x => o
  | obj_top      => o
  | obj_unit     => o
  | obj_arrow o1 o2 => obj_arrow (obj_open_rec j u o1) (obj_open_rec j u o1)
  | obj_star o1 o2  => obj_star (obj_open_rec j u o1) (obj_open_rec j u o1)
  | obj_prod o1 o2  => obj_prod (obj_open_rec j u o1) (obj_open_rec j u o1)
  | obj_ref o1      => obj_ref (obj_open_rec j u o1)
  | obj_at o1       => obj_at (obj_open_rec j u o1)
  | obj_nocap       => o
  | obj_sng o1 o2   => obj_sng (obj_open_rec j u o1) (obj_open_rec j u o1)
  | obj_exists k1 o1 => obj_exists k1 (obj_open_rec (S j) u o1)
  end.

Definition obj_open o u := obj_open_rec 0 u o.
Definition obj_open_var o k x := obj_open o (obj_fvar k x).

(** Local closure *)

Parameter Obj : obj -> Prop. (* todo *)

(** Well-kindedness *)

Reserved Notation "o :: k" (at level 69).

Inductive kinds : obj -> kind -> Prop :=
  | kinds_var : forall x k,
      (obj_fvar k x) :: k
  | kinds_top : 
      obj_top :: kind_val
  | kinds_unit :
      obj_unit :: kind_val
  | kinds_arrow : forall o1 o2,
      o1 :: kind_cmp ->
      o2 :: kind_cmp ->
      (obj_arrow o1 o2) :: kind_val
  | kinds_star : forall o1 o2 k,
      (k = kind_mem \/ k = kind_cap \/ k = kind_cmp) ->
      o1 :: k ->
      o2 :: kind_cap ->
      (obj_star o1 o2) :: k
  | kinds_prod : forall o1 o2 k,
      (k = kind_val \/ k = kind_mem) ->
      o1 :: k ->
      o2 :: k ->
      (obj_prod o1 o2) :: k
  | kinds_ref : forall o1,
      o1 :: kind_mem ->
      (obj_ref o1) :: kind_mem
  | kinds_at : forall o1,
      o1 :: kind_sng ->
      (obj_at o1) :: kind_val
  | kinds_nocap : 
      obj_nocap :: kind_cap
  | kinds_sng : forall o1 o2,
      o1 :: kind_sng ->
      o2 :: kind_mem ->
      (obj_sng o1 o2) :: kind_cap
  | kinds_exists : forall L o1 k1 k2 k,
      (k1 = kind_val \/ k1 = kind_mem \/ k1 = kind_cap \/ k1 = kind_sng) ->
      (k2 = kind_val \/ k2 = kind_mem \/ k2 = kind_cap) ->
      (forall x, x \notin L -> (obj_open_var o1 k1 x) :: k) ->
      (obj_exists k1 o1) :: k

where "o :: k" := (kinds o k).

(** Environments *)

Definition ctx := env obj.

Inductive dnv : ctx -> Prop :=
  | dnv_empty : 
     dnv empty
  | dnv_cons : forall D x o,
     dnv D ->
     o :: kind_val ->
     dnv (D & x ~ o).

Inductive lnv : ctx -> Prop :=
  | lnv_dnv : forall D,
     dnv D ->
     lnv D
  | lnv_cons : forall E x o k,
     (k = kind_val \/ k = kind_cmp \/ k = kind_cap) -> 
     lnv E ->
     o :: k ->
     lnv (E & x ~ o).


(* ********************************************************************** *)
(** ** Typing and translation rules *)

Definition tau := obj.
Definition mem := obj.
Definition cap := obj.
Definition chi := obj.
Definition rgn_sng s := obj_fvar kind_sng s.

Definition shp := env val.

Parameter shp_ok : shp -> Prop.

(** For subtyping operations *)

Parameter sub : obj -> obj -> Val -> Prop.

(** For values and terms *)

Inductive tval : shp -> ctx -> val -> tau -> Val -> Prop :=
  | tval_top : forall S D v V,
     shp_ok S ->
     dnv D ->
     tval S D v obj_top V 
  | tval_unit : forall S D,
     shp_ok S ->
     dnv D ->
     tval S D val_unit obj_unit Val_unit
  | tval_pair : forall S D v1 v2 tau1 tau2 V1 V2,
     tval S D v1 tau1 V1 ->
     tval S D v2 tau2 V2 ->
     tval S D (val_pair v1 v2) (obj_prod tau1 tau2) (Val_pair V1 V2)
  | tval_var : forall S D x tau,
     shp_ok S ->
     dnv D ->
     binds x tau D ->
     tval S D (val_fvar x) tau (Val_fvar x)
  | tval_sng : forall S D s v,
     shp_ok S ->
     dnv D ->
     binds s v S ->
     tval S D v (obj_at (rgn_sng s)) Val_unit
  | tval_abs : forall L S D t1 chi1 chi2 T1,
     dnv D ->
     chi1 :: kind_cmp ->
     (forall x, x \notin L ->
       ttrm S (D & x ~ chi1) (trm_open_var t1 x) chi2 (Trm_open_var T1 x)) ->
     tval S D (val_abs t1) (obj_arrow chi1 chi2) (Val_abs T1)

with ttrm : shp -> ctx -> trm -> chi -> Trm -> Prop :=
  | ttrm_val : forall S D v tau V,
     tval S D v tau V ->
     ttrm S D (trm_val v) tau V
  | ttrm_app : forall chi1 chi2 S D E v1 t2 T1 T2,
     ttrm S D v1 (obj_arrow chi1 chi2) T1 ->
     ttrm S (D & E) t2 chi1 T2 ->
     ttrm S (D & E) (trm_app v1 t2) chi2 (Trm_apps T1 T2)
  | ttrm_sub : forall chi1 chi2 S E t T V,
     ttrm S E t chi1 T ->
     sub chi1 chi2 V ->
     ttrm S E t chi2 (Trm_app V T)
  | ttrm_star_intro : forall S E t chi T x C,
     ttrm S E t chi T ->
     C :: kind_cap ->
     ttrm S (E & x ~ C) t (obj_star chi C) (Val_pairs T (Val_fvar x))
  | ttrm_star_elim : forall x1 x2 S E x o1 C t chi T,
     ttrm S (E & x1 ~ o1 & x2 ~ C) t chi (Trm_open_var (Trm_open_var T x1) x2) ->
     ttrm S (E & x ~ (obj_star o1 C)) t chi (Trm_lets2 T x).

  (* pb: types of polymorphic primitives... *)
 


(* ********************************************************************** *)
(** ** Extra definitions for the proof *)

(** Substitution *)

Parameter val_subst : var -> val -> val -> val.
Parameter trm_subst : var -> val -> trm -> trm.
Parameter Val_subst : var -> Val -> Val -> Val.
Parameter Trm_subst : var -> Val -> Trm -> Trm.

(** Typing of capabilities and memory types *)

Definition locs := vars. (* fset loc. *)
Definition rgns := vars. (* fset rgn. *)

Parameter tcap : sto -> shp -> cap -> locs -> Val -> Prop.
Parameter tmem : sto -> shp -> val -> mem -> locs -> Val -> Prop.

(** Typing at runtime *)

Parameter texe : sto -> shp -> trm -> chi -> locs -> Trm -> Prop.
Parameter tout : sto -> shp -> val -> chi -> locs -> Val -> Prop.

  (* temp "rgns" arguments not necessary for singleton regions *)

(** Preservation of regions *)

Definition shp_kept (S1 S2 : shp) :=
  forall s v, binds s v S1 -> binds s v S2.

(** Preservation of protected state *)

Definition sto_kept (m1 m2 : sto) (L : locs) :=
  forall l v, l \in L -> binds l v m1 -> binds l v m2.

(** Preservation outside used state *)

Definition sto_modif (m1 m2 : sto) (L1 L2 : locs) :=
  forall l v, l \notin L1 -> binds l v m1 -> 
   binds l v m2 /\ l \notin L2.



