(***************************************************************************
* Functional Translation of a Calculus of Capabilities - Definitions       *
* Arthur Charguéraud, January 2009, Coq v8.1                               *
***************************************************************************)

Set Implicit Arguments.
Require Export Eff_Infrastructure.
Implicit Types x : var.

Axiom subset_notin : forall (E F : locs) x,
  F << E -> x \notin E -> x \notin F.

Axiom subset_trans : forall (F E G : locs),
  E << F -> F << G -> E << G.

Axiom disjoint_in_notin : forall (E F : locs) x,
  disjoint E F -> x \in E -> x \notin F.

(* todo: le applys in doit marcher modulo unfold *)
(* todo: forwards sur pattern *)


(* ********************************************************************** *)
(** ** Facts about preservation *)

Lemma shp_kept_refl : forall S,
  shp_kept S S.
Proof. intros_all~. Qed.

Lemma shp_kept_trans : forall S2 S1 S3,
  shp_kept S1 S2 -> 
  shp_kept S2 S3 -> 
  shp_kept S1 S3.
Proof. intros_all~. Qed.

Lemma sto_kept_refl : forall M L,
  sto_kept M M L.
Proof. intros_all~. Qed.

Lemma sto_kept_subset : forall M1 M2 L L',
  sto_kept M1 M2 L ->
  L' << L ->
  sto_kept M1 M2 L'.
Proof. intros_all~. Qed.

Lemma sto_modif_refl : forall M L1 L2,
  L2 << L1 ->
  sto_modif M M L1 L2.
Proof. intros_all~. auto* subset_notin. Qed.

Lemma sto_modif_trans : forall M2 L2 M1 L1 M3 L3,
  sto_modif M1 M2 L1 L2 -> 
  sto_modif M2 M3 L2 L3 -> 
  sto_modif M1 M3 L1 L3.
Proof. introv H1 H2 N B. forwards* [? ?]: (H1 l). Qed.

Lemma sto_modif_extend : forall M1 M2 L1 L2 L',
  sto_modif M1 M2 L1 L2 -> 
  sto_modif M1 M2 (L1 \u L') (L2 \u L').
Proof. introv M N B. forwards* [? ?]: (M l). Qed.

Lemma sto_kept_outside_modif : forall M1 M2 L1 L2 L',
  disjoint L' L1 ->  (* disjoint L' L2 -> *)
  sto_modif M1 M2 L1 L2 -> 
  sto_kept M1 M2 L'.
Proof.
  introv D M N B. forwards* [? ?]: (M l).
  apply* disjoint_in_notin. 
Qed.


(* ********************************************************************** *)
(** ** Weakening and substitution *)

Hint Constructors tval ttrm.

Ltac go := unfold ltac_tag_subst in *|-.

Hint Extern 1 (ok _) => skip.
Hint Extern 1 (lnv _) => skip.
Hint Extern 1 (dnv _) => skip.

Ltac introz :=
  match goal with
  | |- (ltac_tag_subst (?x = ?y) -> ?Q) =>
     let H := fresh "Aux" in 
     intro H; unfold ltac_tag_subst in H;
     try subst x; introz
  | |- ?P -> ?Q => 
     let H := fresh "Hyp" in
     intro H; unfold ltac_tag_subst in H; introz
  | |- forall _, _ => 
     intro; introz
  | |- _ => idtac
  end.

Lemma weaken_val_trm : 
  (forall S D1 D2 D3 v tau V,
  tval S (D1 & D3) v tau V ->
  dnv (D1 & D2 & D3) ->
  tval S (D1 & D2 & D3) v tau V)
  /\ 
  (forall S E1 E2 E3 t chi T,
  ttrm S (E1 & E3) t chi T->
  lnv (E1 & E2 & E3) ->
  ttrm S (E1 & E2 & E3) t chi T).
Proof.
  sets P: (fun S D v tau V (Typ: tval S D v tau V) =>
    forall D1 D2 D3,
    ltac_tag_subst (D = D1 & D3) -> 
    dnv (D1 & D2 & D3) ->
    tval S (D1 & D2 & D3) v tau V).
  sets Q: (fun S E t chi T (Typ: ttrm S E t chi T) =>
    forall E1 E2 E3,
    ltac_tag_subst (E = E1 & E3) ->
    lnv (E1 & E2 & E3) ->
    ttrm S (E1 & E2 & E3) t chi T).
  (* lets: (@tval_ttrm_induct P Q).*)
  cuts [H1 H2]: ((forall S D v tau V (Typ: tval S D v tau V), P S D v tau V Typ)
     /\ (forall S E t chi T (Typ: ttrm S E t chi T), Q S E t chi T Typ)).
   subst P Q. unfolds ltac_tag_subst. simpls*.
   subst P Q. 
  apply tval_ttrm_induct; go; introz.
  auto.
  auto.
  auto.
  apply* tval_var. apply* binds_weaken.
  auto.
  apply_fresh* tval_abs. apply_ih_bind* Hyp2.
  auto.
  apply* ttrm_app. skip. (* env lemma *)
  eauto.
  skip. (* env lemma *)
  skip. (* env lemma *)
Qed.

Parameter subst_val : forall x S D1 D2 v tau V v1 tau1 V1,
  tval S D1 v1 tau1 V1 ->
  tval S (D1 & x ~ tau1 & D2) v tau V ->
  tval S (D1 & D2) (val_subst x v1 v) tau (Val_subst x V1 V).

Parameter subst_trm : forall x S D1 E2 T chi v1 tau1 V1 t,
  tval S D1 v1 tau1 V1 ->
  ttrm S (D1 & x ~ tau1 & E2) t chi T ->
  ttrm S (D1 & E2) (trm_subst x v1 t) chi (Trm_subst x V1 T).

Parameter subst_out : forall m S x chi t chi' T L v V,
  ttrm S (x ~ chi) t chi' T ->
  tout m S v chi L V ->
  exist S' L' T',
     texe m S (trm_subst x v t) chi' L' T'
  /\ star Red (Trm_subst x V T) T'
  /\ shp_kept S S'
  /\ sto_modif m m L L'.


(* ********************************************************************** *)
(** ** Type substitution *)

  (* -- type substitution preserves all judgments... *)


(* ********************************************************************** *)
(** ** Stability *)

Parameter stable_val : forall S S' D v tau V,
  tval S D v tau V ->
  shp_kept S S' ->
  tval S' D v tau V.

Parameter stable_trm : forall S S' E t chi T,
  tval S E t chi T ->
  shp_kept S S' ->
  tval S' E t chi T.

Parameter stable_cap : forall m m' S S' C L V,
  tcap m S C L V ->
  shp_kept S S' ->
  sto_kept m m' L ->
  tcap m' S' C L V.

Parameter stable_mem : forall m m' S S' v tta L V,
  tmem m S v tta L V ->
  shp_kept S S' ->
  sto_kept m m' L ->
  tmem m' S' v tta L V.


(* ********************************************************************** *)
(** ** Subtyping *)

Parameter mem_to_val : forall m S v tau V,
   tmem m S v tau {} V ->
   tval S empty v tau V.

Parameter reduce_sub_val : forall tau1 tau2 V S v V1,
  sub tau1 tau2 V ->
  tval S empty v tau1 V1 ->
  exists V2',
     plus Red (Trm_app V V1) (Trm_val V2')
  /\ tval S empty v tau2 V2'.

Parameter reduce_sub_cap : forall C1 C2 V m S V1 L,
  sub C1 C2 V ->
  tcap m S C1 L V1 ->
  exist S' L' V2',
     plus Red (Trm_app V V1) (Trm_val V2')
  /\ tcap m S' C2 L' V2'
  /\ shp_kept S S' 
  /\ sto_modif m m L L'.

Parameter reduce_sub_mem : forall tta1 tta2 V m S v V1 L,
  sub tta1 tta2 V ->
  tmem m S v tta1 L V1 ->
  exist S' L' V2',
     plus Red (Trm_app V V1) (Trm_val V2')
  /\ tmem m S' v tta2 L' V2'
  /\ shp_kept S S' 
  /\ sto_modif m m L L'.

Parameter reduce_sub_out : forall chi1 chi2 V m S v V1 L,
  sub chi1 chi2 V ->
  tout m S v chi1 L V1 ->
  exist S' L' V2',
     plus Red (Trm_app V V1) (Trm_val V2')
  /\ texe m S' v chi2 L' V2'
  /\ shp_kept S S' 
  /\ sto_modif m m L L'.


(* ********************************************************************** *)
(** ** Reduction *)

Parameter reduction : forall m m' t' S L v1 v2 V1 V2 chi1 chi2,
  red (trm_app v1 (\v2), m) (t', m') ->
  tval S empty v1 (obj_arrow chi1 chi2) V1 ->
  tout m S v2 chi1 L V2 ->
  exist S' L' T',
     star Red (Trm_app V1 V2) T'
  /\ texe m' S' t' chi2 L' T'
  /\ shp_kept S S'
  /\ sto_modif m m' L L'.

Parameter termination : forall m v S L T chi,
  texe m S v chi L T ->
  exist S' L' V',
     plus Red T V'
  /\ texe m S' v chi L' V'
  /\ shp_kept S S'
  /\ sto_modif m m L L'.

Parameter simulation : forall m m' t t' S L T chi,
  red (t, m) (t', m') ->
  texe m S t chi L T ->
  exist S' L' T',
     plus Red T T'
  /\ texe m' S' t' chi L' T'
  /\ shp_kept S S'
  /\ sto_modif m m' L L'.

