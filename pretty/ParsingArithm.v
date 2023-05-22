Set Implicit Arguments.
Require Import Shared.
From Coq Require Import String.
Open Scope string_scope.


(************************************************************)
(* * Extra stuff *)

(** For lists *)

Generalizable Variables A.

Fixpoint mem_decide `{Comparable A} x (l:list A) :=
  match l with
  | nil => false
  | x'::l' => if decide (x = x') then true else mem_decide x l'
  end.

Instance Mem_decidable : forall `{Comparable A} x (l:list A),
  Decidable (Mem x l).
Proof.
  introv C. intros. applys decidable_make (mem_decide x l).
  induction l; simpl; extens; rew_refl in *.
  iff M.
    false.
    inverts M.
  rewrite IHl. case_if; fold_bool; rew_refl in *.
    subst. iff M. constructors*. auto.
    iff M. constructors*. inverts* M.
Qed.

Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.
Open Scope list_scope.


(** For int *)

Require Import Zcompare.

Instance lt_decidable : forall (n m : int),
  Decidable (n < m).
Proof.
  intros.
  sets b: (match Zcompare n m with Datatypes.Lt => true | _ => false end).
  applys decidable_make b.
  skip. (* TODO *)
Qed.

(** For string *)

(** [l1 ~ l2] concatenates two strings *)

Infix "~~" := append (right associativity, at level 60) : mystring_scope.
Open Scope mystring_scope.


Definition char := Ascii.ascii.
Definition char_dec := Ascii.ascii_dec.

Instance char_comparable : Comparable char.
Proof. applys comparable_of_dec char_dec. Qed.

Axiom append_empty_r : forall s,
  s ~~ EmptyString = s.
Axiom append_empty_l : forall s,
  EmptyString ~~ s = s.
Axiom append_assoc : assoc append.

Parameter string_of_int : int -> string.

Definition empty_string := "".

Definition concat (ss:list string) : string :=
  fold_right append empty_string ss.

Coercion string_of_char (c:char) : string :=
  String c EmptyString.


(************************************************************)
(* * Grammar of arithmetic expressions *)

Inductive binop :=
  | binop_add : binop
  | binop_mul : binop
  | binop_sub : binop.

Inductive unop :=
  | unop_neg : unop.

Inductive exp :=
  | exp_int : int -> exp
  | exp_unop : unop -> exp -> exp
  | exp_binop : binop -> exp -> exp -> exp.

Implicit Types e : exp.


(************************************************************)
(* * Evaluation of arithmetic expressions *)

(** --Not used in this file-- *)

Fixpoint value e :=
  match e with
  | exp_int n => n
  | exp_unop op e =>
     let v := value e in
     match op with
     | unop_neg => - v
     end
  | exp_binop op e1 e2 =>
     let v1 := value e1 in
     let v2 := value e2 in
     match op with
     | binop_add => v1 + v2
     | binop_sub => v1 - v2
     | binop_mul => v1 * v2
     end
  end.


(************************************************************)
(* * Syntax of arithmetic expressions *)

(** Priorities (use only even ones) *)

(** Alan: I'd put prio_neg as smallest priority:
# -2 * 3;;
- : int = -6
# 3 * -2;;
- : int = -6
 *)

Definition prio := int.
Definition prio_max := 8.
Definition prio_neg := 6.
Definition prio_add := 4.
Definition prio_sub := 4.
Definition prio_mul := 2.
Definition prio_par := 0.

(** String representation of symbols *)

Definition symb_neg := "-".
Definition symb_add := "+".
Definition symb_sub := "-".
Definition symb_mul := "*".

Definition symb_space := " ".
Definition symb_tab := "	".
Definition symb_par_open := "(".
Definition symb_par_close := ")".

(** Spacing characters *)

Definition spacing_tokens :=
  [ symb_space ; symb_tab ].

Definition spacing s :=
  Mem s spacing_tokens.

(** [spacings s] asserts that [s] is a string made only
     of spacing tokens *)

Inductive spacings : string -> Prop :=
  | spacings_empty :
     spacings EmptyString
  | spacings_string : forall s ss,
     spacing s ->
     spacings ss ->
     spacings (s ~~ ss).

(** [separ ss r] asserts that the list [r] is equal
    obtained as the concatenation of the strings in [ss],
    possibly separated by strings satisfying [spacings],
    including separations at the front and at the tail. *)

Inductive separ : list string -> string -> Prop :=
  | separ_nil : forall g,
      spacings g ->
      separ nil g
  | separ_cons : forall s ss g r,
      separ ss r ->
      spacings g ->
      separ (s::ss) (g ~~ s ~~ r).

(** Specification of a valide representation of an expresion:
    [repr p e s] asserts that [s] is a valid representation of
    [e], in a context where operators with priority less than
    [p] can be represented without parenthesis. *)

Inductive repr : int -> exp -> string -> Prop :=
  | repr_int : forall p n r,
      separ [string_of_int n] r ->
      repr p (exp_int n) r
  | repr_neg : forall p e1 r1 r,
      repr prio_neg e1 r1 ->
      prio_neg < p ->
      separ [symb_neg ; r1] r ->
      repr p (exp_unop unop_neg e1) r
  | repr_add : forall p e1 e2 r1 r2 r,
      repr (prio_add+1) e1 r1 ->
      repr (prio_add+1) e2 r2 ->
      prio_add < p ->
      separ [r1 ; symb_add ; r2] r ->
      repr p (exp_binop binop_add e1 e2) r
  | repr_sub : forall p e1 e2 r1 r2 r,
      repr (prio_sub+1) e1 r1 ->
      repr prio_sub e2 r2 ->
      prio_add < p ->
      separ [r1 ; symb_sub ; r2] r ->
      repr p (exp_binop binop_sub e1 e2) r
  | repr_mul : forall p e1 e2 r1 r2 r,
      repr (prio_mul+1) e1 r1 ->
      repr (prio_mul+1) e2 r2 ->
      prio_mul < p ->
      separ [r1 ; symb_mul ; r2] r ->
      repr p (exp_binop binop_mul e1 e2) r
  | repr_par : forall p e r1 r,
      repr prio_max e r1 ->
      separ [symb_par_open ; r1 ; symb_par_close ] r ->
      repr p e r.


(************************************************************)
(* * Properties of the syntax *)

Hint Extern 1 (_ < _) => math.

(** [repr] is monotonic in the priority *)

Hint Constructors repr.

Lemma repr_prio_le : forall p1 p2 e r,
  repr p1 e r ->
  p1 <= p2 ->
  repr p2 e r.
Proof. introv H. induction H; introv L; try constructors*. Qed.

(** [spacings] stable by concatenation *)

Lemma spacings_concat : forall s1 s2,
  spacings s1 ->
  spacings s2 ->
  spacings (s1 ~~ s2).
Proof.
  introv S1 S2. induction S1.
  rewrite~ append_empty_l.
  rewrite <- append_assoc. constructors~.
Qed.

(** [separ] supports adding spaces at the end of the string *)

Lemma separ_trailing_spaces : forall ss s g,
  spacings s ->
  separ ss g ->
  separ ss (g ~~ s).
Proof.
  introv P S. induction S.
  constructors. applys~ spacings_concat.
  do 2 rewrite <- append_assoc. constructors~.
Qed.

(** [repr] supports adding spaces at the end of the string *)

Lemma repr_trailing_spaces : forall p e s s',
  spacings s' ->
  repr p e s ->
  repr p e (s ~~ s').
Proof.
  hint separ_trailing_spaces.
  introv S R. inverts R; constructors*.
Qed.

(** Results about [spacings] *)

Hint Constructors spacings.

Lemma spacings_char : forall (c:char) s,
  spacing c ->
  spacings s ->
  spacings (String c s).
Proof. introv Sc Ss. applys (spacings_string Sc Ss). Qed.

Hint Resolve spacings_char.

(** Results about [separ] *)

Lemma separ_empty_not :
  separ nil EmptyString.
Proof.
  applys~ separ_nil.
Qed.

Lemma separ_cons_not : forall s ss r,
  separ ss r ->
  separ (s::ss) (s ~~ r).
Proof.
  introv H. rewrite <- append_empty_l.
  applys~ separ_cons.
Qed.

Lemma separ_unary : forall g s,
  spacings g -> separ [s] (g ~~ s).
Proof.
  introv G. rewrite <- append_empty_r.
  rewrite <- append_assoc.
  constructors~. constructors~.
Qed.

Lemma separ_1_alone : forall s,
  separ [s] s.
Proof.
  intros. rewrite <- append_empty_l. applys~ separ_unary.
Qed.

Lemma separ_2_front : forall g s1 s2,
  spacings g -> separ [s1;s2] (g ~~ s1 ~~ s2).
Proof.
  introv G. constructors~. applys separ_1_alone.
Qed.

Lemma separ_enclose : forall g1 g2 s1 s2 s3,
  spacings g1 -> spacings g2 ->
  separ [s1;s2;s3] (g1 ~~ s1 ~~ s2 ~~ g2 ~~ s3).
Proof.
  introv G1 G2. applys~ separ_cons.
  applys~ separ_cons_not. applys~ separ_unary.
Qed.

Hint Resolve separ_empty_not separ_cons_not
  separ_unary separ_1_alone separ_2_front separ_enclose.



(************************************************************)
(* * Parse trees *)

(** Definition of a parse tree -- expression plus parentheses *)

Inductive pexp :=
  | pexp_int : int -> pexp
  | pexp_unop : unop -> pexp -> pexp
  | pexp_binop : binop -> pexp -> pexp -> pexp
  | pexp_par : pexp -> pexp.

(** Conversion of a parse tree into an expression *)

Fixpoint exp_of_pexp f :=
  let r := exp_of_pexp in
  match f with
  | pexp_int n => exp_int n
  | pexp_unop op f1 => exp_unop op (r f1)
  | pexp_binop op f1 f2 => exp_binop op (r f1) (r f2)
  | pexp_par f1 => r f1
  end.


(************************************************************)
(* * Auxiliarly functions for the validator *)

(** [eat_leading t s] returns [None] is [t] is not
    a prefix of [s] and returns [Some s'] if [s = append t s']. *)

Fixpoint eat_leading t s :=
  match t with
  | EmptyString => Some s
  | String c t' =>
      match s with
      | EmptyString => None
      | String c' s' =>
         if decide (c = c')
           then eat_leading t' s'
           else None
      end
  end.

Lemma eat_leading_spec : forall t s s',
  eat_leading t s = Some s' -> s = append t s'.
Proof.
  induction t; introv E; simpls.
  inverts~ E.
  destruct s as [|c s''].
    false.
    case_if. subst. rewrites~ (>> IHt E).
Qed.

(** [eat_spaces s] returns the string obtained
    by removing the leading spacing characters (those
    satisfying the predicate [spacing]) from the string [s]. *)

Fixpoint eat_spaces s :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
     if decide (spacing (c:char))
       then eat_spaces s'
       else s
  end.

Lemma eat_spaces_spec : forall s s',
  eat_spaces s = s' ->
  exists g, spacings g /\ s = append g s'.
Proof.
  induction s; introv E.
  exists~ EmptyString.
  simpls. case_if.
    forwards (g'&G'&E'): IHs E.
     subst s. exists~ (String a g').
    exists~ EmptyString.
Qed.

Lemma eat_spaces_empty : forall s,
  eat_spaces s = EmptyString -> spacings s.
Proof.
  introv H. induction s.
  auto.
  simpls. case_if. applys* spacings_char.
Qed.

(** [eat t s] eats the spaces and the string [t] at the head
    of the string [s], and returns [Some] of the rest, or
    [None] if the eating failed. *)

Definition eat t s :=
  eat_leading t (eat_spaces s).

Lemma eat_spec : forall s s' t,
  eat t s = Some s' ->
  exists g, spacings g /\ s = append (append g t) s'.
Proof.
  introv H. unfolds eat.
  sets_eq u: (eat_spaces s).
  forwards~ (g&G&E): (@eat_spaces_spec s u).
  exists g. splits~.
  forwards: eat_leading_spec H.
  subst s u. rewrite~ append_assoc.
Qed.


(************************************************************)
(* * Validation of a parse tree w.r.t. a string *)

(** Auxiliary definitions *)

Definition if_lt (p q:int) (k:unit->option string) :=
  if decide (p < q) then k tt else None.

Definition if_str (o:option string) (k:string->option string) :=
  match o with
  | None => None
  | Some s => k s
  end.

(** [pexp_validate p f s] returns [Some s'] if [f] is a valid
    parse tree for a string [s''] such that [s = s'' ++ s'],
    in a context of priority [p]. Otherwise it returns [None] *)

Fixpoint pexp_validate p f s :=
  let r := pexp_validate in
  match f with
  | pexp_int n => eat (string_of_int n) s
  | pexp_unop op f1 =>
     match op with
     | unop_neg =>
        if_lt prio_neg p (fun _ =>
        if_str (eat symb_neg s) (fun s1 =>
        if_str (r prio_neg f1 s1) Some))
     end
  | pexp_binop op f1 f2 =>
     match op with
     | binop_add =>
        if_lt prio_add p (fun _ =>
        if_str (r (prio_add+1) f1 s) (fun s1 =>
        if_str (eat symb_add s1) (fun s2 =>
        if_str (r (prio_add+1) f2 s2) Some)))
     | binop_sub =>
        if_lt prio_sub p (fun _ =>
        if_str (r (prio_sub+1) f1 s) (fun s1 =>
        if_str (eat symb_sub s1) (fun s2 =>
        if_str (r prio_sub f2 s2) Some)))
     | binop_mul =>
        if_lt prio_mul p (fun _ =>
        if_str (r (prio_mul+1) f1 s) (fun s1 =>
        if_str (eat symb_mul s1) (fun s2 =>
        if_str (r (prio_mul+1) f2 s2) Some)))
     end
  | pexp_par f1 =>
     if_str (eat symb_par_open s) (fun s1 =>
     if_str (r prio_max f1 s1) (fun s2 =>
     if_str (eat symb_par_close s2) Some))
  end.

Definition pexp_validate_full f s :=
  match pexp_validate prio_max f s with
  | Some s =>
     match eat_spaces s with
     | EmptyString => true
     | _ => false
     end
  | _ => false
  end.

(** Tactic for automating the proof of correctness *)

Ltac step H :=
  match type of H with
  | if_lt _ _ _ = _ =>
    unfold if_lt in H at 1; case_if
  | if_str (eat ?s ?t) _ = _ =>
    let C := fresh "C" in
    (cases (eat s t) as C; simpl in H; [ | false ]);
    let g := fresh "g" in
    let Sg := fresh "Sg" in
    let Eg := fresh "Eg" in
    forwards (g&Sg&Eg): eat_spec C
  | if_str (pexp_validate ?p ?f ?s) _ = _ =>
    let C := fresh "C" in
    (cases (pexp_validate p f s) as C; simpl in H; [ | false]);
    let t := fresh "t" in
    let Et := fresh "Et" in
    let Rt := fresh "Rt" in
    match goal with IH: forall _, _ |- _ => forwards (t&Et&Rt): IH C end
  end.

Ltac steps H :=
  repeat step H; inverts H.

(** Proof of correctness of the validator *)

Lemma pexp_validate_correct : forall f s' p s,
  pexp_validate p f s = Some s' ->
  exists t, s = append t s' /\ repr p (exp_of_pexp f) t.
Proof.
  induction f; introv H; simpls.
  (* int *)
  forwards (g&G&E): eat_spec H.
  esplit. split*.
  (* --unary *)
  destruct u.
  (* neg *)
  steps H. subst. esplit. split.
    rewrite append_assoc. eauto.
    rewrite <- append_assoc. constructors*.
  (* -- binary *)
  destruct b.
  (* add *)
  steps H. subst. esplit. split.
    do 2 rewrite append_assoc. eauto.
    do 2 rewrite <- append_assoc. constructors*.
  (* sub -- copy pasted *)
  steps H. subst. esplit. split.
    do 2 rewrite append_assoc. eauto.
    do 2 rewrite <- append_assoc. constructors*.
  (* mul -- copy pasted  *)
  steps H. subst. esplit. split.
    do 2 rewrite append_assoc. eauto.
    do 2 rewrite <- append_assoc. constructors*.
  (* par *)
  steps H. subst. esplit. split.
    do 2 rewrite append_assoc. eauto.
    do 2 rewrite <- append_assoc. constructors*.
Qed.

(** Corollary for validation of complete strings *)

Theorem pexp_validate_correct_full : forall f s,
  pexp_validate_full f s = true ->
  repr prio_max (exp_of_pexp f) s.
Proof.
  introv M. unfolds in M.
  cases (pexp_validate prio_max f s) as N; tryfalse.
  cases (eat_spaces s0); tryfalse.
  forwards (t&E&R): pexp_validate_correct N.
  subst. apply~ repr_trailing_spaces.
  apply~ eat_spaces_empty.
Qed.



(************************************************************)
(* * Validation of a parse tree w.r.t. a string *)

Coercion pexp_of_int (n:int) : pexp := pexp_int n.
Definition _neg := pexp_unop unop_neg.
Definition _add := pexp_binop binop_add.
Definition _sub := pexp_binop binop_sub.
Definition _mul := pexp_binop binop_mul.
Definition _par := pexp_par.

Definition test_string_of_int := string_of_int 12.

Definition test1_valid := pexp_validate_full
  (1)
  "1".

Definition test2_valid := pexp_validate_full
  (1)
  "  1  ".

Definition test3_valid := pexp_validate_full
  (_add 1 2)
  "  1+ 2 ".

Definition test4_valid := pexp_validate_full
  (_par (_add (_par 1) 2))
  " ( (1)+ 2 )".

Definition test5_valid := pexp_validate_full
  (_add 1 (_par (_neg 2)))
  "  1+ (- 2) ".

Definition test6_valid := pexp_validate_full
  (_add 1 (_neg 2))
  "1+ - 2". (* not correct *)


(*
Definition test6_valid := pexp_validate_full
  (_par (_add (_mul (_par (_neg 5)) 6) 7))
  "((-5)*6+7))".
*)

(*
Definition test6_valid := pexp_validate_full
  (_par (_add (_mul (_par (_neg 5)) 6) 7))
  "((-5)*6+7)".
*)

Definition test_pexp :=
  _sub (_mul 1 (_par (_add 2 (_sub 3 4))))
       (_par (_add (_mul (_par (_neg 5)) 6) 7)).

Definition test_exp := exp_of_pexp test_pexp.

Definition test_exp' :=
  Eval cbv beta iota zeta delta
    [test_exp exp_of_pexp test_pexp _neg _add _sub _mul _par pexp_of_int]
    in test_exp.
  (* Print test_exp'. *)

Definition test7_valid := pexp_validate_full
  test_pexp
  " 1 *(2 +  3  - 4  ) - ((-5)*6+7)".

Definition test8_valid := pexp_validate_full
  test_pexp
  " 1 *(2 +  3  - 4  ) - (-5*6+7)".  (* not the same *)

Definition test9_valid := pexp_validate_full
  (_sub (_mul 1 (_par (_add 2 (_sub 3 4))))
        (_par (_neg (_add (_mul 5 6) 7))))
  " 1 *(2 +  3  - 4  ) - (-5*6+7)".


(************************************************************)
(** * Extraction *)

Extract Constant string_of_int =>
  "(fun n ->
     let int_of_pos p =
       let rec aux factor = function
         | XI p1 -> aux (2*factor) p1 + factor
         | XO p1 -> aux (2*factor) p1
         | XH -> factor
         in
       aux 1 p
       in
     let int_of_z = function
       | Z0 -> 0
       | Zpos p -> int_of_pos p
       | Zneg p -> - (int_of_pos p)
       in
     let ascii_of_char c =
       let i = Char.code c in
       let bit k = (if i land (1 lsl k) > 0 then True else False) in
       Ascii (bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)
       in
     let s = string_of_int (int_of_z n) in
     let r = ref [] in
     String.iter (fun c -> r := ascii_of_char c :: !r) s;
     List.fold_left (fun acc c -> String (c,acc)) EmptyString !r)".

Extraction "eval/demo.ml" test_string_of_int test1_valid test2_valid
  test3_valid test4_valid test5_valid test6_valid test7_valid
  test8_valid test9_valid.

(* From top-level folder, run the command:

coqc -I js -I tlc eval/Arithm.v && ocamlc eval/demo.mli && ocamlc -I eval eval/demo.ml eval/test.ml -o eval/test.out && ./eval/test.out

-- expected output:
true
true
true
true
true
false
true
false
true
12

*)
















