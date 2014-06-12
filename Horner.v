(* Horner.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Horner's method *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.

(* Own modules *)
Require Import Cases.
Require Import Power.
Require Import BinomialCoefficients.
Require Import ListCalculus.
Require Import StreamCalculus.
Require Import DualMoessnersSieve.
Require Import CharacteristicFunction.
Require Import MoessnersTheorem.

(** * Horner's method *)

(** ** Remove last

  *** Definition *)

(*
(* {REMOVELAST} *)
Fixpoint removelast (l:list A) : list A :=
    match l with
      | [] => []
      | [a] => []
      | a :: l => a :: removelast l
    end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_removelast_base_case_nil :
  forall (A : Type),
    removelast ([] : list A) = ([] : list A).
Proof.
  intro A.
  unfold removelast.
  reflexivity.
Qed.
Hint Rewrite unfold_removelast_base_case_nil : listcalc.

Lemma unfold_removelast_base_case_cons :
  forall (A : Type) (x : A),
    removelast [x] = [].
Proof.
  intros A x.
  unfold removelast.
  reflexivity.
Qed.
Hint Rewrite unfold_removelast_base_case_cons : listcalc.

Lemma unfold_removelast_induction_case :
  forall (A : Type) (x x' : A) (xs'' : list A),
    removelast (x :: x' :: xs'') = x :: removelast (x' :: xs'').
Proof.
  intros A x x' xs''.
  unfold removelast.
  reflexivity.
Qed.
Hint Rewrite unfold_removelast_induction_case : listcalc.

(** *** Properties *)

(* {REMOVELAST_LIST_PARTIAL_SUMS_ACC} *)
Lemma removelast_list_partial_sums_acc :
  forall (xs : list nat) (a d : nat),
    list_partial_sums_acc a xs =
    removelast (list_partial_sums_acc a (xs ++ [d])).
(* {END} *)
Proof.
  induction xs as [ | x xs' IH_xs' ].

  Case "xs = []".
  intros a d.
  rewrite -> unfold_list_partial_sums_acc_base_case.
  rewrite -> app_nil_l.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> unfold_list_partial_sums_acc_base_case.
  rewrite -> unfold_removelast_base_case_cons.
  reflexivity.

  Case "xs = x :: xs'".
  intros a d.
  rewrite <- app_comm_cons.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> (IH_xs' (x + a) d).
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  case xs' as [ | x' xs'' ].

  SCase "xs' = []".
  rewrite -> app_nil_l.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> unfold_list_partial_sums_acc_base_case.
  rewrite -> unfold_removelast_induction_case.
  rewrite -> unfold_removelast_base_case_cons.
  reflexivity.

  SCase "xs' = x' :: xs''".
  rewrite <- app_comm_cons.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> unfold_removelast_induction_case.
  reflexivity.
Qed.
Hint Rewrite removelast_list_partial_sums_acc : horner.

(* {LENGTH_LIST_PARTIAL_SUMS_ACC} *)
Lemma length_list_partial_sums_acc :
  forall (xs : list nat) (a b : nat),
    length (list_partial_sums_acc a xs) =
    length (list_partial_sums_acc b xs).
(* {END} *)
Proof.
  induction xs as [ | x xs' IH_xs' ].

  Case "xs = []".
  intros a b.
  rewrite ->2 unfold_list_partial_sums_acc_base_case.
  rewrite -> unfold_length_base_case.
  reflexivity.

  Case "xs = x :: xs'".
  intros a b.
  rewrite ->2 unfold_list_partial_sums_acc_induction_case.
  rewrite ->2 unfold_length_induction_case.
  rewrite -> (IH_xs' (x + a) (x + b)).
  reflexivity.
Qed.
Hint Rewrite length_list_partial_sums_acc : horner.

(* {LENGTH_LIST_PARTIAL_SUMS_AND_MAKE_TUPLE} *)
Lemma length_list_partial_sums_and_make_tuple :
  forall (xs' : list nat) (x a : nat),
    length (list_partial_sums xs') =
    length (make_tuple (x :: xs') a).
(* {END} *)
Proof.
  induction xs' as [ | x' xs'' IH_xs'' ].

  Case "xs' = []".
  intros x a.
  rewrite -> unfold_list_partial_sums.
  rewrite -> unfold_list_partial_sums_acc_base_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_length_base_case.
  reflexivity.

  Case "xs' = x' :: xs''".
  intros x a.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_length_induction_case.
  rewrite <- (IH_xs'' x' (x + a)).
  rewrite -> unfold_list_partial_sums.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> unfold_length_induction_case.
  rewrite -> plus_0_r.
  rewrite -> (length_list_partial_sums_acc xs'' x' 0).
  rewrite <- unfold_list_partial_sums.
  reflexivity.
Qed.
Hint Rewrite length_list_partial_sums_and_make_tuple : horner.

(* {LENGTH_REMOVELAST} *)
Lemma length_removelast :
  forall (xs' : list nat) (x : nat),
    length (removelast (x :: xs')) =
    length xs'.
(* {END} *)
Proof.
  induction xs' as [ | x' xs'' IH_xs'' ].

  Case "xs' = []".
  intro x.
  rewrite -> unfold_removelast_base_case_cons.
  rewrite -> unfold_length_base_case.
  reflexivity.

  Case "xs' = x' :: xs''".
  intro x.
  rewrite -> unfold_length_induction_case.
  rewrite <- (IH_xs'' x).
  rewrite -> unfold_removelast_induction_case.
  rewrite -> unfold_length_induction_case.
  case xs'' as [ | x'' xs''' ].

  SCase "xs'' = []".
  rewrite ->2 unfold_removelast_base_case_cons.
  rewrite -> unfold_length_base_case.
  reflexivity.

  SCase "xs'' = x'' :: xs'''".
  rewrite ->2 unfold_removelast_induction_case.
  rewrite ->2 unfold_length_induction_case.
  reflexivity.
Qed.
Hint Rewrite length_removelast : horner.

(* {PREFIX_AND_REMOVE_LAST} *)
Lemma Str_prefix_and_remove_last :
  forall (n' : nat) (sigma : Stream nat),
    Str_prefix n' sigma =
    removelast (Str_prefix (S n') sigma).
(* {END} *)
Proof.
  induction n' as [ | n'' IH_n'' ].

  Case "n' = 0".
  intro sigma.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_removelast_base_case_cons.
  reflexivity.

  Case "n' = S n''".
  intro sigma.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> (IH_n'' sigma`).
  rewrite ->3 unfold_Str_prefix_induction_case.
  rewrite -> unfold_removelast_induction_case.
  reflexivity.
Qed.
Hint Rewrite Str_prefix_and_remove_last : horner.

(* {LAST_X_XS_VS_DEFAULT} *)
Lemma last_x_xs_vs_default :
  forall (xs' : list nat) (x i j : nat),
    last (x :: xs') i = last (x :: xs') j.
(* {END} *)
Proof.
  induction xs' as [ | x' xs'' IH_xs'' ].

  Case "xs' = []".
  intros x i j.
  rewrite ->2 unfold_last_base_case_cons.
  reflexivity.

  Case "xs' = x' :: xs''".
  intros x i j.
  rewrite -> unfold_last_induction_case.
  rewrite -> (IH_xs'' x' i j).
  rewrite -> unfold_last_induction_case.
  reflexivity.
Qed.
Hint Rewrite last_x_xs_vs_default : horner.

(** ** Horner poly eval acc

  *** Definition *)

(* {POLY_NOTATION} *)
Notation polynomial := (list nat).
(* {END} *)

(* {HORNER_POLY_EVAL_ACC} *)
Fixpoint horner_poly_eval_acc (cs : polynomial) (x a : nat) : nat :=
  match cs with
    | [] => a
    | c :: cs' => horner_poly_eval_acc cs' x (c + x * a)
  end.
(* {END} *)
Hint Unfold horner_poly_eval_acc : horner.

(** *** Unfolding lemmas *)

Lemma unfold_horner_poly_eval_acc_base_case :
  forall (a x  : nat),
    horner_poly_eval_acc [] x a = a.
Proof.
  intros a x.
  unfold horner_poly_eval_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_horner_poly_eval_acc_base_case : horner.

Lemma unfold_horner_poly_eval_acc_induction_case :
  forall (cs' : polynomial) (a x c : nat),
    horner_poly_eval_acc (c :: cs') x a =
    horner_poly_eval_acc cs' x (c + x * a).
Proof.
  intros cs' a x c.
  unfold horner_poly_eval_acc; fold horner_poly_eval_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_horner_poly_eval_acc_induction_case : horner.

(** ** Horner poly eval

  *** Definition *)

(* {HORNER_POLY_EVAL} *)
Definition horner_poly_eval (cs : polynomial) (x : nat) : nat :=
  horner_poly_eval_acc cs x 0.
(* {END} *)
Hint Unfold horner_poly_eval : horner.

(** *** Unfolding lemmas *)

Lemma unfold_horner_poly_eval :
  forall (cs : polynomial) (x : nat),
    horner_poly_eval cs x =
    horner_poly_eval_acc cs x 0.
Proof.
  intros cs x.
  unfold horner_poly_eval.
  reflexivity.
Qed.
Hint Rewrite unfold_horner_poly_eval : horner.

(** ** Horner poly div acc

  *** Definition *)

(* {HORNER_POLY_DIV_ACC} *)
Fixpoint horner_poly_div_acc (cs' : polynomial) (x a : nat) :
  polynomial :=
  match cs' with
    | [] => []
    | c' :: cs'' =>
      (c' + (x * a)) :: (horner_poly_div_acc cs'' x (c' + (x * a)))
  end.
(* {END} *)
Hint Unfold horner_poly_div_acc : horner.

(** *** Unfolding lemmas *)

Lemma unfold_horner_poly_div_acc_base_case :
  forall (x a : nat),
    horner_poly_div_acc [] x a = [].
Proof.
  intros x a.
  unfold horner_poly_div_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_horner_poly_div_acc_base_case : horner.

Lemma unfold_horner_poly_div_acc_induction_case :
  forall (c' x a : nat) (cs'' : polynomial),
    horner_poly_div_acc (c' :: cs'') x a =
    (c' + (x * a)) :: (horner_poly_div_acc cs'' x (c' + (x * a))).
Proof.
  intros c' x a cs''.
  unfold horner_poly_div_acc; fold horner_poly_div_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_horner_poly_div_acc_induction_case : horner.

(** *** Properties *)

(* {LENGTH_HORNER_POLY_DIV_ACC} *)
Lemma length_horner_poly_div_acc :
  forall (cs : polynomial) (x a : nat),
    length (horner_poly_div_acc cs x a) =
    length cs.
(* {END} *)
Proof.
  induction cs as [ | c cs' IH_cs' ].

  Case "cs = []".
  intros x a.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_length_base_case.
  reflexivity.

  Case "cs = c :: cs'".
  intros x a.
  rewrite -> unfold_length_induction_case.
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> unfold_length_induction_case.
  rewrite -> (IH_cs' x (c + x * a)).
  reflexivity.
Qed.
Hint Rewrite length_horner_poly_div_acc : horner.

(** ** Synthetic division

  *** Definition *)

(* {HORNER_POLY_DIV} *)
Definition horner_poly_div (cs : polynomial) (x : nat) : polynomial :=
  match cs with
    | [] => []
    | c :: cs' => c :: (horner_poly_div_acc cs' x c)
  end.
(* {END} *)
Hint Unfold horner_poly_div : horner.

(** *** Unfolding lemmas *)

Lemma unfold_horner_poly_div_base_case :
  forall (x : nat),
    horner_poly_div [] x = [].
Proof.
  intro x.
  unfold horner_poly_div.
  reflexivity.
Qed.
Hint Rewrite unfold_horner_poly_div_base_case : horner.

Lemma unfold_horner_poly_div_induction_case :
  forall (c x : nat) (cs' : polynomial),
    horner_poly_div (c :: cs') x =
    c :: (horner_poly_div_acc cs' x c).
Proof.
  intros c x cs'.
  unfold horner_poly_div.
  reflexivity.
Qed.
Hint Rewrite unfold_horner_poly_div_induction_case : horner.

(** *** Properties *)

(* {LENGTH_HORNER_POLY_DIV} *)
Lemma length_horner_poly_div :
  forall (cs : polynomial) (x : nat),
    length (horner_poly_div cs x) =
    length cs.
(* {END} *)
Proof.
  induction cs as [ | c cs' IH_cs' ].

  Case "cs = []".
  intro x.
  rewrite -> unfold_horner_poly_div_base_case.
  rewrite -> unfold_length_base_case.
  reflexivity.

  Case "cs = x :: cs'".
  intro x.
  rewrite -> unfold_length_induction_case.
  rewrite -> unfold_horner_poly_div_induction_case.
  rewrite -> unfold_length_induction_case.
  rewrite -> length_horner_poly_div_acc.
  reflexivity.
Qed.
Hint Rewrite length_horner_poly_div : horner.

(** ** Equivalence of evaluation and division (Polynomial remainder theorem) *)

(* {HORNER_POLY_EVAL_ACC_EQ_HORNER_POLY_DIV_ACC} *)
Theorem horner_poly_eval_acc_eq_horner_poly_div_acc :
  forall (cs' : polynomial) (c x a : nat),
    horner_poly_eval_acc (c :: cs') x a =
    last (horner_poly_div_acc cs' x (c + x * a)) (c + x * a).
(* {END} *)
Proof.
  induction cs' as [ | c' cs'' IH_cs'' ].

  Case "cs' = []".
  intros c x a.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_horner_poly_eval_acc_induction_case.
  rewrite -> unfold_horner_poly_eval_acc_base_case.
  rewrite -> unfold_last_base_case_nil.
  reflexivity.

  Case "cs' = c' :: cs''".
  intros c x a.
  rewrite -> unfold_horner_poly_eval_acc_induction_case.
  rewrite -> IH_cs''.
  rewrite -> unfold_horner_poly_div_acc_induction_case.

  case cs'' as [ | cs''' ].

  SCase "cs'' = []".
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_last_base_case_nil.
  rewrite -> unfold_last_base_case_cons.
  reflexivity.

  SCase "cs'' = c'' :: cs'''".
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> unfold_last_induction_case.
  rewrite -> (last_x_xs_vs_default _ _ (c' + x * (c + x * a)) (c + x * a)).
  reflexivity.
Qed.
Hint Rewrite horner_poly_eval_acc_eq_horner_poly_div_acc
  : horner.

(* {HORNER_POLY_EVAL_EQ_HORNER_POLY_DIV} *)
Theorem horner_poly_eval_eq_horner_poly_div :
  forall (cs : polynomial) (x : nat),
    horner_poly_eval cs x =
    last (horner_poly_div cs x) 0.
(* {END} *)
Proof.
  intros cs x.
  rewrite -> unfold_horner_poly_eval.
  case cs as [ | c cs' ].

  Case "cs = []".
  rewrite -> unfold_horner_poly_div_base_case.
  rewrite -> unfold_horner_poly_eval_acc_base_case.
  rewrite -> unfold_last_base_case_nil.
  reflexivity.

  Case "cs = c :: cs'".
  rewrite -> unfold_horner_poly_div_induction_case.
  rewrite -> horner_poly_eval_acc_eq_horner_poly_div_acc.
  rewrite -> mult_0_r, -> plus_0_r.
  rewrite -> (last_x_xs_vs_default _ _ 0 c).
  case cs' as [ | c' cs'' ].

  SCase "cs' = []".
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_last_base_case_nil.
  rewrite -> unfold_last_base_case_cons.
  reflexivity.

  SCase "cs' = c' :: cs''".
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> unfold_last_induction_case.
  reflexivity.
Qed.
Hint Rewrite horner_poly_eval_eq_horner_poly_div : corner.

(** ** Create horner block acc

  *** Definition *)

(* {BLOCK_NOTATION} *)
Notation block := (list polynomial).
(* {END} *)

(* {CREATE_HORNER_BLOCK_ACC} *)
Fixpoint create_horner_block_acc (n x : nat) (cs : polynomial) : block :=
  match n with
    | O => []
    | S n' => let cs' := removelast (horner_poly_div cs x) in
              cs' :: create_horner_block_acc n' x cs'
  end.
(* {END} *)
Hint Unfold create_horner_block_acc : horner.

(** *** Unfolding lemmas *)

Lemma unfold_create_horner_block_acc_base_case :
  forall (x : nat) (cs : polynomial),
    create_horner_block_acc 0 x cs = [].
Proof.
  intros x cs.
  unfold create_horner_block_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_create_horner_block_acc_base_case : horner.

Lemma unfold_create_horner_block_acc_induction_case :
  forall (n' x : nat) (cs : polynomial),
    create_horner_block_acc (S n') x cs =
    removelast (horner_poly_div cs x)
               :: create_horner_block_acc n' x
               (removelast (horner_poly_div cs x)).
Proof.
  intros n' x cs.
  unfold create_horner_block_acc; fold create_horner_block_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_create_horner_block_acc_induction_case : horner.

(** ** Create Horner Block

  *** Definition *)

(* {CREATE_HORNER_BLOCK} *)
Definition create_horner_block (n x : nat) (cs : polynomial) : block :=
  match n with
    | 0 => []
    | S n' => let cs' := horner_poly_div cs x in
              cs' :: create_horner_block_acc n' x cs'
  end.
(* {END} *)
Hint Unfold create_horner_block : horner.

(** *** Unfolding lemmas *)

Lemma unfold_create_horner_block_base_case :
  forall (x : nat) (cs : polynomial),
    create_horner_block 0 x cs = [].
Proof.
  intros x cs.
  unfold create_horner_block.
  reflexivity.
Qed.
Hint Rewrite unfold_create_horner_block_base_case : horner.

Lemma unfold_create_horner_block_induction_case :
  forall (n' x : nat) (cs : polynomial),
    create_horner_block (S n') x cs =
    horner_poly_div cs x
      :: create_horner_block_acc n' x (horner_poly_div cs x).
Proof.
  intros n' x cs.
  unfold create_horner_block; fold create_horner_block.
  reflexivity.
Qed.
Hint Rewrite unfold_create_horner_block_induction_case : horner.

(* ** Equivalence between create horner block and create horner block acc *)

(* {REMOVELAST_HORNER_POLY_DIV_ACC} *)
Lemma removelast_horner_poly_div_acc :
  forall (cs : polynomial) (x a : nat),
    removelast (horner_poly_div_acc (cs ++ [0]) x a) =
    horner_poly_div_acc cs x a.
(* {END} *)
Proof.
  induction cs as [ | c cs' IH_cs' ].

  Case "cs = 0".
  intros x a.
  rewrite -> app_nil_l.
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_removelast_base_case_cons.
  reflexivity.

  Case "cs = c :: cs'".
  case cs' as [ | c' cs'' ].

  SCase "cs' = []".
  intros x a.
  unfold app; fold app.
  rewrite ->3 unfold_horner_poly_div_acc_induction_case.
  rewrite ->2 unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_removelast_induction_case.
  rewrite -> unfold_removelast_base_case_cons.
  reflexivity.

  SCase "cs' = c' :: cs''".
  intros x a.
  rewrite <- app_comm_cons.
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite <- app_comm_cons.
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> unfold_removelast_induction_case.
  rewrite <- unfold_horner_poly_div_acc_induction_case.
  rewrite -> app_comm_cons.
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> (IH_cs' x (c + x * a)).
  reflexivity.
Qed.
Hint Rewrite removelast_horner_poly_div_acc : horner.

(* {CREATE_HORNER_BLOCK_EQ_CREATE_HORNER_BLOCK_ACC} *)
Theorem create_horner_block_eq_create_horner_block_acc :
  forall (n x : nat) (cs : polynomial),
    create_horner_block n x cs =
    create_horner_block_acc n x (cs ++ [0]).
(* {END} *)
Proof.
  case n as [ | n' ].

  Case "n = 0".
  intros x cs.
  rewrite -> unfold_create_horner_block_base_case.
  rewrite -> unfold_create_horner_block_acc_base_case.
  reflexivity.

  Case "n = S n'".
  intros x cs.
  rewrite -> unfold_create_horner_block_induction_case.
  rewrite -> unfold_create_horner_block_acc_induction_case.
  case cs as [ | c cs' ].

  SCase "cs = []".
  rewrite -> unfold_horner_poly_div_base_case.
  rewrite -> app_nil_l.
  rewrite -> unfold_horner_poly_div_induction_case.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_removelast_base_case_cons.
  reflexivity.

  SCase "cs = c :: cs'".
  rewrite <- app_comm_cons.
  rewrite ->2 unfold_horner_poly_div_induction_case.
  case cs' as [ | c' cs'' ].

  SSCase "cs' = []".
  rewrite -> app_nil_l.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  rewrite -> unfold_removelast_induction_case.
  rewrite -> unfold_removelast_base_case_cons.
  reflexivity.

  SSCase "cs' = c' :: cs''".
  rewrite <- app_comm_cons.
  rewrite ->2 unfold_horner_poly_div_acc_induction_case.
  rewrite -> unfold_removelast_induction_case.
  rewrite <-2 unfold_horner_poly_div_acc_induction_case.
  rewrite -> app_comm_cons.
  rewrite -> removelast_horner_poly_div_acc.
  reflexivity.
Qed.
Hint Rewrite create_horner_block_eq_create_horner_block_acc : horner.

(** ** Equivalence between create horner block acc and create triangle
  vertically *)

(* {EQUIVALENCE_OF_LIST_PARTIAL_SUMS_ACC_AND_MAKE_TUPLE} *)
Lemma equivalence_of_list_partial_sums_acc_and_make_tuple :
  forall (xs : tuple) (a : nat),
    make_tuple xs a =
    removelast (list_partial_sums_acc a xs).
(* {END} *)
Proof.
  induction xs as [ | x xs' IH_xs' ].

  Case "xs = []".
  intro a.
  rewrite -> unfold_make_tuple_base_case_nil.
  rewrite -> unfold_list_partial_sums_acc_base_case.
  rewrite -> unfold_removelast_base_case_nil.
  reflexivity.

  Case "xs = x :: xs'".
  case xs' as [ | x' xs'' ].

  SCase "xs' = []".
  intro a.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> unfold_list_partial_sums_acc_base_case.
  rewrite -> unfold_removelast_base_case_cons.
  reflexivity.

  SCase "xs' = x' :: xs''".
  intro a.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> (IH_xs' (x + a)).
  rewrite ->3 unfold_list_partial_sums_acc_induction_case.
  rewrite -> unfold_removelast_induction_case.
  reflexivity.
Qed.
Hint Rewrite equivalence_of_list_partial_sums_acc_and_make_tuple : horner.

(* {EQUIVALENCE_OF_LIST_PARTIAL_SUMS_AND_MAKE_TUPLE} *)
Corollary equivalence_of_list_partial_sums_and_make_tuple :
  forall (xs : tuple),
    make_tuple xs 0 =
    removelast (list_partial_sums xs).
(* {END} *)
Proof.
  intro xs.
  rewrite -> unfold_list_partial_sums.
  exact (equivalence_of_list_partial_sums_acc_and_make_tuple xs 0).
Qed.
Hint Rewrite equivalence_of_list_partial_sums_and_make_tuple : horner.

(* {LIST_PARTIAL_SUMS_ACC_EQ_HORNER_POLY_DIV_ACC} *)
Lemma list_partial_sums_acc_eq_horner_poly_div_acc :
  forall (cs : polynomial) (a : nat),
    list_partial_sums_acc a cs =
    horner_poly_div_acc cs 1 a.
(* {END} *)
Proof.
  induction cs as [ | c cs' IH_cs' ].

  Case "cs = []".
  intro a.
  rewrite -> unfold_list_partial_sums_acc_base_case.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  reflexivity.

  Case "cs = c :: cs'".
  intro a.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> mult_1_l.
  rewrite -> (IH_cs' (c + a)).
  reflexivity.
Qed.
Hint Rewrite list_partial_sums_acc_eq_horner_poly_div_acc : horner.

(* {LIST_PARTIAL_SUMS_EQ_HORNER_POLY_DIV} *)
Lemma list_partial_sums_eq_horner_poly_div :
  forall (cs : polynomial),
    list_partial_sums cs =
    horner_poly_div cs 1.
(* {END} *)
Proof.
  intros cs.
  rewrite -> unfold_list_partial_sums.
  rewrite -> list_partial_sums_acc_eq_horner_poly_div_acc.
  case cs as [ | cs' ].

  Case "cs = []".
  rewrite -> unfold_horner_poly_div_base_case.
  rewrite -> unfold_horner_poly_div_acc_base_case.
  reflexivity.

  Case "cs = c :: cs'".
  rewrite -> unfold_horner_poly_div_acc_induction_case.
  rewrite -> unfold_horner_poly_div_induction_case.
  rewrite -> mult_0_r, -> plus_0_r.
  reflexivity.
Qed.
Hint Rewrite list_partial_sums_eq_horner_poly_div : horner.

(* {CREATE_HORNER_BLOCK_ACC_EQ_CREATE_TRIANGLE_VERTICALLY} *)
Theorem create_horner_block_acc_eq_create_triangle_vertically :
  forall (r : nat) (sigma : Stream nat),
    hypotenuse (create_horner_block_acc
                  r 1 (Str_prefix (S r) sigma)) =
    hypotenuse (create_triangle_vertically
                  (tuple_constant (S r) 0) (Str_prefix (S r) sigma)).
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  intro sigma.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> unfold_create_horner_block_acc_base_case.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_hypotenuse_base_case.
  reflexivity.

  Case "r = S r'".
  intro sigma.
  rewrite -> unfold_create_horner_block_acc_induction_case.
  rewrite -> unfold_hypotenuse_induction_case.
  rewrite <- list_partial_sums_eq_horner_poly_div.
  rewrite <- equivalence_of_list_partial_sums_and_make_tuple.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  rewrite -> (IH_r' (stream_partial_sums_acc 0 sigma)).
  symmetry.

  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  rewrite -> unfold_hypotenuse_induction_case.
  reflexivity.
Qed.
Hint Rewrite create_horner_block_acc_eq_create_triangle_vertically
  : horner.
