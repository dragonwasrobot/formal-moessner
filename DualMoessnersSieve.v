(* DualMoessnersSieve.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Dual Moessner's sieve *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.

(* Own modules *)
Require Import Cases.
Require Export ListCalculus.
Require Export StreamCalculus.

(** * Tuple constructors *)

(** ** Notation *)

(* {NOTATION} *)
Notation tuple := (list nat).
Notation triangle := (list tuple).
(* {END} *)

(** ** Tuple constant

  *** Definition *)

(* {TUPLE_CONSTANT} *)
Definition tuple_constant (n c : nat) : tuple :=
  list_constant n c.
(* {END} *)
Hint Unfold tuple_constant : dualsieve.

(** *** Unfolding lemmas *)

Lemma unfold_tuple_constant_base_case :
  forall (c : nat),
    tuple_constant 0 c = [].
Proof.
  intro c.
  unfold tuple_constant.
  rewrite -> unfold_list_constant_base_case.
  reflexivity.
Qed.
Hint Rewrite unfold_tuple_constant_base_case : dualsieve.

Lemma unfold_tuple_constant_induction_case :
  forall (c l' : nat),
    tuple_constant (S l') c = c :: (tuple_constant l' c).
Proof.
  intros c l'.
  unfold tuple_constant.
  rewrite -> unfold_list_constant_induction_case.
  reflexivity.
Qed.
Hint Rewrite unfold_tuple_constant_induction_case : dualsieve.

(** *** Properties *)

Lemma Str_prefix_stream_constant_eq_tuple_constant :
  forall (n c : nat),
    Str_prefix n #c = tuple_constant n c.
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intro c.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> unfold_tuple_constant_base_case.
  reflexivity.

  Case "n = S n'".
  intro c.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> stream_constant_stream_derivative.
  rewrite -> stream_constant_initial_value.
  rewrite -> (IH_n' c).
  rewrite -> unfold_tuple_constant_induction_case.
  reflexivity.
Qed.
Hint Rewrite Str_prefix_stream_constant_eq_tuple_constant : dualsieve.

(** ** Make tuple

  *** Definition *)

(* {MAKE_TUPLE} *)
Fixpoint make_tuple (xs : tuple) (a : nat) : tuple :=
  match xs with
  | [] => []
  | [x] => []
  | x :: (_ :: _) as xs' =>
    let a' := x + a
    in a' :: make_tuple xs' a'
  end.
(* {END} *)
Hint Unfold make_tuple : dualsieve.

(** *** Unfolding lemmas *)

Lemma unfold_make_tuple_base_case_nil :
  forall (a : nat),
    make_tuple [] a = [].
Proof.
  intro a.
  unfold make_tuple.
  reflexivity.
Qed.
Hint Rewrite unfold_make_tuple_base_case_nil : dualsieve.

Lemma unfold_make_tuple_base_case_x_nil :
  forall (x a : nat),
    make_tuple [x] a = [].
Proof.
  intros x a.
  unfold make_tuple.
  reflexivity.
Qed.
Hint Rewrite unfold_make_tuple_base_case_x_nil : dualsieve.

Lemma unfold_make_tuple_induction_case :
  forall (x x' a : nat) (xs' : tuple),
    make_tuple (x :: (x' :: xs')) a =
    (x + a) :: make_tuple (x' :: xs') (x + a).
Proof.
  intros x x' a xs'.
  unfold make_tuple; fold make_tuple.
  reflexivity.
Qed.
Hint Rewrite unfold_make_tuple_induction_case : dualsieve.

(** *** Properties *)

(** *** Length properties *)

Lemma length_tuples_xs_a_eq_ys_b :
  forall (xs ys : tuple) (a b : nat),
    length xs = length ys ->
    length (make_tuple xs a) = length (make_tuple ys b).
Proof.
  induction xs as [ | x xs' IH_xs' ].

  Case "xs = []".
  intros ys a b H_length_nil_eq_length_ys.
  rewrite -> unfold_length_base_case in H_length_nil_eq_length_ys.
  symmetry in H_length_nil_eq_length_ys.
  rewrite -> (length_nil_0 ys H_length_nil_eq_length_ys).
  rewrite->2 unfold_make_tuple_base_case_nil.
  reflexivity.

  Case "xs = x :: xs'".
  intros ys a b H_length_xs'_eq_length_ys.
  case xs' as [ | x' xs'' ].

  SCase "xs' = []".
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_length_base_case.
  case ys as [ | y ys' ].

  SSCase "ys = []".
  inversion H_length_xs'_eq_length_ys.

  SSCase "ys = y :: ys'".
  inversion H_length_xs'_eq_length_ys;
    rename H0 into H_0_eq_length_ys'.
  symmetry in H_0_eq_length_ys'.
  rewrite -> (length_nil_0 ys' H_0_eq_length_ys').
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_length_base_case.
  reflexivity.

  SCase "xs' = x :: xs'".
  case ys as [ | y ys' ].

  SSCase "xs = []".
  inversion H_length_xs'_eq_length_ys.

  SSCase "ys = y :: ys'".
  case ys' as [ | y' ys'' ].

  SSSCase "ys' = []".
  inversion H_length_xs'_eq_length_ys.

  SSSCase "ys' = y' :: ys''".
  rewrite ->2 unfold_make_tuple_induction_case.
  rewrite ->2 unfold_length_induction_case.

  assert (H_hypothesis_helper:
         length (x' :: xs'') = length (y' :: ys'')).
    inversion H_length_xs'_eq_length_ys;
      rename H0 into H_length_xs''_eq_length_ys''.
    rewrite ->2 unfold_length_induction_case.
    rewrite -> H_length_xs''_eq_length_ys''.
    reflexivity.

    rewrite -> (IH_xs' (y' :: ys'') (x + a) (y + b) H_hypothesis_helper).
    reflexivity.
Qed.
Hint Rewrite length_tuples_xs_a_eq_ys_b : dualsieve.

Lemma S_length_make_tuple :
  forall (xs' : tuple) (x a : nat),
    S (length (make_tuple (x :: xs') a)) = length (x :: xs').
Proof.
  induction xs' as [ | x' xs'' IH_xs'' ].

  Case "xs' = []".
  intros x a.
  rewrite -> unfold_length_induction_case.
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_length_base_case.
  reflexivity.

  Case "xs' = x :: xs''".
  intros x a.
  rewrite -> unfold_length_induction_case.
  rewrite <- (IH_xs'' x' a).
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_length_induction_case.
  rewrite -> (length_tuples_xs_a_eq_ys_b (x' :: xs'') (x' :: xs'') a (x + a));
    reflexivity.
Qed.
Hint Rewrite S_length_make_tuple : dualsieve.

(** *** Equivalence properties *)

(* {EQUIVALENCE_OF_MAKE_TUPLE_AND_STREAM_PARTIAL_SUMS_ACC} *)
Theorem equivalence_of_make_tuple_and_stream_partial_sums_acc :
  forall (l' a : nat) (sigma : Stream nat),
    make_tuple (Str_prefix (S l') sigma) a =
    Str_prefix l' (stream_partial_sums_acc a sigma).
(* {END} *)
Proof.
  induction l' as [ | l'' IH_l'' ].

  Case "l' = 0".
  intros a sigma.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  reflexivity.

  Case "l' = S l''".
  intros a sigma.
  rewrite ->3 unfold_Str_prefix_induction_case.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite <- (IH_l'' (sigma(0) + a) sigma`).
  rewrite -> unfold_Str_prefix_induction_case.
  reflexivity.
Qed.
Hint Rewrite equivalence_of_make_tuple_and_stream_partial_sums_acc : dualsieve.

(* {EQUIVALENCE_OF_MAKE_TUPLE_AND_LIST_PARTIAL_SUMS_ACC} *)
Theorem equivalence_of_make_tuple_and_list_partial_sums_acc :
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
Hint Rewrite equivalence_of_make_tuple_and_list_partial_sums_acc : horner.

Corollary equivalence_of_make_tuple_and_list_partial_sums :
  forall (xs : tuple),
    make_tuple xs 0 =
    removelast (list_partial_sums xs).
Proof.
  intro xs.
  rewrite -> unfold_list_partial_sums.
  exact (equivalence_of_make_tuple_and_list_partial_sums_acc xs 0).
Qed.
Hint Rewrite equivalence_of_make_tuple_and_list_partial_sums : horner.

(** * Triangle constructors *)

(** ** Create triangle horizontally

  *** Definition *)

(* {CREATE_TRIANGLE_HORIZONTALLY} *)
Fixpoint create_triangle_horizontally (xs ys : tuple) : triangle :=
  match ys with
    | [] => []
    | [y] => []
    | y :: (_ :: _) as ys' =>
      let xs' := make_tuple xs y
      in xs' :: (create_triangle_horizontally xs' ys')
  end.
(* {END} *)
Hint Unfold create_triangle_horizontally : dualsieve.

(** *** Unfolding lemmas *)

Lemma unfold_create_triangle_horizontally_base_case_nil :
  forall (xs : tuple),
    create_triangle_horizontally xs [] = [].
Proof.
  intro xs.
  unfold create_triangle_horizontally.
  reflexivity.
Qed.
Hint Rewrite unfold_create_triangle_horizontally_base_case_nil : dualsieve.

Lemma unfold_create_triangle_horizontally_base_case_y_nil :
  forall (xs : tuple) (y : nat),
    create_triangle_horizontally xs [y] = [].
Proof.
  intros xs y.
  unfold create_triangle_horizontally.
  reflexivity.
Qed.
Hint Rewrite unfold_create_triangle_horizontally_base_case_y_nil : dualsieve.

Lemma unfold_create_triangle_horizontally_induction_case :
  forall (xs ys'' : tuple) (y y' : nat),
    create_triangle_horizontally xs (y :: y' :: ys'') =
    (make_tuple xs y) :: (create_triangle_horizontally
                            (make_tuple xs y) (y' :: ys'')).
Proof.
  intros xs ys'' y y'.
  unfold create_triangle_horizontally; fold create_triangle_horizontally.
  reflexivity.
Qed.
Hint Rewrite unfold_create_triangle_horizontally_induction_case : dualsieve.

(** ** Create triangle vertically

  *** Definition *)

(* {CREATE_TRIANGLE_VERTICALLY} *)
Fixpoint create_triangle_vertically (xs ys : tuple) : triangle :=
  match xs with
    | [] => []
    | [x] => []
    | x :: (_ :: _) as xs' =>
      let ys' := make_tuple ys x
      in ys' :: (create_triangle_vertically xs' ys')
  end.
(* {END} *)
Hint Unfold create_triangle_vertically : dualsieve.

(** *** Unfolding lemmas *)

Lemma unfold_create_triangle_vertically_base_case_nil :
  forall (ys : tuple),
    create_triangle_vertically [] ys = [].
Proof.
  intro ys.
  unfold create_triangle_vertically.
  reflexivity.
Qed.
Hint Rewrite unfold_create_triangle_vertically_base_case_nil : dualsieve.

Lemma unfold_create_triangle_vertically_base_case_x_nil :
  forall (ys : tuple) (x : nat),
    create_triangle_vertically [x] ys = [].
Proof.
  intros ys x.
  unfold create_triangle_vertically.
  reflexivity.
Qed.
Hint Rewrite unfold_create_triangle_vertically_base_case_x_nil : dualsieve.

Lemma unfold_create_triangle_vertically_induction_case :
  forall (ys xs'' : tuple) (x x' : nat),
    create_triangle_vertically (x :: x' :: xs'') ys =
    (make_tuple ys x) :: (create_triangle_vertically
                            (x' :: xs'') (make_tuple ys x)).
Proof.
  intros ys xs'' x x'.
  unfold create_triangle_vertically; fold create_triangle_vertically.
  reflexivity.
Qed.
Hint Rewrite unfold_create_triangle_vertically_induction_case : dualsieve.

(** * Equivalence relation of the two triangle creation algorithms *)

(* {EQUIVALENCE_OF_VERTICAL_AND_HORIZONTAL_TRIANGLE_SWAP} *)
Theorem equivalence_of_vertical_and_horizontal_triangle_swap :
  forall (xs ys : tuple),
    (create_triangle_horizontally xs ys) =
    (create_triangle_vertically ys xs).
(* {END} *)
Proof.
  intros xs ys; revert xs.
  induction ys as [ | y ys' IH_ys' ].

  Case "ys = []".
  intro xs.
  rewrite -> unfold_create_triangle_horizontally_base_case_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  reflexivity.

  Case "ys = y :: ys'".
  case xs as [ | x xs' ].

  SCase "xs = []".
  case ys' as [ | y' ys'' ].

  SSCase "ys' = []".
  rewrite -> unfold_create_triangle_horizontally_base_case_y_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  reflexivity.

  SSCase "ys' = y' :: ys''".
  rewrite -> unfold_create_triangle_horizontally_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_make_tuple_base_case_nil.
  rewrite -> (IH_ys' []).
  reflexivity.

  SCase "xs = x :: xs'".
  case ys' as [ | y' ys'' ].

  SSCase "ys' = []".
  rewrite -> unfold_create_triangle_horizontally_base_case_y_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  reflexivity.

  SSCase "ys' = y' :: ys''".
  rewrite -> unfold_create_triangle_horizontally_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> (IH_ys' (make_tuple (x :: xs') y)).
  reflexivity.
Qed.
Hint Rewrite equivalence_of_vertical_and_horizontal_triangle_swap : dualsieve.

(* {EQUIVALENCE_OF_VERTICAL_AND_HORIZONTAL_TRIANGLE_INDICES} *)
Theorem equivalence_of_vertical_and_horizontal_triangle_indices :
  forall (i j : nat) (xs ys : tuple),
    (length xs) = (length ys) ->
    (nth i (nth j (create_triangle_horizontally xs ys) []) 0) =
    (nth j (nth i (create_triangle_vertically xs ys) []) 0).
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  induction j as [ | j' IH_j' ].

  SCase "j = 0".
  case xs as [ | x xs' ].

  SSCase "xs = []".
  intros ys H_length_nil_eq_length_ys.
  rewrite -> unfold_length_base_case in H_length_nil_eq_length_ys.
  symmetry in H_length_nil_eq_length_ys.
  rewrite -> (length_nil_0 ys H_length_nil_eq_length_ys).
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite -> unfold_create_triangle_horizontally_base_case_nil.
  rewrite -> unfold_nth_base_case_nil.
  reflexivity.

  SSCase "xs = x :: xs'".
  case ys as [ | y ys' ].

  SSSCase "ys = []".
  intro H_length_xs_eq_length_ys.
  inversion H_length_xs_eq_length_ys.

  SSSCase "ys = y :: ys'".
  intro H_length_xs_eq_length_ys.
  case xs' as [ | x' xs'' ].

  SSSSCase "xs' = []".
  inversion H_length_xs_eq_length_ys;
    rename H0 into H_0_eq_length_ys'.
  symmetry in H_0_eq_length_ys'.
  rewrite -> (length_nil_0 ys' H_0_eq_length_ys').
  rewrite -> unfold_create_triangle_horizontally_base_case_y_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_nth_base_case_nil.
  reflexivity.

  SSSSCase "xs' = x' :: xs''".
  case ys' as [ | y' ys'' ].

  SSSSSCase "ys' = []".
  inversion H_length_xs_eq_length_ys.

  SSSSSCase "ys' = y' :: ys''".
  rewrite -> unfold_create_triangle_horizontally_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite ->2 unfold_nth_base_case_cons.
  rewrite ->2 unfold_make_tuple_induction_case.
  rewrite ->2 unfold_nth_base_case_cons.
  rewrite -> plus_comm.
  reflexivity.

  SCase "j = S j'".
  case xs as [ | x xs' ].

  SSCase "xs = []".
  intros ys H_length_xs_eq_length_ys.
  rewrite -> unfold_length_base_case in H_length_xs_eq_length_ys.
  symmetry in H_length_xs_eq_length_ys.
  rewrite -> (length_nil_0 ys H_length_xs_eq_length_ys).
  rewrite -> unfold_create_triangle_horizontally_base_case_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite ->2 unfold_nth_base_case_nil.
  rewrite -> unfold_nth_induction_case_nil.
  reflexivity.

  SSCase "xs = x :: xs'".
  case ys as [ | y ys' ].

  SSSCase "ys = []".
  intro H_length_xs_eq_length_ys.
  inversion H_length_xs_eq_length_ys.

  SSSCase "ys = y :: ys'".
  intro H_length_xs_eq_length_ys.
  case xs' as [ | x' xs'' ].

  SSSSCase "xs' = []".
  inversion H_length_xs_eq_length_ys;
    rename H0 into H_0_eq_length_ys'.
  symmetry in H_0_eq_length_ys'.
  rewrite -> (length_nil_0 ys' H_0_eq_length_ys').
  rewrite -> unfold_create_triangle_horizontally_base_case_y_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite ->2 unfold_nth_base_case_nil.
  rewrite -> unfold_nth_induction_case_nil.
  reflexivity.

  SSSSCase "xs' = x' :: xs''".
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  case ys' as [ | y' ys'' ].

  SSSSSCase "ys' = []".
  inversion H_length_xs_eq_length_ys.

  SSSSSCase "ys' = y' :: ys''".
  rewrite -> unfold_create_triangle_horizontally_induction_case.
  rewrite ->2 unfold_make_tuple_induction_case.
  rewrite ->2 unfold_nth_induction_case_cons.

  assert (H_hypothesis_helper: length (x + y :: make_tuple (x' :: xs'') (x + y))
                               = length (y' :: ys'')).
    rewrite -> unfold_length_induction_case.
    rewrite -> S_length_make_tuple.
    rewrite ->2 unfold_length_induction_case.
    inversion H_length_xs_eq_length_ys;
      rename H0 into H_length_xs''_eq_length_ys''.
    rewrite -> H_length_xs''_eq_length_ys''.
    reflexivity.

  rewrite -> (IH_j' (x + y :: make_tuple (x' :: xs'') (x + y)) (y' :: ys'')
                    H_hypothesis_helper); clear H_hypothesis_helper.
  case xs'' as [ | x'' xs''' ].

  SSSSSSCase "xs'' = []".
  inversion H_length_xs_eq_length_ys;
   rename H0 into H_0_eq_length_ys''.
  symmetry in H_0_eq_length_ys''.
  rewrite -> (length_nil_0 ys'' H_0_eq_length_ys'').
  rewrite ->2 unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_nth_base_case_nil.
  rewrite -> nth_n_nil.
  reflexivity.

  SSSSSSCase "xs'' = x'' :: xs'''".
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> plus_comm.
  reflexivity.

  Case "i = S i'".
  induction j as [ | j' IH_j' ].

  SCase "j = 0".
  case xs as [ | x xs' ].

  SSCase "xs = []".
  intros ys H_length_xs_eq_length_ys.
  rewrite -> unfold_length_base_case in H_length_xs_eq_length_ys.
  symmetry in H_length_xs_eq_length_ys.
  rewrite -> (length_nil_0 ys H_length_xs_eq_length_ys).
  rewrite -> unfold_create_triangle_horizontally_base_case_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite ->2 unfold_nth_induction_case_nil.
  rewrite -> unfold_nth_base_case_nil.
  reflexivity.

  SSCase "xs = x :: xs'".
  case ys as [ | y ys' ].

  SSSCase "ys = []".
  intro H_length_xs_eq_length_ys.
  inversion H_length_xs_eq_length_ys.

  SSSCase "ys = y :: ys'".
  case ys' as [ | y' ys'' ].

  SSSSCase "ys = []".
  intro H_length_xs_eq_length_ys.
  rewrite -> unfold_create_triangle_horizontally_base_case_y_nil.
  rewrite -> unfold_nth_base_case_nil.
  rewrite -> unfold_nth_induction_case_nil.
  case xs' as [ | x' xs'' ].

  SSSSSCase "xs' = []".
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_nth_induction_case_nil.
  rewrite -> unfold_nth_base_case_nil.
  reflexivity.

  SSSSSCase "xs' = x' :: xs''".
  inversion H_length_xs_eq_length_ys.

  SSSSCase "ys' = y' :: ys''".
  rewrite -> unfold_create_triangle_horizontally_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  case xs' as [ | x' xs'' ].

  SSSSSCase "xs' = []".
  intro H_length_xs_eq_length_ys.
  inversion H_length_xs_eq_length_ys.

  SSSSSCase "xs' = x' :: xs''".
  intro H_length_xs_eq_length_ys.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_nth_induction_case_cons.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_nth_induction_case_cons.

  assert (H_hypothesis_helper:
            length (x' :: xs'') = length (make_tuple (y :: y' :: ys'') x)).
    rewrite <- (S_length_make_tuple xs'' x' x).
    rewrite -> unfold_make_tuple_induction_case.
    rewrite -> unfold_length_induction_case.
    inversion H_length_xs_eq_length_ys;
      rename H0 into H_length_xs''_eq_length_ys''.
    rewrite <- (length_tuples_xs_a_eq_ys_b (x' :: xs'') (y' :: ys'') x (y + x)).
    reflexivity.
    rewrite ->2 unfold_length_induction_case.
    rewrite -> H_length_xs''_eq_length_ys''.
    reflexivity.

  rewrite <- (IH_i' 0 (x' :: xs'') (make_tuple (y :: y' :: ys'') x)
                    H_hypothesis_helper);
      clear H_hypothesis_helper.

  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> plus_comm.
  case xs'' as [ | x'' xs''' ].

  SSSSSSCase "xs'' = []".
  inversion H_length_xs_eq_length_ys;
    rename H0 into H_0_eq_length_ys''.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> nth_n_nil.
  symmetry in H_0_eq_length_ys''.
  rewrite -> (length_nil_0 ys'' H_0_eq_length_ys'').
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_create_triangle_horizontally_base_case_y_nil.
  rewrite -> unfold_nth_base_case_nil.
  rewrite -> nth_n_nil.
  reflexivity.

  SSSSSSCase "xs'' = x'' :: xs'''".
  inversion H_length_xs_eq_length_ys;
    rename H0 into H_S_length_xs'''_eq_length_ys''.
  rewrite -> unfold_make_tuple_induction_case.
  case ys'' as [ | y'' ys''' ].

  SSSSSSSCase "ys'' = []".
  inversion H_length_xs_eq_length_ys.

  SSSSSSSCase "ys'' = y'' :: ys'''".
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_create_triangle_horizontally_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> unfold_make_tuple_induction_case.
  reflexivity.

  SCase "j = S j'".
  case xs as [ | x xs' ].

  SSCase "xs = []".
  intros ys H_length_xs_eq_length_ys.
  rewrite -> unfold_length_base_case in H_length_xs_eq_length_ys.
  symmetry in H_length_xs_eq_length_ys.
  rewrite -> (length_nil_0 ys H_length_xs_eq_length_ys).
  rewrite -> unfold_create_triangle_horizontally_base_case_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite -> unfold_nth_induction_case_nil.
  rewrite -> unfold_nth_induction_case_nil.
  reflexivity.

  SSCase "xs = x :: xs'".
  case ys as [ | y ys' ].

  SSSCase "ys = []".
  intro H_length_xs_eq_length_ys.
  inversion H_length_xs_eq_length_ys.

  SSSCase "ys = y :: ys'".
  case ys' as [ | y' ys'' ].

  SSSSCase "ys' = []".
  intro H_length_xs_eq_length_ys.
  inversion H_length_xs_eq_length_ys;
    rename H0 into H_length_xs'_eq_0.
  rewrite -> (length_nil_0 xs' H_length_xs'_eq_0).
  rewrite -> unfold_create_triangle_horizontally_base_case_y_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_length_base_case.
  rewrite ->2 unfold_nth_induction_case_nil.
  reflexivity.

  SSSSCase "ys' = y' :: ys''".
  intro H_length_xs_eq_length_ys.
  case xs' as [ | x' xs'' ].

  SSSSSCase "xs' = []".
  inversion H_length_xs_eq_length_ys.

  SSSSSCase "xs' = x' :: xs''".
  rewrite -> unfold_create_triangle_horizontally_induction_case.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_nth_induction_case_cons.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_nth_induction_case_cons.

  assert (H_hypothesis_helper:
          length (x + y :: make_tuple (x' :: xs'') (x + y)) =
          length (y' :: ys'')).
    rewrite -> unfold_length_induction_case.
    rewrite -> S_length_make_tuple.
    apply eq_add_S.
    exact H_length_xs_eq_length_ys.

  rewrite -> (IH_j' (x + y :: make_tuple (x' :: xs'') (x + y))
                    (y' :: ys'')
                    H_hypothesis_helper);
      clear H_hypothesis_helper.
  case xs'' as [ | x'' xs''' ].

  SSSSSSCase "xs'' = []".
  inversion H_length_xs_eq_length_ys;
    rename H0 into H_0_eq_length_ys''.
  symmetry in H_0_eq_length_ys''.
  rewrite -> (length_nil_0 ys'' H_0_eq_length_ys'').
  rewrite ->2 unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_nth_induction_case_nil.
  rewrite ->2 nth_n_nil.
  rewrite -> unfold_nth_induction_case_nil.
  reflexivity.

  SSSSSSCase "xs'' = x'' :: xs'''".
  case ys'' as [ | y'' ys''' ].

  SSSSSSSCase "ys'' = []".
  inversion H_length_xs_eq_length_ys.

  SSSSSSSCase "ys'' = y'' :: ys'''".
  rewrite -> plus_comm.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_nth_induction_case_cons.

  assert (H_hypothesis_helper:
          length (x' :: x'' :: xs''') =
          length (y + x :: y' + (y + x) ::
            make_tuple (y'' :: ys''') (y' + (y + x)))).
    rewrite ->4 unfold_length_induction_case.
    rewrite -> S_length_make_tuple.
    rewrite -> unfold_length_induction_case.
    inversion H_length_xs_eq_length_ys.
      rename H0 into H_length_xs'''_eq_length_ys'''.
    rewrite -> H_length_xs'''_eq_length_ys'''.
    reflexivity.

  rewrite <- (IH_i' (S j') (x' :: x'' :: xs''')
                    (y + x :: y' + (y + x) ::
                      make_tuple (y'' :: ys''') (y' + (y + x)))
                    H_hypothesis_helper);
      clear H_hypothesis_helper.

  rewrite -> unfold_create_triangle_horizontally_induction_case.
  rewrite -> unfold_nth_induction_case_cons.

  assert (H_hypothesis_helper:
            length (make_tuple (x' :: x'' :: xs''') (y + x)) =
            length (y' + (y + x) :: make_tuple (y'' :: ys''') (y' + (y + x)))).
    rewrite -> unfold_make_tuple_induction_case.
    rewrite ->2 unfold_length_induction_case.
    rewrite <- (length_tuples_xs_a_eq_ys_b (x'' :: xs''') (y'' :: ys''')
                                           (x' + (y + x)) (y' + (y + x))).
    reflexivity.
    inversion H_length_xs_eq_length_ys.
      rename H0 into H_length_xs'''_eq_length_ys'''.
    rewrite ->2 unfold_length_induction_case.
    rewrite -> H_length_xs'''_eq_length_ys'''.
    reflexivity.

  rewrite -> (IH_i' j'
                    (make_tuple (x' :: x'' :: xs''') (y + x))
                    (y' + (y + x) :: make_tuple (y'' :: ys''') (y' + (y + x)))
                    H_hypothesis_helper);
      clear H_hypothesis_helper.

  rewrite -> unfold_make_tuple_induction_case.
  reflexivity.
Qed.
Hint Rewrite equivalence_of_vertical_and_horizontal_triangle_indices
   : dualsieve.

(** * Dual sieve *)

(** ** Hypotenuse

  *** Definition *)

(* {HYPOTENUSE} *)
Fixpoint hypotenuse (ts : triangle) : tuple :=
  match ts with
    | [] => []
    | t :: ts' => (last t 0) :: (hypotenuse ts')
  end.
(* {END} *)
Hint Unfold hypotenuse : dualsieve.

(** *** Unfolding lemmas *)

Lemma unfold_hypotenuse_base_case :
  hypotenuse [] = [].
Proof.
  unfold hypotenuse.
  reflexivity.
Qed.
Hint Rewrite unfold_hypotenuse_base_case : dualsieve.

Lemma unfold_hypotenuse_induction_case :
  forall (t : tuple) (ts' : triangle),
    hypotenuse (t :: ts') = (last t 0) :: (hypotenuse ts').
Proof.
  intros t ts'.
  unfold hypotenuse; fold hypotenuse.
  reflexivity.
Qed.
Hint Rewrite unfold_hypotenuse_induction_case : dualsieve.

(** ** Create triangles vertically

  *** Definition *)

(* {CREATE_TRIANGLES_VERTICALLY} *)
Fixpoint create_triangles_vertically (n : nat) (xs ys : tuple)
  : list triangle :=
  match n with
    | 0 => [create_triangle_vertically xs ys]
    | S n' =>
      let ts := create_triangle_vertically xs ys
      in ts :: (create_triangles_vertically n' xs
                 (rev (cons 0 (hypotenuse ts))))
  end.
(* {END} *)
Hint Unfold create_triangles_vertically : dualsieve.

(** *** Unfolding lemmas *)

Lemma unfold_create_triangles_vertically_base_case :
  forall (xs ys : tuple),
    create_triangles_vertically 0 xs ys =
    [(create_triangle_vertically xs ys)].
Proof.
  intros xs ys.
  unfold create_triangles_vertically.
  reflexivity.
Qed.
Hint Rewrite unfold_create_triangles_vertically_base_case : dualsieve.

Lemma unfold_create_triangles_vertically_induction_case :
  forall (n' : nat) (xs ys : tuple),
    create_triangles_vertically (S n') xs ys =
    (create_triangle_vertically xs ys)
      :: (create_triangles_vertically
            n'
            xs
            ((rev (cons 0 (hypotenuse
                           (create_triangle_vertically xs ys)))))).
Proof.
  intros n' xs ys.
  unfold create_triangles_vertically;
    fold create_triangles_vertically.
  reflexivity.
Qed.
Hint Rewrite unfold_create_triangles_vertically_induction_case : dualsieve.