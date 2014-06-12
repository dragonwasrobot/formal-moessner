(* TriangleGrid. *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * A Grid of Triangles *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.

(* Own modules *)
Require Import Cases.
Require Import BinomialCoefficients.
Require Import ListCalculus.
Require Import StreamCalculus.
Require Import DualMoessnersSieve.
Require Import CharacteristicFunction.
Require Import MoessnersTheorem.

(** * Upgrade seed tuple procedure *)

(** ** Monomial rank decomposition *)

(*
(* {MONOMIAL_DECOMPOSE_RANK} *)
Theorem monomial_decompose_rank :
  forall (t r' n' : nat),
    monomial t (S r') (S n') =
    monomial t r' (S n') + t * monomial t r' n'.
(* {END} *)
*)

(** ** Upgrade seed tuple aux

  *** Definition *)

(* {UPGRADE_SEED_TUPLE_AUX} *)
Fixpoint upgrade_seed_tuple_aux (t a : nat) (xs : tuple) : tuple :=
  match xs with
    | [] => [a]
    | x :: xs' => (S t) * x + a :: upgrade_seed_tuple_aux t x xs'
  end.
(* {END} *)
Hint Unfold upgrade_seed_tuple_aux : trigrid.

(** *** Unfolding lemmas *)

Lemma unfold_upgrade_seed_tuple_aux_base_case :
  forall (t a : nat),
    upgrade_seed_tuple_aux t a [] = [a].
Proof.
  intros t a.
  unfold upgrade_seed_tuple_aux.
  reflexivity.
Qed.
Hint Rewrite unfold_upgrade_seed_tuple_aux_base_case : trigrid.

Lemma unfold_upgrade_seed_tuple_aux_induction_case :
  forall (t a x : nat) (xs' : tuple),
    upgrade_seed_tuple_aux t a (x :: xs') = (S t) * x + a :: upgrade_seed_tuple_aux t x xs'.
Proof.
  intros t a x xs'.
  unfold upgrade_seed_tuple_aux; fold upgrade_seed_tuple_aux.
  reflexivity.
Qed.
Hint Rewrite unfold_upgrade_seed_tuple_aux_induction_case : trigrid.

(** *** Properties *)

(* {CORRECTNESS_OF_UPGRADE_SEED_TUPLE_AUX_LIST} *)
Lemma correctness_of_upgrade_seed_tuple_aux_list :
   forall n r t : nat,
     upgrade_seed_tuple_aux
       t (monomial (S t) r (S n)) (monomials_list (S t) r n) =
     monomials_list (S t) (S r) (S n).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r t.
  rewrite -> unfold_monomials_list_induction_case.
  rewrite ->2 unfold_monomials_list_base_case.
  rewrite -> unfold_upgrade_seed_tuple_aux_induction_case.
  rewrite -> unfold_upgrade_seed_tuple_aux_base_case.
  rewrite -> plus_comm.
  rewrite <- monomial_decompose_rank.
  rewrite ->2 monomial_k_eq_0_implies_1.
  reflexivity.

  Case "n = S n'".
  intros r t.
  symmetry.
  rewrite -> unfold_monomials_list_induction_case.
  rewrite <- (IH_n' r t).
  rewrite -> unfold_monomials_list_induction_case.
  rewrite -> unfold_upgrade_seed_tuple_aux_induction_case.
  f_equal.
  rewrite -> plus_comm.
  rewrite <- monomial_decompose_rank.
  reflexivity.
Qed.
Hint Rewrite correctness_of_upgrade_seed_tuple_aux_list : trigrid.

(* {CORRECTNESS_OF_UPGRADE_SEED_TUPLE_AUX} *)
Theorem correctness_of_upgrade_seed_tuple_aux :
  forall (n t : nat),
    (S t) * (moessner_entry n n 0 t)
              :: upgrade_seed_tuple_aux
              t (moessner_entry n n 0 t)
              (Str_prefix n (moessner_entries n n 1 t)) =
    Str_prefix (S (S n)) (moessner_entries (S n) (S n) 0 t).
(* {END} *)
Proof.
  intros n t.

  (* Rewrite in order to use upgrade_seed_tuple_aux *)
  replace (moessner_entries (S n) (S n) 0 t)
  with (moessner_entries (S n) (S n) ((S n) - (S n)) t);
    [ idtac | rewrite -> minus_diag; reflexivity ].
  rewrite -> (monomials_list_eq_Str_prefix_moessner_entries (S n) (S n) t);
    [ idtac | apply le_n ].

  rewrite <- (correctness_of_upgrade_seed_tuple_aux_list n n t).

  (* Now start the actual proof *)
  case n as [ | n' ].

  Case "n = 0".
  rewrite -> unfold_monomials_list_base_case.
  rewrite -> unfold_upgrade_seed_tuple_aux_induction_case.
  rewrite -> unfold_upgrade_seed_tuple_aux_base_case.
  rewrite -> unfold_upgrade_seed_tuple_aux_base_case.
  rewrite <- plus_comm.
  rewrite -> monomial_k_eq_0_implies_1.
  rewrite -> unfold_moessner_entry_base_case_O.
  rewrite -> monomial_r_lt_n_implies_0;
    [ idtac | unfold lt; apply le_n ].
  rewrite -> plus_0_l.
  rewrite -> mult_1_r.
  reflexivity.

  Case "n = S n'".
  symmetry.
  rewrite <- monomials_list_eq_Str_prefix_moessner_entries;
    [ idtac | apply le_n ].
  rewrite -> minus_diag.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_upgrade_seed_tuple_aux_induction_case.
  rewrite -> moessner_entries_initial_value.
  rewrite -> plus_comm.
  rewrite -> monomial_r_lt_n_implies_0;
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  rewrite -> moessner_entries_stream_derivative.
  reflexivity.
Qed.
Hint Rewrite correctness_of_upgrade_seed_tuple_aux : trigrid.

(** ** Upgrade seed tuple

  *** Definition *)

(* {UPGRADE_SEED_TUPLE} *)
Definition upgrade_seed_tuple (t : nat) (xs : tuple) : tuple :=
  upgrade_seed_tuple_aux t 0 xs.
(* {END} *)
Hint Unfold upgrade_seed_tuple : trigrid.

(*
(* {UPGRADE_EXAMPLES} *)
upgrade_seed_tuple 0 (rev (Str_prefix 4 (monomials 1 3 0))) =
rev (Str_prefix 5 (monomials 1 4 0)).

upgrade_seed_tuple 1 (rev (Str_prefix 4 (monomials 2 3 0))) =
rev (Str_prefix 5 (monomials 2 4 0)).

upgrade_seed_tuple 2 (rev (Str_prefix 4 (monomials 3 3 0))) =
rev (Str_prefix 5 (monomials 3 4 0)).
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_upgrade_seed_tuple :
  forall (t : nat) (xs : tuple),
    upgrade_seed_tuple t xs = upgrade_seed_tuple_aux t 0 xs.
Proof.
  intros t xs.
  unfold upgrade_seed_tuple.
  reflexivity.
Qed.
Hint Rewrite unfold_upgrade_seed_tuple : trigrid.

(** *** Properties *)

(* {CORRECTNESS_OF_UPGRADE_SEED_TUPLE} *)
Theorem correctness_of_upgrade_seed_tuple :
  forall (n t : nat),
    upgrade_seed_tuple t (rev (Str_prefix (S n) (monomials (S t) n 0))) =
    rev (Str_prefix (S (S n)) (monomials (S t) (S n) 0)).
(* {END} *)
Proof.
  intros n t.

  (* rewrite goal *)
  rewrite <-2 rev_Str_prefix_moessner_entries_eq_monomials.
  rewrite -> unfold_upgrade_seed_tuple.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> moessner_entries_initial_value.
  rewrite -> moessner_entries_stream_derivative.
  rewrite -> unfold_upgrade_seed_tuple_aux_induction_case.
  rewrite -> plus_0_r.

  (*
  (* {CORRECTNESS_OF_UPGRADE_SEED_TUPLE_INTERMEDIATE} *)
   S t * moessner_entry n n 0 t
   :: upgrade_seed_tuple_aux t (moessner_entry n n 0 t)
        (Str_prefix n (moessner_entries n n 1 t)) =
   Str_prefix (S (S n)) (moessner_entries (S n) (S n) 0 t)
  (* {END} *)
   *)
  rewrite <- correctness_of_upgrade_seed_tuple_aux.

  reflexivity.
Qed.
Hint Rewrite correctness_of_upgrade_seed_tuple : trigrid.

(* {UPGRADE_SEED_TUPLE_CREATE_TRIANGLE_VERTICALLY} *)
Corollary upgrade_seed_tuple_create_triangle_vertically :
  forall (n t : nat),
    upgrade_seed_tuple
      t (hypotenuse
           (create_triangle_vertically
              (tuple_constant (S (S n)) 0)
              (Str_prefix (S (S n)) (monomials t n 0)))) =
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S (S (S n))) 0)
         (Str_prefix (S (S (S n))) (monomials t (S n) 0))).
(* {END} *)
Proof.
  intros n t.
  rewrite ->2 hypotenuse_create_triangle_vertically.
  rewrite -> correctness_of_upgrade_seed_tuple.
  reflexivity.
Qed.
Hint Rewrite upgrade_seed_tuple_create_triangle_vertically : trigrid.

(** * Rank decomposition rules *)

(** ** Rotated moessner entry *)

(* {ROTATED_MOESSNER_ENTRY_RANK_DECOMPOSE_BY_ROW} *)
Theorem rotated_moessner_entry_rank_decompose_by_row :
  forall (r c n t : nat),
  rotated_moessner_entry (S n) (S r) c t =
  t * rotated_moessner_entry n r c t +
  rotated_moessner_entry n (S r) c t.
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  induction c as [ | c' IH_c' ].

  SCase "c = 0".
  intros n t.
  rewrite -> rotated_moessner_entry_r_eq_0_implies_1.
  rewrite -> mult_1_r.
  rewrite ->2 unfold_rotated_moessner_entry.
  rewrite -> plus_0_l.
  rewrite ->2 unfold_moessner_entry_induction_case_O.
  rewrite ->2 unfold_moessner_entry_base_case_O.
  rewrite -> plus_comm.
  symmetry.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  f_equal.
  rewrite ->2 unfold_monomial.
  rewrite -> power_b_1.
  rewrite -> Pascal_s_rule.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  rewrite -> mult_plus_distr_r.
  rewrite -> mult_1_l.
  reflexivity.

  SCase "c = S c'".
  intros n t.
  rewrite -> rotated_moessner_entry_r_eq_0_implies_1.
  rewrite -> mult_1_r.
  rewrite ->2 rotated_moessner_entry_Pascal_s_rule.
  rewrite ->2 rotated_moessner_entry_r_eq_0_implies_1.
  rewrite <- plus_permute.
  f_equal.
  rewrite -> IH_c'.
  rewrite -> rotated_moessner_entry_r_eq_0_implies_1.
  rewrite -> mult_1_r.
  reflexivity.

  Case "r = S r'".
  induction c as [ | c' IH_c' ].

  SCase "c = 0".
  intros n t.
  rewrite -> rotated_moessner_entry_c_eq_0.
  rewrite -> IH_r'.
  symmetry.
  rewrite -> rotated_moessner_entry_c_eq_0.
  rewrite -> mult_plus_distr_l.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  symmetry.
  rewrite <- plus_permute.
  f_equal.
  rewrite -> monomial_decompose_rank.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  symmetry.
  rewrite -> rotated_moessner_entry_c_eq_0.
  reflexivity.

  SCase "c = S c'".
  intros n t.
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  rewrite -> (IH_c' n t).
  rewrite -> (IH_r' (S c') n t).
  symmetry.
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  rewrite -> mult_plus_distr_l.
  rewrite <-3 plus_assoc.
  f_equal.
  symmetry.
  rewrite <-2 (plus_permute (t * rotated_moessner_entry n (S r') c' t)).
  f_equal.
  symmetry.
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  rewrite <- plus_assoc.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_rank_decompose_by_row : trigrid.

(* {MOESSNER_ENTRY_RANK_DECOMPOSE_BY_ROW} *)
Corollary moessner_entry_rank_decompose_by_row :
  forall (r c n t : nat),
   moessner_entry (S n) (c + S r) c t =
   t * moessner_entry n (c + r) c t +
   moessner_entry n (c + S r) c t.
(* {END} *)
Proof.
  intros r c n t.
  rewrite <-3 unfold_rotated_moessner_entry.
  apply rotated_moessner_entry_rank_decompose_by_row.
Qed.
Hint Rewrite moessner_entry_rank_decompose_by_row : trigrid.

(* {ROTATED_MOESSNER_ENTRY_RANK_DECOMPOSE_PASCAL_LIKE_C_EQ_0} *)
Corollary rotated_moessner_entry_rank_decompose_Pascal_like_c_eq_0 :
  forall (r n t : nat),
    rotated_moessner_entry (S n) (S r) 0 t =
    (S t) * rotated_moessner_entry n r 0 t +
    monomial t n (S r).
(* {END} *)
Proof.
  intros r n t.
  rewrite -> rotated_moessner_entry_rank_decompose_by_row.
  unfold mult; fold mult.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  f_equal.
  rewrite -> rotated_moessner_entry_c_eq_0.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_rank_decompose_Pascal_like_c_eq_0 : trigrid.

(* {MOESSNER_ENTRY_RANK_DECOMPOSE_PASCAL_LIKE_C_EQ_0} *)
Corollary moessner_entry_rank_decompose_Pascal_like_c_eq_0 :
  forall (r n t : nat),
    moessner_entry (S n) (S r) 0 t =
    S t * moessner_entry n r 0 t +
    monomial t n (S r).
(* {END} *)
Proof.
  intros r n t.
  rewrite <- (plus_0_l (S r)).
  rewrite <- unfold_rotated_moessner_entry.
  rewrite <- (plus_0_l r).
  rewrite <- unfold_rotated_moessner_entry.
  rewrite -> plus_0_l.
  exact (rotated_moessner_entry_rank_decompose_Pascal_like_c_eq_0 r n t).
Qed.
Hint Rewrite moessner_entry_rank_decompose_Pascal_like_c_eq_0 : trigrid.

(* {ROTATED_MOESSNER_ENTRY_RANK_DECOMPOSE_PASCAL_LIKE_C_GT_0} *)
Corollary rotated_moessner_entry_rank_decompose_Pascal_like_c_gt_0 :
  forall (r c n t : nat),
  rotated_moessner_entry (S n) (S r) (S c) t =
  (S t) * rotated_moessner_entry n r (S c) t +
  rotated_moessner_entry n (S r) c t.
(* {END} *)
Proof.
  intros r c n t.
  rewrite -> rotated_moessner_entry_rank_decompose_by_row.
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  unfold mult; fold mult.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_rank_decompose_Pascal_like_c_gt_0
  : trigrid.

(* {MOESSNER_ENTRY_RANK_DECOMPOSE_PASCAL_LIKE_C_GT_0} *)
Corollary moessner_entry_rank_decompose_Pascal_like_c_gt_0 :
  forall (r c n t : nat),
   moessner_entry (S n) (S c + S r) (S c) t =
   (S t) * moessner_entry n (S c + r) (S c) t +
   moessner_entry n (c + S r) c t.
(* {END} *)
Proof.
  intros r c n t.
  rewrite -> moessner_entry_rank_decompose_by_row.
  rewrite <- plus_n_Sm.
  rewrite -> moessner_entry_Pascal_s_rule.
  unfold mult; fold mult.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite moessner_entry_rank_decompose_Pascal_like_c_gt_0
  : trigrid.

(** ** Create triangle vertically *)

(* {CREATE_TRIANGLE_VERTICALLY_DECOMPOSE_BY_RANK} *)
Corollary create_triangle_vertically_decompose_by_rank :
  forall (i j r t : nat),
    j <= r -> S i <= r - j ->
    (nth (S i) (nth j
      (create_triangle_vertically
        (tuple_constant (S (S (S r))) 0)
        (Str_prefix (S (S (S r))) (monomials t (S r) 0))) []) 0) =
    t * (nth i (nth j
      (create_triangle_vertically
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (monomials t r 0))) []) 0) +
    (nth (S i) (nth j
      (create_triangle_vertically
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (monomials t r 0))) []) 0).
(* {END} *)
Proof.
  intros i j r t H_j_le_r H_S_i_le_r_minus_j.
  rewrite -> correctness_of_rotated_moessner_entry;
    [ idtac |
      apply le_S; apply le_S; exact H_j_le_r |
      rewrite <- minus_Sn_m;
        [ idtac | apply le_S; exact H_j_le_r ];
        apply le_n_S; rewrite <- minus_Sn_m; [ idtac | exact H_j_le_r ];
        apply le_S; exact H_S_i_le_r_minus_j ].

  rewrite -> correctness_of_rotated_moessner_entry;
    [ idtac |
      apply le_S; exact H_j_le_r |
      rewrite <- minus_Sn_m; [ idtac | exact H_j_le_r ];
      apply le_S; exact H_S_i_le_r_minus_j ].

  rewrite -> correctness_of_rotated_moessner_entry;
    [ idtac |
      apply le_S; exact H_j_le_r |
      rewrite <- minus_Sn_m; [ idtac | exact H_j_le_r ];
      apply le_n_S; exact H_S_i_le_r_minus_j ].

  exact (rotated_moessner_entry_rank_decompose_by_row i j r t).
Qed.
Hint Rewrite create_triangle_vertically_decompose_by_rank : trigrid.

(* {CREATE_TRIANGLE_VERTICALLY_RANK_DECOMPOSE_PASCAL_LIKE_C_EQ_0} *)
Corollary create_triangle_vertically_rank_decompose_Pascal_like_c_eq_0 :
  forall (i r t : nat),
    i < (S r) ->
    (nth (S i) (nth 0
      (create_triangle_vertically
         (tuple_constant (S (S (S r))) 0)
         (Str_prefix (S (S (S r))) (monomials t (S r) 0))) []) 0) =
    (S t) * (nth i (nth 0
      (create_triangle_vertically
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (monomials t r 0))) []) 0) +
    monomial t r (S i).
(* {END} *)
Proof.
  intros i r t H_i_lt_S_r.

  rewrite -> correctness_of_rotated_moessner_entry;
    [ idtac |
      exact (le_0_n (S (S r))) |
      unfold lt in H_i_lt_S_r; rewrite <- minus_n_O;
      apply le_n_S; exact H_i_lt_S_r ].

  rewrite -> correctness_of_rotated_moessner_entry;
    [ idtac |
      exact (le_0_n (S r)) |
      unfold lt in H_i_lt_S_r; rewrite <- minus_n_O;
      exact H_i_lt_S_r ].

  exact (rotated_moessner_entry_rank_decompose_Pascal_like_c_eq_0 i r t).
Qed.
Hint Resolve create_triangle_vertically_rank_decompose_Pascal_like_c_eq_0
  : trigrid.

(* {CREATE_TRIANGLE_VERTICALLY_RANK_DECOMPOSE_PASCAL_LIKE_C_GT_0} *)
Corollary create_triangle_vertically_rank_decompose_Pascal_like_c_gt_0 :
  forall (i j r t : nat),
    j <= r -> S i <= r - j ->
    (nth (S i) (nth (S j)
      (create_triangle_vertically
         (tuple_constant (S (S (S r))) 0)
         (Str_prefix (S (S (S r))) (monomials t (S r) 0))) []) 0) =
    (S t) * (nth i (nth (S j)
      (create_triangle_vertically
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (monomials t r 0))) []) 0) +
    (nth (S i) (nth j
      (create_triangle_vertically
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (monomials t r 0))) []) 0).
(* {END} *)
Proof.
  intros i j r t H_j_le_r H_S_i_le_r_minus_j.

  rewrite -> correctness_of_rotated_moessner_entry;
    [ idtac |
      apply le_S; apply le_n_S; exact H_j_le_r |
      rewrite <- minus_Sn_m; [ idtac | apply le_n_S; exact H_j_le_r ];
      unfold minus; fold minus;
      apply le_n_S; exact H_S_i_le_r_minus_j ].

  rewrite -> correctness_of_rotated_moessner_entry;
    [ idtac |
      apply le_n_S; exact H_j_le_r |
      unfold minus; fold minus; exact H_S_i_le_r_minus_j ].

  rewrite -> correctness_of_rotated_moessner_entry;
    [ idtac |
      apply le_S; exact H_j_le_r |
      rewrite <- minus_Sn_m; [ idtac | exact H_j_le_r ];
      apply le_n_S; exact H_S_i_le_r_minus_j ].

  exact (rotated_moessner_entry_rank_decompose_Pascal_like_c_gt_0 i j r t).
Qed.
Hint Rewrite create_triangle_vertically_rank_decompose_Pascal_like_c_gt_0
  : trigrid.