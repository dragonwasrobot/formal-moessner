(* MoessnersTheorem.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Moessner's theorem *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.

(* 3rd party *)
Require Import paco.

(* Own modules *)
Require Import Cases.
Require Import Power.
Require Import BinomialCoefficients.
Require Import ListCalculus.
Require Import StreamCalculus.
Require Import DualMoessnersSieve.
Require Import CharacteristicFunction.

(** * Moessner's theorem *)

(** Decomposition proof of rotated moessner entry, which is actually a part of
  the TriangleGrid.v script, but put here due to interdependency *)

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
  rewrite -> (IH_c' n t).
  rewrite -> rotated_moessner_entry_r_eq_0_implies_1.
  rewrite -> mult_1_r.
  reflexivity.

  Case "r = S r'".
  induction c as [ | c' IH_c' ].

  SCase "c = 0".
  intros n t.
  rewrite -> rotated_moessner_entry_c_eq_0.
  rewrite -> (IH_r' 0 n t).
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

(** * Equivalence between [rotated_moessner_entry] and [monomial] *)

(* {ROTATED_MOESSNER_ENTRY_CONSTRAINED_NEGATIVE_PASCAL_S_RULE} *)
Lemma rotated_moessner_entry_constrained_negative_Pascal_s_rule :
  forall (n' k' t : nat),
    S k' <= n' ->
    rotated_moessner_entry n' k' (n' - k') t +
    rotated_moessner_entry n' (S k') (n' - S k') t =
    rotated_moessner_entry n' (S k') (n' - k') t.
(* {END} *)
Proof.
  induction n' as [ | n'' IH_n'' ].

  Case "n' = 0".
  intros k' t H_absurd.
  inversion H_absurd.

  Case "n' = S n''".
  induction k' as [ | k'' IH_k'' ].

  SCase "k' = 0".
  intros t _.
  unfold minus; fold minus.
  rewrite <- minus_n_O.
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  reflexivity.

  SCase "k' = S k''".
  intros t H_S_S_k''_le_S_n''.
  rewrite <- (minus_Sn_m);
    [ idtac | apply gt_S_le; unfold gt, lt; exact H_S_S_k''_le_S_n'' ].
  rewrite ->3 rotated_moessner_entry_Pascal_s_rule.
  rewrite -> NPeano.Nat.sub_succ.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_constrained_negative_Pascal_s_rule : mosthe.

(* {ROTATED_MOESSNER_ENTRY_EQ_MONOMIAL} *)
Theorem rotated_moessner_entry_eq_monomial :
  forall (n k t : nat),
    k <= n ->
    rotated_moessner_entry n k (n - k) t =
    monomial (S t) n k.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros k t H_k_le_0.
  inversion_clear H_k_le_0.
  rewrite <- minus_n_O.
  rewrite -> rotated_moessner_entry_r_eq_0_implies_1.
  rewrite -> monomial_k_eq_0_implies_1.
  reflexivity.

  Case "n = S n'".
  induction k as [ | k' IH_k' ].

  SCase "k = 0".
  intros t _.
  rewrite <- minus_n_O.
  rewrite -> rotated_moessner_entry_r_eq_0_implies_1.
  rewrite -> monomial_k_eq_0_implies_1.
  reflexivity.

  SCase "k = S k'".
  intros t H_S_k'_le_S_n'.
  inversion_clear H_S_k'_le_S_n'.

  SSCase "k' = n'".
  rewrite -> minus_diag.
  rewrite -> rotated_moessner_entry_rank_decompose_by_row.
  specialize (IH_n' n' t).
  rewrite -> minus_diag in IH_n'.
  rewrite -> IH_n'; [ idtac | apply le_n ].
  rewrite -> rotated_moessner_entry_c_eq_0.
  rewrite -> IH_n'; [ idtac | apply le_n ].
  rewrite -> monomial_decompose_rank.
  unfold mult; fold mult.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  rewrite -> (monomial_r_lt_n_implies_0 t n' (S n'));
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  rewrite -> (monomial_r_lt_n_implies_0 (S t) n' (S n'));
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  reflexivity.

  SSCase "S k' <= n'".
  subst; rename H into H_S_k'_le_n'.
  rewrite <- minus_Sn_m;
    [ idtac | apply H_S_k'_le_n' ].
  rewrite -> rotated_moessner_entry_rank_decompose_by_row.
  rewrite -> monomial_decompose_rank.
  rewrite <- (IH_n' (S k') t);
    [ idtac | apply H_S_k'_le_n' ].
  rewrite -> minus_Sn_m;
    [ idtac | apply H_S_k'_le_n' ].
  rewrite -> NPeano.Nat.sub_succ.
  rewrite <- (IH_n' k' t);
    [ idtac | apply lt_le_weak; unfold lt; exact H_S_k'_le_n' ].
  unfold mult; fold mult.
  symmetry.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.

  rewrite <- (plus_permute
                (t * rotated_moessner_entry n' k' (n' - k') t) _).
  f_equal.

  rewrite -> rotated_moessner_entry_constrained_negative_Pascal_s_rule;
    [ idtac | apply H_S_k'_le_n' ].
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_eq_monomial : mosthe.

(* {MOESSNER_ENTRY_EQ_MONOMIAL} *)
Corollary moessner_entry_eq_monomial :
  forall (n k t : nat),
    k <= n ->
    moessner_entry n n (n - k) t =
    monomial (S t) n k.
(* {END} *)
Proof.
  intros n k t H.
  assert (H_helper:
            moessner_entry n n (n - k) t =
            moessner_entry n (n - k + k) (n - k) t).
    rewrite -> (NPeano.Nat.sub_add k n H).
    reflexivity.

  rewrite -> H_helper; clear H_helper.
  rewrite <- unfold_rotated_moessner_entry.
  rewrite -> (rotated_moessner_entry_eq_monomial n k t H).
  reflexivity.
Qed.
Hint Rewrite moessner_entry_eq_monomial : mosthe.

(** ** The Binomial Theorem *)

(* {BINOMIAL_THEOREM} *)
Theorem Binomial_theorem :
  forall (t n : nat),
    (S t) ^ n = Str_nth (S n) (stream_partial_sums (monomials t n 0)).
(* {END} *)
Proof.
  intros t n.
  rewrite -> stream_partial_sums_monomials_bisim_monomials_sum.
  rewrite -> Str_nth_monomials_sum_eq_rotated_moessner_entry;
    rewrite -> plus_0_r.
  rewrite -> rotated_moessner_entry_c_eq_0.
  rewrite -> monomial_r_lt_n_implies_0;
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  rewrite <- (minus_diag n);
    rewrite -> rotated_moessner_entry_eq_monomial;
    [ idtac | apply le_n ].
  rewrite -> monomial_r_eq_n_implies_power.
  reflexivity.
Qed.
Hint Rewrite Binomial_theorem : mosthe.

(** * Moessner's theorem *)

(** * Proof that the hypotenuse of a created triangle is equal to [monomials] *)

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY_ROTATED_MOESSNER_ENTRIES} *)
Theorem hypotenuse_create_triangle_vertically_rotated_moessner_entries :
  forall (n r c t : nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S n) 0)
         (Str_prefix (S n) (rotated_moessner_entries r 0 c t))) =
    Str_prefix n (moessner_entries r (c + n) (S c) t).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r c t.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_hypotenuse_base_case.
  reflexivity.

  Case "n = S n'".
  intros r c t.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite <-2 unfold_Str_prefix_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite -> unfold_hypotenuse_induction_case.

  symmetry.

  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> moessner_entries_initial_value.
  rewrite -> moessner_entries_stream_derivative.
  rewrite -> make_tuple_rotated_moessner_entries.
  f_equal.

  SCase "head".
  rewrite -> last_of_rotated_moessner_entries_to_binomial.
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.

  SCase "tail".
  rewrite -> (IH_n' r (S c) t).
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically_rotated_moessner_entries
  : mosthe.

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY_MONOMIALS} *)
Theorem hypotenuse_create_triangle_vertically_monomials :
  forall (n r t : nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S (S n)) 0)
         (Str_prefix (S (S n)) (monomials t r 0))) =
    (Str_prefix (S n) (moessner_entries r n 0 t)).
(* {END} *)
Proof.
  intros n r t.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite <-2 unfold_Str_prefix_induction_case.
  rewrite -> make_tuple_monomials_eq_monomials_sum.
  rewrite -> rotated_moessner_entries_bisim_monomials_sum.
  rewrite -> unfold_hypotenuse_induction_case.
  symmetry.
  rewrite -> unfold_Str_prefix_induction_case.
  f_equal.

  Case "head".
  rewrite -> (length_implies_last_index n);
    [ idtac | rewrite -> Str_prefix_length; reflexivity ].
  rewrite -> nth_and_Str_nth;
    [ idtac | unfold lt; apply le_n ].
  rewrite -> Str_nth_rotated_moessner_entries.
  rewrite -> plus_0_l.
  rewrite -> moessner_entries_initial_value.
  reflexivity.

  Case "tail".
  rewrite -> moessner_entries_stream_derivative.
  symmetry.

  rewrite -> hypotenuse_create_triangle_vertically_rotated_moessner_entries.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically_monomials
  : mosthe.

(** ** Monomials list

  *** Definition *)

(* {MONOMIALS_LIST} *)
Fixpoint monomials_list (t r n : nat) : list nat :=
  match n with
    | 0 => [monomial t r 0]
    | S n' => (monomial t r (S n')) :: (monomials_list t r n')
  end.
(* {END} *)
Hint Unfold monomials_list : mosthe.

(** *** Unfolding lemmas *)

Lemma unfold_monomials_list_base_case :
  forall (t r : nat),
    monomials_list t r 0 = [monomial t r 0].
Proof.
  intros t r.
  unfold monomials_list.
  reflexivity.
Qed.
Hint Rewrite unfold_monomials_list_base_case : mosthe.

Lemma unfold_monomials_list_induction_case :
  forall (t r n' : nat),
    monomials_list t r (S n') =
    (monomial t r (S n')) :: (monomials_list t r n').
Proof.
  intros t r n'.
  unfold monomials_list; fold monomials_list.
  reflexivity.
Qed.
Hint Rewrite unfold_monomials_list_induction_case : mosthe.

(** *** Properties *)

(* {MONOMIALS_LIST_EQ_REV_STR_PREFIX_MONOMIALS} *)
Lemma monomials_list_eq_rev_Str_prefix_monomials :
  forall (n r t : nat),
    monomials_list t r n =
    rev (Str_prefix (S n) (monomials t r 0)).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r t.
  rewrite -> unfold_monomials_list_base_case.

  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> monomials_initial_value.
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> app_nil_l.
  reflexivity.

  Case "n = S n'".
  intros r t.
  rewrite -> unfold_monomials_list_induction_case.
  rewrite -> (IH_n' r t).
  symmetry.

  rewrite -> rev_Str_prefix_monomials.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite monomials_list_eq_rev_Str_prefix_monomials : mosthe.

(* {MONOMIALS_LIST_EQ_STR_PREFIX_MOESSNER_ENTRIES} *)
Lemma monomials_list_eq_Str_prefix_moessner_entries :
  forall (l n t' : nat),
    l <= n ->
    Str_prefix (S l) (moessner_entries n n (n - l) t') =
    monomials_list (S t') n l.
(* {END} *)
Proof.
  induction l as [ | l' IH_l' ].

  Case "l = 0".
  intros n t' H_0_le_n.
  rewrite <- minus_n_O.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> moessner_entries_initial_value.
  rewrite -> moessner_entry_n_eq_k_implies_1.

  rewrite -> unfold_monomials_list_base_case.
  rewrite -> unfold_monomial.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  rewrite -> unfold_power_base_case.
  rewrite -> mult_1_r.
  reflexivity.

  Case "l = S l'".
  intros n t' H_S_l'_le_n.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> moessner_entries_stream_derivative.
  rewrite -> minus_Sn_m;
    [ idtac | apply H_S_l'_le_n ].
  rewrite -> NPeano.Nat.sub_succ.
  rewrite -> IH_l';
    [ idtac | apply lt_le_weak; unfold lt; exact H_S_l'_le_n ].
  rewrite -> moessner_entries_initial_value.
  rewrite -> unfold_monomials_list_induction_case.
  f_equal.
  rewrite -> moessner_entry_eq_monomial;
    [ reflexivity | exact H_S_l'_le_n ].
Qed.
Hint Rewrite monomials_list_eq_Str_prefix_moessner_entries : mosthe.

(* {REV_STR_PREFIX_MOESSNER_ENTRIES_EQ_MONOMIALS} *)
Lemma rev_Str_prefix_moessner_entries_eq_monomials :
  forall (r t' : nat),
    Str_prefix (S r) (moessner_entries r r 0 t') =
    rev (Str_prefix (S r) (monomials (S t') r 0)).
(* {END} *)
Proof.
  intros r t'.
  rewrite <- (minus_diag r).
  rewrite -> monomials_list_eq_Str_prefix_moessner_entries;
    [ idtac | apply le_n ].
  rewrite -> monomials_list_eq_rev_Str_prefix_monomials.
  rewrite -> minus_diag.
  reflexivity.
Qed.
Hint Rewrite rev_Str_prefix_moessner_entries_eq_monomials : mosthe.

Lemma pad_monomials :
  forall (r t n : nat),
    Str_prefix (S (S r)) (monomials (S t) r n) =
    Str_prefix (S r) (monomials (S t) r n) ++ [0].
Proof.
  intros r t n.
  rewrite -> Str_prefix_split_with_Str_nth.
  unfold Str_nth.
  rewrite -> monomials_tail_of_0s.
  rewrite -> stream_constant_initial_value.
  reflexivity.
Qed.
Hint Rewrite pad_monomials : mosthe.

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY} *)
Theorem hypotenuse_create_triangle_vertically :
  forall (r t' : nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (monomials t' r 0))) =
    (rev (Str_prefix (S r) (monomials (S t') r 0))).
(* {END} *)
Proof.
  intros r t'.
  rewrite -> hypotenuse_create_triangle_vertically_monomials.
  exact (rev_Str_prefix_moessner_entries_eq_monomials r t').
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically : mosthe.

(** * Characterization of the [n]th triangle *)

(* {NTH_TRIANGLE_CREATE_TRIANGLES_VERTICALLY} *)
Theorem nth_triangle_create_triangles_vertically :
  forall (n r t : nat),
    nth n
      (create_triangles_vertically
         n
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (monomials t r 0)))
      [] =
    (create_triangle_vertically
       (tuple_constant (S (S r)) 0)
       (Str_prefix (S (S r)) (monomials (n + t) r 0))).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r t.
  rewrite -> unfold_create_triangles_vertically_base_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> plus_0_l.
  reflexivity.

  Case "n = S n'".
  intros r t.
  rewrite -> unfold_create_triangles_vertically_induction_case.
  rewrite -> hypotenuse_create_triangle_vertically.
  rewrite -> unfold_rev_induction_case.
  rewrite -> rev_involutive.
  rewrite <- pad_monomials.
  rewrite -> unfold_nth_induction_case_cons.
  rewrite -> (IH_n' r (S t)).
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite nth_triangle_create_triangles_vertically : mosthe.

Corollary hypotenuse_of_last_triangle_create_triangles_vertically :
  forall (n r t : nat),
    hypotenuse
      (nth n
           (create_triangles_vertically
              n
              (tuple_constant (S (S r)) 0)
              (Str_prefix (S (S r)) (monomials t r 0)))
           []) =
    monomials_list (S (n + t)) r r.
Proof.
  intros n r t.
  rewrite -> nth_triangle_create_triangles_vertically.
  rewrite -> hypotenuse_create_triangle_vertically.
  rewrite <- monomials_list_eq_rev_Str_prefix_monomials.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_of_last_triangle_create_triangles_vertically
  : mosthe.

Corollary bottom_element_of_nth_triangle_create_triangles_vertically :
  forall (n r t : nat),
    nth 0
        (hypotenuse
           (nth n
                (create_triangles_vertically
                   n
                   (tuple_constant (S (S r)) 0)
                   (Str_prefix (S (S r)) (monomials t r 0)))
                []))
        1 = monomial (S (n + t)) r r.
Proof.
  intros n r t.
  rewrite -> hypotenuse_of_last_triangle_create_triangles_vertically.
  case r as [ | r' ].

  Case "r = 0".
  rewrite -> unfold_monomials_list_base_case.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.

  Case "r = S r'".
  rewrite -> unfold_monomials_list_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.
Qed.
Hint Rewrite bottom_element_of_nth_triangle_create_triangles_vertically
  : mosthe.

(* {BOTTOM_ELEMENT_OF_NTH_TRIANGLE_IS_POWER} *)
Corollary bottom_element_of_nth_triangle_is_power :
  forall (n r : nat),
    nth 0
        (hypotenuse
           (nth n
                (create_triangles_vertically
                   n
                   (tuple_constant (S (S r)) 0)
                   (Str_prefix (S (S r)) (monomials 0 r 0)))
                []))
        1 = (S n) ^ r.
(* {END} *)
Proof.
  intros n r.
  rewrite -> bottom_element_of_nth_triangle_create_triangles_vertically.
  rewrite -> monomial_r_eq_n_implies_power.
  rewrite -> plus_0_r.
  reflexivity.
Qed.
Hint Rewrite bottom_element_of_nth_triangle_is_power : mosthe.

(** ** Moessner Stream

  *** Definition *)

(* {MOESSNER_STREAM} *)
CoFixpoint moessner_stream (n r : nat) : Stream nat :=
  (nth 0 (hypotenuse
            (nth n
                 (create_triangles_vertically
                    n
                    (tuple_constant (S (S r)) 0)
                    (Str_prefix (S (S r)) (monomials 0 r 0)))
                 [])) 1)
    ::: (moessner_stream (S n) r).
(* {END} *)
Hint Unfold moessner_stream : mosthe.

(** *** Unfolding lemmas *)

Lemma unfold_moessner_stream :
  forall (n r : nat),
    (moessner_stream n r) =
    (nth 0 (hypotenuse
              (nth n
                   (create_triangles_vertically
                      n
                      (tuple_constant (S (S r)) 0)
                      (Str_prefix (S (S r)) (monomials 0 r 0)))
                   [])) 1)
      ::: (moessner_stream (S n) r).
Proof.
  intros n r.
  rewrite -> (unfold_Stream (moessner_stream n r)).
  unfold moessner_stream; fold moessner_stream.
  reflexivity.
Qed.
Hint Rewrite unfold_moessner_stream : mosthe.

Lemma moessner_stream_initial_value :
  forall (n r : nat),
    (moessner_stream n r)(0) =
    (nth 0 (hypotenuse
              (nth n
                   (create_triangles_vertically
                      n
                      (tuple_constant (S (S r)) 0)
                      (Str_prefix (S (S r)) (monomials 0 r 0)))
                   [])) 1).
Proof.
  intros n r.
  rewrite -> initial_value.
  rewrite -> unfold_moessner_stream.
  reflexivity.
Qed.
Hint Rewrite moessner_stream_initial_value : mosthe.

Lemma moessner_stream_stream_derivative :
  forall (n r : nat),
    (moessner_stream n r)` = (moessner_stream (S n) r).
Proof.
  intros n r.
  rewrite -> stream_derivative.
  rewrite -> unfold_moessner_stream.
  reflexivity.
Qed.
Hint Rewrite moessner_stream_stream_derivative : mosthe.

(** ** Moessner's theorem *)

(* {MOESSNER_S_THEOREM} *)
Theorem Moessner_s_theorem :
  forall (b e : nat),
    moessner_stream b e ~ successive_powers b e.
(* {END} *)
Proof.
  pcofix coIH.
  intros b e.
  bisimilar.

  Case "initial value".
  rewrite -> moessner_stream_initial_value.
  rewrite -> bottom_element_of_nth_triangle_is_power.
  rewrite -> successive_powers_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> moessner_stream_stream_derivative.
  rewrite -> successive_powers_stream_derivative.
  exact (coIH (S b) e).
Qed.
Hint Rewrite Moessner_s_theorem : mosthe.
