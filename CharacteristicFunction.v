(* CharacteristicFunctionv. *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Characteristic Function *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.

(* Own modules *)
Require Import Cases.
Require Import Power.
Require Import StreamCalculus.
Require Import DualMoessnersSieve.
Require Import BinomialCoefficients.

(** * Monomials of the binomial expansion *)

(** ** Monomial

  *** Definition *)

(* {MONOMIAL} *)
Definition monomial (t r n : nat) : nat :=
  C(r, n) * (t ^ n).
(* {END} *)
Hint Unfold monomial : charfun.

(** *** Unfolding lemmas *)

Lemma unfold_monomial :
  forall (t r n : nat),
    monomial t r n = C(r, n) * t ^ n.
Proof.
  intros t r n.
  unfold monomial.
  reflexivity.
Qed.
Hint Rewrite unfold_monomial : charfun.

(** *** Properties *)

(* {MONOMIAL_K_EQ_0_IMPLIES_1} *)
Lemma monomial_k_eq_0_implies_1 :
  forall (t r : nat),
    monomial t r 0 = 1.
(* {END} *)
Proof.
  intros t r.
  rewrite -> unfold_monomial.
  rewrite -> mult_1_r.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  reflexivity.
Qed.
Hint Rewrite monomial_k_eq_0_implies_1 : charfun.

(* {MONOMIAL_R_LT_N_IMPLIES_0} *)
Lemma monomial_r_lt_n_implies_0 :
  forall (t r n : nat),
    r < n ->
    monomial t r n = 0.
(* {END} *)
Proof.
  intros t r n H_r_lt_n.
  rewrite -> unfold_monomial.
  inversion_clear H_r_lt_n.

  Case "n = S r".
  rewrite -> binomial_coefficient_n_lt_k_implies_0;
    [ idtac | unfold lt; apply le_n ].
  rewrite -> mult_0_l.
  reflexivity.

  Case "k = S m".
  rename H into H_S_r_le_m.
  rewrite -> binomial_coefficient_n_lt_k_implies_0;
    [ idtac | unfold lt; apply le_S; exact H_S_r_le_m ].
  rewrite -> mult_0_l.
  reflexivity.
Qed.
Hint Resolve monomial_r_lt_n_implies_0 : charfun.

(* {MONOMIAL_R_EQ_N_IMPLIES_POWER} *)
Lemma monomial_r_eq_n_implies_power :
  forall (t r : nat),
    monomial t r r = t ^ r.
(* {END} *)
Proof.
  intros t r.
  rewrite -> unfold_monomial.
  rewrite -> binomial_coefficient_n_eq_k_implies_1.
  rewrite -> mult_1_l.
  reflexivity.
Qed.
Hint Rewrite monomial_r_eq_n_implies_power : charfun.

(* {MONOMIAL_DECOMPOSE_RANK} *)
Theorem monomial_decompose_rank :
  forall (t r' n' : nat),
    monomial t (S r') (S n') =
    monomial t r' (S n') + t * monomial t r' n'.
(* {END} *)
Proof.
  intros t r' n'.
  rewrite ->2 unfold_monomial.
  rewrite -> Pascal_s_rule.
  rewrite -> mult_plus_distr_r.
  rewrite <- unfold_monomial.
  rewrite -> unfold_power_induction_case.
  rewrite -> NPeano.Nat.mul_shuffle3.
  rewrite <- unfold_monomial.
  reflexivity.
Qed.
Hint Rewrite monomial_decompose_rank : charfun.

(** * Characteristic functions for entries in Moessner triangles

  NOTE: Be aware that [r] means rank for [moessner_entry] and row [r] for
  [rotated_moessner_entry]. *)

(** ** Moessner entry

  Given a rank [r], a row [n], a column [k], and a triangle [t],
  calculate the specific entry of a Moessner triangle.

  *** Definition *)

(* {MOESSNER_ENTRY} *)
Fixpoint moessner_entry (r n k t : nat) : nat :=
  match n with
    | 0 => match k with
             | 0 => 1
             | S k' => 0
           end
    | S n' => match k with
                | 0 => monomial t r (S n') +
                       moessner_entry r n' 0 t
                | S k' => moessner_entry r n' (S k') t +
                          moessner_entry r n' k' t
              end
  end.
(* {END} *)
Hint Unfold moessner_entry : charfun.

(** *** Unfolding lemmas *)

Lemma unfold_moessner_entry_base_case_O :
  forall (r t : nat),
    moessner_entry r 0 0 t = 1.
Proof.
  intros r t.
  unfold moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_moessner_entry_base_case_O : charfun.

Lemma unfold_moessner_entry_base_case_S :
  forall (r k' t : nat),
    moessner_entry r 0 (S k') t = 0.
Proof.
  intros r k' t.
  unfold moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_moessner_entry_base_case_S : charfun.

Lemma unfold_moessner_entry_induction_case_O :
  forall (n' r t : nat),
    moessner_entry r (S n') 0 t =
    monomial t r (S n') + moessner_entry r n' 0 t.
Proof.
  intros n' r t.
  unfold moessner_entry; fold moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_moessner_entry_induction_case_O : charfun.

(* {UNFOLD_MOESSNER_ENTRY_INDUCTION_CASE_S} *)
Lemma unfold_moessner_entry_induction_case_S :
  forall (n' r k' t : nat),
    moessner_entry r (S n') (S k') t =
    moessner_entry r n' (S k') t +
    moessner_entry r n' k' t.
(* {END} *)
Proof.
  intros n' r k' t.
  unfold moessner_entry; fold moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_moessner_entry_induction_case_S : charfun.

(** *** Properties *)

Definition moessner_entry_Pascal_s_rule :=
  unfold_moessner_entry_induction_case_S.
Hint Rewrite moessner_entry_Pascal_s_rule : charfun.

(*
(* {MOESSNER_ENTRY_PASCAL_S_RULE} *)
Theorem moessner_entry_Pascal_s_rule :
  forall (n' r k' t : nat),
    moessner_entry r (S n') (S k') t =
    moessner_entry r n' (S k') t +
    moessner_entry r n' k' t.
(* {END} *)
*)

(* {MOESSNER_ENTRY_EQ_BINOMIAL_COEFFICIENT} *)
Theorem moessner_entry_eq_binomial_coefficient :
  forall (n k r : nat),
    moessner_entry r n k 0 = C(n, k).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros k r.
  unfold moessner_entry, binomial_coefficient.
  reflexivity.

  Case "n = S n'".
  case k as [ | k' ].

  SCase "k = 0".
  intro r.
  rewrite -> unfold_moessner_entry_induction_case_O.
  rewrite -> (IH_n' 0 r).
  rewrite -> unfold_monomial.
  rewrite -> power_0_e.
  rewrite -> mult_0_r.
  rewrite -> plus_0_l.
  rewrite ->2 unfold_binomial_coefficient_base_case_n_0.
  reflexivity.

  SCase "k = S k'".
  intro r.
  rewrite -> moessner_entry_Pascal_s_rule.
  rewrite -> (IH_n' (S k') r).
  rewrite -> (IH_n' k' r).
  rewrite <- Pascal_s_rule.
  reflexivity.
Qed.
Hint Rewrite moessner_entry_eq_binomial_coefficient : charfun.

(* {MOESSNER_ENTRY_N_LT_K_IMPLIES_0} *)
Lemma moessner_entry_n_lt_k_implies_0 :
  forall (r n k t : nat),
    n < k ->
    moessner_entry r n k t = 0.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  case k as [ | k' ].

  SCase "k = 0".
  intros t H_absurd; inversion H_absurd.

  SCase "k = S k'".
  intros t H_0_lt_S_k'.
  rewrite -> unfold_moessner_entry_base_case_S.
  reflexivity.

  Case "n = S n'".
  case k as [ | k' ].

  SCase "k = 0".
  intros t H_absurd; inversion H_absurd.

  SCase "k = S k'".
  intros t H_S_n'_lt_S_k'.
  rewrite -> moessner_entry_Pascal_s_rule.

  assert (H_n'_lt_S_k': n' < S k').
    apply lt_S_n.
    unfold lt.
    apply le_S.
    unfold lt in H_S_n'_lt_S_k'.
    exact H_S_n'_lt_S_k'.

  rewrite -> (IH_n' (S k') t H_n'_lt_S_k'); clear H_n'_lt_S_k'.
  rewrite -> plus_0_l.

  assert (H_n'_lt_k': n' < k').
    apply lt_S_n.
    exact H_S_n'_lt_S_k'.

  rewrite -> (IH_n' k' t H_n'_lt_k').
  reflexivity.
Qed.
Hint Resolve moessner_entry_n_lt_k_implies_0 : charfun.

(* {MOESSNER_ENTRY_N_EQ_K_IMPLIES_1} *)
Lemma moessner_entry_n_eq_k_implies_1 :
  forall (n r t : nat),
    moessner_entry r n n t = 1.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r t.
  rewrite -> unfold_moessner_entry_base_case_O.
  reflexivity.

  Case "n = S n'".
  intros r t.
  rewrite -> moessner_entry_Pascal_s_rule.
  rewrite -> (IH_n' r t).
  rewrite -> moessner_entry_n_lt_k_implies_0;
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  reflexivity.
Qed.
Hint Rewrite moessner_entry_n_eq_k_implies_1 : charfun.

(** ** Moessner entries

  Enumerates a row of moessner entries.

  *** Definition *)

(* {MOESSNER_ENTRIES} *)
CoFixpoint moessner_entries (r n k t : nat) : Stream nat :=
  (moessner_entry r n k t) :::
  (moessner_entries r n (S k) t).
(* {END} *)
Hint Unfold moessner_entries : charfun.

(** *** Unfolding lemmas *)

Lemma unfold_moessner_entries :
  forall (r n k t : nat),
    moessner_entries r n k t =
    (moessner_entry r n k t) :::
    (moessner_entries r n (S k) t).
Proof.
  intros r n k t.
  rewrite -> (unfold_Stream (moessner_entries r n k t)).
  unfold moessner_entries; fold moessner_entries.
  reflexivity.
Qed.
Hint Rewrite unfold_moessner_entries : charfun.

Lemma moessner_entries_initial_value :
  forall (r n k t : nat),
    (moessner_entries r n k t)(0) =
    (moessner_entry r n k t).
Proof.
  intros r n k t.
  rewrite -> initial_value.
  rewrite -> unfold_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite moessner_entries_initial_value : charfun.

Lemma moessner_entries_stream_derivative :
  forall (r n k t : nat),
    (moessner_entries r n k t)` =
    (moessner_entries r n (S k) t).
Proof.
  intros r n k t.
  rewrite -> stream_derivative.
  rewrite -> unfold_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite moessner_entries_stream_derivative : charfun.

(** ** Properties *)

(* {STR_NTH_MOESSNER_ENTRIES} *)
Lemma Str_nth_moessner_entries :
  forall (i r n k t : nat),
    Str_nth i (moessner_entries r n k t) =
    moessner_entry r n (i + k) t.
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros r n k t.
  rewrite -> Str_nth_0.
  rewrite -> moessner_entries_initial_value.
  rewrite -> plus_0_l.
  reflexivity.

  Case "i = S i'".
  intros r n k t.
  rewrite -> Str_nth_S_n.
  rewrite -> moessner_entries_stream_derivative.
  rewrite -> (IH_i' r n (S k) t).
  rewrite <- plus_n_Sm.
  rewrite -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite Str_nth_moessner_entries : charfun.

(** ** Rotated moessner entry

  Given a rank [n], a row [r], a column [c], and a triangle [t],
  calculate the specific entry of a Moessner triangle.

  *** Definition *)

(* {ROTATED_MOESSNER_ENTRY} *)
Definition rotated_moessner_entry (n r c t : nat) : nat :=
  moessner_entry n (c + r) c t.
(* {END} *)
Hint Unfold rotated_moessner_entry : charfun.

(** *** Unfolding lemmas *)

Lemma unfold_rotated_moessner_entry :
  forall (n r c t : nat),
    rotated_moessner_entry n r c t =
    moessner_entry n (c + r) c t.
Proof.
  intros n r c t.
  unfold rotated_moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_moessner_entry : charfun.

(* {ROTATED_MOESSNER_ENTRY_PASCAL_S_RULE} *)
Lemma rotated_moessner_entry_Pascal_s_rule :
  forall (n r' c' t : nat),
    rotated_moessner_entry n (S r') (S c') t =
    rotated_moessner_entry n r' (S c') t +
    rotated_moessner_entry n (S r') c' t.
(* {END} *)
Proof.
  intros n r' c' t.
  rewrite ->3 unfold_rotated_moessner_entry.
  rewrite <-2 plus_n_Sm.
  rewrite -> plus_Sn_m.
  rewrite -> moessner_entry_Pascal_s_rule.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_Pascal_s_rule : charfun.

(** *** Properties *)

(* {ROTATED_MOESSNER_ENTRY_EQ_BINOMIAL_COEFFICIENT} *)
Corollary rotated_moessner_entry_eq_binomial_coefficient :
  forall (n r c : nat),
    rotated_moessner_entry n r c 0 = C(r + c, c).
(* {END} *)
Proof.
  intros n r c.
  rewrite -> unfold_rotated_moessner_entry.
  rewrite -> moessner_entry_eq_binomial_coefficient.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite moessner_entry_eq_binomial_coefficient : charfun.

(* {ROTATED_MOESSNER_ENTRY_EQ_ROTATED_BINOMIAL_COEFFICIENT} *)
Corollary rotated_moessner_entry_eq_rotated_binomial_coefficient :
  forall (n r c : nat),
    rotated_moessner_entry n r c 0 = R(r, c).
(* {END} *)
Proof.
  intros n r c.
  rewrite -> rotated_moessner_entry_eq_binomial_coefficient.
  rewrite -> rotated_binomial_coefficient_is_symmetric.
  rewrite -> unfold_rotated_binomial_coefficient.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_eq_rotated_binomial_coefficient : charfun.

(* {ROTATED_MOESSNER_ENTRY_R_EQ_0_IMPLIES_1} *)
Lemma rotated_moessner_entry_r_eq_0_implies_1 :
  forall (c n t : nat),
    rotated_moessner_entry n 0 c t = 1.
(* {END} *)
Proof.
  intros c n t.
  rewrite -> unfold_rotated_moessner_entry.
  rewrite -> plus_0_r.
  rewrite -> moessner_entry_n_eq_k_implies_1.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_r_eq_0_implies_1 : charfun.

(* {ROTATED_MOESSNER_ENTRY_C_EQ_0} *)
Lemma rotated_moessner_entry_c_eq_0 :
  forall (r' n t : nat),
    rotated_moessner_entry n (S r') 0 t =
    monomial t n (S r') + rotated_moessner_entry n r' 0 t.
(* {END} *)
Proof.
  intros r' n t.
  rewrite ->2 unfold_rotated_moessner_entry.
  rewrite ->2 plus_0_l.
  rewrite -> unfold_moessner_entry_induction_case_O.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entry_c_eq_0 : charfun.

(** ** Rotated moessner entries

  *** Definition *)

(* {ROTATED_MOESSNER_ENTRIES} *)
CoFixpoint rotated_moessner_entries (n r c t : nat) : Stream nat :=
  (rotated_moessner_entry n r c t) :::
  (rotated_moessner_entries n (S r) c t).
(* {END} *)
Hint Unfold rotated_moessner_entries : charfun.

(** *** Unfolding lemmas *)

Lemma unfold_rotated_moessner_entries :
  forall (n r c t : nat),
    rotated_moessner_entries n r c t =
    (rotated_moessner_entry n r c t) :::
    (rotated_moessner_entries n (S r) c t).
Proof.
  intros n r c t.
  rewrite -> (unfold_Stream (rotated_moessner_entries n r c t)).
  unfold rotated_moessner_entries; fold rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_moessner_entries : charfun.

Lemma rotated_moessner_entries_initial_value :
  forall (n r c t : nat),
    (rotated_moessner_entries n r c t)(0) =
    (rotated_moessner_entry n r c t).
Proof.
  intros n r c t.
  rewrite -> initial_value.
  rewrite -> unfold_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entries_initial_value : charfun.

Lemma rotated_moessner_entries_stream_derivative :
  forall (n r c t : nat),
    (rotated_moessner_entries n r c t)` =
    (rotated_moessner_entries n (S r) c t).
Proof.
  intros n r c t.
  rewrite -> stream_derivative.
  rewrite -> unfold_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entries_stream_derivative : charfun.

(** ** Properties *)

(* {STR_NTH_ROTATED_MOESSNER_ENTRIES} *)
Lemma Str_nth_rotated_moessner_entries :
  forall (i n r c t : nat),
    Str_nth i (rotated_moessner_entries n r c t) =
    rotated_moessner_entry n (r + i) c t.
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros n r c t.
  rewrite -> Str_nth_0.
  rewrite -> rotated_moessner_entries_initial_value.
  rewrite -> plus_0_r.
  reflexivity.

  Case "i = S i'".
  intros n r c t.
  rewrite -> Str_nth_S_n.
  rewrite -> rotated_moessner_entries_stream_derivative.
  rewrite -> (IH_i' n (S r) c t).
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite Str_nth_rotated_moessner_entries : charfun.

Corollary Str_nth_rotated_moessner_entries_t_eq_0 :
  forall (i n r c : nat),
    Str_nth i (rotated_moessner_entries n r c 0) =
    C(r + i + c, c).
Proof.
  intros i n r c.
  rewrite -> Str_nth_rotated_moessner_entries.
  rewrite -> rotated_moessner_entry_eq_binomial_coefficient.
  reflexivity.
Qed.
Hint Rewrite Str_nth_rotated_moessner_entries_t_eq_0 : charfun.

(* {ROTATED_MOESSNER_ENTRIES_PASCAL_S_RULE} *)
Lemma rotated_moessner_entries_Pascal_s_rule :
  forall (n r' c' t : nat),
    rotated_moessner_entries n (S r') (S c') t ~
    (rotated_moessner_entries n (S r') c' t) s+
    (rotated_moessner_entries n r' (S c') t).
(* {END} *)
Proof.
  pcofix coIH.
  intros n r' c' t.
  bisimilar.

  Case "initial value".
  rewrite -> stream_sum_initial_value.
  rewrite ->3 rotated_moessner_entries_initial_value.
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  rewrite -> plus_comm.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_sum_stream_derivative.
  rewrite ->3 rotated_moessner_entries_stream_derivative.
  exact (coIH n (S r') c' t).
Qed.
Hint Rewrite rotated_moessner_entries_Pascal_s_rule : charfun.

(** ** Monomials

  Enumerates the monomials of the binomial expansion.

  *** Definition *)

(* {MONOMIALS} *)
CoFixpoint monomials (t r n : nat) : Stream nat :=
  (monomial t r n) ::: (monomials t r (S n)).
(* {END} *)
Hint Unfold monomials : charfun.

(** *** Unfolding lemmas *)

Lemma unfold_monomials :
  forall (t r n : nat),
    monomials t r n = (monomial t r n) ::: (monomials t r (S n)).
Proof.
  intros t r n.
  rewrite -> (unfold_Stream (monomials t r n)).
  unfold monomials; fold monomials.
  reflexivity.
Qed.
Hint Rewrite unfold_monomials : charfun.

(* {MONOMIALS_INITIAL_VALUE} *)
Lemma monomials_initial_value :
  forall (t r n : nat),
    (monomials t r n)(0) = (monomial t r n).
(* {END} *)
Proof.
  intros t r n.
  rewrite -> initial_value.
  rewrite -> unfold_monomials.
  reflexivity.
Qed.
Hint Rewrite monomials_initial_value : charfun.

(* {MONOMIALS_STREAM_DERIVATIVE} *)
Lemma monomials_stream_derivative :
  forall (t r n : nat),
    (monomials t r n)` = (monomials t r (S n)).
(* {END} *)
Proof.
  intros t r n.
  rewrite -> stream_derivative.
  rewrite -> unfold_monomials.
  reflexivity.
Qed.
Hint Rewrite monomials_stream_derivative : charfun.

(** *** Properties *)

(* {STR_NTH_MONOMIALS} *)
Lemma Str_nth_monomials :
  forall (i t r n : nat),
    Str_nth i (monomials t r n) = monomial t r (i + n).
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros t r n.
  rewrite -> Str_nth_0.
  rewrite -> monomials_initial_value.
  rewrite -> plus_0_l.
  reflexivity.

  Case "i = S i'".
  intros t r n.
  rewrite -> Str_nth_S_n.
  rewrite -> monomials_stream_derivative.
  rewrite -> (IH_i' t r (S n)).
  rewrite -> plus_Sn_m, <- plus_n_Sm.
  reflexivity.
Qed.
Hint Rewrite Str_nth_monomials : charfun.

Lemma Str_nth_monomials_i_plus_n_gt_r_implies_0 :
  forall (i r n t : nat),
    r < n + i ->
    Str_nth i (monomials t r n) = 0.
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros r n t H_r_lt_n.
  rewrite -> plus_0_r in H_r_lt_n.
  rewrite -> Str_nth_0.
  rewrite -> monomials_initial_value.
  rewrite -> unfold_monomial.
  rewrite -> (binomial_coefficient_n_lt_k_implies_0 r n H_r_lt_n).
  rewrite -> mult_0_l.
  reflexivity.

  Case "i = S i'".
  intros r n t H_r_lt_n_plus_S_i'.
  rewrite -> Str_nth_S_n.
  rewrite monomials_stream_derivative.
  rewrite -> (IH_i' r (S n) t);
    [ idtac | rewrite -> plus_Sn_m, -> plus_n_Sm; exact H_r_lt_n_plus_S_i' ].
  reflexivity.
Qed.
Hint Resolve Str_nth_monomials_i_plus_n_gt_r_implies_0 : charfun.

(* {REV_STR_PREFIX_MONOMIALS} *)
Lemma rev_Str_prefix_monomials :
  forall (l n r t : nat),
    rev (Str_prefix (S l) (monomials t r n)) =
    monomial t r (n + l) :: rev (Str_prefix l (monomials t r n)).
(* {END} *)
Proof.
  induction l as [ | l' IH_l' ].

  Case "l = 0".
  intros n r t.
  rewrite -> plus_0_r.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> monomials_initial_value.
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> app_nil_l.
  reflexivity.

  Case "l = S l'".
  intros n r t.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_rev_induction_case.
  rewrite -> monomials_stream_derivative.
  rewrite -> IH_l'.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> monomials_initial_value.
  rewrite -> monomials_stream_derivative.
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  rewrite -> unfold_rev_induction_case.
  rewrite <- app_comm_cons.
  reflexivity.
Qed.
Hint Rewrite rev_Str_prefix_monomials : charfun.

(* {REV_STR_PREFIX_ROTATED_MOESSNER_ENTRIES} *)
Lemma rev_Str_prefix_rotated_moessner_entries :
  forall (l n r c t : nat),
    rev (Str_prefix (S l) (rotated_moessner_entries n r c t)) =
    rotated_moessner_entry n (r + l) c t
      :: rev (Str_prefix l (rotated_moessner_entries n r c t )).
(* {END} *)
Proof.
  induction l as [ | l' IH_l' ].

  Case "l = 0".
  intros n r c t.
  rewrite -> plus_0_r.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> rotated_moessner_entries_initial_value.
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> app_nil_l.
  reflexivity.

  Case "l = S l'".
  intros n r c t.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_rev_induction_case.
  rewrite -> rotated_moessner_entries_stream_derivative.
  rewrite -> IH_l'.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> rotated_moessner_entries_initial_value.
  rewrite -> rotated_moessner_entries_stream_derivative.
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  rewrite -> unfold_rev_induction_case.
  rewrite <- app_comm_cons.
  reflexivity.
Qed.
Hint Rewrite rev_Str_prefix_rotated_moessner_entries : charfun.

Lemma monomials_tail_of_0s :
  forall (i n t : nat),
    Str_nth_tl (S i) (monomials t i n) ~ #0.
Proof.
  pcofix coIH.
  intros i n t.
  bisimilar.

  Case "initial value".
  rewrite <- unfold_Str_nth.
  rewrite -> Str_nth_monomials_i_plus_n_gt_r_implies_0;
    [ idtac | unfold lt; apply le_plus_r ].
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> Str_nth_tl_stream_derivative_case_i_gt_0.
  rewrite ->2 monomials_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH i (S n) t).
Qed.
Hint Rewrite monomials_tail_of_0s : tupmos.

(** ** Monomials sum

  Enumerates the partial sums of the monomials of the binomial expansion.

  *** Definition *)

(* {MONOMIALS_SUM} *)
CoFixpoint monomials_sum (t r n a : nat) : Stream nat :=
  let a' := (monomial t r n) + a in
  a' ::: (monomials_sum t r (S n) a').
(* {END} *)
Hint Unfold monomials_sum : charfun.

(** *** Unfolding lemmas *)

Lemma unfold_monomials_sum :
  forall (t r n a : nat),
    monomials_sum t r n a =
    ((monomial t r n) + a) :::
    (monomials_sum t r (S n) ((monomial t r n) + a)).
Proof.
  intros t r n a.
  rewrite -> (unfold_Stream (monomials_sum t r n a)).
  unfold monomials_sum; fold monomials_sum.
  reflexivity.
Qed.
Hint Rewrite unfold_monomials_sum : charfun.

(* {MONOMIALS_SUM_INITIAL_VALUE} *)
Lemma monomials_sum_initial_value :
  forall (t r n a : nat),
    (monomials_sum t r n a)(0) = (monomial t r n) + a.
(* {END} *)
Proof.
  intros t r n a.
  rewrite -> initial_value.
  rewrite -> unfold_monomials_sum.
  reflexivity.
Qed.
Hint Rewrite monomials_sum_initial_value : charfun.

(* {MONOMIALS_SUM_STREAM_DERIVATIVE} *)
Lemma monomials_sum_stream_derivative :
  forall (t r n a : nat),
    (monomials_sum t r n a)` =
    (monomials_sum t r (S n) ((monomial t r n) + a)).
(* {END} *)
Proof.
  intros t r n a.
  rewrite -> stream_derivative.
  rewrite -> unfold_monomials_sum.
  reflexivity.
Qed.
Hint Rewrite monomials_sum_stream_derivative : charfun.

(** *** Properties *)

Lemma monomials_sum_acc_aux :
  forall (t l n i j : nat),
    (monomials_sum t l n (i + j)) ~
    (monomials_sum t l n i) s+ #j.
Proof.
  pcofix coIH.
  intros t l n i j.
  bisimilar.

  Case "initial value".
  rewrite -> monomials_sum_initial_value.
  rewrite -> stream_sum_initial_value.
  rewrite -> monomials_sum_initial_value.
  rewrite -> stream_constant_initial_value.
  rewrite <- plus_assoc.
  reflexivity.

  Case "stream derivative".
  rewrite -> monomials_sum_stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite -> monomials_sum_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  rewrite -> plus_assoc.
  exact (coIH t l (S n) (monomial t l n + i) j).
Qed.
Hint Rewrite monomials_sum_acc_aux : charfun.

Corollary monomials_sum_acc :
  forall (t l n a : nat),
    (monomials_sum t l n a) ~
    (monomials_sum t l n 0) s+ #a.
Proof.
  intros t l n a.
  rewrite <- monomials_sum_acc_aux.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite monomials_sum_acc : charfun.

(* {STR_NTH_MONOMIALS_SUM_STREAM_DERIVATIVE} *)
Lemma Str_nth_monomials_sum_stream_derivative :
  forall (i n t l a : nat),
    Str_nth i (monomials_sum t l n a)` =
    Str_nth i ((monomials_sum t l (S n) a) s+ #(monomial t l n)).
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros n t l a.
  rewrite -> monomials_sum_stream_derivative.
  rewrite ->2 Str_nth_0.
  rewrite -> stream_sum_initial_value.
  rewrite ->2 monomials_sum_initial_value.
  rewrite -> stream_constant_initial_value.
  rewrite <- plus_assoc.
  f_equal.
  rewrite -> plus_comm.
  reflexivity.

  Case "i = S i'".
  intros n t l a.
  rewrite ->2 Str_nth_S_n.
  rewrite -> monomials_sum_stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite -> (IH_i' (S n) t l (monomial t l n + a)).
  rewrite -> monomials_sum_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  rewrite <-2 monomials_sum_acc_aux.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  rewrite -> (plus_comm a _).
  reflexivity.
Qed.
Hint Rewrite Str_nth_monomials_sum_stream_derivative : charfun.

Corollary monomials_sum_stream_derivative_bisim :
  forall (n t l a : nat),
    (monomials_sum t l n a)` ~
    (monomials_sum t l (S n) a) s+ #(monomial t l n).
Proof.
  intros n t l a.
  apply Str_nth_implies_bisimilarity; intro i.
  exact (Str_nth_monomials_sum_stream_derivative i n t l a).
Qed.
Hint Rewrite monomials_sum_stream_derivative_bisim : charfun.

Lemma Str_nth_monomials_sum_r_eq_0 :
  forall (i t n' m' a : nat),
    Str_nth i (monomials_sum t 0 (S n') a) =
    Str_nth i (monomials_sum t 0 (S m') a).
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros t n' m' a.
  rewrite ->2 Str_nth_0.
  rewrite ->2 monomials_sum_initial_value.
  rewrite ->2 unfold_monomial.
  rewrite ->2 unfold_binomial_coefficient_base_case_0_S_k'.
  rewrite ->2 mult_0_l.
  rewrite -> plus_0_l.
  reflexivity.

  Case "i = S i'".
  intros t n' m' a.
  rewrite ->2 Str_nth_S_n.
  rewrite ->2 Str_nth_monomials_sum_stream_derivative.
  unfold stream_sum.
  rewrite ->2 Str_nth_stream_zip.
  rewrite -> (IH_i' t (S n') (S m') a).
  reflexivity.
Qed.
Hint Rewrite Str_nth_monomials_sum_r_eq_0 : charfun.

(* {SHIFT_START_INDEX_MONOMIALS_SUM} *)
Lemma shift_start_index_monomials_sum :
  forall (i' r n a t : nat),
    (monomial t r n) + (Str_nth i' (monomials_sum t r (S n) a)) =
    (monomial t r (n + (S i'))) + (Str_nth i' (monomials_sum t r n a)).
(* {END} *)
Proof.
  induction i' as [ | i'' IH_i'' ].

  Case "i' = 0".
  intros r n a t.
  rewrite ->2 Str_nth_0.
  rewrite ->2 monomials_sum_initial_value.
  rewrite -> plus_permute.
  rewrite -> (plus_comm n 1).
  reflexivity.

  Case "i' = S i''".
  intros r n a t.
  rewrite -> Str_nth_S_n.
  rewrite -> Str_nth_monomials_sum_stream_derivative.
  unfold stream_sum.
  rewrite -> Str_nth_stream_zip.
  rewrite -> Str_nth_stream_constant.
  rewrite <- (plus_comm (monomial t r (S n)) _).
  rewrite -> (IH_i'' r (S n) a t).
  rewrite <-3 plus_n_Sm, -> plus_Sn_m.

  rewrite -> Str_nth_S_n.
  rewrite -> Str_nth_monomials_sum_stream_derivative.
  unfold stream_sum.
  rewrite -> Str_nth_stream_zip.
  rewrite -> Str_nth_stream_constant.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  reflexivity.
Qed.
Hint Rewrite shift_start_index_monomials_sum : charfun.

(** * Relations between monomials, monomials sum,
 moessner  entry rotated, make tuple, and partial sums acc *)

(* {STR_NTH_MONOMIALS_SUM_EQ_ROTATED_MOESSNER_ENTRY} *)
Theorem Str_nth_monomials_sum_eq_rotated_moessner_entry :
  forall (i t r a : nat),
    Str_nth i (monomials_sum t r 0 a) =
    (rotated_moessner_entry r i 0 t) + a.
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros t r a.
  rewrite -> Str_nth_0.
  rewrite -> monomials_sum_initial_value.
  rewrite -> unfold_monomial.
  rewrite -> unfold_power_base_case.
  rewrite -> mult_1_r.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.

  rewrite -> unfold_rotated_moessner_entry.
  rewrite -> plus_0_r.
  rewrite -> unfold_moessner_entry_base_case_O.
  reflexivity.

  Case "i = S i'".
  intros t r a.
  rewrite -> Str_nth_S_n.
  rewrite -> Str_nth_monomials_sum_stream_derivative.
  unfold stream_sum.
  rewrite -> Str_nth_stream_zip.
  rewrite -> Str_nth_stream_constant.
  rewrite -> plus_comm.

  unfold rotated_moessner_entry in *.
  rewrite -> plus_0_l in *.
  rewrite -> unfold_moessner_entry_induction_case_O.
  rewrite <- plus_assoc.
  rewrite <- (IH_i' t r a).
  rewrite -> shift_start_index_monomials_sum.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite Str_nth_monomials_sum_eq_rotated_moessner_entry : charfun.

(* {STREAM_PARTIAL_SUMS_ACC_MONOMIALS_BISIM_MONOMIALS_SUM} *)
Lemma stream_partial_sums_acc_monomials_bisim_monomials_sum :
  forall (t r n a : nat),
    stream_partial_sums_acc a (monomials t r n) ~
    monomials_sum t r n a.
(* {END} *)
Proof.
  pcofix coIH.
  intros t n k a.
  bisimilar.

  Case "initial value".
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> monomials_initial_value.
  rewrite -> monomials_sum_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> monomials_stream_derivative.
  rewrite -> monomials_sum_stream_derivative.
  rewrite -> monomials_initial_value.
  exact (coIH t n (S k) (monomial t n k + a)).
Qed.
Hint Rewrite stream_partial_sums_acc_monomials_bisim_monomials_sum : charfun.

(* {STREAM_PARTIAL_SUMS_MONOMIALS_BISIM_MONOMIALS_SUM} *)
Corollary stream_partial_sums_monomials_bisim_monomials_sum :
  forall (t r n : nat),
    stream_partial_sums (monomials t r n) ~
    monomials_sum t r n 0.
(* {END} *)
Proof.
  intros t r n.
  rewrite -> unfold_stream_partial_sums.
  exact (stream_partial_sums_acc_monomials_bisim_monomials_sum t r n 0).
Qed.
Hint Rewrite stream_partial_sums_monomials_bisim_monomials_sum : charfun.

(* {MAKE_TUPLE_MONOMIALS_EQ_MONOMIALS_SUM} *)
Corollary make_tuple_monomials_eq_monomials_sum :
  forall (l t r n a : nat),
    make_tuple (Str_prefix (S l) (monomials t r n)) a =
    Str_prefix l (monomials_sum t r n a).
(* {END} *)
Proof.
  intros l t r n a.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  rewrite -> stream_partial_sums_acc_monomials_bisim_monomials_sum.
  reflexivity.
Qed.
Hint Rewrite make_tuple_monomials_eq_monomials_sum : charfun.

(* {MONOMIALS_AND_ROTATED_MOESSNER_ENTRY} *)
Corollary monomials_and_rotated_moessner_entry :
  forall (l t r a : nat),
    nth l (make_tuple (Str_prefix (S (S l)) (monomials t r 0)) a) 0 =
    rotated_moessner_entry r l 0 t + a.
(* {END} *)
Proof.
  intros l t r a.
  rewrite <- Str_nth_monomials_sum_eq_rotated_moessner_entry.
  rewrite -> make_tuple_monomials_eq_monomials_sum.
  rewrite -> (nth_and_Str_nth l (S l) (monomials_sum t r 0 a));
      [ idtac | unfold lt; apply le_n ].
  reflexivity.
Qed.
Hint Rewrite monomials_and_rotated_moessner_entry : charfun.

(* {MONOMIALS_SUM_BISIM_ROTATED_MOESSNER_ENTRIES} *)
Corollary rotated_moessner_entries_bisim_monomials_sum :
  forall (n t : nat),
    monomials_sum t n 0 0 ~
    rotated_moessner_entries n 0 0 t.
(* {END} *)
Proof.
  intros n t.
  apply Str_nth_implies_bisimilarity; intro i.
  rewrite -> Str_nth_rotated_moessner_entries.
  rewrite -> plus_0_l.
  rewrite -> Str_nth_monomials_sum_eq_rotated_moessner_entry.
  rewrite -> plus_0_r.
  reflexivity.
Qed.
Hint Rewrite rotated_moessner_entries_bisim_monomials_sum : charfun.

(* {MAKE_TUPLE_MONOMIALS_EQ_ROTATED_MOESSNER_ENTRIES} *)
Corollary make_tuple_monomials_eq_rotated_moessner_entries :
  forall (l' n' t : nat),
    make_tuple (Str_prefix (S l') (monomials t n' 0)) 0 =
    Str_prefix l' (rotated_moessner_entries n' 0 0 t).
(* {END} *)
Proof.
  intros l' n' t.
  rewrite -> make_tuple_monomials_eq_monomials_sum.
  rewrite -> rotated_moessner_entries_bisim_monomials_sum.
  reflexivity.
Qed.
Hint Rewrite make_tuple_monomials_eq_rotated_moessner_entries : charfun.

(** * Relation between consecutive columns of arbitrary Moessner triangles *)

(** * Proof that partially summing the [c']th column of rotated moessner entries
  gives the [S c']th column *)

(* {STR_NTH_ROTATED_MOESSNER_ENTRIES_OVER_R} *)
Lemma Str_nth_rotated_moessner_entries_over_r :
  forall (i n r' c' t : nat),
    Str_nth i (rotated_moessner_entries n (S r') (S c') t) =
    Str_nth i (stream_partial_sums_acc
                 (rotated_moessner_entry n r' (S c') t)
                 (rotated_moessner_entries n (S r') c' t)).
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros n r' c' t.
  rewrite ->2 Str_nth_0.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite ->2 rotated_moessner_entries_initial_value.
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  rewrite -> plus_comm.
  reflexivity.

  Case "i = S i'".
  intros n r' c' t.
  rewrite ->2 Str_nth_S_n.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite ->2 rotated_moessner_entries_stream_derivative.
  rewrite -> rotated_moessner_entries_initial_value.
  rewrite -> (IH_i' n (S r') c' t).
  rewrite -> rotated_moessner_entry_Pascal_s_rule.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite Str_nth_rotated_moessner_entries_over_r : charfun.

Corollary partial_sums_rotated_moessner_entries_bisim_next_column_over_r :
  forall (n r' c' t : nat),
    (rotated_moessner_entries n (S r') (S c') t) ~
    (stream_partial_sums_acc (rotated_moessner_entry n r' (S c') t)
                      (rotated_moessner_entries n (S r') c' t)).
Proof.
  intros n r' c' t.
  apply Str_nth_implies_bisimilarity; intro i.
  exact
  (Str_nth_rotated_moessner_entries_over_r i n r' c' t).
Qed.
Hint Rewrite partial_sums_rotated_moessner_entries_bisim_next_column_over_r
  : charfun.

(* {STR_NTH_PARTIAL_SUMS_ROTATED_MOESSNER_ENTRIES} *)
Theorem Str_nth_partial_sums_rotated_moessner_entries :
  forall (i n c' t : nat),
    Str_nth i (stream_partial_sums_acc
                 0 (rotated_moessner_entries n 0 c' t)) =
    Str_nth i (rotated_moessner_entries n 0 (S c') t).
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros n c' t.
  rewrite ->2 Str_nth_0.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> plus_0_r.
  rewrite ->2 rotated_moessner_entries_initial_value.
  rewrite ->2 unfold_rotated_moessner_entry.
  rewrite ->2 plus_0_r.
  rewrite -> moessner_entry_Pascal_s_rule.
  rewrite -> (moessner_entry_n_lt_k_implies_0 n c' (S c') t);
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  reflexivity.

  Case "i = S i'".
  intros n c' t.
  rewrite ->2 Str_nth_S_n.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> plus_0_r.
  rewrite ->2 rotated_moessner_entries_stream_derivative.
  rewrite -> rotated_moessner_entries_initial_value.
  rewrite -> Str_nth_rotated_moessner_entries_over_r.
  rewrite ->2 unfold_rotated_moessner_entry.
  rewrite ->2 plus_0_r.
  rewrite -> moessner_entry_Pascal_s_rule.
  rewrite -> (moessner_entry_n_lt_k_implies_0 n c' (S c') t);
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  reflexivity.
Qed.
Hint Rewrite Str_nth_partial_sums_rotated_moessner_entries : charfun.

(* {PARTIAL_SUMS_ROTATED_MOESSNER_ENTRIES_BISIM_NEXT_COLUMN} *)
Corollary partial_sums_rotated_moessner_entries_bisim_next_column :
  forall (n c' t : nat),
    (stream_partial_sums_acc 0 (rotated_moessner_entries n 0 c' t)) ~
    (rotated_moessner_entries n 0 (S c') t).
(* {END} *)
Proof.
  intros n c' t.
  apply Str_nth_implies_bisimilarity; intro i.
  exact (Str_nth_partial_sums_rotated_moessner_entries i n c' t).
Qed.
Hint Rewrite partial_sums_rotated_moessner_entries_bisim_next_column : charfun.

Lemma last_of_rotated_moessner_entries :
  forall (c l n t : nat),
    last (Str_prefix (S l) (rotated_moessner_entries n 0 c t)) 0 =
    rotated_moessner_entry n l c t.
Proof.
  intros c l n t.
  rewrite -> (length_implies_last_index l);
    [ idtac | rewrite -> Str_prefix_length; reflexivity ].
  rewrite -> nth_and_Str_nth;
    [ idtac | unfold lt; apply le_n ].
  rewrite -> Str_nth_rotated_moessner_entries.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite last_of_rotated_moessner_entries : charfun.

(* {LAST_OF_ROTATED_MOESSNER_ENTRIES_TO_BINOMIAL} *)
Corollary last_of_rotated_moessner_entries_to_binomial :
  forall (c l n t : nat),
    last (Str_prefix (S l) (rotated_moessner_entries n 0 c t)) 0 =
    moessner_entry n (c + l) c t.
(* {END} *)
Proof.
  intros c l n t.
  rewrite -> last_of_rotated_moessner_entries.
  rewrite -> unfold_rotated_moessner_entry.
  reflexivity.
Qed.
Hint Rewrite last_of_rotated_moessner_entries_to_binomial : charfun.

(** *** Proof that applying [make_tuple] on a column of [rotated_moessner_entries]
  gives the next column *)

(* {MAKE_TUPLE_ROTATED_MOESSNER_ENTRIES} *)
Corollary make_tuple_rotated_moessner_entries :
  forall (l' n' c' t : nat),
    make_tuple (Str_prefix
                  (S l') (rotated_moessner_entries n' 0 c' t)) 0 =
    Str_prefix l' (rotated_moessner_entries n' 0 (S c') t).
(* {END} *)
Proof.
  intros l' n' c' t.
  rewrite <- partial_sums_rotated_moessner_entries_bisim_next_column.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  reflexivity.
Qed.
Hint Rewrite make_tuple_rotated_moessner_entries : charfun.

(** * Spelled out correctness proof of moessner entry rotated *)

(** ** Repeat make tuple

  *** Definition *)

(* {REPEAT_MAKE_TUPLE} *)
Fixpoint repeat_make_tuple (ys : tuple) (a n : nat) : tuple :=
  match n with
    | 0 => ys
    | S n' => repeat_make_tuple (make_tuple ys a) a n'
  end.
(* {END} *)
Hint Unfold repeat_make_tuple : charfun.

(** *** Unfolding lemmas *)

Lemma unfold_repeat_make_tuple_base_case :
  forall (ys : tuple) (a : nat),
    repeat_make_tuple ys a 0 = ys.
Proof.
  intros ys a.
  unfold repeat_make_tuple.
  reflexivity.
Qed.
Hint Rewrite unfold_repeat_make_tuple_base_case : charfun.

Lemma unfold_repeat_make_tuple_induction_case :
  forall (ys : tuple) (a n' : nat),
    repeat_make_tuple ys a (S n') =
    repeat_make_tuple (make_tuple ys a) a n'.
Proof.
  intros ys a n'.
  unfold repeat_make_tuple; fold repeat_make_tuple.
  reflexivity.
Qed.
Hint Rewrite unfold_repeat_make_tuple_induction_case : charfun.

(** *** Properties *)

Lemma repeat_make_tuple_nil :
  forall (a n : nat),
    repeat_make_tuple [] a n = [].
Proof.
  intros a n; revert a.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intro a.
  rewrite -> unfold_repeat_make_tuple_base_case.
  reflexivity.

  Case "n = S n'".
  intro a.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_make_tuple_base_case_nil.
  exact (IH_n' a).
Qed.
Hint Rewrite repeat_make_tuple_nil : charfun.

Lemma repeat_make_tuple_l_eq_0 :
  forall (ys : tuple) (n : nat),
    (length ys) <= n ->
    repeat_make_tuple ys 0 n = [].
Proof.
  intros ys n; revert ys.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros ys H_length_ys_le_0.
  rewrite -> unfold_repeat_make_tuple_base_case.
  inversion H_length_ys_le_0;
   rename H0 into H_length_ys_eq_0.
  rewrite -> (length_nil_0 ys H_length_ys_eq_0).
  reflexivity.

  Case "n = S n'".
  intros ys H_length_ys_le_S_n'.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> IH_n'.
  reflexivity.
  case ys as [ | y ys' ].

  SCase "ys = []".
  rewrite -> unfold_make_tuple_base_case_nil.
  rewrite -> unfold_length_base_case.
  exact (le_0_n n').

  SCase "ys = y :: ys'".
  case ys' as [ | y' ys'' ].

  SSCase "ys' = []".
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_length_base_case.
  exact (le_0_n n').

  SSCase "ys' = y' :: ys''".
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_length_induction_case.
  rewrite -> S_length_make_tuple.
  rewrite -> unfold_length_induction_case.
  rewrite ->2 unfold_length_induction_case in H_length_ys_le_S_n'.
  rewrite -> (le_S_n (S (length ys'')) n');
    [ reflexivity | exact H_length_ys_le_S_n' ].
Qed.
Hint Resolve repeat_make_tuple_l_eq_0 : charfun.

(* {SHIFT_MAKE_TUPLE_IN_REPEAT_MAKE_TUPLE} *)
Lemma shift_make_tuple_in_repeat_make_tuple :
  forall (ys : tuple) (n a : nat),
    make_tuple (repeat_make_tuple ys a n) a =
    repeat_make_tuple (make_tuple ys a) a n.
(* {END} *)
Proof.
  intros ys n a; revert ys a.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros ys a.
  rewrite ->2 unfold_repeat_make_tuple_base_case.
  reflexivity.

  Case "n = S n'".
  intros ys a.
  rewrite ->2 unfold_repeat_make_tuple_induction_case.
  rewrite -> (IH_n' (make_tuple ys a) a).
  reflexivity.
Qed.
Hint Rewrite shift_make_tuple_in_repeat_make_tuple : charfun.

Lemma length_repeat_make_tuple :
  forall (ys : tuple) (a n : nat),
    length (repeat_make_tuple ys a n) = (length ys) - n.
Proof.
  intros ys a n; revert ys a.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros ys a.
  rewrite -> unfold_repeat_make_tuple_base_case.
  rewrite <- minus_n_O.
  reflexivity.

  Case "n = S n'".
  intros ys a.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> IH_n'.
  case ys as [ | y ys' ].

  SCase "ys = []".
  rewrite -> unfold_make_tuple_base_case_nil.
  rewrite -> unfold_length_base_case.
  unfold minus.
  reflexivity.

  SCase "ys = y :: ys'".
  case ys' as [ | y' ys'' ].

  SSCase "ys' = []".
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_length_induction_case.
  rewrite -> unfold_length_base_case.
  unfold minus.
  reflexivity.

  SSCase "ys' = y' :: ys''".
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_length_induction_case.
  rewrite -> S_length_make_tuple.
  rewrite ->3 unfold_length_induction_case.
  rewrite -> NPeano.Nat.sub_succ.
  reflexivity.
Qed.
Hint Rewrite length_repeat_make_tuple : charfun.

(** ** Correctness proof of repeat_make_tuple and rotated_moessner_entry *)

(* {REPEAT_MAKE_TUPLE_ROTATED_MOESSNER_ENTRIES} *)
Theorem repeat_make_tuple_rotated_moessner_entries :
  forall (c l n t : nat),
    repeat_make_tuple
      (Str_prefix (c + l) (rotated_moessner_entries n 0 0 t)) 0 c =
    Str_prefix l (rotated_moessner_entries n 0 c t).
(* {END} *)
Proof.
  induction c as [ | c' IH_c' ].

  Case "c = 0".
  intros l n t.
  rewrite -> plus_0_l.
  rewrite -> unfold_repeat_make_tuple_base_case.
  reflexivity.

  Case "c = S c'".
  intros l n t.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite <- shift_make_tuple_in_repeat_make_tuple.
  rewrite -> plus_Sn_m, -> plus_n_Sm.
  rewrite -> (IH_c' (S l) n t).
  rewrite -> make_tuple_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite repeat_make_tuple_rotated_moessner_entries : charfun.

(* {REPEAT_MAKE_TUPLE_MONOMIALS_EQ_MOESSNER_ENTRIES} *)
Corollary repeat_make_tuple_monomials_eq_moessner_entries :
  forall (c l n t : nat),
    repeat_make_tuple
      (Str_prefix (S c + l) (monomials t n 0)) 0 (S c) =
    Str_prefix l (rotated_moessner_entries n 0 c t).
(* {END} *)
Proof.
  intros c l n t.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> plus_Sn_m.
  rewrite -> make_tuple_monomials_eq_monomials_sum.
  rewrite -> rotated_moessner_entries_bisim_monomials_sum.
  rewrite -> repeat_make_tuple_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite repeat_make_tuple_monomials_eq_moessner_entries : charfun.

(* {REPEAT_MAKE_TUPLE_MONOMIALS_EQ_MOESSNER_ENTRIES_GENERAL} *)
Lemma repeat_make_tuple_monomials_eq_moessner_entries_general :
  forall (k j n t : nat),
    j <= k ->
    Str_prefix (k - j) (rotated_moessner_entries n 0 j t) =
    repeat_make_tuple (Str_prefix (S k) (monomials t n 0)) 0 (S j).
(* {END} *)
Proof.
  induction k as [ | k' IH_k' ].

  Case "k = 0".
  intros j n t H_j_le_0.
  unfold minus.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> monomials_initial_value.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> repeat_make_tuple_nil.
  reflexivity.

  Case "k = S k'".
  induction j as [ | j' IH_j' ].

  SCase "j = 0".
  intros n t H_0_le_S_k'.
  rewrite <- minus_n_O.
  rewrite <- repeat_make_tuple_monomials_eq_moessner_entries.
  reflexivity.

  SCase "j = S j'".
  intros n t H_S_j_le_S_k.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite <- shift_make_tuple_in_repeat_make_tuple.
  rewrite <- (IH_j' n t);
    [ idtac | apply lt_le_weak; unfold lt; exact H_S_j_le_S_k ].
  rewrite <- make_tuple_rotated_moessner_entries.
  rewrite -> NPeano.Nat.sub_succ.
  rewrite -> minus_Sn_m;
    [ idtac | apply gt_S_le; unfold gt, lt; exact H_S_j_le_S_k ].
  reflexivity.
Qed.
Hint Resolve repeat_make_tuple_monomials_eq_moessner_entries_general : charfun.

(** *** Prove relation between [repeat_make_tuple]
  and [create_triangle_vertically] *)

(* {SHIFT_MAKE_TUPLE_CREATE_TRIANGLE_VERTICALLY} *)
Lemma shift_make_tuple_create_triangle_vertically :
  forall (j' : nat) (ys : tuple),
   make_tuple
     (nth j'
          (create_triangle_vertically
             (tuple_constant (length ys) 0) ys) []) 0 =
   nth (S j')
       (create_triangle_vertically
          (tuple_constant (length ys) 0) ys) [].
(* {END} *)
Proof.
  induction j' as [ | j'' IH_j'' ].

  Case "j' = 0".
  case ys as [ | y ys' ].

  SCase "ys = []".
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite -> unfold_nth_base_case_nil.
  rewrite -> unfold_make_tuple_base_case_nil.
  rewrite -> nth_n_nil.
  reflexivity.

  SCase "ys = y :: ys'".
  case ys' as [ | y' ys'' ].

  SSCase "ys' = []".
  rewrite -> unfold_length_induction_case.
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_nth_base_case_nil.
  rewrite -> unfold_make_tuple_base_case_nil.
  rewrite -> nth_n_nil.
  reflexivity.

  SSCase "ys' = y' :: ys''".
  case ys'' as [ | y'' ys''' ].

  SSSCase "ys'' = []".
  rewrite ->2 unfold_length_induction_case.
  rewrite -> unfold_length_base_case.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> unfold_nth_induction_case_cons.
  rewrite -> unfold_nth_base_case_nil.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  reflexivity.

  SSSCase "ys'' = y'' :: ys'''".
  rewrite ->3 unfold_length_induction_case.
  rewrite ->3 unfold_tuple_constant_induction_case.
  rewrite ->2 unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> unfold_nth_induction_case_cons.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.

  Case "j' = S j''".
  case ys as [ | y ys' ].

  SCase "ys = []".
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite ->2 nth_n_nil.
  rewrite -> unfold_make_tuple_base_case_nil.
  reflexivity.

  SCase "ys = y :: ys'".
  case ys' as [ | y' ys'' ].

  SSCase "ys' = []".
  rewrite -> unfold_length_induction_case.
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite ->2 nth_n_nil.
  rewrite -> unfold_make_tuple_base_case_nil.
  reflexivity.

  SSCase "ys' = y' :: ys''".
  symmetry.
  rewrite ->2 unfold_length_induction_case.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite <- (unfold_length_induction_case y' ys'').
  rewrite -> unfold_nth_induction_case_cons.
  rewrite <- (S_length_make_tuple ys'' y' 0).
  rewrite <- (unfold_length_induction_case y (make_tuple (y' :: ys'') 0)).
  rewrite -> unfold_nth_induction_case_cons.

  assert (H: (length (y :: make_tuple (y' :: ys'') 0)) =
             (length (make_tuple (y :: y' :: ys'') 0))).
    rewrite -> unfold_length_induction_case.
    rewrite -> unfold_make_tuple_induction_case.
    rewrite -> unfold_length_induction_case.
    rewrite -> plus_0_r.
    rewrite -> (length_tuples_xs_a_eq_ys_b
                  (y' :: ys'')
                  (y' :: ys'')
                  0
                  y); reflexivity.

  rewrite -> H; clear H.
  rewrite <- (IH_j'' (make_tuple (y :: y' :: ys'') 0)).
  reflexivity.
Qed.
Hint Rewrite shift_make_tuple_create_triangle_vertically : charfun.

(* {CORRECTNESS_OF_REPEAT_MAKE_TUPLE} *)
Theorem correctness_of_repeat_make_tuple :
  forall (j : nat) (ys : tuple),
    (repeat_make_tuple ys 0 (S j)) =
    (nth j (create_triangle_vertically
              (tuple_constant (length ys) 0)
              ys)
         []).
(* {END} *)
Proof.
  induction j as [ | j' IH_j' ].

  Case "j = 0".
  case ys as [ | y ys' ].

  SCase "ys = []".
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_repeat_make_tuple_base_case.
  rewrite -> unfold_make_tuple_base_case_nil.

  rewrite -> unfold_length_base_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite -> unfold_nth_base_case_nil.
  reflexivity.

  SCase "ys = y :: ys'".
  case ys' as [ | x' ys'' ].

  SSCase "ys' = []".
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_repeat_make_tuple_base_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.

  rewrite -> unfold_length_induction_case.
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_nth_base_case_nil.
  reflexivity.

  SSCase "ys' = y' :: ys''".
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_repeat_make_tuple_base_case.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> plus_0_r.

  rewrite ->2 unfold_length_induction_case.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> plus_0_r.
  reflexivity.

  Case "j = S j'".
  case ys as [ | y ys' ].

  SCase "ys = []".
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite -> unfold_nth_induction_case_nil.

  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_make_tuple_base_case_nil.

  rewrite -> repeat_make_tuple_l_eq_0;
    [ reflexivity | rewrite -> unfold_length_base_case; exact (le_O_n j') ].

  SCase "ys = y :: ys''".
  case ys' as [ | y' ys'' ].

  SSCase "ys' = []".
  rewrite -> unfold_length_induction_case.
  rewrite -> unfold_length_base_case.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_nth_induction_case_nil.

  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_make_tuple_base_case_nil.

  rewrite -> repeat_make_tuple_l_eq_0;
    [ reflexivity | rewrite -> unfold_length_base_case; exact (le_O_n j') ].

  SSCase "ys' = y' :: ys''".
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite <- shift_make_tuple_in_repeat_make_tuple.
  rewrite -> (IH_j' (y :: y' :: ys'')).
  rewrite -> shift_make_tuple_create_triangle_vertically.
  reflexivity.
Qed.
Hint Rewrite correctness_of_repeat_make_tuple : charfun.

(* {CORRECTNESS_OF_ROTATED_MOESSNER_ENTRY} *)
Theorem correctness_of_rotated_moessner_entry :
  forall (i j r t : nat),
    j <= S r ->
    S i <= S r - j ->
    (nth i
         (nth j
              (create_triangle_vertically
                 (tuple_constant (S (S r)) 0)
                 (Str_prefix (S (S r)) (monomials t r 0)))
              [])
         0) =
    rotated_moessner_entry r i j t.
(* {END} *)
Proof.
  intros i j r t H_j_le_S_r H_S_i_le_S_r_minus_j.

  assert (H_length_helper: (S (S r)) =
             (length (Str_prefix (S (S r)) (monomials t r 0)))).
    rewrite -> Str_prefix_length.
    reflexivity.

  assert (H_rewrite_helper:
            (tuple_constant (S (S r)) 0) =
            (tuple_constant
               (length (Str_prefix (S (S r)) (monomials t r 0))) 0)).
    f_equal.
    exact H_length_helper.

  rewrite -> H_rewrite_helper; clear H_length_helper H_rewrite_helper.

  rewrite <- correctness_of_repeat_make_tuple.

  rewrite <- repeat_make_tuple_monomials_eq_moessner_entries_general;
    [ idtac | exact H_j_le_S_r ].

  rewrite -> nth_and_Str_nth;
    [ idtac | unfold lt; exact H_S_i_le_S_r_minus_j ].

  rewrite -> Str_nth_rotated_moessner_entries.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Resolve correctness_of_rotated_moessner_entry : charfun.