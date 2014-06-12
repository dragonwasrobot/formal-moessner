(* LongsTheorem.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Long's Theorem *)

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

(** * Parameterized monomial *)

(* {P_MONOMIAL} *)
Definition p_monomial (x n k d : nat) : nat :=
  d * C(n,k) * x ^ k.
(* {END} *)
Hint Unfold p_monomial : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_monomial :
  forall (x n k d : nat),
    p_monomial x n k d = d * C(n, k) * x ^ k.
Proof.
  intros x n k c.
  unfold p_monomial.
  reflexivity.
Qed.
Hint Rewrite unfold_p_monomial : long.

(** *** Properties *)

Lemma p_monomial_k_eq_0_implies_d :
  forall (x n d : nat),
    p_monomial x n 0 d = d.
Proof.
  intros x n d.
  rewrite -> unfold_p_monomial.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  rewrite ->2 mult_1_r.
  reflexivity.
Qed.
Hint Rewrite p_monomial_k_eq_0_implies_d : long.

Lemma p_monomial_n_lt_k_implies_0 :
  forall (x n k d : nat),
    n < k ->
    p_monomial x n k d = 0.
Proof.
  intros x n k d H_n_lt_k.
  rewrite -> unfold_p_monomial.
  inversion_clear H_n_lt_k.

  Case "k = S n".
  rewrite -> binomial_coefficient_n_lt_k_implies_0;
    [ idtac | unfold lt; apply le_n ].
  rewrite -> mult_0_r, mult_0_l.
  reflexivity.

  Case "k = S m".
  rename H into H_S_n_le_m.
  rewrite -> binomial_coefficient_n_lt_k_implies_0;
    [ idtac | unfold lt; apply le_S; exact H_S_n_le_m ].
  rewrite -> mult_0_r, -> mult_0_l.
  reflexivity.
Qed.
Hint Rewrite p_monomial_n_lt_k_implies_0 : long.

Lemma p_monomial_n_eq_k_implies_power :
  forall (x n d : nat),
    p_monomial x n n d = d * x ^ n.
Proof.
  intros x n d.
  rewrite -> unfold_p_monomial.
  rewrite -> binomial_coefficient_n_eq_k_implies_1.
  rewrite -> mult_1_r.
  reflexivity.
Qed.
Hint Rewrite p_monomial_n_eq_k_implies_power : long.

Lemma p_monomial_Pascal_s_rule :
  forall (x n' k' d : nat),
    p_monomial x (S n') (S k') d =
    p_monomial x n' (S k') d + x * p_monomial x n' k' d.
Proof.
  intros x n' k' d.
  rewrite ->2 unfold_p_monomial.
  rewrite -> Pascal_s_rule.
  rewrite <- mult_assoc.
  rewrite -> mult_plus_distr_r.
  rewrite -> mult_plus_distr_l.
  rewrite -> mult_assoc.
  rewrite <- unfold_p_monomial.
  rewrite -> unfold_power_induction_case.
  rewrite -> (NPeano.Nat.mul_shuffle3 (C(n', k')) x (x ^ k')).
  rewrite -> NPeano.Nat.mul_shuffle3.
  rewrite -> (mult_assoc d _ _).
  rewrite <- (unfold_p_monomial _ _ _ d).
  reflexivity.
Qed.
Hint Rewrite p_monomial_Pascal_s_rule : long.

(** * Parameteriezd characteristic function of Moessner's sieve *)

(** ** Moessner Entry Binomial

  Given a value [d], rank [r], a row [n], a column [k], and a triangle [t],
  calculate the specific entry of a Moessner triangle.

  *** Definition *)

(* {P_MOESSNER_ENTRY} *)
Fixpoint p_moessner_entry (r n k t d : nat) : nat :=
  match n with
    | 0 => match k with
             | 0 => d
             | S k' => 0
           end
    | S n' => match k with
                | 0 => p_monomial t r (S n') d +
                       p_moessner_entry r n' 0 t d
                | S k' => p_moessner_entry r n' (S k') t d +
                          p_moessner_entry r n' k' t d
              end
  end.
(* {END} *)
Hint Unfold p_moessner_entry : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_moessner_entry_base_case_O :
  forall (r t d : nat),
    p_moessner_entry r 0 0 t d = d.
Proof.
  intros r t d.
  unfold p_moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_p_moessner_entry_base_case_O : long.

Lemma unfold_p_moessner_entry_base_case_S :
  forall (r k' t d : nat),
    p_moessner_entry r 0 (S k') t d = 0.
Proof.
  intros r k' t d.
  unfold p_moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_p_moessner_entry_base_case_S : long.

Lemma unfold_p_moessner_entry_induction_case_O :
  forall (n' r t d : nat),
    p_moessner_entry r (S n') 0 t d =
    p_monomial t r (S n') d + p_moessner_entry r n' 0 t d.
Proof.
  intros n' r t d.
  unfold p_moessner_entry; fold p_moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_p_moessner_entry_induction_case_O : long.

Lemma unfold_p_moessner_entry_induction_case_S :
  forall (n' r k' t d : nat),
    p_moessner_entry r (S n') (S k') t d =
    p_moessner_entry r n' (S k') t d +
    p_moessner_entry r n' k' t d.
Proof.
  intros n' r k' t d.
  unfold p_moessner_entry; fold p_moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_p_moessner_entry_induction_case_S : long.

(** *** Properties *)

Definition p_moessner_entry_Pascal_s_rule :=
  unfold_p_moessner_entry_induction_case_S.
Hint Rewrite p_moessner_entry_Pascal_s_rule : long.

Lemma p_moessner_entry_eq_c_binomial_coefficient :
  forall (r k n d : nat),
    p_moessner_entry n r k 0 d = d * C(r, k).
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  intros n k d.
  unfold p_moessner_entry, binomial_coefficient.
  case n as [ | n' ];
    [ rewrite -> mult_1_r; reflexivity |
      rewrite -> mult_0_r; reflexivity ].

  Case "r = S r'".
  case k as [ | k' ].

  SCase "k = 0".
  intros n d.
  rewrite -> unfold_p_moessner_entry_induction_case_O.
  rewrite -> (IH_r' 0 n).
  rewrite -> unfold_p_monomial.
  rewrite -> power_0_e.
  rewrite -> mult_0_r.
  rewrite -> plus_0_l.
  rewrite ->2 unfold_binomial_coefficient_base_case_n_0.
  rewrite -> mult_1_r.
  reflexivity.

  SCase "k = S k'".
  intros n d.
  rewrite -> p_moessner_entry_Pascal_s_rule.
  rewrite -> (IH_r' (S k') n).
  rewrite -> (IH_r' k' n).
  rewrite <- mult_plus_distr_l.
  rewrite <- Pascal_s_rule.
  reflexivity.
Qed.
Hint Rewrite p_moessner_entry_eq_c_binomial_coefficient : long.

Lemma p_moessner_entry_n_lt_k_implies_0 :
  forall (r n k t d : nat),
    n < k ->
    p_moessner_entry r n k t d = 0.
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  case k as [ | k' ].

  SCase "k = 0".
  intros t d H_absurd; inversion H_absurd.

  SCase "k = S k'".
  intros t d H_0_lt_S_k'.
  rewrite -> unfold_p_moessner_entry_base_case_S.
  reflexivity.

  Case "n = S n'".
  case k as [ | k' ].

  SCase "k = 0".
  intros t d H_absurd; inversion H_absurd.

  SCase "k = S k'".
  intros t d H_S_n'_lt_S_k'.
  rewrite -> p_moessner_entry_Pascal_s_rule.

  assert (H_n'_lt_S_k': n' < S k').
    apply lt_S_n.
    unfold lt.
    apply le_S.
    unfold lt in H_S_n'_lt_S_k'.
    exact H_S_n'_lt_S_k'.

  rewrite -> (IH_n' (S k') t d H_n'_lt_S_k'); clear H_n'_lt_S_k'.
  rewrite -> plus_0_l.

  assert (H_n'_lt_k': n' < k').
    apply lt_S_n.
    exact H_S_n'_lt_S_k'.

  rewrite -> (IH_n' k' t d H_n'_lt_k').
  reflexivity.
Qed.
Hint Resolve p_moessner_entry_n_lt_k_implies_0 : long.

Lemma p_moessner_entry_n_eq_k_implies_d :
  forall (n r t d : nat),
    p_moessner_entry r n n t d = d.
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r t d.
  rewrite -> unfold_p_moessner_entry_base_case_O.
  reflexivity.

  Case "n = S n'".
  intros r t d.
  rewrite -> p_moessner_entry_Pascal_s_rule.
  rewrite -> (IH_n' r t).
  rewrite -> p_moessner_entry_n_lt_k_implies_0;
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  reflexivity.
Qed.
Hint Rewrite p_moessner_entry_n_eq_k_implies_d : long.

(** ** Moessner Entries Binomial

  [p_moessner_entry] as a [Stream nat].

  *** Definition *)

(* {P_MOESSNER_ENTRIES} *)
CoFixpoint p_moessner_entries (r n k t d : nat) : Stream nat :=
  (p_moessner_entry r n k t d) :::
  (p_moessner_entries r n (S k) t d).
(* {END} *)
Hint Unfold p_moessner_entries : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_moessner_entries :
  forall (r n k t d : nat),
    p_moessner_entries r n k t d =
    (p_moessner_entry r n k t d) :::
    (p_moessner_entries r n (S k) t d).
Proof.
  intros r n k t d.
  rewrite -> (unfold_Stream (p_moessner_entries r n k t d)).
  unfold p_moessner_entries; fold p_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite unfold_p_moessner_entries : long.

Lemma p_moessner_entries_initial_value :
  forall (r n k t d : nat),
    (p_moessner_entries r n k t d)(0) =
    (p_moessner_entry r n k t d).
Proof.
  intros r n k t d.
  rewrite -> initial_value.
  rewrite -> unfold_p_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite p_moessner_entries_initial_value : long.

Lemma p_moessner_entries_stream_derivative :
  forall (r n k t d : nat),
    (p_moessner_entries r n k t d)` =
    (p_moessner_entries r n (S k) t d).
Proof.
  intros r n k t d.
  rewrite -> stream_derivative.
  rewrite -> unfold_p_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite p_moessner_entries_stream_derivative : long.

(** ** Properties *)

Lemma Str_nth_p_moessner_entries :
  forall (i r n k t d : nat),
    Str_nth i (p_moessner_entries r n k t d) =
    p_moessner_entry r n (i + k) t d.
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros r n k t d.
  rewrite -> Str_nth_0.
  rewrite -> p_moessner_entries_initial_value.
  rewrite -> plus_0_l.
  reflexivity.

  Case "i = S i'".
  intros r n k t d.
  rewrite -> Str_nth_S_n.
  rewrite -> p_moessner_entries_stream_derivative.
  rewrite -> (IH_i' r n (S k) t d).
  rewrite <- plus_n_Sm.
  rewrite -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_moessner_entries : long.

(** ** Moessner Entry Rotated

  Given a rank [n], a row [r], a column [c], and a triangle [t],
  calculate the specific entry of a Moessner triangle.

  *** Definition *)

(* {P_ROTATED_MOESSNER_ENTRY} *)
Definition p_rotated_moessner_entry (n r c t d : nat) : nat :=
  p_moessner_entry n (c + r) c t d.
(* {END} *)
Hint Unfold p_rotated_moessner_entry : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_rotated_moessner_entry :
  forall (n r c t d : nat),
    p_rotated_moessner_entry n r c t d =
    p_moessner_entry n (c + r) c t d.
Proof.
  intros n r c t d.
  unfold p_rotated_moessner_entry.
  reflexivity.
Qed.
Hint Rewrite unfold_p_rotated_moessner_entry : long.

Lemma p_rotated_moessner_entry_Pascal_s_rule :
  forall (n r' c' t d : nat),
    p_rotated_moessner_entry n (S r') (S c') t d =
    p_rotated_moessner_entry n r' (S c') t d +
    p_rotated_moessner_entry n (S r') c' t d.
Proof.
  intros n r' c' t d.
  rewrite ->3 unfold_p_rotated_moessner_entry.
  rewrite <-2 plus_n_Sm.
  rewrite -> plus_Sn_m.
  rewrite -> p_moessner_entry_Pascal_s_rule.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_Pascal_s_rule : long.

(** *** Properties *)

Lemma p_rotated_moessner_entry_eq_d_binomial_coefficient :
  forall (n r c d : nat),
    p_rotated_moessner_entry n r c 0 d = d * C(c + r, c).
Proof.
  intros n r c d.
  rewrite -> unfold_p_rotated_moessner_entry.
  rewrite -> p_moessner_entry_eq_c_binomial_coefficient.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_eq_d_binomial_coefficient : long.

(* {P_ROTATED_MOESSNER_ENTRY_EQ_D_ROTATED_BINOMIAL_COEFFICIENT} *)
Corollary p_rotated_moessner_entry_eq_d_rotated_binomial_coefficient :
  forall (n r c d : nat),
    p_rotated_moessner_entry n r c 0 d = d * R(r, c).
(* {END} *)
Proof.
  intros n r c d.
  rewrite -> p_rotated_moessner_entry_eq_d_binomial_coefficient.
  rewrite -> rotated_binomial_coefficient_is_symmetric.
  rewrite -> unfold_rotated_binomial_coefficient.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_eq_d_rotated_binomial_coefficient : long.

Lemma p_rotated_moessner_entry_r_eq_0_implies_d :
  forall (c n t d : nat),
    p_rotated_moessner_entry n 0 c t d = d.
Proof.
  intros c n t d.
  rewrite -> unfold_p_rotated_moessner_entry.
  rewrite -> plus_0_r.
  rewrite -> p_moessner_entry_n_eq_k_implies_d.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_r_eq_0_implies_d : long.

Lemma p_rotated_moessner_entry_c_eq_0 :
  forall (r' n t d : nat),
    p_rotated_moessner_entry n (S r') 0 t d =
    p_monomial t n (S r') d + p_rotated_moessner_entry n r' 0 t d.
Proof.
  intros r' n t d.
  rewrite ->2 unfold_p_rotated_moessner_entry.
  rewrite ->2 plus_0_l.
  rewrite -> unfold_p_moessner_entry_induction_case_O.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_c_eq_0 : long.

(** ** Moessner Entries Rotated

  *** Definition *)

(* {P_ROTATED_MOESSNER_ENTRIES} *)
CoFixpoint p_rotated_moessner_entries (n r c t d : nat) : Stream nat :=
  (p_rotated_moessner_entry n r c t d) :::
  (p_rotated_moessner_entries n (S r) c t d).
(* {END} *)
Hint Unfold p_rotated_moessner_entries : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_rotated_moessner_entries :
  forall (n r c t d : nat),
    p_rotated_moessner_entries n r c t d =
    (p_rotated_moessner_entry n r c t d) :::
    (p_rotated_moessner_entries n (S r) c t d).
Proof.
  intros n r c t d.
  rewrite -> (unfold_Stream (p_rotated_moessner_entries n r c t d)).
  unfold p_rotated_moessner_entries; fold p_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite unfold_p_rotated_moessner_entries : long.

Lemma p_rotated_moessner_entries_initial_value :
  forall (n r c t d : nat),
    (p_rotated_moessner_entries n r c t d)(0) =
    (p_rotated_moessner_entry n r c t d).
Proof.
  intros n r c t d.
  rewrite -> initial_value.
  rewrite -> unfold_p_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entries_initial_value : long.

Lemma p_rotated_moessner_entries_stream_derivative :
  forall (n r c t d : nat),
    (p_rotated_moessner_entries n r c t d)` =
    (p_rotated_moessner_entries n (S r) c t d).
Proof.
  intros n r c t d.
  rewrite -> stream_derivative.
  rewrite -> unfold_p_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entries_stream_derivative : long.

(** ** Properties *)

Lemma Str_nth_p_rotated_moessner_entries :
  forall (i n r c t d : nat),
    Str_nth i (p_rotated_moessner_entries n r c t d) =
    p_rotated_moessner_entry n (r + i) c t d.
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros n r c t d.
  rewrite -> Str_nth_0.
  rewrite -> p_rotated_moessner_entries_initial_value.
  rewrite -> plus_0_r.
  reflexivity.

  Case "i = S i'".
  intros n r c t d.
  rewrite -> Str_nth_S_n.
  rewrite -> p_rotated_moessner_entries_stream_derivative.
  rewrite -> (IH_i' n (S r) c t d).
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_rotated_moessner_entries : long.

Corollary Str_nth_p_rotated_moessner_entries_t_eq_0 :
  forall (i n r c d : nat),
    Str_nth i (p_rotated_moessner_entries n r c 0 d) =
    d * C(c + (r + i), c).
Proof.
  intros i n r c d.
  rewrite -> Str_nth_p_rotated_moessner_entries.
  rewrite -> p_rotated_moessner_entry_eq_d_binomial_coefficient.
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_rotated_moessner_entries_t_eq_0 : long.

Lemma p_rotated_moessner_entries_Pascal_s_rule :
  forall (n r' c' t d : nat),
    p_rotated_moessner_entries n (S r') (S c') t d ~
    (p_rotated_moessner_entries n (S r') c' t d) s+
    (p_rotated_moessner_entries n r' (S c') t d).
Proof.
  pcofix coIH.
  intros n r' c' t d.
  bisimilar.

  Case "initial value".
  rewrite -> stream_sum_initial_value.
  rewrite ->3 p_rotated_moessner_entries_initial_value.
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  rewrite -> plus_comm.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_sum_stream_derivative.
  rewrite ->3 p_rotated_moessner_entries_stream_derivative.
  exact (coIH n (S r') c' t d).
Qed.
Hint Rewrite p_rotated_moessner_entries_Pascal_s_rule : long.

(** * Streams of P_Monomials *)

(** ** P_Monomials

  The stream of p_monomials of the binomial expansion.

  *** Definition *)

(* {P_MONOMIALS} *)
CoFixpoint p_monomials (t r n d : nat) : Stream nat :=
  (p_monomial t r n d) ::: (p_monomials t r (S n) d).
(* {END} *)
Hint Unfold p_monomials : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_monomials :
  forall (t r n d : nat),
    p_monomials t r n d = (p_monomial t r n d) ::: (p_monomials t r (S n) d).
Proof.
  intros t r n d.
  rewrite -> (unfold_Stream (p_monomials t r n d)).
  unfold p_monomials; fold p_monomials.
  reflexivity.
Qed.
Hint Rewrite unfold_p_monomials : long.

Lemma p_monomials_initial_value :
  forall (t r n d : nat),
    (p_monomials t r n d)(0) = (p_monomial t r n d).
Proof.
  intros t r n d.
  rewrite -> initial_value.
  rewrite -> unfold_p_monomials.
  reflexivity.
Qed.
Hint Rewrite p_monomials_initial_value : long.

Lemma p_monomials_stream_derivative :
  forall (t r n d : nat),
    (p_monomials t r n d)` = (p_monomials t r (S n) d).
Proof.
  intros t r n d.
  rewrite -> stream_derivative.
  rewrite -> unfold_p_monomials.
  reflexivity.
Qed.
Hint Rewrite p_monomials_stream_derivative : long.

(** *** Properties *)

Lemma Str_nth_p_monomials :
  forall (i t r n d : nat),
    Str_nth i (p_monomials t r n d) = p_monomial t r (i + n) d.
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros t r n d.
  rewrite -> Str_nth_0.
  rewrite -> p_monomials_initial_value.
  rewrite -> plus_0_l.
  reflexivity.

  Case "i = S i'".
  intros t r n d.
  rewrite -> Str_nth_S_n.
  rewrite -> p_monomials_stream_derivative.
  rewrite -> (IH_i' t r (S n) d).
  rewrite -> plus_Sn_m, <- plus_n_Sm.
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_monomials : long.

Lemma Str_nth_p_monomials_i_plus_n_gt_r_implies_0 :
  forall (i r n t d : nat),
    r < n + i ->
    Str_nth i (p_monomials t r n d) = 0.
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros r n t d H_r_lt_n.
  rewrite -> plus_0_r in H_r_lt_n.
  rewrite -> Str_nth_0.
  rewrite -> p_monomials_initial_value.
  rewrite -> unfold_p_monomial.
  rewrite -> (binomial_coefficient_n_lt_k_implies_0 r n H_r_lt_n).
  rewrite -> mult_0_r, -> mult_0_l.
  reflexivity.

  Case "i = S i'".
  intros r n t d H_r_lt_n_plus_S_i'.
  rewrite -> Str_nth_S_n.
  rewrite p_monomials_stream_derivative.
  rewrite -> (IH_i' r (S n) t d);
    [ idtac | rewrite -> plus_Sn_m, -> plus_n_Sm; exact H_r_lt_n_plus_S_i' ].
  reflexivity.
Qed.
Hint Resolve Str_nth_p_monomials_i_plus_n_gt_r_implies_0 : long.

Lemma p_monomials_t_eq_0_aux :
  forall (k n d : nat),
    (p_monomials 0 k n d)` ~ #0.
Proof.
  pcofix coIH.
  intros k n d.
  bisimilar.

  Case "initial value".
  rewrite -> p_monomials_stream_derivative.
  rewrite -> p_monomials_initial_value.
  rewrite -> unfold_p_monomial.
  rewrite -> power_0_e.
  rewrite -> mult_0_r.
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> p_monomials_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH k (S n) d).
Qed.
Hint Rewrite p_monomials_t_eq_0_aux : long.

Corollary p_monomials_t_eq_0 :
  forall (k d : nat),
    (p_monomials 0 k 0 d) ~ d ::: #0.
Proof.
  intros k d.
  rewrite -> (decompose_Stream (p_monomials 0 k 0 d)).
  rewrite -> (p_monomials_t_eq_0_aux k 0).
  rewrite -> p_monomials_initial_value.
  rewrite -> unfold_p_monomial.
  rewrite -> unfold_power_base_case.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  rewrite ->2 mult_1_r.
  reflexivity.
Qed.
Hint Rewrite p_monomials_t_eq_0 : long.

Lemma p_monomials_tail_of_0s :
  forall (i n t d : nat),
    Str_nth_tl (S i) (p_monomials t i n d) ~ #0.
Proof.
  pcofix coIH.
  intros i n t d.
  bisimilar.

  Case "initial value".
  rewrite <- unfold_Str_nth.
  rewrite -> Str_nth_p_monomials_i_plus_n_gt_r_implies_0;
    [ idtac | unfold lt; apply le_plus_r ].
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> Str_nth_tl_stream_derivative_case_i_gt_0.
  rewrite ->2 p_monomials_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH i (S n) t d).
Qed.
Hint Rewrite p_monomials_tail_of_0s : long.

Lemma rev_Str_prefix_p_monomials :
  forall (l n r t d : nat),
    rev (Str_prefix (S l) (p_monomials t r n d)) =
    p_monomial t r (n + l) d :: rev (Str_prefix l (p_monomials t r n d)).
Proof.
  induction l as [ | l' IH_l' ].

  Case "l = 0".
  intros n r t d.
  rewrite -> plus_0_r.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> p_monomials_initial_value.
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> app_nil_l.
  reflexivity.

  Case "l = S l'".
  intros n r t d.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_rev_induction_case.
  rewrite -> p_monomials_stream_derivative.
  rewrite -> IH_l'.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> p_monomials_initial_value.
  rewrite -> p_monomials_stream_derivative.
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  rewrite -> unfold_rev_induction_case.
  rewrite <- app_comm_cons.
  reflexivity.
Qed.
Hint Rewrite rev_Str_prefix_p_monomials : long.

(** ** P_Monomials Sum

  *** Definition *)

(* {P_MONOMIALS_SUM} *)
CoFixpoint p_monomials_sum (t r n a d : nat) : Stream nat :=
  let a' := (p_monomial t r n d) + a in
  a' ::: (p_monomials_sum t r (S n) a' d).
(* {END} *)
Hint Unfold p_monomials_sum : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_monomials_sum :
  forall (t r n a d : nat),
    p_monomials_sum t r n a d =
    ((p_monomial t r n d) + a) :::
    (p_monomials_sum t r (S n) ((p_monomial t r n d) + a) d).
Proof.
  intros t r n a d.
  rewrite -> (unfold_Stream (p_monomials_sum t r n a d)).
  unfold p_monomials_sum; fold p_monomials_sum.
  reflexivity.
Qed.
Hint Rewrite unfold_p_monomials_sum : long.

Lemma p_monomials_sum_initial_value :
  forall (t r n a d : nat),
    (p_monomials_sum t r n a d)(0) = (p_monomial t r n d) + a.
Proof.
  intros t r n a d.
  rewrite -> initial_value.
  rewrite -> unfold_p_monomials_sum.
  reflexivity.
Qed.
Hint Rewrite p_monomials_sum_initial_value : long.

Lemma p_monomials_sum_stream_derivative :
  forall (t r n a d : nat),
    (p_monomials_sum t r n a d)` =
    (p_monomials_sum t r (S n) ((p_monomial t r n d) + a) d).
Proof.
  intros t r n a d.
  rewrite -> stream_derivative.
  rewrite -> unfold_p_monomials_sum.
  reflexivity.
Qed.
Hint Rewrite p_monomials_sum_stream_derivative : long.

(** *** Properties *)

Lemma p_monomials_sum_acc_aux :
  forall (t l n i j d : nat),
    (p_monomials_sum t l n (i + j) d) ~
    (p_monomials_sum t l n i d) s+ #j.
Proof.
  pcofix coIH.
  intros t l n i j d.
  bisimilar.

  Case "initial value".
  rewrite -> p_monomials_sum_initial_value.
  rewrite -> stream_sum_initial_value.
  rewrite -> p_monomials_sum_initial_value.
  rewrite -> stream_constant_initial_value.
  rewrite <- plus_assoc.
  reflexivity.

  Case "stream derivative".
  rewrite -> p_monomials_sum_stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite -> p_monomials_sum_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  rewrite -> plus_assoc.
  exact (coIH t l (S n) ((p_monomial t l n d) + i) j d).
Qed.
Hint Rewrite p_monomials_sum_acc_aux : long.

Corollary p_monomials_sum_acc :
  forall (t l n a d : nat),
    (p_monomials_sum t l n a d) ~
    (p_monomials_sum t l n 0 d) s+ #a.
Proof.
  intros t l n a d.
  rewrite <- p_monomials_sum_acc_aux.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite p_monomials_sum_acc : long.

Lemma Str_nth_p_monomials_sum_stream_derivative :
  forall (i n t l a d : nat),
    Str_nth i (p_monomials_sum t l n a d)` =
    Str_nth i ((p_monomials_sum t l (S n) a d) s+ #(p_monomial t l n d)).
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros n t l a d.
  rewrite -> p_monomials_sum_stream_derivative.
  rewrite ->2 Str_nth_0.
  rewrite -> stream_sum_initial_value.
  rewrite ->2 p_monomials_sum_initial_value.
  rewrite -> stream_constant_initial_value.
  rewrite <- plus_assoc.
  f_equal.
  rewrite -> plus_comm.
  reflexivity.

  Case "i = S i'".
  intros n t l a d.
  rewrite ->2 Str_nth_S_n.
  rewrite -> p_monomials_sum_stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite -> (IH_i' (S n) t l ((p_monomial t l n d) + a)).
  rewrite -> p_monomials_sum_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  rewrite <-2 p_monomials_sum_acc_aux.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  rewrite -> (plus_comm a _).
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_monomials_sum_stream_derivative : long.

Corollary p_monomials_sum_stream_derivative_bisim :
  forall (n t l a d : nat),
    (p_monomials_sum t l n a d)` ~
    (p_monomials_sum t l (S n) a d) s+ #(p_monomial t l n d).
Proof.
  intros n t l a d.
  apply Str_nth_implies_bisimilarity; intro i.
  exact (Str_nth_p_monomials_sum_stream_derivative i n t l a d).
Qed.
Hint Rewrite p_monomials_sum_stream_derivative_bisim : long.

Lemma Str_nth_p_monomials_sum_r_eq_0 :
  forall (i t n' m' a d : nat),
    Str_nth i (p_monomials_sum t 0 (S n') a d) =
    Str_nth i (p_monomials_sum t 0 (S m') a d).
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros t n' m' a d.
  rewrite ->2 Str_nth_0.
  rewrite ->2 p_monomials_sum_initial_value.
  rewrite ->2 unfold_p_monomial.
  rewrite ->2 unfold_binomial_coefficient_base_case_0_S_k'.
  rewrite -> mult_0_r, ->2 mult_0_l.
  rewrite -> plus_0_l.
  reflexivity.

  Case "i = S i'".
  intros t n' m' a d.
  rewrite ->2 Str_nth_S_n.
  rewrite ->2 Str_nth_p_monomials_sum_stream_derivative.
  unfold stream_sum.
  rewrite ->2 Str_nth_stream_zip.
  rewrite -> (IH_i' t (S n') (S m') a d).
  rewrite ->2 Str_nth_stream_constant.
  rewrite ->2 unfold_p_monomial.
  rewrite ->2 unfold_binomial_coefficient_base_case_0_S_k'.
  rewrite -> mult_0_r, -> mult_0_l, ->2 plus_0_r.
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_monomials_sum_r_eq_0 : long.

Lemma about_p_monomial_and_p_monomials_sum :
  forall (i' r n a t d : nat),
   p_monomial t r n d + Str_nth i' (p_monomials_sum t r (S n) a d) =
   p_monomial t r (n + (S i')) d + Str_nth i' (p_monomials_sum t r n a d).
Proof.
  induction i' as [ | i'' IH_i'' ].

  Case "i' = 0".
  intros r n a t d.
  rewrite ->2 Str_nth_0.
  rewrite ->2 p_monomials_sum_initial_value.
  rewrite -> plus_permute.
  rewrite -> (plus_comm n 1).
  reflexivity.

  Case "i' = S i''".
  intros r n a t d.
  rewrite -> Str_nth_S_n.
  rewrite -> Str_nth_p_monomials_sum_stream_derivative.
  unfold stream_sum.
  rewrite -> Str_nth_stream_zip.
  rewrite -> Str_nth_stream_constant.
  rewrite <- (plus_comm (p_monomial t r (S n) d) _).
  rewrite -> (IH_i'' r (S n) a t d).
  rewrite <-3 plus_n_Sm, -> plus_Sn_m.

  rewrite -> Str_nth_S_n.
  rewrite -> Str_nth_p_monomials_sum_stream_derivative.
  unfold stream_sum.
  rewrite -> Str_nth_stream_zip.
  rewrite -> Str_nth_stream_constant.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  reflexivity.
Qed.
Hint Rewrite about_p_monomial_and_p_monomials_sum : long.

(** * Equivalence relations *)

Theorem Str_nth_p_monomials_sum_eq_p_rotated_moessner_entry :
  forall (i t r a d : nat),
    Str_nth i (p_monomials_sum t r 0 a d) =
    (p_rotated_moessner_entry r i 0 t d) + a.
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros t r a d.
  rewrite -> Str_nth_0.
  rewrite -> p_monomials_sum_initial_value.
  rewrite -> unfold_p_monomial.
  rewrite -> unfold_power_base_case.
  rewrite -> mult_1_r.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.

  rewrite -> unfold_p_rotated_moessner_entry.
  rewrite -> plus_0_r, -> mult_1_r.
  rewrite -> unfold_p_moessner_entry_base_case_O.
  reflexivity.

  Case "i = S i'".
  intros t r a d.
  rewrite -> Str_nth_S_n.
  rewrite -> Str_nth_p_monomials_sum_stream_derivative.
  unfold stream_sum.
  rewrite -> Str_nth_stream_zip.
  rewrite -> Str_nth_stream_constant.
  rewrite -> plus_comm.

  unfold p_rotated_moessner_entry in *.
  rewrite -> plus_0_l in *.
  rewrite -> unfold_p_moessner_entry_induction_case_O.
  rewrite <- plus_assoc.
  rewrite <- (IH_i' t r a d).
  rewrite -> about_p_monomial_and_p_monomials_sum.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_monomials_sum_eq_p_rotated_moessner_entry : long.

Lemma stream_partial_sums_acc_p_monomials_bisim_p_monomials_sum :
  forall (t l n a d : nat),
    stream_partial_sums_acc a (p_monomials t l n d) ~
    p_monomials_sum t l n a d.
Proof.
  pcofix coIH.
  intros t l n a d.
  bisimilar.

  Case "initial value".
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> p_monomials_initial_value.
  rewrite -> p_monomials_sum_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> p_monomials_stream_derivative.
  rewrite -> p_monomials_sum_stream_derivative.
  rewrite -> p_monomials_initial_value.
  exact (coIH t l (S n) (p_monomial t l n d + a) d).
Qed.
Hint Rewrite stream_partial_sums_acc_p_monomials_bisim_p_monomials_sum : long.

(* {STREAM_PARTIAL_SUMS_P_MONOMIALS_BISIM_P_MONOMIALS_SUM} *)
Corollary stream_partial_sums_p_monomials_bisim_p_monomials_sum :
  forall (t l n d : nat),
    stream_partial_sums (p_monomials t l n d) ~
    p_monomials_sum t l n 0 d.
(* {END} *)
Proof.
  intros t l n d.
  rewrite -> unfold_stream_partial_sums.
  exact (stream_partial_sums_acc_p_monomials_bisim_p_monomials_sum t l n 0 d).
Qed.
Hint Rewrite stream_partial_sums_p_monomials_bisim_p_monomials_sum : long.

(* {P_MONOMIALS_AND_MAKE_TUPLE} *)
Corollary p_monomials_and_make_tuple :
  forall (l t r n a d : nat),
    make_tuple (Str_prefix (S l) (p_monomials t r n d)) a =
    Str_prefix l (p_monomials_sum t r n a d).
(* {END} *)
Proof.
  intros l t r n a d.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  rewrite -> stream_partial_sums_acc_p_monomials_bisim_p_monomials_sum.
  reflexivity.
Qed.
Hint Rewrite p_monomials_and_make_tuple : long.

Corollary p_monomials_and_p_rotated_moessner_entry :
  forall (l t r a d : nat),
    nth l (make_tuple (Str_prefix (S (S l)) (p_monomials t r 0 d)) a) 0 =
    p_rotated_moessner_entry r l 0 t d + a.
Proof.
  intros l t r a d.
  rewrite <- Str_nth_p_monomials_sum_eq_p_rotated_moessner_entry.
  rewrite -> p_monomials_and_make_tuple.
  rewrite -> (nth_and_Str_nth l (S l) (p_monomials_sum t r 0 a d));
      [ idtac | unfold lt; apply le_n ].
  reflexivity.
Qed.
Hint Rewrite p_monomials_and_p_rotated_moessner_entry : long.

(* {P_ROTATED_MOESSNER_ENTRIES_BISIM_P_MONOMIALS_SUM} *)
Corollary p_rotated_moessner_entries_bisim_p_monomials_sum :
  forall (n t d : nat),
    p_rotated_moessner_entries n 0 0 t d ~
    p_monomials_sum t n 0 0 d.
(* {END} *)
Proof.
  intros n t d.
  apply Str_nth_implies_bisimilarity; intro i.
  rewrite -> Str_nth_p_rotated_moessner_entries.
  rewrite -> plus_0_l.
  rewrite -> Str_nth_p_monomials_sum_eq_p_rotated_moessner_entry.
  rewrite -> plus_0_r.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entries_bisim_p_monomials_sum : long.

(** * Columns of Moessner Entries Rotated *)

(** Proof that partially summing the [c']th column of rotated moessner entries
  gives the [S c']th column *)

Lemma Str_nth_p_rotated_moessner_entries_inductive_case :
  forall (i n r' c' t d : nat),
    Str_nth i (p_rotated_moessner_entries n (S r') (S c') t d) =
    Str_nth i (stream_partial_sums_acc
                 (p_rotated_moessner_entry n r' (S c') t d)
                 (p_rotated_moessner_entries n (S r') c' t d)).
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros n r' c' t d.
  rewrite ->2 Str_nth_0.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite ->2 p_rotated_moessner_entries_initial_value.
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  rewrite -> plus_comm.
  reflexivity.

  Case "i = S i'".
  intros n r' c' t d.
  rewrite ->2 Str_nth_S_n.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite ->2 p_rotated_moessner_entries_stream_derivative.
  rewrite -> p_rotated_moessner_entries_initial_value.
  rewrite -> (IH_i' n (S r') c' t d).
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_rotated_moessner_entries_inductive_case : long.

(* {P_ROTATED_MOESSNER_ENTRIES_BISIM_PREVIOUS_COLUMN_INDUCTIVE_CASE} *)
Corollary p_rotated_moessner_entries_bisim_previous_column_inductive_case :
  forall (n r' c' t d : nat),
    (p_rotated_moessner_entries n (S r') (S c') t d) ~
    (stream_partial_sums_acc (p_rotated_moessner_entry n r' (S c') t d)
                      (p_rotated_moessner_entries n (S r') c' t d)).
(* {END} *)
Proof.
  intros n r' c' t d.
  apply Str_nth_implies_bisimilarity; intro i.
  exact
  (Str_nth_p_rotated_moessner_entries_inductive_case i n r' c' t d).
Qed.
Hint Rewrite p_rotated_moessner_entries_bisim_previous_column_inductive_case
  : long.

Lemma Str_nth_p_rotated_moessner_entries_base_case :
  forall (i n c' t d : nat),
    Str_nth i (p_rotated_moessner_entries n 0 (S c') t d) =
    Str_nth i (stream_partial_sums_acc 0 (p_rotated_moessner_entries n 0 c' t d)).
Proof.
  case i as [ | i' ].

  Case "i = 0".
  intros n c' t d.
  rewrite ->2 Str_nth_0.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> plus_0_r.
  rewrite ->2 p_rotated_moessner_entries_initial_value.
  rewrite ->2 unfold_p_rotated_moessner_entry.
  rewrite ->2 plus_0_r.
  rewrite -> p_moessner_entry_Pascal_s_rule.
  rewrite -> p_moessner_entry_n_lt_k_implies_0;
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  reflexivity.

  Case "i = S i'".
  intros n c' t d.
  rewrite ->2 Str_nth_S_n.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> plus_0_r.
  rewrite ->2 p_rotated_moessner_entries_stream_derivative.
  rewrite -> p_rotated_moessner_entries_initial_value.
  rewrite -> Str_nth_p_rotated_moessner_entries_inductive_case.
  rewrite ->2 unfold_p_rotated_moessner_entry.
  rewrite ->2 plus_0_r.
  rewrite -> p_moessner_entry_Pascal_s_rule.
  rewrite -> p_moessner_entry_n_lt_k_implies_0;
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  reflexivity.
Qed.
Hint Rewrite Str_nth_p_rotated_moessner_entries_base_case : long.

(* {P_ROTATED_MOESSNER_ENTRIES_BISIM_PREVIOUS_COLUMN_BASE_CASE} *)
Corollary p_rotated_moessner_entries_bisim_previous_column_base_case :
  forall (n c' t d : nat),
    (p_rotated_moessner_entries n 0 (S c') t d) ~
    (stream_partial_sums_acc 0 (p_rotated_moessner_entries n 0 c' t d)).
(* {END} *)
Proof.
  intros n c' t d.
  apply Str_nth_implies_bisimilarity; intro i.
  exact (Str_nth_p_rotated_moessner_entries_base_case i n c' t d).
Qed.
Hint Rewrite p_rotated_moessner_entries_bisim_previous_column_base_case : long.

Lemma last_of_p_rotated_moessner_entries :
  forall (c l n t d : nat),
    last (Str_prefix (S l) (p_rotated_moessner_entries n 0 c t d)) 0 =
    p_rotated_moessner_entry n l c t d.
Proof.
  intros c l n t d.
  rewrite -> (length_implies_last_index l);
    [ idtac | rewrite -> Str_prefix_length; reflexivity ].
  rewrite -> nth_and_Str_nth;
    [ idtac | unfold lt; apply le_n ].
  rewrite -> Str_nth_p_rotated_moessner_entries.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite last_of_p_rotated_moessner_entries : long.

Corollary last_of_p_rotated_moessner_entries_to_binomial :
  forall (c l n t d : nat),
    last (Str_prefix (S l) (p_rotated_moessner_entries n 0 c t d)) 0 =
    p_moessner_entry n (c + l) c t d.
Proof.
  intros c l n t d.
  rewrite -> last_of_p_rotated_moessner_entries.
  rewrite -> unfold_p_rotated_moessner_entry.
  reflexivity.
Qed.
Hint Rewrite last_of_p_rotated_moessner_entries_to_binomial : long.

(** Proof that applying [make_tuple] on a column of [p_rotated_moessner_entries]
  gives the next column *)

(* {MAKE_TUPLE_P_ROTATED_MOESSNER_ENTRIES} *)
Corollary make_tuple_p_rotated_moessner_entries :
  forall (l' n' c' t d : nat),
    make_tuple (Str_prefix (S l') (p_rotated_moessner_entries n' 0 c' t d)) 0 =
    Str_prefix l' (p_rotated_moessner_entries n' 0 (S c') t d).
(* {END} *)
Proof.
  intros l' n' c' t d.
  rewrite -> p_rotated_moessner_entries_bisim_previous_column_base_case.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  reflexivity.
Qed.
Hint Rewrite make_tuple_p_rotated_moessner_entries : long.

(** * Spelled out correctness proof of P Moessner Entry Rotated *)

(** ** Correctness proof of repeat_make_tuple and p_rotated_moessner_entry *)

Theorem Str_prefix_p_rotated_moessner_entries :
  forall (c l n t d : nat),
    Str_prefix l (p_rotated_moessner_entries n 0 c t d) =
    repeat_make_tuple
      (Str_prefix (c + l) (p_rotated_moessner_entries n 0 0 t d)) 0 c.
Proof.
  induction c as [ | c' IH_c' ].

  Case "c = 0".
  intros l n t d.
  rewrite -> plus_0_l.
  rewrite -> unfold_repeat_make_tuple_base_case.
  reflexivity.

  Case "c = S c'".
  intros l n t d.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite <- shift_make_tuple_in_repeat_make_tuple.
  rewrite -> plus_Sn_m, -> plus_n_Sm.
  rewrite <- (IH_c' (S l) n t d).
  rewrite -> make_tuple_p_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite Str_prefix_p_rotated_moessner_entries : long.

(* {REPEAT_MAKE_TUPLE_P_MONOMIALS_EQ_MOESSNER_ENTRIES} *)
Corollary repeat_make_tuple_p_monomials_eq_moessner_entries :
  forall (c l n t d : nat),
    Str_prefix l (p_rotated_moessner_entries n 0 c t d) =
    repeat_make_tuple (Str_prefix (S c + l) (p_monomials t n 0 d)) 0 (S c).
(* {END} *)
Proof.
  intros c l n t d.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> plus_Sn_m.
  rewrite -> p_monomials_and_make_tuple.
  rewrite <- p_rotated_moessner_entries_bisim_p_monomials_sum.
  rewrite <- Str_prefix_p_rotated_moessner_entries.
  reflexivity.
Qed.
Hint Rewrite repeat_make_tuple_p_monomials_eq_moessner_entries : long.

Lemma repeat_make_tuple_p_monomials_eq_moessner_entries_general :
  forall (k j n t d : nat),
    j <= k ->
    Str_prefix (k - j) (p_rotated_moessner_entries n 0 j t d) =
    repeat_make_tuple (Str_prefix (S k) (p_monomials t n 0 d)) 0 (S j).
Proof.
  induction k as [ | k' IH_k' ].

  Case "k = 0".
  intros j n t d H_j_le_0.
  unfold minus.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> p_monomials_initial_value.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> repeat_make_tuple_nil.
  reflexivity.

  Case "k = S k'".
  induction j as [ | j' IH_j' ].

  SCase "j = 0".
  intros n t d H_0_le_S_k'.
  rewrite <- minus_n_O.
  rewrite -> repeat_make_tuple_p_monomials_eq_moessner_entries.
  reflexivity.

  SCase "j = S j'".
  intros n t d H_S_j_le_S_k.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite <- shift_make_tuple_in_repeat_make_tuple.
  rewrite <- (IH_j' n t d);
    [ idtac | apply lt_le_weak; unfold lt; exact H_S_j_le_S_k ].
  rewrite <- make_tuple_p_rotated_moessner_entries.
  rewrite -> NPeano.Nat.sub_succ.
  rewrite -> minus_Sn_m;
    [ idtac | apply gt_S_le; unfold gt, lt; exact H_S_j_le_S_k ].
  reflexivity.
Qed.
Hint Resolve repeat_make_tuple_p_monomials_eq_moessner_entries_general : long.

(* {CORRECTNESS_OF_P_ROTATED_MOESSNER_ENTRY} *)
Theorem correctness_of_p_rotated_moessner_entry :
  forall (i j r t d : nat),
    j <= S r ->
    S i <= S r - j ->
    (nth i
         (nth j
              (create_triangle_vertically
                 (tuple_constant (S (S r)) 0)
                 (Str_prefix (S (S r)) (p_monomials t r 0 d)))
              [])
         0) =
    p_rotated_moessner_entry r i j t d.
(* {END} *)
Proof.
  intros i j r t d H_j_le_S_r H_S_i_le_S_r_minus_j.

  assert (H_length_helper: (S (S r)) =
             (length (Str_prefix (S (S r)) (p_monomials t r 0 d)))).
    rewrite -> Str_prefix_length.
    reflexivity.

  assert (H_rewrite_helper:
            (tuple_constant (S (S r)) 0) =
            (tuple_constant
               (length (Str_prefix (S (S r)) (p_monomials t r 0 d)))) 0).
    f_equal.
    exact H_length_helper.

  rewrite -> H_rewrite_helper; clear H_length_helper H_rewrite_helper.
  rewrite <- correctness_of_repeat_make_tuple.

  rewrite <- repeat_make_tuple_p_monomials_eq_moessner_entries_general;
    [ idtac | exact H_j_le_S_r ].

  rewrite -> nth_and_Str_nth;
    [ idtac | unfold lt; exact H_S_i_le_S_r_minus_j ].

  rewrite -> Str_nth_p_rotated_moessner_entries.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Resolve correctness_of_p_rotated_moessner_entry : long.

(** * Decomposition by Rank *)

(* Decomposition by rank (moessner entry rotated) *)

Theorem p_rotated_moessner_entry_rank_decompose_by_row :
  forall (r c n t d : nat),
  p_rotated_moessner_entry (S n) (S r) c t d =
  t * p_rotated_moessner_entry n r c t d +
  p_rotated_moessner_entry n (S r) c t d.
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  induction c as [ | c' IH_c' ].

  SCase "c = 0".
  intros n t d.
  rewrite -> p_rotated_moessner_entry_r_eq_0_implies_d.
  rewrite ->2 unfold_p_rotated_moessner_entry.
  rewrite -> plus_0_l.
  rewrite ->2 unfold_p_moessner_entry_induction_case_O.
  rewrite ->2 unfold_p_moessner_entry_base_case_O.
  rewrite -> plus_comm.
  symmetry.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  f_equal.
  rewrite ->2 unfold_p_monomial.
  rewrite -> power_b_1.
  rewrite -> Pascal_s_rule.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  rewrite -> mult_plus_distr_l.
  rewrite -> mult_plus_distr_r.
  rewrite -> mult_1_r.
  rewrite -> (mult_comm d t).
  reflexivity.

  SCase "c = S c'".
  intros n t d.
  rewrite -> p_rotated_moessner_entry_r_eq_0_implies_d.
  rewrite ->2 p_rotated_moessner_entry_Pascal_s_rule.
  rewrite ->2 p_rotated_moessner_entry_r_eq_0_implies_d.
  rewrite <- plus_permute.
  f_equal.
  rewrite -> (IH_c' n t d).
  rewrite -> p_rotated_moessner_entry_r_eq_0_implies_d.
  reflexivity.

  Case "r = S r'".
  induction c as [ | c' IH_c' ].

  SCase "c = 0".
  intros n t d.
  rewrite -> p_rotated_moessner_entry_c_eq_0.
  rewrite -> IH_r'.
  symmetry.
  rewrite -> p_rotated_moessner_entry_c_eq_0.
  rewrite -> mult_plus_distr_l.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  symmetry.
  rewrite <- plus_permute.
  f_equal.
  rewrite -> p_monomial_Pascal_s_rule.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  symmetry.
  rewrite ->2 p_rotated_moessner_entry_c_eq_0.
  reflexivity.

  SCase "c = S c'".
  intros n t d.
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  rewrite -> (IH_c' n t d).
  rewrite -> (IH_r' (S c') n t d).
  symmetry.
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  rewrite -> mult_plus_distr_l.
  rewrite <-3 plus_assoc.
  f_equal.
  symmetry.
  rewrite <-2 (plus_permute (t * p_rotated_moessner_entry n (S r') c' t d)).
  f_equal.
  symmetry.
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  rewrite <- plus_assoc.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_rank_decompose_by_row : long.

Corollary p_moessner_entry_rank_decompose_by_row :
  forall (r c n t d : nat),
   p_moessner_entry (S n) (c + S r) c t d =
   t * p_moessner_entry n (c + r) c t d +
   p_moessner_entry n (c + S r) c t d.
Proof.
  intros r c n t d.
  rewrite <-3 unfold_p_rotated_moessner_entry.
  exact (p_rotated_moessner_entry_rank_decompose_by_row r c n t d).
Qed.
Hint Rewrite p_moessner_entry_rank_decompose_by_row : long.

Corollary p_rotated_moessner_entry_rank_decompose_Pascal_like_c_eq_0 :
  forall (r n t d : nat),
    p_rotated_moessner_entry (S n) (S r) 0 t d =
    (S t) * p_rotated_moessner_entry n r 0 t d +
    p_monomial t n (S r) d.
Proof.
  intros r n t d.
  rewrite -> p_rotated_moessner_entry_rank_decompose_by_row.
  unfold mult; fold mult.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  f_equal.
  rewrite -> p_rotated_moessner_entry_c_eq_0.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_rank_decompose_Pascal_like_c_eq_0 : long.

Corollary p_moessner_entry_rank_decompose_Pascal_like_c_eq_0 :
  forall (r n t d : nat),
    p_moessner_entry (S n) (S r) 0 t d =
    S t * p_moessner_entry n r 0 t d +
    p_monomial t n (S r) d.
Proof.
  intros r n t d.
  rewrite <- (plus_0_l (S r)).
  rewrite <- unfold_p_rotated_moessner_entry.
  rewrite <- (plus_0_l r).
  rewrite <- unfold_p_rotated_moessner_entry.
  rewrite -> plus_0_l.
  exact (p_rotated_moessner_entry_rank_decompose_Pascal_like_c_eq_0 r n t d).
Qed.
Hint Rewrite p_moessner_entry_rank_decompose_Pascal_like_c_eq_0 : long.

Corollary p_rotated_moessner_entry_rank_decompose_Pascal_like_c_gt_0 :
  forall (r c n t d : nat),
  p_rotated_moessner_entry (S n) (S r) (S c) t d =
  (S t) * p_rotated_moessner_entry n r (S c) t d +
  p_rotated_moessner_entry n (S r) c t d.
Proof.
  intros r c n t d.
  rewrite -> p_rotated_moessner_entry_rank_decompose_by_row.
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  unfold mult; fold mult.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_rank_decompose_Pascal_like_c_gt_0
  : long.

Corollary p_moessner_entry_rank_decompose_Pascal_like_c_gt_0 :
  forall (r c n t d : nat),
   p_moessner_entry (S n) (S c + S r) (S c) t d =
   (S t) * p_moessner_entry n (S c + r) (S c) t  d+
   p_moessner_entry n (c + S r) c t d.
Proof.
  intros r c n t d.
  rewrite -> p_moessner_entry_rank_decompose_by_row.
  rewrite <- plus_n_Sm.
  rewrite -> p_moessner_entry_Pascal_s_rule.
  unfold mult; fold mult.
  rewrite <- plus_assoc.
  rewrite <- plus_permute.
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite p_moessner_entry_rank_decompose_Pascal_like_c_gt_0
  : long.

(* Decomposition by rank (create_triangle_vertically) *)

Corollary p_create_triangle_vertically_decompose_by_rank :
  forall (i j r t d : nat),
    j <= r ->
    S i <= r - j ->
    (nth (S i)
         (nth j
              (create_triangle_vertically
                 (tuple_constant (S (S (S r))) 0)
                 (Str_prefix (S (S (S r))) (p_monomials t (S r) 0 d)))
              [])
         0) =
    t * (nth i
             (nth j
                  (create_triangle_vertically
                     (tuple_constant (S (S r)) 0)
                     (Str_prefix (S (S r)) (p_monomials t r 0 d)))
                  [])
             0) +
    (nth (S i)
         (nth j
              (create_triangle_vertically
                 (tuple_constant (S (S r)) 0)
                 (Str_prefix (S (S r)) (p_monomials t r 0 d)))
              [])
         0).
Proof.
  intros i j r t d H_j_le_r H_S_i_le_r_minus_j.
  rewrite -> correctness_of_p_rotated_moessner_entry;
    [ idtac |
      apply le_S; apply le_S; exact H_j_le_r |
      rewrite <- minus_Sn_m;
        [ idtac | apply le_S; exact H_j_le_r ];
        apply le_n_S; rewrite <- minus_Sn_m; [ idtac | exact H_j_le_r ];
        apply le_S; exact H_S_i_le_r_minus_j ].

  rewrite -> correctness_of_p_rotated_moessner_entry;
    [ idtac |
      apply le_S; exact H_j_le_r |
      rewrite <- minus_Sn_m; [ idtac | exact H_j_le_r ];
      apply le_S; exact H_S_i_le_r_minus_j ].

  rewrite -> correctness_of_p_rotated_moessner_entry;
    [ idtac |
      apply le_S; exact H_j_le_r |
      rewrite <- minus_Sn_m; [ idtac | exact H_j_le_r ];
      apply le_n_S; exact H_S_i_le_r_minus_j ].

  exact (p_rotated_moessner_entry_rank_decompose_by_row i j r t d).
Qed.
Hint Rewrite p_create_triangle_vertically_decompose_by_rank : long.

Corollary p_create_triangle_vertically_rank_decompose_Pascal_like_c_eq_0 :
  forall (i r t d : nat),
    i < (S r) ->
    (nth (S i)
         (nth 0
              (create_triangle_vertically
                 (tuple_constant (S (S (S r))) 0)
                 (Str_prefix (S (S (S r))) (p_monomials t (S r) 0 d)))
              [])
         0) =
    (S t) * (nth i
                 (nth 0
                      (create_triangle_vertically
                         (tuple_constant (S (S r)) 0)
                         (Str_prefix (S (S r)) (p_monomials t r 0 d)))
                      [])
                   0) +
    p_monomial t r (S i) d.
Proof.
  intros i r t d H_i_lt_S_r.

  rewrite -> correctness_of_p_rotated_moessner_entry;
    [ idtac |
      exact (le_0_n (S (S r))) |
      unfold lt in H_i_lt_S_r; rewrite <- minus_n_O;
      apply le_n_S; exact H_i_lt_S_r ].

  rewrite -> correctness_of_p_rotated_moessner_entry;
    [ idtac |
      exact (le_0_n (S r)) |
      unfold lt in H_i_lt_S_r; rewrite <- minus_n_O;
      exact H_i_lt_S_r ].

  exact (p_rotated_moessner_entry_rank_decompose_Pascal_like_c_eq_0 i r t d).
Qed.
Hint Resolve p_create_triangle_vertically_rank_decompose_Pascal_like_c_eq_0
  : long.

Corollary p_create_triangle_vertically_rank_decompose_Pascal_like_c_gt_0 :
  forall (i j r t d : nat),
    j <= r ->
    S i <= r - j ->
    (nth (S i)
         (nth (S j)
              (create_triangle_vertically
                 (tuple_constant (S (S (S r))) 0)
                 (Str_prefix (S (S (S r))) (p_monomials t (S r) 0 d)))
              [])
         0) =

    (S t) * (nth i
                 (nth (S j)
                      (create_triangle_vertically
                         (tuple_constant (S (S r)) 0)
                         (Str_prefix (S (S r)) (p_monomials t r 0 d)))
                      [])
                   0) +
    (nth (S i)
         (nth j
              (create_triangle_vertically
                 (tuple_constant (S (S r)) 0)
                 (Str_prefix (S (S r)) (p_monomials t r 0 d)))
              [])
         0).
Proof.
  intros i j r t d H_j_le_r H_S_i_le_r_minus_j.

  rewrite -> correctness_of_p_rotated_moessner_entry;
    [ idtac |
      apply le_S; apply le_n_S; exact H_j_le_r |
      rewrite <- minus_Sn_m; [ idtac | apply le_n_S; exact H_j_le_r ];
      unfold minus; fold minus;
      apply le_n_S; exact H_S_i_le_r_minus_j ].

  rewrite -> correctness_of_p_rotated_moessner_entry;
    [ idtac |
      apply le_n_S; exact H_j_le_r |
      unfold minus; fold minus; exact H_S_i_le_r_minus_j ].

  rewrite -> correctness_of_p_rotated_moessner_entry;
    [ idtac |
      apply le_S; exact H_j_le_r |
      rewrite <- minus_Sn_m; [ idtac | exact H_j_le_r ];
      apply le_n_S; exact H_S_i_le_r_minus_j ].

  exact (p_rotated_moessner_entry_rank_decompose_Pascal_like_c_gt_0 i j r t d).
Qed.
Hint Rewrite p_create_triangle_vertically_rank_decompose_Pascal_like_c_gt_0
  : long.

(** * Equivalence of Characteristic function and P_Monomial *)

Lemma p_rotated_moessner_entry_constrained_negative_Pascal_s_rule :
  forall (n' k' t d : nat),
    S k' <= n' ->
    p_rotated_moessner_entry n' k' (n' - k') t d +
    p_rotated_moessner_entry n' (S k') (n' - S k') t d =
    p_rotated_moessner_entry n' (S k') (n' - k') t d.
Proof.
  induction n' as [ | n'' IH_n'' ].

  Case "n' = 0".
  intros k' t d H_absurd.
  inversion H_absurd.

  Case "n' = S n''".
  induction k' as [ | k'' IH_k'' ].

  SCase "k' = 0".
  intros t H d.
  unfold minus; fold minus.
  rewrite <- minus_n_O.
  rewrite -> p_rotated_moessner_entry_Pascal_s_rule.
  reflexivity.

  SCase "k' = S k''".
  intros t d H.
  rewrite <- (minus_Sn_m);
    [ idtac | apply gt_S_le; unfold gt, lt; exact H ].
  rewrite ->3 p_rotated_moessner_entry_Pascal_s_rule.
  unfold minus;fold minus.
  reflexivity.
Qed.

(* {P_ROTATED_MOESSNER_ENTRY_EQ_P_MONOMIAL} *)
Theorem p_rotated_moessner_entry_eq_p_monomial :
  forall (n k t d : nat),
    k <= n ->
    p_rotated_moessner_entry n k (n - k) t d =
    p_monomial (S t) n k d.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros k t d H.
  inversion_clear H.
  rewrite <- minus_n_O.
  rewrite -> p_rotated_moessner_entry_r_eq_0_implies_d.
  rewrite -> p_monomial_k_eq_0_implies_d.
  reflexivity.

  Case "n = S n'".
  induction k as [ | k' IH_k' ].

  SCase "k = 0".
  intros t d _.
  rewrite <- minus_n_O.
  rewrite -> p_rotated_moessner_entry_r_eq_0_implies_d.
  rewrite -> p_monomial_k_eq_0_implies_d.
  reflexivity.

  SCase "k = S k'".
  intros t d H_S_k'_le_S_n'.
  inversion_clear H_S_k'_le_S_n'.

  SSCase "k' = n'".
  rewrite -> minus_diag.
  rewrite -> p_rotated_moessner_entry_rank_decompose_by_row.
  specialize (IH_n' n' t d).
  rewrite -> minus_diag in IH_n'.
  rewrite -> IH_n'; [ idtac | apply le_n ].
  rewrite -> p_rotated_moessner_entry_c_eq_0.
  rewrite -> IH_n'; [ idtac | apply le_n ].
  rewrite -> p_monomial_Pascal_s_rule.
  unfold mult; fold mult.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  rewrite -> (p_monomial_n_lt_k_implies_0 t n' (S n') d);
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  rewrite -> (p_monomial_n_lt_k_implies_0 (S t) n' (S n') d);
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  reflexivity.

  SSCase "S k' <= n'".
  subst; rename H into H_S_k'_le_n'.
  rewrite <- minus_Sn_m;
    [ idtac | apply H_S_k'_le_n' ].
  rewrite -> p_rotated_moessner_entry_rank_decompose_by_row.
  rewrite -> p_monomial_Pascal_s_rule.
  rewrite <- (IH_n' (S k') t d);
    [ idtac | apply H_S_k'_le_n' ].
  rewrite -> minus_Sn_m;
    [ idtac | apply H_S_k'_le_n' ].
  rewrite -> NPeano.Nat.sub_succ.
  rewrite <- (IH_n' k' t d);
    [ idtac | apply lt_le_weak; unfold lt; exact H_S_k'_le_n' ].
  unfold mult; fold mult.
  symmetry.
  rewrite -> plus_comm.
  rewrite <- plus_assoc.

  rewrite <- (plus_permute
                (t * p_rotated_moessner_entry n' k' (n' - k') t d) _).
  f_equal.

  rewrite -> p_rotated_moessner_entry_constrained_negative_Pascal_s_rule;
    [ idtac | apply H_S_k'_le_n' ].
  reflexivity.
Qed.
Hint Rewrite p_rotated_moessner_entry_eq_p_monomial : long.

(* {P_MOESSNER_ENTRY_EQ_P_MONOMIAL} *)
Corollary p_moessner_entry_eq_p_monomial :
  forall (n k t d : nat),
    k <= n ->
    p_moessner_entry n n (n - k) t d =
    p_monomial (S t) n k d.
(* {END} *)
Proof.
  intros n k t d H.
  assert (H_helper:
            p_moessner_entry n n (n - k) t d =
            p_moessner_entry n (n - k + k) (n - k) t d).
    rewrite -> (NPeano.Nat.sub_add k n H).
    reflexivity.

  rewrite -> H_helper; clear H_helper.
  rewrite <- unfold_p_rotated_moessner_entry.
  rewrite -> (p_rotated_moessner_entry_eq_p_monomial n k t d H).
  reflexivity.
Qed.
Hint Rewrite p_moessner_entry_eq_p_monomial : long.

(** ** The p_Binomial Theorem *)

Theorem p_Binomial_theorem :
  forall (t n d : nat),
    d * (S t) ^ n = Str_nth (S n) (stream_partial_sums (p_monomials t n 0 d)).
Proof.
  intros t n d.
  rewrite -> stream_partial_sums_p_monomials_bisim_p_monomials_sum.
  rewrite -> Str_nth_p_monomials_sum_eq_p_rotated_moessner_entry;
    rewrite -> plus_0_r.
  rewrite -> p_rotated_moessner_entry_c_eq_0.
  rewrite -> p_monomial_n_lt_k_implies_0;
    [ rewrite -> plus_0_l | unfold lt; apply le_n ].
  rewrite <- (minus_diag n);
    rewrite -> p_rotated_moessner_entry_eq_p_monomial;
    [ idtac | apply le_n ].
  rewrite -> p_monomial_n_eq_k_implies_power.
  reflexivity.
Qed.
Hint Rewrite p_Binomial_theorem : long.

(** * Describing the diagonal of a triangle *)

(** Proof that [read_diagonal] of [create_triangle] starting from
  [p_monomials] yields a row [p_moessner_entry] *)

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY_P_ROTATED_MOESSNER_ENTRIES} *)
Theorem hypotenuse_create_triangle_vertically_p_rotated_moessner_entries :
  forall (l r c t d : nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S l) 0)
         (Str_prefix (S l) (p_rotated_moessner_entries r 0 c t d))) =
    Str_prefix l (p_moessner_entries r (c + l) (S c) t d).
(* {END} *)
Proof.
  induction l as [ | l' IH_l' ].

  Case "l = 0".
  intros r c t d.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_hypotenuse_base_case.
  reflexivity.

  Case "l = S l'".
  intros r c t d.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite <-2 unfold_Str_prefix_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite -> unfold_hypotenuse_induction_case.

  symmetry.

  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> p_moessner_entries_initial_value.
  rewrite -> p_moessner_entries_stream_derivative.
  rewrite -> make_tuple_p_rotated_moessner_entries.
  f_equal.

  SCase "head".
  rewrite -> last_of_p_rotated_moessner_entries_to_binomial.
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.

  SCase "tail".
  rewrite -> (IH_l' r (S c) t d).
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically_p_rotated_moessner_entries
  : long.

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY_MOESSNER_ENTRIES_P_MONOMIALS} *)
Lemma hypotenuse_create_triangle_vertically_moessner_entries_p_monomials :
  forall (l r t d : nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S (S l)) 0)
         (Str_prefix (S (S l)) (p_monomials t r 0 d))) =
    (Str_prefix (S l) (p_moessner_entries r l 0 t d)).
(* {END} *)
Proof.
  intros l r t d.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite <-2 unfold_Str_prefix_induction_case.
  rewrite -> p_monomials_and_make_tuple.
  rewrite <- p_rotated_moessner_entries_bisim_p_monomials_sum.
  rewrite -> unfold_hypotenuse_induction_case.
  symmetry.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> p_moessner_entries_initial_value.
  rewrite -> p_moessner_entries_stream_derivative.
  f_equal.

  Case "head".
  rewrite -> (length_implies_last_index l);
    [ idtac | rewrite -> Str_prefix_length; reflexivity ].
  rewrite -> nth_and_Str_nth;
    [ idtac | unfold lt; apply le_n ].
  rewrite -> Str_nth_p_rotated_moessner_entries.
  rewrite -> plus_0_l.
  reflexivity.

  Case "tail".
  symmetry.
  rewrite -> hypotenuse_create_triangle_vertically_p_rotated_moessner_entries.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically_moessner_entries_p_monomials
  : long.

(** P_Monomials List

  The list of p_monomials of the binomial expansion.

  *** Definition *)

(* {P_MONOMIALS_LIST} *)
Fixpoint p_monomials_list (t r n d : nat) : list nat :=
  match n with
    | 0 => [p_monomial t r 0 d]
    | S n' => (p_monomial t r (S n') d) :: (p_monomials_list t r n' d)
  end.
(* {END} *)
Hint Unfold p_monomials_list : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_monomials_list_base_case :
  forall (t r d : nat),
    p_monomials_list t r 0 d = [p_monomial t r 0 d].
Proof.
  intros t r d.
  unfold p_monomials_list.
  reflexivity.
Qed.
Hint Rewrite unfold_p_monomials_list_base_case : long.

Lemma unfold_p_monomials_list_induction_case :
  forall (t r n' d : nat),
    p_monomials_list t r (S n') d =
    (p_monomial t r (S n') d) :: (p_monomials_list t r n' d).
Proof.
  intros t r n' d.
  unfold p_monomials_list; fold p_monomials_list.
  reflexivity.
Qed.
Hint Rewrite unfold_p_monomials_list_induction_case : long.

(** *** Properties *)

Lemma rev_p_monomials_list_eq_p_monomials :
  forall (n r t d : nat),
    p_monomials_list t r n d =
    rev (Str_prefix (S n) (p_monomials t r 0 d)).
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r t d.
  rewrite -> unfold_p_monomials_list_base_case.

  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> p_monomials_initial_value.
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> app_nil_l.
  reflexivity.

  Case "n = S n'".
  intros r t d.
  rewrite -> unfold_p_monomials_list_induction_case.
  rewrite -> (IH_n' r t d).
  symmetry.

  rewrite -> rev_Str_prefix_p_monomials.
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite rev_p_monomials_list_eq_p_monomials : long.

Lemma p_monomials_list_eq_Str_prefix_p_moessner_entries :
  forall (l n t' d : nat),
    l <= n ->
    Str_prefix (S l) (p_moessner_entries n n (n - l) t' d) =
    p_monomials_list (S t') n l d.
Proof.
  induction l as [ | l' IH_l' ].

  Case "l = 0".
  intros n t' d H_0_le_n.
  rewrite <- minus_n_O.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> p_moessner_entries_initial_value.
  rewrite -> p_moessner_entry_n_eq_k_implies_d.

  rewrite -> unfold_p_monomials_list_base_case.
  rewrite -> unfold_p_monomial.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  rewrite -> unfold_power_base_case.
  rewrite ->2 mult_1_r.
  reflexivity.

  Case "l = S l'".
  intros n t' d H_S_l'_le_n.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> p_moessner_entries_stream_derivative.
  rewrite -> minus_Sn_m;
    [ idtac | apply H_S_l'_le_n ].
  rewrite -> NPeano.Nat.sub_succ.
  rewrite -> IH_l';
    [ idtac | apply lt_le_weak; unfold lt; exact H_S_l'_le_n ].
  rewrite -> p_moessner_entries_initial_value.
  rewrite -> unfold_p_monomials_list_induction_case.
  f_equal.
  rewrite -> p_moessner_entry_eq_p_monomial;
    [ reflexivity | exact H_S_l'_le_n ].
Qed.
Hint Rewrite p_monomials_list_eq_Str_prefix_p_moessner_entries : long.

Lemma rev_Str_prefix_p_moessner_entries_eq_p_monomials :
  forall (r t' d : nat),
    Str_prefix (S r) (p_moessner_entries r r 0 t' d) =
    rev (Str_prefix (S r) (p_monomials (S t') r 0 d)).
Proof.
  intros r t' d.
  rewrite <- (minus_diag r).
  rewrite -> p_monomials_list_eq_Str_prefix_p_moessner_entries;
    [ idtac | apply le_n ].
  rewrite -> rev_p_monomials_list_eq_p_monomials.
  rewrite -> minus_diag.
  reflexivity.
Qed.
Hint Rewrite rev_Str_prefix_p_moessner_entries_eq_p_monomials : long.

Lemma pad_p_monomials :
  forall (r t n d : nat),
    Str_prefix (S (S r)) (p_monomials (S t) r n d) =
    Str_prefix (S r) (p_monomials (S t) r n d) ++ [0].
Proof.
  intros r t n d.
  rewrite -> Str_prefix_split_with_Str_nth.
  unfold Str_nth.
  rewrite -> p_monomials_tail_of_0s.
  rewrite -> stream_constant_initial_value.
  reflexivity.
Qed.
Hint Rewrite pad_p_monomials : long.

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY_P_MONOMIALS} *)
Corollary hypotenuse_create_triangle_vertically_p_monomials :
  forall (r t d : nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (p_monomials t r 0 d))) =
    (rev (Str_prefix (S r) (p_monomials (S t) r 0 d))).
(* {END} *)
Proof.
  intros r t d.
  rewrite -> hypotenuse_create_triangle_vertically_moessner_entries_p_monomials.
  rewrite -> rev_Str_prefix_p_moessner_entries_eq_p_monomials.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically_p_monomials : long.

(** * P Long's weak theorem *)

(* {NTH_TRIANGLE_CREATE_TRIANGLES_VERTICALLY_P_MONOMIALS} *)
Theorem nth_triangle_create_triangles_vertically_p_monomials :
  forall (n r t d : nat),
    nth n
      (create_triangles_vertically n
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S (S r)) (p_monomials t r 0 d)))
      [] =
    (create_triangle_vertically
       (tuple_constant (S (S r)) 0)
       (Str_prefix (S (S r)) (p_monomials (n + t) r 0 d))).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r t d.
  rewrite -> unfold_create_triangles_vertically_base_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> plus_0_l.
  reflexivity.

  Case "n = S n'".
  intros r t d.
  rewrite -> unfold_create_triangles_vertically_induction_case.
  rewrite -> hypotenuse_create_triangle_vertically_p_monomials.
  rewrite -> unfold_rev_induction_case.
  rewrite -> rev_involutive.
  rewrite <- pad_p_monomials.
  rewrite -> unfold_nth_induction_case_cons.
  rewrite -> (IH_n' r (S t)).
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite nth_triangle_create_triangles_vertically_p_monomials : long.

Corollary hypotenuse_of_last_triangle_create_triangles_vertically_p_monomials :
  forall (n r t d : nat),
    hypotenuse
      (nth n
           (create_triangles_vertically
              n
              (tuple_constant (S (S r)) 0)
              (Str_prefix (S (S r)) (p_monomials t r 0 d)))
           []) =
    p_monomials_list (S (n + t)) r r d.
Proof.
  intros n r t d.
  rewrite -> nth_triangle_create_triangles_vertically_p_monomials.
  rewrite -> hypotenuse_create_triangle_vertically_p_monomials.
  rewrite <- rev_p_monomials_list_eq_p_monomials.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_of_last_triangle_create_triangles_vertically_p_monomials
  : long.

Corollary bottom_element_of_nth_triangle_create_triangles_vertically_p_monomials :
  forall (n r t d : nat),
    nth 0
        (hypotenuse
           (nth n
                (create_triangles_vertically
                   n
                   (tuple_constant (S (S r)) 0)
                   (Str_prefix (S (S r)) (p_monomials t r 0 d)))
                []))
        1 = p_monomial (S (n + t)) r r d.
Proof.
  intros n r t d.
  rewrite -> hypotenuse_of_last_triangle_create_triangles_vertically_p_monomials.
  case r as [ | r' ].

  Case "r = 0".
  rewrite -> unfold_p_monomials_list_base_case.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.

  Case "r = S r'".
  rewrite -> unfold_p_monomials_list_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.
Qed.
Hint Rewrite bottom_element_of_nth_triangle_create_triangles_vertically_p_monomials
  : long.

(* {BOTTOM_ELEMENT_OF_NTH_TRIANGLE_P_MONOMIALS_IS_POWER} *)
Corollary bottom_element_of_nth_triangle_p_monomials_is_power :
  forall (n r d : nat),
    nth 0
        (hypotenuse
           (nth n
                (create_triangles_vertically
                   n
                   (tuple_constant (S (S r)) 0)
                   (Str_prefix (S (S r)) (p_monomials 0 r 0 d)))
                []))
        1 = d * (S n) ^ r.
(* {END} *)
Proof.
  intros n r d.
  rewrite -> bottom_element_of_nth_triangle_create_triangles_vertically_p_monomials.
  rewrite -> p_monomial_n_eq_k_implies_power.
  rewrite -> plus_0_r.
  reflexivity.
Qed.
Hint Rewrite bottom_element_of_nth_triangle_p_monomials_is_power : long.

(** ** Moessner Stream

  *** Definition *)

(* {P_MOESSNER_STREAM} *)
CoFixpoint p_moessner_stream (n r d : nat) : Stream nat :=
  (nth 0 (hypotenuse
            (nth n
                 (create_triangles_vertically
                    n
                    (tuple_constant (S (S r)) 0)
                    (Str_prefix (S (S r)) (p_monomials 0 r 0 d)))
                 [])) 1)
    ::: (p_moessner_stream (S n) r d).
(* {END} *)
Hint Unfold p_moessner_stream : long.

(** *** Unfolding lemmas *)

Lemma unfold_p_moessner_stream :
  forall (n r d : nat),
    (p_moessner_stream n r d) =
    (nth 0 (hypotenuse
              (nth n
                   (create_triangles_vertically
                      n
                      (tuple_constant (S (S r)) 0)
                      (Str_prefix (S (S r)) (p_monomials 0 r 0 d)))
                   [])) 1)
      ::: (p_moessner_stream (S n) r d).
Proof.
  intros n r d.
  rewrite -> (unfold_Stream (p_moessner_stream n r d)).
  unfold p_moessner_stream; fold p_moessner_stream.
  reflexivity.
Qed.
Hint Rewrite unfold_p_moessner_stream : long.

Lemma p_moessner_stream_initial_value :
  forall (n r d : nat),
    (p_moessner_stream n r d)(0) =
    (nth 0 (hypotenuse
              (nth n
                   (create_triangles_vertically
                      n
                      (tuple_constant (S (S r)) 0)
                      (Str_prefix (S (S r)) (p_monomials 0 r 0 d)))
                   [])) 1).
Proof.
  intros n r d.
  rewrite -> initial_value.
  rewrite -> unfold_p_moessner_stream.
  reflexivity.
Qed.
Hint Rewrite p_moessner_stream_initial_value : long.

Lemma p_moessner_stream_stream_derivative :
  forall (n r d : nat),
    (p_moessner_stream n r d)` = (p_moessner_stream (S n) r d).
Proof.
  intros n r d.
  rewrite -> stream_derivative.
  rewrite -> unfold_p_moessner_stream.
  reflexivity.
Qed.
Hint Rewrite p_moessner_stream_stream_derivative : long.

(** ** Long's weak theorem *)

(* {LONG_S_WEAK_THEOREM} *)
Theorem Long_s_weak_theorem :
  forall (b e d : nat),
    p_moessner_stream b e d ~ d n* successive_powers b e.
(* {END} *)
Proof.
  pcofix coIH.
  intros b e d.
  bisimilar.

  Case "initial value".
  rewrite -> p_moessner_stream_initial_value.
  rewrite -> bottom_element_of_nth_triangle_p_monomials_is_power.
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite -> successive_powers_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> p_moessner_stream_stream_derivative.
  rewrite -> stream_scalar_multiplication_stream_derivative.
  rewrite -> successive_powers_stream_derivative.
  exact (coIH (S b) e d).
Qed.
Hint Rewrite Long_s_weak_theorem : long.

(** * Long's idealized theorem *)

(* If we look at how we can decompose a Long-like sieve,

     d     d      d       d      d     d        d       d       d      d     d     d
 c c+d  c+2d   c+3d    c+4d   c+5d           c+6d    c+7d    c+8d   c+9d c+10d
 0 c+d 2c+3d  3c+6d  4c+10d                5c+16d  6c+23d  7c+31d 8c+40d
 0 c+d 3c+4d 6c+10d                       11c+26d 17c+49d 24c+80d
 0 c+d 4c+5d                              15c+31d 32c+80d
 0 c+d                                    16c+32d
 0

  into a sum of two sieves, where we also generalize the stream of [d]s to be a
  [d] followed by 0s

      0   0   0   0   0   0        0   0   0   0   0   0

  c   c   c   c   c   c            c   c   c   c   c
  0   c  2c  3c  4c               5c  6c  7c  8c
  0   c  3c  6c                  11c 17c 24c
  0   c  4c                      15c 32c
  0   c                          16c
  0

  +

      d   0   0   0   0   0   0        0   0   0   0   0   0   0

  0   d   d   d   d   d   d            d   d   d   d   d   d
  0   d  2d  3d  4d  5d               6d  7d  8d  9d 10d
  0   d  3d  6d 10d                  16d 23d 31d 40d
  0   d  4d 10d                      26d 49d 80d
  0   d  5d                          31d 80d
  0   d                              32d
  0

  then we can use the symmetric property to flip the two seed tuples for the [d]
  sieve which gives us

      0   0   0   0   0   0        0   0   0   0   0   0

  c   c   c   c   c   c            c   c   c   c   c
  0   c  2c  3c  4c               5c  6c  7c  8c
  0   c  3c  6c                  11c 17c 24c
  0   c  4c                      15c 32c
  0   c                          16c
  0

  +

      0   0   0   0   0   0   0        0   0   0   0   0   0   0

  d   d   d   d   d   d   d            d   d   d   d   d   d
  0   d  2d  3d  4d  5d               6d  7d  8d  9d 10d
  0   d  3d  6d 10d                  16d 23d 31d 40d
  0   d  4d 10d                      26d 49d 80d
  0   d  5d                          31d 80d
  0   d                              32d
  0

  which we can then recompose into a Long-like sieve, if we want:

     0     0      0       0      0     0     0             0       0       0      0     0     0      0
 d   d     d      d       d      d     d           d       d       d       d      d     d     d
 c c+d  c+2d   c+3d    c+4d   c+5d             c+ 5d    c+6d    c+7d    c+8d   c+9d c+10d
 0 c+d 2c+3d  3c+6d  4c+10d                   4c+10d  5c+16d  6c+23d  7c+31d 8c+40d
 0 c+d 3c+4d 6c+10d                           6c+10d 11c+26d 17c+49d 24c+80d
 0 c+d 4c+5d                                  4c+ 5d 15c+31d 32c+80d
 0 c+d                                         c+  d 16c+32d
 0                                                 0

*)

(** ** Distributivity of sum in seed tuples for Moessner triangles *)

(** *** Helper lemmas *)

(* {LENGTH_OF_LIST_SUM} *)
Lemma length_of_list_sum :
  forall (xs ys : list nat),
    length (xs l+ ys) = max (length xs) (length ys).
(* {END} *)
Proof.
  induction xs as [ | x xs' IH_xs' ].

  Case "xs = []".
  case ys as [ | y ys' ].

  SCase "ys = []".
  rewrite -> unfold_list_sum_base_case_nil.
  rewrite -> unfold_length_base_case.
  unfold max.
  reflexivity.

  SCase "ys = y :: ys'".
  rewrite -> unfold_list_sum_base_case_cons.
  rewrite -> unfold_length_base_case.
  unfold max.
  reflexivity.

  Case "xs = x :: xs'".
  case ys as [ | y ys' ].

  SCase "ys = []".
  rewrite -> unfold_list_sum_induction_case_nil.
  rewrite -> unfold_length_base_case.
  rewrite -> Max.max_0_r.
  reflexivity.

  SCase "ys = y :: ys'".
  rewrite -> unfold_list_sum_induction_case_cons.
  rewrite -> unfold_length_induction_case.
  rewrite -> (IH_xs' ys').
  rewrite ->2 unfold_length_induction_case.
  unfold max; fold max.
  reflexivity.
Qed.
Hint Rewrite length_of_list_sum : long.

(* {NTH_MAKE_TUPLE_LIST_SUM} *)
Lemma nth_make_tuple_list_sum :
  forall (n r i j : nat) (sigma tau : Stream nat),
    nth n (make_tuple (Str_prefix r sigma) i) 0 +
    nth n (make_tuple (Str_prefix r tau) j) 0 =
    nth n ((make_tuple (Str_prefix r sigma) i) l+
           (make_tuple (Str_prefix r tau) j)) 0.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  case r as [ | r' ].

  SCase "r = 0".
  intros i j sigma tau.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite ->2 unfold_make_tuple_base_case_nil.
  rewrite -> unfold_list_sum_base_case_nil.
  rewrite -> unfold_nth_base_case_nil.
  rewrite -> plus_0_r.
  reflexivity.

  SCase "r = S r'".
  case r' as [ | r'' ].

  SSCase "r' = 0".
  intros i j sigma tau.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite ->2 unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_list_sum_base_case_nil.
  rewrite -> unfold_nth_base_case_nil.
  rewrite -> plus_0_r.
  reflexivity.

  SSCase "r' = S r''".
  intros i j sigma tau.
  rewrite ->4 unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_make_tuple_induction_case.
  rewrite ->2 unfold_nth_base_case_cons.
  rewrite -> unfold_list_sum_induction_case_cons.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.

  Case "n = S n'".
  case r as [ | r' ].

  SCase "r = 0".
  intros i j sigma tau.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite ->2 unfold_make_tuple_base_case_nil.
  rewrite -> unfold_list_sum_base_case_nil.
  rewrite -> unfold_nth_induction_case_nil.
  rewrite -> plus_0_r.
  reflexivity.

  SCase "r = S r'".
  case r' as [ | r'' ].

  SSCase "r' = 0".
  intros i j sigma tau.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite ->2 unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_list_sum_base_case_nil.
  rewrite -> unfold_nth_induction_case_nil.
  rewrite -> plus_0_r.
  reflexivity.

  SSCase "r' = S r''".
  intros i j sigma tau.
  rewrite ->4 unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_make_tuple_induction_case.
  rewrite ->2 unfold_nth_induction_case_cons.
  rewrite <-2 unfold_Str_prefix_induction_case.
  rewrite -> (IH_n' (S r'') (sigma(0) + i) (tau(0) + j)).
  rewrite -> unfold_list_sum_induction_case_cons.
  rewrite -> unfold_nth_induction_case_cons.
  reflexivity.
Qed.
Hint Rewrite nth_make_tuple_list_sum : long.

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY_LIST_SUM} *)
Theorem hypotenuse_create_triangle_vertically_list_sum :
  forall (r : nat) (sigma tau : Stream nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant r 0)
         ((Str_prefix r sigma) l+
          (Str_prefix r tau))) =
    (hypotenuse
       (create_triangle_vertically
          (tuple_constant r 0)
          (Str_prefix r sigma))) l+
    (hypotenuse
       (create_triangle_vertically
          (tuple_constant r 0)
          (Str_prefix r tau))).
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  intros sigma tau.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_list_sum_base_case_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_nil.
  rewrite -> unfold_hypotenuse_base_case.
  rewrite -> unfold_list_sum_base_case_nil.
  reflexivity.

  Case "r = S r'".
  case r' as [ | r'' ].

  SCase "r' = 0".
  intros sigma tau.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_list_sum_induction_case_cons.
  rewrite -> unfold_list_sum_base_case_nil.
  rewrite ->3 unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_hypotenuse_base_case.
  rewrite -> unfold_list_sum_base_case_nil.
  reflexivity.

  SCase "r' = S r'".
  intros sigma tau.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_hypotenuse_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite -> unfold_list_sum.
  rewrite <- Str_prefix_stream_zip.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  rewrite -> stream_partial_sums_acc_sum.
  unfold stream_sum.
  rewrite -> Str_prefix_stream_zip.
  rewrite <- unfold_list_sum.
  rewrite -> (IH_r' (stream_partial_sums_acc 0 sigma) (stream_partial_sums_acc 0 tau)).
  symmetry.

  rewrite -> unfold_tuple_constant_induction_case.
  rewrite ->2 unfold_create_triangle_vertically_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite ->2 unfold_hypotenuse_induction_case.
  rewrite -> unfold_list_sum_induction_case_cons.
  rewrite <-2 equivalence_of_make_tuple_and_stream_partial_sums_acc.
  f_equal.

  (*
  (* {LAST_MAKE_TUPLE_EXAMPLE} *)
    last (make_tuple (Str_prefix (S (S r'')) sigma) 0) 0 +
    last (make_tuple (Str_prefix (S (S r'')) tau) 0) 0 =
    last ((make_tuple (Str_prefix (S (S r'')) sigma) 0) l+
          (make_tuple (Str_prefix (S (S r'')) tau) 0)) 0
  (* {END} *)
  *)

  rewrite -> (length_implies_last_index r'');
    [ idtac | rewrite ->2 unfold_Str_prefix_induction_case;
              rewrite -> unfold_make_tuple_induction_case;
              rewrite -> unfold_length_induction_case;
              rewrite -> S_length_make_tuple;
              rewrite <- unfold_Str_prefix_induction_case;
              rewrite -> Str_prefix_length;
              reflexivity ].

  rewrite -> (length_implies_last_index r'');
    [ idtac | rewrite ->2 unfold_Str_prefix_induction_case;
              rewrite -> unfold_make_tuple_induction_case;
              rewrite -> unfold_length_induction_case;
              rewrite -> S_length_make_tuple;
              rewrite <- unfold_Str_prefix_induction_case;
              rewrite -> Str_prefix_length;
              reflexivity ].

  rewrite -> nth_make_tuple_list_sum.
  rewrite -> (length_implies_last_index r'');
    [ idtac | rewrite -> length_of_list_sum;
              rewrite ->4 unfold_Str_prefix_induction_case;
              rewrite ->2 unfold_make_tuple_induction_case;
              rewrite ->2 unfold_length_induction_case;
              rewrite ->2 S_length_make_tuple;
              rewrite ->2 unfold_length_induction_case;
              rewrite ->2 Str_prefix_length;
              rewrite -> Max.max_idempotent;
              reflexivity ].

  reflexivity.
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically_list_sum : long.

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY_P_MONOMIALS_LIST_SUM} *)
Corollary hypotenuse_create_triangle_vertically_p_monomials_list_sum :
  forall (r t d c : nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S (S (S r))) 0)
         ((Str_prefix (S (S (S r))) (0 ::: (p_monomials t r 0 c))) l+
          (Str_prefix (S (S (S r))) (p_monomials t (S r) 0 d)))) =
    (hypotenuse
       (create_triangle_vertically
          (tuple_constant (S (S (S r))) 0)
          (Str_prefix (S (S (S r))) (0 ::: (p_monomials t r 0 c))))) l+
    (hypotenuse
       (create_triangle_vertically
          (tuple_constant (S (S (S r))) 0)
          (Str_prefix (S (S (S r))) (p_monomials t (S r) 0 d)))).
(* {END} *)
Proof.
  intros r t d c.
  exact (hypotenuse_create_triangle_vertically_list_sum
           (S (S (S r)))
           (0 ::: p_monomials t r 0 c)
           (p_monomials t (S r) 0 d)).
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically_p_monomials_list_sum
  : long.

(** ** Distributivity of list sum for the [n]th Moessner triangle *)

(* {HYPOTENUSE_CREATE_TRIANGLE_VERTICALLY_REMOVE_PADDING} *)
Lemma hypotenuse_create_triangle_vertically_remove_padding :
  forall (r : nat) (sigma : Stream nat),
    hypotenuse (create_triangle_vertically
                  (tuple_constant (S r) 0)
                  (Str_prefix (S r) (0 ::: sigma))) =
    hypotenuse (create_triangle_vertically
                  (tuple_constant (S r) 0)
                  (Str_prefix r sigma)).
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  intro sigma.
  rewrite -> unfold_tuple_constant_induction_case.
  rewrite -> unfold_tuple_constant_base_case.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> initial_value.
  rewrite ->2 unfold_create_triangle_vertically_base_case_x_nil.
  reflexivity.

  Case "r = S r'".
  intro sigma.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite ->2 unfold_create_triangle_vertically_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite ->2 unfold_hypotenuse_induction_case.
  f_equal.

  SCase "hd".
  induction r' as [ | r'' IH_r'' ].

  SSCase "r' = 0".
  rewrite ->3 unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> initial_value.
  rewrite -> stream_derivative.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite ->2 unfold_make_tuple_base_case_x_nil.
  rewrite -> plus_0_r.
  rewrite -> unfold_last_base_case_cons.
  rewrite -> unfold_last_base_case_nil.
  reflexivity.

  SSCase "r' = S r''".
  rewrite ->5 unfold_Str_prefix_induction_case.
  rewrite ->3 unfold_make_tuple_induction_case.
  rewrite -> unfold_last_induction_case.
  rewrite ->2 plus_0_r.
  rewrite -> stream_derivative.
  reflexivity.

  SCase "tl".
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.

  replace (stream_partial_sums_acc 0 (0 ::: sigma))
  with (0 ::: (stream_partial_sums_acc 0 sigma));
    [ idtac | symmetry;
              rewrite -> unfold_stream_partial_sums_acc;
              rewrite -> initial_value;
              rewrite -> plus_0_r;
              rewrite -> stream_derivative;
              reflexivity ].

  rewrite -> (IH_r' (stream_partial_sums_acc 0 sigma)).
  rewrite <- equivalence_of_make_tuple_and_stream_partial_sums_acc.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_create_triangle_vertically_remove_padding : long.

(* {CREATE_TRIANGLE_VERTICALLY_HORIZONTAL_SEED_TUPLE_PADDING} *)
Lemma create_triangle_vertically_horizontal_seed_tuple_padding :
  forall (r : nat) (sigma : Stream nat),
    hypotenuse
      (create_triangle_vertically
         (tuple_constant (S (S r)) 0)
         (Str_prefix (S r) sigma)) =
    (hypotenuse
       (create_triangle_vertically
          (tuple_constant (S r) 0)
          (Str_prefix (S r) sigma))) ++ [0].
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  intro sigma.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_create_triangle_vertically_base_case_x_nil.
  rewrite -> unfold_hypotenuse_base_case.
  rewrite -> unfold_hypotenuse_induction_case.
  rewrite -> unfold_hypotenuse_base_case.
  rewrite -> app_nil_l.
  rewrite -> unfold_last_base_case_nil.
  reflexivity.

  Case "r = S r'".
  intro sigma.
  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite -> unfold_hypotenuse_induction_case.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  rewrite -> (IH_r' (stream_partial_sums_acc 0 sigma)).
  rewrite <- equivalence_of_make_tuple_and_stream_partial_sums_acc.
  symmetry.

  rewrite ->2 unfold_tuple_constant_induction_case.
  rewrite -> unfold_create_triangle_vertically_induction_case.
  rewrite <- unfold_tuple_constant_induction_case.
  rewrite -> unfold_hypotenuse_induction_case.
  rewrite -> app_comm_cons.
  reflexivity.
Qed.
Hint Rewrite create_triangle_vertically_horizontal_seed_tuple_padding : long.

(* {LIST_ZIP_APPEND} *)
Lemma list_zip_append :
  forall (vs xs ws ys : list nat) (f : nat -> nat -> nat),
    length vs = length xs ->
    length ws = length ys ->
    list_zip f (vs ++ ws) (xs ++ ys) =
    (list_zip f vs xs) ++ (list_zip f ws ys).
(* {END} *)
Proof.
  induction vs as [ | v vs' IH_vs' ].

  Case "vs = []".
  case xs as [ | x xs' ].

  SCase "xs = []".
  intros ws ys f H_length_vs_xs H_length_ws_ys.
  rewrite ->2 app_nil_l.
  rewrite -> unfold_list_zip_base_case_nil.
  rewrite -> app_nil_l.
  reflexivity.

  SCase "xs = x :: xs'".
  intros ws ys f H_length_vs_xs H_length_ws_ys.
  inversion H_length_vs_xs.

  Case "vs = v :: vs'".
  case xs as [ | x xs' ].

  SCase "xs = []".
  intros ws ys f H_length_vs_xs H_length_ws_ys.
  inversion H_length_vs_xs.

  SCase "xs = x :: xs'".
  intros ws ys f H_length_vs_xs H_length_ws_ys.
  rewrite -> unfold_list_zip_induction_case_cons.
  rewrite <-3 app_comm_cons.
  rewrite -> unfold_list_zip_induction_case_cons.
  f_equal.
  rewrite -> IH_vs';
    [ idtac |
      apply eq_add_S; exact H_length_vs_xs |
      exact H_length_ws_ys ].
  reflexivity.
Qed.
Hint Resolve list_zip_append : long.

(* {REV_LIST_ZIP} *)
Lemma rev_list_zip :
  forall (xs ys : list nat) (f : nat -> nat -> nat),
    length xs = length ys ->
    rev (list_zip f xs ys) =
    (list_zip f (rev xs) (rev ys)).
(* {END} *)
Proof.
  induction xs as [ | x xs' IH_xs' ].

  Case "xs = []".
  case ys as [ | y ys' ].

  SCase "ys = []".
  intros f H_length_xs_ys.
  rewrite ->2 unfold_rev_base_case.
  rewrite -> unfold_list_zip_base_case_nil.
  reflexivity.

  SCase "ys = y :: ys'".
  intros f H_length_xs_ys.
  inversion H_length_xs_ys.

  Case "xs = x :: xs'".
  case ys as [ | y ys' ].

  SCase "ys = []".
  intros f H_length_xs_ys.
  inversion H_length_xs_ys.

  SCase "ys = y :: ys'".
  intros f H_length_xs_ys.
  rewrite -> unfold_list_zip_induction_case_cons.
  rewrite ->3 unfold_rev_induction_case.
  rewrite -> IH_xs';
    [ idtac | apply eq_add_S;
              exact H_length_xs_ys ].
  rewrite -> list_zip_append;
    [ idtac | rewrite ->2 rev_length;
              apply eq_add_S;
              exact H_length_xs_ys | rewrite ->2 unfold_length_induction_case;
                                     rewrite -> unfold_length_base_case;
                                     reflexivity ].
  rewrite -> unfold_list_zip_induction_case_cons.
  rewrite -> unfold_list_zip_base_case_nil.
  reflexivity.
Qed.
Hint Resolve rev_list_zip : long.

(* {NTH_TRIANGLE_CREATE_TRIANGLES_VERTICALLY_P_MONOMIALS_LIST_SUM} *)
Theorem nth_triangle_create_triangles_vertically_p_monomials_list_sum :
  forall (n r t d c : nat),
    nth n
      (create_triangles_vertically n
         (tuple_constant (S (S (S r))) 0)
         ((Str_prefix (S (S (S r))) (0 ::: (p_monomials t r 0 c))) l+
          (Str_prefix (S (S (S r))) (p_monomials t (S r) 0 d)))) [] =
    (create_triangle_vertically
       (tuple_constant (S (S (S r))) 0)
       ((Str_prefix (S (S (S r))) (0 ::: (p_monomials (n + t) r 0 c))) l+
        (Str_prefix (S (S (S r))) (p_monomials (n + t) (S r) 0 d)))).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros r t d c.
  rewrite -> unfold_create_triangles_vertically_base_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> plus_0_l.
  reflexivity.

  Case "n = S n'".
  intros r t d c.
  rewrite -> unfold_create_triangles_vertically_induction_case.
  rewrite -> unfold_nth_induction_case_cons.
  rewrite -> hypotenuse_create_triangle_vertically_p_monomials_list_sum.
  rewrite -> hypotenuse_create_triangle_vertically_p_monomials.
  rewrite -> hypotenuse_create_triangle_vertically_remove_padding.
  rewrite -> create_triangle_vertically_horizontal_seed_tuple_padding.
  rewrite -> hypotenuse_create_triangle_vertically_p_monomials.
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_list_sum.
  rewrite -> rev_list_zip;
    [ idtac | rewrite -> app_length;
              rewrite -> unfold_length_induction_case;
              rewrite -> unfold_length_base_case;
              rewrite ->2 rev_length;
              rewrite ->2 Str_prefix_length;
              rewrite -> plus_comm;
              reflexivity ].
  rewrite -> rev_app_distr.
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> app_nil_l.
  rewrite ->2 rev_involutive.
  rewrite <- unfold_list_sum.

  replace ([0] ++ Str_prefix (S r) (p_monomials (S t) r 0 c))
  with (Str_prefix (S (S r))  (0 ::: (p_monomials (S t) r 0 c)));
    [ idtac | reflexivity ].

  replace (Str_prefix (S (S r)) (0 ::: p_monomials (S t) r 0 c)
         l+ Str_prefix (S (S r)) (p_monomials (S t) (S r) 0 d) ++
         [0])
  with ((Str_prefix (S (S r)) (0 ::: p_monomials (S t) r 0 c) ++ [0]) l+
        (Str_prefix (S (S r)) (p_monomials (S t) (S r) 0 d) ++ [0]));
    [ idtac |
      rewrite -> unfold_list_sum;
        rewrite -> list_zip_append;
        [ rewrite ->4 unfold_Str_prefix_induction_case;
          rewrite -> stream_derivative;
          rewrite ->3 p_monomials_stream_derivative;
          rewrite ->3 unfold_list_zip_induction_case_cons, -> plus_0_r;
          rewrite ->2 unfold_list_sum_induction_case_cons;
          rewrite -> unfold_list_zip_base_case_nil;
          rewrite -> p_monomials_initial_value;
          rewrite -> initial_value, -> plus_0_l;
          unfold list_sum;
          reflexivity | rewrite ->4 unfold_Str_prefix_induction_case;
                        rewrite ->4 unfold_length_induction_case;
                        rewrite ->2 p_monomials_stream_derivative;
                        rewrite ->2 Str_prefix_length;
                        reflexivity | reflexivity ] ].

  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> initial_value.
  rewrite -> stream_derivative.
  rewrite <- pad_p_monomials.
  rewrite <- app_comm_cons.
  rewrite <- pad_p_monomials.

  replace (0 :: Str_prefix (S (S r)) (p_monomials (S t) r 0 c))
  with (Str_prefix (S (S (S r))) (0 ::: (p_monomials (S t) r 0 c)));
    [ idtac | reflexivity ].

  rewrite -> (IH_n' r (S t)).
  rewrite <- plus_n_Sm, -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite nth_triangle_create_triangles_vertically_p_monomials_list_sum
  : long.

(** ** Hypotenuse and bottom element of [n]th Moessner triangle *)

Corollary hypotenuse_of_last_triangle_create_triangles_vertically_p_monomials_list_sum :
  forall (n r t d c : nat),
    hypotenuse
      (nth n
           (create_triangles_vertically
              n
              (tuple_constant (S (S (S r))) 0)
              ((Str_prefix (S (S (S r))) (0 ::: (p_monomials t r 0 c))) l+
               (Str_prefix (S (S (S r))) (p_monomials t (S r) 0 d))))
           []) =
    (p_monomials_list (S (n + t)) r r c ++ [0])
      l+ (p_monomials_list (S (n + t)) (S r) (S r) d).
Proof.
  intros n r t d c.
  rewrite -> nth_triangle_create_triangles_vertically_p_monomials_list_sum.
  rewrite -> hypotenuse_create_triangle_vertically_p_monomials_list_sum.
  rewrite -> hypotenuse_create_triangle_vertically_p_monomials.
  rewrite -> hypotenuse_create_triangle_vertically_remove_padding.
  rewrite -> create_triangle_vertically_horizontal_seed_tuple_padding.
  rewrite -> hypotenuse_create_triangle_vertically_p_monomials.
  rewrite <-2 rev_p_monomials_list_eq_p_monomials.
  reflexivity.
Qed.
Hint Rewrite hypotenuse_of_last_triangle_create_triangles_vertically_p_monomials_list_sum
  : long.

Corollary bottom_element_of_nth_triangle_create_triangles_vertically_p_monomials_list_sum :
  forall (n r t d c : nat),
    nth 0
        (hypotenuse
           (nth n
                (create_triangles_vertically
                   n
                   (tuple_constant (S (S (S r))) 0)
                   ((Str_prefix (S (S (S r))) (0 ::: (p_monomials t r 0 c))) l+
                    (Str_prefix (S (S (S r))) (p_monomials t (S r) 0 d))))
                []))
        1 = p_monomial (S (n + t)) r r c + p_monomial (S (n + t)) (S r) (S r) d.
Proof.
  intros n r t d c.
  rewrite -> hypotenuse_of_last_triangle_create_triangles_vertically_p_monomials_list_sum.
  case r as [ | r' ].

  Case "r = 0".
  rewrite -> unfold_p_monomials_list_induction_case.
  rewrite ->2 unfold_p_monomials_list_base_case.
  unfold app; fold app.
  rewrite ->2 unfold_list_sum_induction_case_cons.
  rewrite -> unfold_list_sum_base_case_nil.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.

  Case "r = S r'".
  rewrite -> unfold_p_monomials_list_induction_case.
  rewrite <- app_comm_cons.
  rewrite -> unfold_p_monomials_list_induction_case.
  rewrite -> unfold_list_sum_induction_case_cons.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.
Qed.
Hint Rewrite bottom_element_of_nth_triangle_create_triangles_vertically_p_monomials_list_sum
  : long.

(* {BOTTOM_ELEMENT_OF_NTH_TRIANGLE_IS_POWER_P_MONOMIALS_LIST_SUM} *)
Corollary bottom_element_of_nth_triangle_is_power_p_monomials_list_sum :
  forall (n r d c : nat),
    nth 0
        (hypotenuse
           (nth n
                (create_triangles_vertically
                   n
                   (tuple_constant (S (S (S r))) 0)
                   ((Str_prefix (S (S (S r)))
                                (0 ::: (p_monomials 0 r 0 c))) l+
                    (Str_prefix (S (S (S r)))
                                (p_monomials 0 (S r) 0 d)))) [])) 1 =
    (c * (S n) ^ r) + (d * (S n) ^ (S r)).
(* {END} *)
Proof.
  intros n r d c.
  rewrite ->
  bottom_element_of_nth_triangle_create_triangles_vertically_p_monomials_list_sum.
  rewrite ->2 p_monomial_n_eq_k_implies_power.
  rewrite -> plus_0_r.
  reflexivity.
Qed.
Hint Rewrite bottom_element_of_nth_triangle_is_power_p_monomials_list_sum : long.

(** ** Long Stream

  *** Definition *)

(* {LONG_STREAM} *)
CoFixpoint long_stream (n r d c : nat) : Stream nat :=
  (nth 0 (hypotenuse
            (nth n
                 (create_triangles_vertically
                    n
                    (tuple_constant (S (S (S r))) 0)
                    ((Str_prefix (S (S (S r)))
                                 (0 ::: (p_monomials 0 r 0 c))) l+
                    (Str_prefix (S (S (S r)))
                                (p_monomials 0 (S r) 0 d)))) [])) 1)
    ::: (long_stream (S n) r d c).
(* {END} *)
Hint Unfold long_stream : long.

(** *** Unfolding lemmas *)

Lemma unfold_long_stream :
  forall (n r d c : nat),
    (long_stream n r d c) =
  (nth 0 (hypotenuse
            (nth n
                 (create_triangles_vertically
                    n
                    (tuple_constant (S (S (S r))) 0)
                    ((Str_prefix (S (S (S r)))
                                 (0 ::: (p_monomials 0 r 0 c))) l+
                    (Str_prefix (S (S (S r)))
                                (p_monomials 0 (S r) 0 d)))) [])) 1)
      ::: (long_stream (S n) r d c).
Proof.
  intros n r d c.
  rewrite -> (unfold_Stream (long_stream n r d c)).
  unfold long_stream; fold long_stream.
  reflexivity.
Qed.
Hint Rewrite unfold_long_stream : long.

Lemma long_stream_initial_value :
  forall (n r d c : nat),
    (long_stream n r d c)(0) =
  (nth 0 (hypotenuse
            (nth n
                 (create_triangles_vertically
                    n
                    (tuple_constant (S (S (S r))) 0)
                    ((Str_prefix (S (S (S r)))
                                 (0 ::: (p_monomials 0 r 0 c))) l+
                    (Str_prefix (S (S (S r)))
                                (p_monomials 0 (S r) 0 d)))) [])) 1).
Proof.
  intros n r d c.
  rewrite -> initial_value.
  rewrite -> unfold_long_stream.
  reflexivity.
Qed.
Hint Rewrite long_stream_initial_value : long.

Lemma long_stream_stream_derivative :
  forall (n r d c : nat),
    (long_stream n r d c)` = (long_stream (S n) r d c).
Proof.
  intros n r d c.
  rewrite -> stream_derivative.
  rewrite -> unfold_long_stream.
  reflexivity.
Qed.
Hint Rewrite long_stream_stream_derivative : long.

(** ** Long's theorem *)

(* {LONG_S_THEOREM} *)
Theorem Long_s_theorem :
  forall (b e d c : nat),
    long_stream b e d c ~
    (c n* (successive_powers b e)) s+ (d n* (successive_powers b (S e))).
(* {END} *)
Proof.
  pcofix coIH.
  intros b e d c.
  bisimilar.

  Case "initial value".
  rewrite -> long_stream_initial_value.
  rewrite -> bottom_element_of_nth_triangle_is_power_p_monomials_list_sum.
  rewrite -> stream_sum_initial_value.
  rewrite ->2 stream_scalar_multiplication_initial_value.
  rewrite ->2 successive_powers_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> long_stream_stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite ->2 stream_scalar_multiplication_stream_derivative.
  rewrite ->2 successive_powers_stream_derivative.
  exact (coIH (S b) e d c).
Qed.
Hint Rewrite Long_s_theorem : long.