(* BinomialCoefficients.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Binomial coefficients

This modules defines the following functions:

- [binomial_coefficient]
- [rotated_binomial_coefficient]
- [rotated_hockey_stick]
- [hockey_stick]

*)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.

(* Own modules *)
Require Import Cases.
Require Import Power.

(** * Binomial coefficients *)

(** ** Binomial coefficient *)

(* Normalized binomial coefficient (same as Print binomial_coefficient)

(* {BINOMIAL_COEFFICIENT_NORMALIZED} *)
Fixpoint binomial_coefficient (n k : nat) : nat :=
  match n with
    | 0 => match k with
             | 0 => 1
             | S k' => 0
           end
    | S n' => match k with
                | 0 => 1
                | S k' => binomial_coefficient n' (S k') +
                          binomial_coefficient n' k'
              end
  end.
(* {END} *)
*)

(* {BINOMIAL_COEFFICIENT} *)
Fixpoint binomial_coefficient (n k : nat) : nat :=
  match n, k with
    | n, 0 => 1
    | 0, S k' => 0
    | S n', S k' => binomial_coefficient n' (S k') +
                    binomial_coefficient n' k'
  end.
Notation "C( n , k )" := (binomial_coefficient n k).
(* {END} *)
Hint Unfold binomial_coefficient : binomial.

(** *** Unfolding lemmas *)

(* {UNFOLD_BINOMIAL_COEFFICIENT_BASE_CASE_N_0} *)
Lemma unfold_binomial_coefficient_base_case_n_0 :
  forall (n : nat),
    C(n, 0) = 1.
(* {END} *)
Proof.
  case n as [ | n' ].

  Case "n = 0".
  unfold binomial_coefficient.
  reflexivity.

  Case "n = S n'".
  unfold binomial_coefficient.
  reflexivity.
Qed.
Hint Rewrite unfold_binomial_coefficient_base_case_n_0 : binomial.

(* {UNFOLD_BINOMIAL_COEFFICIENT_BASE_CASE_0_S_K'} *)
Lemma unfold_binomial_coefficient_base_case_0_S_k' :
  forall (k' : nat), C(0, S k') = 0.
(* {END} *)
Proof.
  intro k'.
  unfold binomial_coefficient.
  reflexivity.
Qed.
Hint Rewrite unfold_binomial_coefficient_base_case_0_S_k' : binomial.

(* {UNFOLD_BINOMIAL_COEFFICIENT_INDUCTION_CASE_S_N'_S_K'} *)
Lemma unfold_binomial_coefficient_induction_case_S_n'_S_k' :
  forall (n' k' : nat), C(S n', S k') = C(n', S k') + C(n', k').
(* {END} *)
Proof.
  intros n' k'.
  unfold binomial_coefficient; fold binomial_coefficient.
  reflexivity.
Qed.
Hint Rewrite unfold_binomial_coefficient_induction_case_S_n'_S_k' : binomial.

(** *** Properties *)

(*
(* {PASCAL_S_RULE} *)
Theorem Pascal_s_rule' :
  forall (n' k' : nat),
    C(S n', S k') = C(n', S k') + C(n', k').
(* {END} *)
*)

Definition Pascal_s_rule :=
  unfold_binomial_coefficient_induction_case_S_n'_S_k'.
Hint Rewrite Pascal_s_rule : binomial.

(* {BINOMIAL_COEFFICIENT_N_LT_K_IMPLIES_0} *)
Lemma binomial_coefficient_n_lt_k_implies_0 :
  forall (n k : nat), n < k -> C(n, k) = 0.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  case k as [ | k' ].

  SCase "k = 0".
  intro H_absurd.
  inversion H_absurd.

  SCase "k = S k'".
  intro H_0_lt_S_k'.
  rewrite -> unfold_binomial_coefficient_base_case_0_S_k'.
  reflexivity.

  Case "n = S n'".
  case k as [ | k' ].

  SCase "k = 0".
  intro H_absurd.
  inversion H_absurd.

  SCase "k = S k'".
  intro H_S_n'_lt_S_k'.
  rewrite -> unfold_binomial_coefficient_induction_case_S_n'_S_k'.

  rewrite -> (IH_n' k');
    [ idtac | apply gt_S_le; unfold gt; exact H_S_n'_lt_S_k' ].
  rewrite -> (IH_n' (S k'));
    [ idtac | apply lt_le_weak; exact H_S_n'_lt_S_k' ].
  rewrite -> plus_0_r.
  reflexivity.
Qed.
Hint Resolve binomial_coefficient_n_lt_k_implies_0 : binomial.

(* {BINOMIAL_COEFFICIENT_N_EQ_K_IMPLIES_1} *)
Lemma binomial_coefficient_n_eq_k_implies_1 :
  forall (n : nat), C(n, n) = 1.
(* {END} *)
Proof.
  induction n as [ | n' ].

  Case "n = 0".
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  reflexivity.

  Case "n = S n'".
  rewrite -> unfold_binomial_coefficient_induction_case_S_n'_S_k'.
  rewrite -> IHn'.
  rewrite ->
    (binomial_coefficient_n_lt_k_implies_0 n' (S n') (lt_n_Sn n')).
  rewrite -> plus_0_l.
  reflexivity.
Qed.
Hint Rewrite binomial_coefficient_n_eq_k_implies_1 : binomial.

(* {BINOMIAL_COEFFICIENT_N_I_EQ_N} *)
Lemma binomial_coefficient_n_i_eq_n :
  forall (n : nat),
    C(n, 1) = n.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  rewrite -> unfold_binomial_coefficient_base_case_0_S_k'.
  reflexivity.

  Case "n = S n'".
  rewrite -> unfold_binomial_coefficient_induction_case_S_n'_S_k'.
  rewrite -> IH_n'.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite binomial_coefficient_n_i_eq_n : binomial.

(** ** Rotated binomial coefficient

  *** Definition *)

(*
(* {ROTATED_BINOMIAL_COEFFICIENT_NOT_GUARDED} *)
Fixpoint rotated_binomial_coefficient (r c : nat) : nat :=
  match r, c with
    | r, 0 => 1
    | 0, c => 1
    | S r', S c' => rotated_binomial_coefficient r' (S c') +
                    rotated_binomial_coefficient (S r') c'
  end.
(* {END} *)
*)

(*
(* {ROTATED_BINOMIAL_COEFFICIENT_SYM} *)
Definition rotated_binomial_coefficient (r c : nat) : nat :=
  C(c + r, c).
Notation "R( r , c )" := (rotated_binomial_coefficient r c).
(* {END} *)
*)

(* {ROTATED_BINOMIAL_COEFFICIENT} *)
Definition rotated_binomial_coefficient (r c : nat) : nat :=
  C(c + r, r).
Notation "R( r , c )" := (rotated_binomial_coefficient r c).
(* {END} *)
Hint Unfold rotated_binomial_coefficient : binomial.

(** *** Unfolding lemmas *)

(* {UNFOLD_ROTATED_BINOMIAL_COEFFICIENT} *)
Lemma unfold_rotated_binomial_coefficient :
  forall (r c : nat),
    R(r,c) = C(c + r, r).
(* {END} *)
Proof.
  intros r c.
  unfold rotated_binomial_coefficient.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_binomial_coefficient : binomial.

(* {UNFOLD_ROTATED_BINOMIAL_COEFFICIENT_BASE_CASE_R_0} *)
Lemma unfold_rotated_binomial_coefficient_base_case_r_0 :
  forall (r : nat),
    R(r, 0) = 1.
(* {END} *)
Proof.
  case r as [ | r' ].

  Case "r = 0".
  rewrite -> unfold_rotated_binomial_coefficient.
  rewrite -> plus_0_r.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  reflexivity.

  Case "r = S r'".
  rewrite -> unfold_rotated_binomial_coefficient.
  rewrite -> plus_0_l.
  exact (binomial_coefficient_n_eq_k_implies_1 (S r')).
Qed.
Hint Rewrite unfold_rotated_binomial_coefficient_base_case_r_0 : binomial.

(* {UNFOLD_ROTATED_BINOMIAL_COEFFICIENT_BASE_CASE_0_C} *)
Lemma unfold_rotated_binomial_coefficient_base_case_0_c :
  forall (c : nat),
    0 < c -> R(0, c) = 1.
(* {END} *)
Proof.
  case c as [ | c' ].

  Case "c = 0".
  intro H_absurd.
  inversion H_absurd.

  Case "0 < S c'".
  intro H_0_lt_S_c'.
  rewrite -> unfold_rotated_binomial_coefficient.
  rewrite -> plus_0_r.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_binomial_coefficient_base_case_0_c : binomial.

(* {UNFOLD_ROTATED_BINOMIAL_COEFFICIENT_INDUCTION_CASE_S_R'_S_C'} *)
Lemma unfold_rotated_binomial_coefficient_induction_case_S_r'_S_c' :
  forall (r' c' : nat),
    R(S r', S c') = R(S r', c') + R(r', S c').
(* {END} *)
Proof.
  case r' as [ | r'' ].

  Case "r' = 0".
  intro c'.
  rewrite ->3 unfold_rotated_binomial_coefficient.
  rewrite <-2 plus_n_Sm.
  rewrite ->2 plus_0_r.
  rewrite -> unfold_binomial_coefficient_induction_case_S_n'_S_k'.
  reflexivity.

  Case "r' = S r''".
  intro c'.
  rewrite ->3 unfold_rotated_binomial_coefficient.
  rewrite <-4 plus_n_Sm.
  rewrite -> plus_Sn_m.
  rewrite ->6 unfold_binomial_coefficient_induction_case_S_n'_S_k'.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_binomial_coefficient_induction_case_S_r'_S_c'
  : binomial.

(** *** Properties *)

(*
(* {ROTATED_PASCAL_S_RULE} *)
Theorem rotated_Pascal_s_rule' :
  forall (r' c' : nat),
    R(S r', S c') = R(S r', c') + R(r', S c').
(* {END} *)
*)

Definition rotated_Pascal_s_rule :=
  unfold_rotated_binomial_coefficient_induction_case_S_r'_S_c'.
Hint Rewrite rotated_Pascal_s_rule : binomial.

Lemma rotated_binomial_coefficient_r_or_c_eq_0_implies_1 :
  forall (r c : nat),
    r = 0 \/ c = 0 ->
    R(r, c) = 1.
Proof.
  case r as [ | r' ].

  Case "r = 0".
  case c as [ | c' ].

  SCase "c = 0".
  intros _.
  rewrite -> unfold_rotated_binomial_coefficient_base_case_r_0.
  reflexivity.

  SCase "c = S c'".
  intros _.
  rewrite -> unfold_rotated_binomial_coefficient.
  rewrite -> plus_0_r.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  reflexivity.

  Case "r = S r'".
  case c as [ | c' ].

  SCase "c = 0".
  intros _.
  rewrite -> unfold_rotated_binomial_coefficient_base_case_r_0.
  reflexivity.

  SCase "c = S c'".
  intro H_absurd.
  destruct H_absurd as [ H_absurd | H_absurd ];
    inversion H_absurd.
Qed.
Hint Resolve rotated_binomial_coefficient_r_or_c_eq_0_implies_1 : binomial.

(* {ROTATED_BINOMIAL_COEFFICIENT_IS_SYMMETRIC} *)
Theorem rotated_binomial_coefficient_is_symmetric :
  forall (r c : nat), R(r, c) = R(c, r).
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  intro c.
  rewrite -> unfold_rotated_binomial_coefficient_base_case_r_0.
  rewrite -> rotated_binomial_coefficient_r_or_c_eq_0_implies_1;
    [ reflexivity | (left; reflexivity) ].

  Case "r = S r'".
  induction c as [ | c' IH_c' ].

  SCase "c = 0".
  rewrite -> unfold_rotated_binomial_coefficient_base_case_r_0.
  rewrite -> (unfold_rotated_binomial_coefficient_base_case_0_c
                (S r') (lt_0_Sn r')).
  reflexivity.

  SCase "c = S c'".
  rewrite ->2 rotated_Pascal_s_rule.
  rewrite -> (IH_r' (S c')).
  rewrite -> IH_c'.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite rotated_binomial_coefficient_is_symmetric : binomial.

(* {BINOMIAL_COEFFICIENT_EQ_ROTATED_BINOMIAL_COEFFICIENT} *)
Corollary binomial_coefficient_eq_rotated_binomial_coefficient :
  forall (n k : nat),
    k <= n ->
    C(n, k) = R(n - k, k).
(* {END} *)
Proof.
  intros n k H_k_le_n.
  rewrite -> rotated_binomial_coefficient_is_symmetric.
  unfold rotated_binomial_coefficient.
  rewrite -> (NPeano.Nat.sub_add k n H_k_le_n).
  reflexivity.
Qed.
Hint Resolve binomial_coefficient_eq_rotated_binomial_coefficient : binomial.

(* {BINOMIAL_COEFFICIENT_IS_SYMMETRIC} *)
Theorem binomial_coefficient_is_symmetric :
  forall (n k : nat),
    k <= n ->
    C(n, k) = C(n, n - k).
(* {END} *)
Proof.
  intros n k H_k_le_n.
  rewrite -> (binomial_coefficient_eq_rotated_binomial_coefficient
                n k H_k_le_n).
  unfold rotated_binomial_coefficient.
  rewrite <- (le_plus_minus k n H_k_le_n).
  reflexivity.
Qed.
Hint Resolve binomial_coefficient_is_symmetric : binomial.

(* {BINOMIAL_COEFFICIENT_IS_SYMMETRIC_ALT} *)
Theorem binomial_coefficient_is_symmetric_alt :
  forall (n k : nat),
    C(n + k, n) = C(k + n, k).
(* {END} *)
Proof.
  intros n k.
  rewrite -> plus_comm.
  rewrite <- unfold_rotated_binomial_coefficient.
  rewrite -> plus_comm.
  rewrite <- unfold_rotated_binomial_coefficient.
  rewrite -> rotated_binomial_coefficient_is_symmetric.
  reflexivity.
Qed.
Hint Rewrite binomial_coefficient_is_symmetric_alt : binomial.

(** * Hockey sticks *)

(** ** (Canonical) hockey stick aux

 *** Definition *)

(* {HOCKEY_STICK_AUX} *)
Fixpoint hockey_stick_aux (n k : nat) : nat :=
  match n with
    | 0 => C(0, k)
    | S n' => C(S n', k) + hockey_stick_aux n' k
  end.
(* {END} *)
Hint Unfold hockey_stick_aux : binomial.

(** *** Unfolding lemmas *)

Lemma unfold_hockey_stick_aux_base_case :
  forall (k : nat),
    hockey_stick_aux 0 k = C(0, k).
Proof.
  intro k.
  unfold hockey_stick_aux.
  reflexivity.
Qed.
Hint Rewrite unfold_hockey_stick_aux_base_case : binomial.

Lemma unfold_hockey_stick_aux_induction_case :
  forall (n' k : nat),
    hockey_stick_aux (S n') k =
    C(S n', k) + hockey_stick_aux n' k.
Proof.
  intros n' k.
  unfold hockey_stick_aux; fold hockey_stick_aux.
  reflexivity.
Qed.
Hint Rewrite unfold_hockey_stick_aux_induction_case : binomial.

(** *** Properties *)

(* {BINOMIAL_COEFFICIENT_EQ_HOCKEY_STICK_AUX} *)
Theorem binomial_coefficient_eq_hockey_stick_aux :
  forall (n k : nat),
    C((S n), (S k)) = (hockey_stick_aux n k).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intro k.
  rewrite -> unfold_binomial_coefficient_induction_case_S_n'_S_k'.
  rewrite -> unfold_binomial_coefficient_base_case_0_S_k'.
  rewrite -> plus_0_l.
  rewrite -> unfold_hockey_stick_aux_base_case.
  reflexivity.

  Case "n = S n'".
  intro k.
  rewrite -> unfold_binomial_coefficient_induction_case_S_n'_S_k'.
  rewrite -> IH_n'.
  rewrite -> plus_comm.
  rewrite <- unfold_hockey_stick_aux_induction_case.
  reflexivity.
Qed.
Hint Rewrite binomial_coefficient_eq_hockey_stick_aux : binomial.

(** ** Hockey Stick *)

(* {HOCKEY_STICK} *)
Definition hockey_stick (n k : nat) : nat :=
  match n with
    | 0 => match k with
             | 0 => 1
             | S _ => 0
           end
    | S n' => match k with
                | 0 => 1
                | S k' => hockey_stick_aux n' k'
              end
  end.
Notation "CH( n , k )" := (hockey_stick n k).
(* {END} *)
Hint Unfold hockey_stick : binomial.

(** *** Unfolding lemmas *)

Lemma unfold_hockey_stick_base_case_n_0 :
  forall (n : nat), CH(n, 0) = 1.
Proof.
  case n as [ | n' ].

  Case "n = 0".
  unfold hockey_stick.
  reflexivity.

  Case "n = S n'".
  unfold hockey_stick.
  reflexivity.
Qed.
Hint Rewrite unfold_hockey_stick_base_case_n_0 : binomial.

Lemma unfold_hockey_stick_base_case_0_S_k' :
  forall (k' : nat), CH(0, S k') = 0.
Proof.
  intro k'.
  unfold hockey_stick.
  reflexivity.
Qed.
Hint Rewrite unfold_hockey_stick_base_case_0_S_k' : binomial.

Lemma unfold_hockey_stick_induction_case_S_n'_S_k' :
  forall (n' k' : nat), CH((S n'), (S k')) = hockey_stick_aux n' k'.
Proof.
  intros n' k'.
  unfold hockey_stick.
  reflexivity.
Qed.
Hint Rewrite unfold_hockey_stick_induction_case_S_n'_S_k' : binomial.

(** *** Properties *)

(* {BINOMIAL_COEFFICIENT_EQ_HOCKEY_STICK} *)
Theorem binomial_coefficient_eq_hockey_stick :
  forall (n k : nat),
    C(n, k) = CH(n, k).
(* {END} *)
Proof.
  case n as [ | n' ].

  Case "n = 0".
  intro k.
  unfold binomial_coefficient, hockey_stick.
  reflexivity.

  Case "n = S n'".
  case k as [ | k' ].

  SCase "k = 0".
  rewrite -> unfold_hockey_stick_base_case_n_0.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  reflexivity.

  SCase "k = S k'".
  rewrite -> binomial_coefficient_eq_hockey_stick_aux.
  unfold hockey_stick.
  reflexivity.
Qed.
Hint Rewrite binomial_coefficient_eq_hockey_stick : binomial.

(* {HOCKEY_STICK_PASCAL_S_RULE} *)
Corollary hockey_stick_Pascal_s_rule :
  forall (n' k' : nat),
    CH(S n', S k') = CH(n', S k') + CH(n', k').
(* {END} *)
Proof.
  intros n' k'.
  rewrite <-3 binomial_coefficient_eq_hockey_stick.
  rewrite -> Pascal_s_rule.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite hockey_stick_Pascal_s_rule : binomial.

(* {HOCKEY_STICK_IS_SYMMETRIC} *)
Corollary hockey_stick_is_symmetric :
  forall (n k : nat),
    k <= n -> CH(n, k) = CH(n, n - k).
(* {END} *)
Proof.
  intros n k H_k_le_n.
  rewrite <-2 binomial_coefficient_eq_hockey_stick.
  exact (binomial_coefficient_is_symmetric n k H_k_le_n).
Qed.
Hint Resolve hockey_stick_is_symmetric : binomial.

(* {HOCKEY_STICK_IS_SYMMETRIC_ALT} *)
Theorem hockey_stick_is_symmetric_alt :
  forall (n k : nat),
    CH(n + k, n) = CH(k + n, k).
(* {END} *)
Proof.
  intros n k.
  rewrite <-2 binomial_coefficient_eq_hockey_stick.
  exact (binomial_coefficient_is_symmetric_alt n k).
Qed.
Hint Rewrite hockey_stick_is_symmetric_alt : binomial.

(** ** Rotated hockey stick aux

 *** Definition *)

(* {ROTATED_HOCKEY_STICK_AUX} *)
Fixpoint rotated_hockey_stick_aux (i c : nat) : nat :=
  match i with
    | 0 => R(0, c)
    | S i' => R(S i', c) + rotated_hockey_stick_aux i' c
  end.
(* {END} *)
Hint Unfold rotated_hockey_stick_aux : binomial.

(** *** Unfolding lemmas *)

(* {UNFOLD_ROTATED_HOCKEY_STICK_AUX_BASE_CASE} *)
Lemma unfold_rotated_hockey_stick_aux_base_case :
  forall (c : nat),
    rotated_hockey_stick_aux 0 c = R(0, c).
(* {END} *)
Proof.
  intro c.
  unfold rotated_hockey_stick_aux.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_hockey_stick_aux_base_case : binomial.

(* {UNFOLD_ROTATED_HOCKEY_STICK_AUX_INDUCTION_CASE} *)
Lemma unfold_rotated_hockey_stick_aux_induction_case :
  forall (i' c : nat),
    rotated_hockey_stick_aux (S i') c =
    R(S i', c) + rotated_hockey_stick_aux i' c.
(* {END} *)
Proof.
  intros i' c.
  unfold rotated_hockey_stick_aux; fold rotated_hockey_stick_aux.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_hockey_stick_aux_induction_case : binomial.

(** *** Properties *)

(* {ROTATED_HOCKEY_STICK_AUX_0_C} *)
Lemma rotated_hockey_stick_aux_0_c :
  forall (c : nat),
    rotated_hockey_stick_aux 0 c = 1.
(* {END} *)
Proof.
  intro c.
  unfold rotated_hockey_stick_aux.
  rewrite -> rotated_binomial_coefficient_r_or_c_eq_0_implies_1;
    [ reflexivity | (left; reflexivity) ].
Qed.
Hint Rewrite rotated_hockey_stick_aux_0_c : binomial.

(* {ROTATED_BINOMIAL_COEFFICIENT_EQ_ROTATED_HOCKEY_STICK_AUX} *)
Lemma rotated_binomial_coefficient_eq_rotated_hockey_stick_aux :
  forall (r c' : nat),
    R(r, S c') = rotated_hockey_stick_aux r c'.
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  intro c'.
  rewrite -> unfold_rotated_hockey_stick_aux_base_case.
  rewrite -> (unfold_rotated_binomial_coefficient_base_case_0_c
                (S c') (lt_0_Sn c')).
  rewrite -> rotated_binomial_coefficient_r_or_c_eq_0_implies_1;
    [ reflexivity | (left; reflexivity) ].

  Case "r = S r'".
  intro c'.
  rewrite -> unfold_rotated_binomial_coefficient_induction_case_S_r'_S_c'.
  rewrite -> (IH_r' c').
  rewrite -> unfold_rotated_hockey_stick_aux_induction_case.
  reflexivity.
Qed.
Hint Rewrite rotated_binomial_coefficient_eq_rotated_hockey_stick_aux
  : binomial.

(** ** Rotated hockey stick *)

(* {ROTATED_HOCKEY_STICK} *)
Definition rotated_hockey_stick (r c : nat) : nat :=
  match c with
    | 0 => 1
    | S c' => rotated_hockey_stick_aux r c'
  end.
Notation "RH( r , c )" := (rotated_hockey_stick r c).
(* {END} *)
Hint Unfold rotated_hockey_stick : binomial.

(** *** Unfolding lemmas *)

(* {UNFOLD_ROTATED_HOCKEY_STICK_BASE_CASE_R_0} *)
Lemma unfold_rotated_hockey_stick_base_case_r_0 :
  forall (r : nat),
    RH(r, 0) = 1.
(* {END} *)
Proof.
  intro r.
  unfold rotated_hockey_stick.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_hockey_stick_base_case_r_0 : binomial.

(* {UNFOLD_ROTATED_HOCKEY_STICK_INDUCTION_CASE_R_S_C'} *)
Lemma unfold_rotated_hockey_stick_induction_case_r_S_c' :
  forall (r c' : nat),
    RH(r, S c') = rotated_hockey_stick_aux r c'.
(* {END} *)
Proof.
  intros r c'.
  unfold rotated_hockey_stick.
  reflexivity.
Qed.
Hint Rewrite unfold_rotated_hockey_stick_induction_case_r_S_c' : binomial.

(** *** Properties *)

(* {ROTATED_BINOMIAL_COEFFICIENT_EQ_ROTATED_HOCKEY_STICK} *)
Theorem rotated_binomial_coefficient_eq_rotated_hockey_stick :
  forall (r c : nat),
    R(r, c) = RH(r, c).
(* {END} *)
Proof.
  case c as [ | c' ].

  Case "c = 0".
  rewrite -> unfold_rotated_hockey_stick_base_case_r_0.
  rewrite -> unfold_rotated_binomial_coefficient_base_case_r_0.
  reflexivity.

  Case "c = S c'".
  rewrite -> unfold_rotated_hockey_stick_induction_case_r_S_c'.
  exact (rotated_binomial_coefficient_eq_rotated_hockey_stick_aux r c').
Qed.
Hint Rewrite rotated_binomial_coefficient_eq_rotated_hockey_stick : binomial.

(* {ROTATED_HOCKEY_STICK_PASCAL_S_RULE} *)
Corollary Rotated_hockey_stick_Pascal_s_rule :
  forall (r' c' : nat),
    RH(S r', S c') = RH(S r', c') + RH(r', S c').
(* {END} *)
Proof.
  intros r' c'.
  rewrite <-3 rotated_binomial_coefficient_eq_rotated_hockey_stick.
  rewrite -> rotated_Pascal_s_rule.
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Rewrite Rotated_hockey_stick_Pascal_s_rule : binomial.

(* {ROTATED_HOCKEY_STICK_IS_SYMMETRIC} *)
Corollary Rotated_hockey_stick_is_symmetric :
  forall (r c : nat),
    RH(r, c) = RH(c, r).
(* {END} *)
Proof.
  intros r c.
  rewrite <-2 rotated_binomial_coefficient_eq_rotated_hockey_stick.
  exact (rotated_binomial_coefficient_is_symmetric r c).
Qed.
Hint Rewrite Rotated_hockey_stick_is_symmetric : binomial.

(* {EQUIVALENCE_OF_COEFFICIENTS} *)
Theorem equivalence_of_coefficients :
  forall (n k : nat),
    k <= n ->
    C(n, k) = R(n - k, k) /\
    CH(n, k) = C(n, k) /\
    RH(n - k, k) = CH(n, k).
(* {END} *)
Proof.
  intros n k H_k_le_n.
  split.

  Case "C(n, k) = R(n - k, k)".
  exact (binomial_coefficient_eq_rotated_binomial_coefficient n k H_k_le_n).
  split.

  Case "CH(n, k) = C(n, k)".
  symmetry.
  exact (binomial_coefficient_eq_hockey_stick n k).

  Case "RH(n - k, k) = CH(n, k)".
  rewrite <- binomial_coefficient_eq_hockey_stick.
  rewrite -> (binomial_coefficient_eq_rotated_binomial_coefficient
                n k H_k_le_n).
  rewrite -> rotated_binomial_coefficient_eq_rotated_hockey_stick.
  reflexivity.
Qed.
Hint Resolve equivalence_of_coefficients : binomial.