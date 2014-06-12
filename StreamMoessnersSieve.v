(* StreamMoessnersSieve.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Stream Moessner's sieve

  This module defines the stream-based version of Moessner's sieve.

  stream operators:
  - [drop]
  - [sieve_step]
  - [sieve]

*)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.
Require Import Setoid.
Require Import Morphisms.

(* Own modules *)
Require Import Cases.
Require Import StreamCalculus.
Require Import DualMoessnersSieve.
Require Import CharacteristicFunction.

(** * Stream operators *)

(** ** Drop

  *** Definition *)

(* {DROP} *)
CoFixpoint drop (i k : nat) (sigma : Stream nat) : Stream nat :=
  match i with
    | 0 => (sigma`)(0) ::: drop (k - 2) k sigma``
    | S i' => sigma(0) ::: drop i' k sigma`
  end.
(* {END} *)
Hint Unfold drop : streammoessner.

(** *** Unfolding lemmas *)

Lemma unfold_drop_base_case :
  forall (k : nat) (sigma : Stream nat),
    drop 0 k sigma = (sigma`)(0) ::: drop (k - 2) k sigma``.
Proof.
  intros k sigma.
  rewrite -> (unfold_Stream (drop 0 k sigma)).
  unfold drop; fold drop.
  reflexivity.
Qed.
Hint Rewrite unfold_drop_base_case : streammoessner.

Lemma unfold_drop_inductive_case :
  forall (i' k : nat) (sigma : Stream nat),
    drop (S i') k sigma = sigma(0) ::: drop i' k sigma`.
Proof.
  intros i' k sigma.
  rewrite -> (unfold_Stream (drop (S i') k sigma)).
  unfold drop; fold drop.
  reflexivity.
Qed.
Hint Rewrite unfold_drop_inductive_case : streammoessner.

Lemma drop_initial_value_case_i_eq_0 :
  forall (k : nat) (sigma : Stream nat),
    (drop 0 k sigma)(0) = (sigma`)(0).
Proof.
  intros k sigma.
  rewrite -> initial_value.
  rewrite -> unfold_drop_base_case.
  reflexivity.
Qed.
Hint Rewrite drop_initial_value_case_i_eq_0 : streammoessner.

Lemma drop_initial_value_case_i_gt_0 :
  forall (i' k : nat) (sigma : Stream nat),
    (drop (S i') k sigma)(0) = sigma(0).
Proof.
  intros i' k sigma.
  rewrite -> initial_value.
  rewrite -> unfold_drop_inductive_case.
  reflexivity.
Qed.
Hint Rewrite drop_initial_value_case_i_gt_0 : streammoessner.

Lemma drop_stream_derivative_case_i_eq_0 :
  forall (k : nat) (sigma : Stream nat),
    (drop 0 k sigma)` = drop (k-2) k (sigma``).
Proof.
  intros k sigma.
  rewrite -> stream_derivative.
  rewrite -> unfold_drop_base_case.
  reflexivity.
Qed.
Hint Rewrite drop_stream_derivative_case_i_eq_0 : streammoessner.

Lemma drop_stream_derivative_case_i_gt_0 :
  forall (i' k : nat) (sigma : Stream nat),
    (drop (S i') k sigma)` = drop i' k (sigma`).
Proof.
  intros i' k sigma.
  rewrite -> unfold_drop_inductive_case.
  rewrite -> stream_derivative.
  reflexivity.
Qed.
Hint Rewrite drop_stream_derivative_case_i_gt_0 : streammoessner.

(** *** [drop] preserves [bisimilarity] *)

Global Instance drop_proper i k :
  Proper (bisimilarity ==> bisimilarity) (drop i k).
Proof.
  unfold Proper; unfold respectful.
  intros sigma tau H_bisim_sigma_tau; revert sigma tau H_bisim_sigma_tau i k.

  pcofix coIH.
  intros sigma tau H_bisim_sigma_tau [ | i' ] k.

  Case "i = 0".
  bisimilar.

  SCase "initial value".
  rewrite ->2 drop_initial_value_case_i_eq_0.
  rewrite -> H_bisim_sigma_tau.
  reflexivity.

  SCase "stream derivative".
  rewrite ->2 drop_stream_derivative_case_i_eq_0.
  apply (coIH (sigma``) (tau``)).
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  pdestruct R_stream_derivatives;
    rewrite <- unfold_bisimilarity in R_stream_derivatives;
    rename sigma0 into sigma_tl, tau0 into tau_tl.
  exact R_stream_derivatives.

  Case "i = S i'".
  bisimilar.

  SCase "initial value".
  rewrite ->2 drop_initial_value_case_i_gt_0.
  rewrite -> H_bisim_sigma_tau.
  reflexivity.

  SCase "initial value".
  rewrite ->2 drop_stream_derivative_case_i_gt_0.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  exact (coIH (sigma`) (tau`) R_stream_derivatives i' k).
Qed.

(** *** Properties *)

(* {DROP_STREAM_CONSTANT} *)
Lemma drop_stream_constant :
  forall (i k n : nat),
    (drop i k #n) ~ #n.
(* {END} *)
Proof.
  pcofix coIH.
  intros [ | i' ] k n.

  Case "i = 0".
  bisimilar.

  SCase "initial value".
  rewrite -> drop_initial_value_case_i_eq_0.
  rewrite -> stream_constant_stream_derivative.
  reflexivity.

  SCase "stream derivative".
  rewrite -> drop_stream_derivative_case_i_eq_0.
  rewrite ->2 stream_constant_stream_derivative.
  exact (coIH (k - 2) k n).

  Case "i = S i'".
  bisimilar.

  SCase "initial value".
  rewrite -> drop_initial_value_case_i_gt_0.
  reflexivity.

  SCase "stream derivative".
  rewrite -> drop_stream_derivative_case_i_gt_0.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH i' k n).
Qed.
Hint Rewrite drop_stream_constant : streammoessner.

(* {DROP_STREAM_MAP} *)
Lemma drop_stream_map :
  forall (i k : nat) (sigma : Stream nat) (f : nat -> nat),
    drop i k (stream_map f sigma) ~
    stream_map f (drop i k sigma).
(* {END} *)
Proof.
  pcofix coIH.
  intros [ | i' ] k sigma f.

  Case "i = 0".
  bisimilar.

  SCase "initial value".
  rewrite -> drop_initial_value_case_i_eq_0.
  rewrite -> stream_map_initial_value.
  rewrite -> drop_initial_value_case_i_eq_0.
  rewrite -> stream_map_stream_derivative.
  rewrite -> stream_map_initial_value.
  reflexivity.

  SCase "stream derivative".
  rewrite -> drop_stream_derivative_case_i_eq_0.
  rewrite ->2 stream_map_stream_derivative.
  exact (coIH (k - 2) k (sigma``) f).

  Case "i = S i'".
  bisimilar.

  SCase "initial value".
  rewrite -> drop_initial_value_case_i_gt_0.
  rewrite ->2 stream_map_initial_value.
  rewrite -> drop_initial_value_case_i_gt_0.
  reflexivity.

  SCase "stream derivative".
  rewrite -> drop_stream_derivative_case_i_gt_0.
  rewrite ->2 stream_map_stream_derivative.
  rewrite -> drop_stream_derivative_case_i_gt_0.
  exact (coIH i' k sigma` f).
Qed.
Hint Rewrite drop_stream_map : streammoessner.

(* {DROP_STREAM_ZIP} *)
Lemma drop_stream_zip :
  forall (i k : nat) (sigma tau : Stream nat) (f : nat -> nat -> nat),
    drop i k (stream_zip f sigma tau) ~
    stream_zip f (drop i k sigma) (drop i k tau).
(* {END} *)
Proof.
  pcofix coIH.
  intros [ | i' ] k sigma tau f.

  Case "i = 0".
  bisimilar.

  SCase "initial value".
  rewrite -> drop_initial_value_case_i_eq_0.
  rewrite -> stream_zip_stream_derivative.
  rewrite ->2 stream_zip_initial_value.
  rewrite ->2 drop_initial_value_case_i_eq_0.
  reflexivity.

  SCase "stream derivative".
  rewrite -> drop_stream_derivative_case_i_eq_0.
  rewrite ->3 stream_zip_stream_derivative.
  rewrite ->2 drop_stream_derivative_case_i_eq_0.
  exact (coIH (k - 2) k (sigma``) (tau``) f).

  Case "i = S i'".
  bisimilar.

  SCase "initial value".
  rewrite -> drop_initial_value_case_i_gt_0.
  rewrite ->2 stream_zip_initial_value.
  rewrite ->2 drop_initial_value_case_i_gt_0.
  reflexivity.

  SCase "stream derivative".
  rewrite -> drop_stream_derivative_case_i_gt_0.
  rewrite ->2 stream_zip_stream_derivative.
  rewrite ->2 drop_stream_derivative_case_i_gt_0.
  exact (coIH i' k (sigma`) (tau`) f).
Qed.
Hint Rewrite drop_stream_zip : streammoessner.

(* {DROP_SUM} *)
Lemma drop_sum :
  forall (i k : nat) (sigma tau : Stream nat),
    drop i k (sigma s+ tau) ~ (drop i k sigma) s+ (drop i k tau).
(* {END} *)
Proof.
  intros i k sigma tau.
  exact (drop_stream_zip i k sigma tau plus).
Qed.
Hint Rewrite drop_sum : streammoessner.

(* {DROP_STREAM_PRODUCT} *)
Lemma drop_stream_product :
  forall (i k : nat) (sigma tau : Stream nat),
    drop i k (sigma s* tau) ~ (drop i k sigma) s* (drop i k tau).
(* {END} *)
Proof.
  intros i k sigma tau.
  exact (drop_stream_zip i k sigma tau mult).
Qed.
Hint Rewrite drop_stream_product : streammoessner.

(** ** Sieve step

  *** Definition *)

(* {SIEVE_STEP} *)
Definition sieve_step (i k : nat) (sigma : Stream nat) :=
  stream_partial_sums (drop i k sigma).
(* {END} *)
Hint Unfold sieve_step : streammoessner.

(** *** Unfolding lemmas *)

Lemma unfold_sieve_step :
  forall (i k : nat) (sigma : Stream nat),
  sieve_step i k sigma = stream_partial_sums (drop i k sigma).
Proof.
  intros i k sigma.
  unfold sieve_step.
  reflexivity.
Qed.
Hint Rewrite unfold_sieve_step : streammoessner.

(* {SIEVE_STEP_INITIAL_VALUE_CASE_I_EQ_0} *)
Lemma sieve_step_initial_value_case_i_eq_0 :
  forall (k : nat) (sigma : Stream nat),
    (sieve_step 0 k sigma)(0) = (sigma`)(0).
(* {END} *)
Proof.
  intros k sigma.
  rewrite -> unfold_sieve_step.
  rewrite -> stream_partial_sums_initial_value.
  rewrite -> drop_initial_value_case_i_eq_0.
  reflexivity.
Qed.
Hint Rewrite sieve_step_initial_value_case_i_eq_0 : streammoessner.

(* {SIEVE_STEP_INITIAL_VALUE_CASE_I_GT_0} *)
Lemma sieve_step_initial_value_case_i_gt_0 :
  forall (i' k : nat) (sigma : Stream nat),
    (sieve_step (S i') k sigma)(0) = sigma(0).
(* {END} *)
Proof.
  intros i' k sigma.
  rewrite -> unfold_sieve_step.
  rewrite -> stream_partial_sums_initial_value.
  rewrite -> drop_initial_value_case_i_gt_0.
  reflexivity.
Qed.
Hint Rewrite sieve_step_initial_value_case_i_gt_0 : streammoessner.

(* {SIEVE_STEP_STREAM_DERIVATIVE_CASE_I_EQ_0} *)
Lemma sieve_step_stream_derivative_case_i_eq_0 :
  forall (k : nat) (sigma : Stream nat),
    (sieve_step 0 k sigma)` ~ (sieve_step (k - 2) k sigma``) s+ #((sigma`)(0)).
(* {END} *)
Proof.
  intros k sigma.
  rewrite ->2 unfold_sieve_step.
  rewrite -> stream_partial_sums_stream_derivative_bisim.
  rewrite -> stream_derivative; rewrite -> initial_value.
  rewrite -> unfold_drop_base_case.
  reflexivity.
Qed.
Hint Rewrite sieve_step_stream_derivative_case_i_eq_0 : streammoessner.

(* {SIEVE_STEP_STREAM_DERIVATIVE_CASE_I_GT_0} *)
Lemma sieve_step_stream_derivative_case_i_gt_0 :
  forall (i' k : nat) (sigma : Stream nat),
    (sieve_step (S i') k sigma)` ~ (sieve_step i' k sigma`) s+ #(sigma(0)).
(* {END} *)
Proof.
  intros i' k sigma.
  rewrite ->2 unfold_sieve_step.
  rewrite -> stream_partial_sums_stream_derivative_bisim.
  rewrite -> stream_derivative; rewrite -> initial_value.
  rewrite -> unfold_drop_inductive_case.
  reflexivity.
Qed.
Hint Rewrite sieve_step_stream_derivative_case_i_gt_0 : streammoessner.

(** *** [sieve_step] preserves [bisimilarity] *)

Global Instance sieve_step_proper :
  forall (i k : nat),
  Proper (bisimilarity ==> bisimilarity) (sieve_step i k).
Proof.
  unfold Proper; unfold respectful.
  intros i k sigma tau H_bisim_sigma_tau.
  rewrite -> unfold_sieve_step.
  apply stream_partial_sums_proper.
  apply drop_proper.
  exact H_bisim_sigma_tau.
Qed.

(** *** Properties *)

(* {SIEVE_STEP_SUM} *)
Lemma sieve_step_sum :
  forall (i k : nat) (sigma tau : Stream nat),
    sieve_step i k (sigma s+ tau) ~ (sieve_step i k sigma) s+ (sieve_step i k tau).
(* {END} *)
Proof.
  intros i k sigma tau.
  rewrite -> unfold_sieve_step.
  rewrite -> (drop_sum i k sigma tau).
  exact (stream_partial_sums_sum (drop i k sigma) (drop i k tau)).
Qed.
Hint Rewrite sieve_step_sum : streammoessner.

(* {SIEVE_STEP_STREAM_PRODUCT_STREAM_CONSTANT} *)
Lemma sieve_step_stream_product_stream_constant :
  forall (i k n : nat) (sigma : Stream nat),
    sieve_step i k (#n s* sigma) ~ #n s* (sieve_step i k sigma).
(* {END} *)
Proof.
  intros i k n sigma.
  rewrite -> unfold_sieve_step.
  rewrite -> drop_stream_product.
  rewrite -> drop_stream_constant.
  apply stream_partial_sums_stream_constant_assoc.
Qed.
Hint Rewrite sieve_step_stream_product_stream_constant : streammoessner.

(* {SIEVE_STEP_0} *)
Lemma sieve_step_0 :
  forall (i k : nat),
    sieve_step i k #0 ~ #0.
(* {END} *)
Proof.
  intros i k.
  rewrite -> unfold_sieve_step.
  rewrite -> drop_stream_constant.
  exact stream_partial_sums_0.
Qed.
Hint Rewrite sieve_step_0 : streammoessner.

(** ** Sieve

  *** Definition *)

(* {SIEVE} *)
Fixpoint sieve (i k n : nat) (sigma : Stream nat) : Stream nat :=
  match n with
    | 0 => sieve_step i k sigma
    | S n' => sieve_step i k (sieve (S i) (S k) n' sigma)
  end.
(* {END} *)
Hint Unfold sieve : streammoessner.

(*
(* {SIEVE_EXAMPLE} *)
Str_prefix 3 (sieve 1 2 3 #1) = [1; 16; 81].
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_sieve_base_case :
  forall (i k : nat) (sigma : Stream nat),
    sieve i k 0 sigma = sieve_step i k sigma.
Proof.
  intros i k sigma.
  unfold sieve.
  reflexivity.
Qed.
Hint Rewrite unfold_sieve_base_case : streammoessner.

Lemma unfold_sieve_induction_case :
  forall (i k n' : nat) (sigma : Stream nat),
    sieve i k (S n') sigma = sieve_step i k (sieve (S i) (S k) n' sigma).
Proof.
  intros i k n' sigma.
  unfold sieve; fold sieve.
  reflexivity.
Qed.
Hint Rewrite unfold_sieve_induction_case : streammoessner.

(* {SIEVE_INITIAL_VALUE_CASE_N_EQ_0} *)
Lemma sieve_initial_value_case_n_eq_0 :
  forall (i k : nat) (sigma : Stream nat),
    (sieve i k 0 sigma)(0) = (sieve_step i k sigma)(0).
(* {END} *)
Proof.
  intros i k sigma.
  rewrite -> unfold_sieve_base_case.
  reflexivity.
Qed.
Hint Rewrite sieve_initial_value_case_n_eq_0 : streammoessner.

(* {SIEVE_INITIAL_VALUE_CASE_N_GT_0} *)
Lemma sieve_initial_value_case_n_gt_0 :
  forall (i k n' : nat) (sigma : Stream nat),
    (sieve i k (S n') sigma)(0) =
    (sieve_step i k (sieve (S i) (S k) n' sigma))(0).
(* {END} *)
Proof.
  intros i k n' sigma.
  rewrite -> unfold_sieve_induction_case.
  reflexivity.
Qed.
Hint Rewrite sieve_initial_value_case_n_gt_0 : streammoessner.

(* {SIEVE_STREAM_DERIVATIVE_CASE_N_EQ_0} *)
Lemma sieve_stream_derivative_case_n_eq_0 :
  forall (i k : nat) (sigma : Stream nat),
    (sieve i k 0 sigma)` = (sieve_step i k sigma)`.
(* {END} *)
Proof.
  intros i k sigma.
  rewrite -> unfold_sieve_base_case.
  reflexivity.
Qed.
Hint Rewrite sieve_stream_derivative_case_n_eq_0 : streammoessner.

(* {SIEVE_STREAM_DERIVATIVE_CASE_N_GT_0} *)
Lemma sieve_stream_derivative_case_n_gt_0 :
  forall (i k n' : nat) (sigma : Stream nat),
    (sieve i k (S n') sigma)` =
    (sieve_step i k (sieve (S i) (S k) n' sigma))`.
(* {END} *)
Proof.
  intros i k n sigma.
  rewrite -> unfold_sieve_induction_case.
  reflexivity.
Qed.
Hint Rewrite sieve_stream_derivative_case_n_gt_0 : streammoessner.

(** *** [sieve] preserves [bisimilarity] *)

Global Instance sieve_proper :
  forall (n i k : nat),
    Proper (bisimilarity ==> bisimilarity) (sieve i k n).
Proof.
  induction n as [ | n' ].

  Case "n = 0".
  unfold Proper; unfold respectful.
  intros i k sigma tau H_bisim_sigma_tau.
  rewrite ->2 unfold_sieve_base_case.
  rewrite -> H_bisim_sigma_tau.
  reflexivity.

  Case "n = S n'".
  unfold Proper; unfold respectful.
  intros i k sigma tau H_bisim_sigma_tau.
  rewrite -> unfold_sieve_induction_case.
  rewrite -> H_bisim_sigma_tau.
  reflexivity.
Qed.

(** *** Properties *)

(* {SIEVE_SIEVE_STEP} *)
Lemma sieve_sieve_step :
  forall (i k n' : nat) (sigma : Stream nat),
    sieve i k (S n') sigma =
    sieve i k n' (sieve_step (S(i + n')) (S(k + n')) sigma).
(* {END} *)
Proof.
  intros i k n' sigma; revert i k sigma.
  induction n' as [ | n'' IH_n'' ].

  Case "n' = 0".
  intros i k sigma.
  rewrite -> unfold_sieve_induction_case.
  rewrite -> unfold_sieve_base_case.
  rewrite ->2 plus_0_r.
  rewrite -> unfold_sieve_base_case.
  reflexivity.

  Case "n' = S n''".
  intros i k sigma.
  rewrite -> unfold_sieve_induction_case.
  rewrite -> IH_n''.
  rewrite -> unfold_sieve_induction_case.
  rewrite <-2 plus_n_Sm.
  rewrite ->2 plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite sieve_sieve_step : streammoessner.

(* {SIEVE_SUM} *)
Lemma sieve_sum :
  forall (n i k : nat) (sigma tau : Stream nat),
    sieve i k n (sigma s+ tau) ~ (sieve i k n sigma) s+ (sieve i k n tau).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros i k sigma tau.
  rewrite ->3 unfold_sieve_base_case.
  rewrite -> sieve_step_sum.
  reflexivity.

  Case "n = S n'".
  intros i k sigma tau.
  rewrite ->3 unfold_sieve_induction_case.
  rewrite -> IH_n'.
  rewrite -> sieve_step_sum.
  reflexivity.
Qed.
Hint Rewrite sieve_sum : streammoessner.

(* {SIEVE_STREAM_PRODUCT} *)
Lemma sieve_stream_product :
  forall (n i k c : nat) (sigma : Stream nat),
    sieve i k n (#c s* sigma) ~ #c s* (sieve i k n sigma).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros i k c sigma.
  rewrite ->2 unfold_sieve_base_case.
  rewrite -> sieve_step_stream_product_stream_constant.
  reflexivity.

  Case "n = S n'".
  intros i k c sigma.
  rewrite ->2 unfold_sieve_induction_case.
  rewrite -> IH_n'.
  rewrite -> sieve_step_stream_product_stream_constant.
  reflexivity.
Qed.
Hint Rewrite sieve_stream_product : streammoessner.

(* {SIEVE_0} *)
Lemma sieve_0 :
  forall (n i k : nat),
    sieve i k n #0 ~ #0.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros i k.
  rewrite -> unfold_sieve_base_case.
  exact (sieve_step_0 i k).

  Case "n = S n'".
  intros i k.
  rewrite -> unfold_sieve_induction_case.
  rewrite -> (IH_n' (S i) (S k)).
  exact (sieve_step_0 i k).
Qed.
Hint Rewrite sieve_0 : streammoessner.

(** * Equivalence proof between make_tuple and sieve *)

(** ** Helper lemmas *)

(* {STR_PREFIX_DROP} *)
Lemma Str_prefix_drop :
  forall (i k : nat) (sigma : Stream nat),
    Str_prefix i (drop i k sigma) =
    Str_prefix i sigma.
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros k sigma.
  rewrite ->2 unfold_Str_prefix_base_case.
  reflexivity.

  Case "i = S i'".
  intros k sigma.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite -> drop_initial_value_case_i_gt_0.
  f_equal.
  rewrite -> drop_stream_derivative_case_i_gt_0.
  exact (IH_i' k sigma`).
Qed.
Hint Resolve Str_prefix_drop : streammoessner.

(* {STR_PREFIX_DROP_GEN} *)
Lemma Str_prefix_drop_gen :
  forall (l i k : nat) (sigma : Stream nat),
    l <= i ->
    Str_prefix l (drop i k sigma) =
    Str_prefix l sigma.
(* {END} *)
Proof.
  induction l as [ | l' IH_l' ].

  Case "l = 0".
  intros i k sigma H_0_le_i.
  rewrite ->2 unfold_Str_prefix_base_case.
  reflexivity.

  Case "l = S l'".
  induction i as [ | i' IH_i' ].

  SCase "i = 0".
  intros k sigma H_absurd; inversion H_absurd.

  SCase "i = S i'".
  intros k sigma H_S_l_le_S_i.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite -> drop_initial_value_case_i_gt_0.
  f_equal.
  rewrite -> drop_stream_derivative_case_i_gt_0.
  rewrite -> (IH_l' i' k sigma`);
    [ idtac | apply gt_S_le; unfold gt, lt; exact H_S_l_le_S_i ].
  reflexivity.
Qed.
Hint Resolve Str_prefix_drop_gen : streammoessner.

(** ** Equivalence relation between make_tuple and sieve_step *)

(* {EQUIVALENCE_OF_MAKE_TUPLE_AND_SIEVE_STEP_GEN} *)
Theorem equivalence_of_make_tuple_and_sieve_step_gen :
  forall (l i k a : nat) (sigma : Stream nat),
    l <= i ->
    make_tuple (Str_prefix (S l) sigma) a =
    Str_prefix l ((sieve_step i k sigma) s+ #a).
(* {END} *)
Proof.
  intros l i k a sigma H_l_le_i.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  rewrite -> unfold_sieve_step.
  rewrite -> unfold_stream_partial_sums.
  rewrite -> stream_sum_comm.
  rewrite <- stream_partial_sums_acc_stream_constant_plus_stream_partial_sums.
  rewrite ->2 Str_prefix_stream_partial_sums_acc_eq_list_partial_sums_acc.
  rewrite -> Str_prefix_drop_gen;
    [ idtac | exact H_l_le_i].
  reflexivity.
Qed.
Hint Resolve equivalence_of_make_tuple_and_sieve_step_gen : streammoessner.

(* {EQUIVALENCE_OF_MAKE_TUPLE_AND_SIEVE_STEP} *)
Corollary equivalence_of_make_tuple_and_sieve_step :
  forall (l : nat) (sigma : Stream nat),
    make_tuple (Str_prefix (S l) sigma) 0 =
    Str_prefix l ((sieve_step l (S l) sigma)).
(* {END} *)
Proof.
  intros l sigma.
  rewrite -> (equivalence_of_make_tuple_and_sieve_step_gen l l (S l) 0 sigma);
    [ idtac | apply le_n ].
  rewrite -> stream_sum_0_r.
  reflexivity.
Qed.
Hint Rewrite equivalence_of_make_tuple_and_sieve_step : streammoessner.

(* {STR_PREFIX_SIEVE} *)
Lemma Str_prefix_sieve :
  forall (n l i : nat) (sigma : Stream nat),
    l <= i ->
    Str_prefix l (sieve (S i) (S (S i)) n sigma) =
    Str_prefix l (sieve (S (S i)) (S (S (S i))) n sigma).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros l i sigma H_l_le_i.
  rewrite ->2 unfold_sieve_base_case.
  rewrite <- (stream_sum_0_r (sieve_step _ _ _)).
  rewrite <- equivalence_of_make_tuple_and_sieve_step_gen;
    [ idtac | apply le_S; exact H_l_le_i ].
  rewrite <- (stream_sum_0_r (sieve_step _ _ _)).
  rewrite <- equivalence_of_make_tuple_and_sieve_step_gen;
    [ idtac | apply le_S; apply le_S; exact H_l_le_i ].
  reflexivity.

  Case "n = S n'".
  intros l i sigma H_l_le_i.
  rewrite ->2 unfold_sieve_induction_case.
  rewrite <- (stream_sum_0_r (sieve_step _ _ _)).
  rewrite <- equivalence_of_make_tuple_and_sieve_step_gen;
    [ idtac | apply le_S; exact H_l_le_i ].
  rewrite <- (stream_sum_0_r (sieve_step _ _ _)).
  rewrite <- equivalence_of_make_tuple_and_sieve_step_gen;
    [ idtac | apply le_S; apply le_S; exact H_l_le_i ].
  rewrite -> (IH_n' (S l) (S i) sigma);
    [ idtac | apply gt_le_S; apply le_gt_S; exact H_l_le_i ].
  reflexivity.
Qed.
Hint Resolve Str_prefix_sieve : streammoessner.

(** ** Equivalence relation between make_tuple and sieve *)

(* {EQUIVALENCE_OF_REPEAT_MAKE_TUPLE_AND_SIEVE} *)
Theorem equivalence_of_repeat_make_tuple_and_sieve :
  forall (i n : nat) (sigma : Stream nat),
    n <= i ->
    repeat_make_tuple (Str_prefix (S i) sigma) 0 (S n)  =
    Str_prefix (i - n) (sieve i (S i) n sigma).
(* {END} *)
Proof.
  case i as [ | i' ].

  Case "i = 0".
  intros n sigma H_n_le_i.
  unfold minus.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_make_tuple_base_case_x_nil.
  rewrite -> repeat_make_tuple_l_eq_0;
    [ idtac | rewrite -> unfold_length_base_case; apply le_0_n ].
  reflexivity.

  Case "i = S i'".
  induction n as [ | n' IH_n' ].

  SCase "n = 0".
  intros sigma H_0_le_S_i'.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite -> unfold_repeat_make_tuple_base_case.
  rewrite -> unfold_make_tuple_induction_case.
  rewrite -> plus_0_r.
  symmetry.

  rewrite <- minus_n_O.
  rewrite -> unfold_sieve_base_case.
  rewrite -> unfold_sieve_step.
  rewrite -> unfold_stream_partial_sums.
  rewrite -> Str_prefix_stream_partial_sums_acc_eq_list_partial_sums_acc.
  rewrite -> Str_prefix_drop.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> plus_0_r.
  f_equal.

  rewrite <- unfold_Str_prefix_induction_case.
  rewrite -> equivalence_of_make_tuple_and_stream_partial_sums_acc.
  rewrite -> Str_prefix_stream_partial_sums_acc_eq_list_partial_sums_acc.
  reflexivity.

  SCase "n = S n'".
  intros sigma H_S_n'_le_S_i'.

  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite -> unfold_repeat_make_tuple_induction_case.
  rewrite <-2 unfold_Str_prefix_induction_case.
  rewrite <- shift_make_tuple_in_repeat_make_tuple.
  rewrite -> (IH_n' sigma);
    [ idtac | apply lt_le_weak; unfold lt; exact H_S_n'_le_S_i' ].
  rewrite <- minus_Sn_m;
    [ idtac | apply le_S_n; exact H_S_n'_le_S_i' ].
  rewrite -> equivalence_of_make_tuple_and_sieve_step.
  rewrite -> NPeano.Nat.sub_succ.
  rewrite -> unfold_sieve_induction_case.
  rewrite ->2 unfold_sieve_step.
  rewrite -> unfold_stream_partial_sums.
  rewrite -> Str_prefix_stream_partial_sums_acc_eq_list_partial_sums_acc.
  rewrite -> Str_prefix_drop.
  rewrite -> unfold_stream_partial_sums.
  rewrite -> Str_prefix_stream_partial_sums_acc_eq_list_partial_sums_acc.
  rewrite -> Str_prefix_drop_gen;
    [ idtac | rewrite -> le_minus; apply le_S; apply le_n ].
  rewrite -> Str_prefix_sieve;
    [ idtac | rewrite -> le_minus; apply le_n ].
  reflexivity.
Qed.
Hint Resolve equivalence_of_repeat_make_tuple_and_sieve : streammoessner.

(* {EQUIVALENCE_OF_SIEVE_AND_CREATE_TRIANGLE_HORIZONTALLY} *)
Corollary equivalence_of_sieve_and_create_triangle_horizontally :
  forall (n i : nat) (sigma : Stream nat),
    n <= i ->
    Str_prefix (i - n) (sieve i (S i) n sigma) =
    nth n (create_triangle_horizontally
             (Str_prefix (S i) sigma)
             (tuple_constant
                (length (Str_prefix (S i) sigma)) 0)) [].
(* {END} *)
Proof.
  intros n i sigma H_n_le_i.
  rewrite <- equivalence_of_repeat_make_tuple_and_sieve;
    [ idtac | exact H_n_le_i ].
  rewrite -> correctness_of_repeat_make_tuple.
  rewrite -> equivalence_of_vertical_and_horizontal_triangle_swap.
  reflexivity.
Qed.
Hint Resolve equivalence_of_sieve_and_create_triangle_horizontally : streammoessner.