(* StreamCalculus.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Stream calculus

  This module defines a small calculus over the [Stream nat] type with the
  following selectors:

  - [hd] / [initial_value]
  - [tl] / [stream_derivative]
  - [Str_nth]
  - [Str_nth_tl]
  - [Str_prefix]

  constructors:

  - [make_stream]
  - [stream_constant]
  - [stream_successor]

  and operators:

  - [stream_map]
  - [stream_scalar_multiplication]
  - [stream_exponentiation]
  - [stream_zip]
  - [stream_sum]
  - [stream_product]
  - [stream_partial_sums_acc]
  - [stream_partial_sums]

  and equality:

  - [bisimilarity]

*)

(** * Preliminaries *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.
Require Export List.
Export ListNotations.
Require Export Streams.
Require Import Setoid.
Require Import Morphisms.

(* 3rd party *)
Require Export paco.

(* Own modules *)
Require Import Cases.
Require Export Power.
Require Export ListCalculus.

(** * Stream basics *)

(** ** Stream type *)

(** ** Stream

  *** Definition *)

(*
(* {STREAM} *)
CoInductive Stream (A : Type) : Type :=
  Cons : A -> Stream A -> Stream A.
Notation "s ::: sigma" := (Cons s sigma) (at level 60, right associativity).
(* {END} *)
*)
Notation "s ::: sigma" := (Cons s sigma) (at level 60, right associativity).

(** ** Stream selectors *)

(** ** Hd

  *** Definition *)

(*
(* {HD} *)
Definition hd {A : Type} (sigma : Stream A) :=
  match sigma with
    |  s ::: _ => s
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_hd :
  forall (sigma : Stream nat),
    hd sigma = match sigma with
             | Cons h _ => h
           end.
Proof.
  intro sigma.
  unfold hd.
  reflexivity.
Qed.
Hint Rewrite unfold_hd : streamcalc.

(** ** Tl

  *** Definition *)

(*
(* {TL} *)
Definition tl {A : Type} (sigma : Stream A) :=
  match sigma with
    | _ ::: sigma' => sigma'
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_tl :
  forall (sigma : Stream nat),
    tl sigma = match sigma with
           | Cons _ sigma' => sigma'
         end.
Proof.
  intro sigma.
  unfold tl.
  reflexivity.
Qed.
Hint Rewrite unfold_tl : streamcalc.

(** *** Notation *)

(* {INITIAL_VALUE} *)
Definition initial_value := unfold_hd.
Notation "sigma (0)" := (hd sigma) (at level 8, left associativity).
(* {END} *)
Hint Unfold initial_value : streamcalc.

(* {STREAM_DERIVATIVE} *)
Definition stream_derivative := unfold_tl.
Notation "sigma `" := (tl sigma) (at level 8, left associativity).
(* {END} *)
Hint Unfold stream_derivative : streamcalc.

(* {DECOMPOSE_STREAM} *)
Lemma decompose_Stream :
  forall (sigma : Stream nat),
    sigma = sigma(0) ::: sigma`.
(* {END} *)
Proof.
  intro sigma.
  case sigma as [ s sigma' ].
  rewrite -> unfold_hd.
  rewrite -> unfold_tl.
  reflexivity.
Qed.
Hint Rewrite decompose_Stream : streamcalc.

(** ** Str nth tl

  Returns the [n]th tail of a stream [sigma].

  *** Definition *)

(*
(* {STR_NTH_TL} *)
Fixpoint Str_nth_tl {A : Type} (n : nat) (sigma : Stream A) : Stream A :=
  match n with
  | O => sigma
  | S n' => Str_nth_tl n' sigma`
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_Str_nth_tl_base_case :
  forall (sigma : Stream nat),
    Str_nth_tl 0 sigma = sigma.
Proof.
  intro sigma.
  unfold Str_nth_tl.
  reflexivity.
Qed.
Hint Rewrite unfold_Str_nth_tl_base_case : streamcalc.

Lemma unfold_Str_nth_tl_induction_case :
  forall (n' : nat) (sigma : Stream nat),
    Str_nth_tl (S n') sigma = Str_nth_tl n' (sigma`).
Proof.
  intros n' sigma.
  unfold Str_nth_tl.
  reflexivity.
Qed.
Hint Rewrite unfold_Str_nth_tl_induction_case : streamcalc.

Lemma Str_nth_tl_initial_value_case_i_eq_0 :
  forall (sigma : Stream nat),
    (Str_nth_tl 0 sigma)(0) = sigma(0).
Proof.
  intro sigma.
  rewrite -> unfold_Str_nth_tl_base_case.
  reflexivity.
Qed.
Hint Rewrite Str_nth_tl_initial_value_case_i_eq_0 : streamcalc.

Lemma Str_nth_tl_initial_value_case_i_gt_0 :
  forall (n' : nat) (sigma : Stream nat),
    (Str_nth_tl (S n') sigma)(0) = (Str_nth_tl n' (sigma`))(0).
Proof.
  intros n' sigma.
  rewrite -> unfold_Str_nth_tl_induction_case.
  reflexivity.
Qed.
Hint Rewrite Str_nth_tl_initial_value_case_i_gt_0 : streamcalc.

Lemma Str_nth_tl_stream_derivative_case_i_eq_0 :
  forall (sigma : Stream nat),
    (Str_nth_tl 0 sigma)` = sigma`.
Proof.
  intro sigma.
  rewrite -> unfold_Str_nth_tl_base_case.
  reflexivity.
Qed.
Hint Rewrite Str_nth_tl_initial_value_case_i_eq_0 : streamcalc.

Lemma Str_nth_tl_stream_derivative_case_i_gt_0 :
  forall (n' : nat) (sigma : Stream nat),
    (Str_nth_tl (S n') sigma)` = (Str_nth_tl n' (sigma``)).
Proof.
  intros n' sigma.
  rewrite -> unfold_Str_nth_tl_induction_case.
  exact (tl_nth_tl n' sigma`).
Qed.
Hint Rewrite Str_nth_tl_stream_derivative_case_i_gt_0 : streamcalc.

(** ** Str nth

  Returns the [n]th element of a stream [sigma].

  *** Definition *)

(*
(* {STR_NTH} *)
Definition Str_nth {A : Type} (n : nat) (sigma : Stream A) : A :=
  (Str_nth_tl n sigma)(0).
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_Str_nth :
  forall (n : nat) (sigma : Stream nat),
    Str_nth n sigma = (Str_nth_tl n sigma)(0).
Proof.
  intros n sigma.
  unfold Str_nth.
  reflexivity.
Qed.
Hint Rewrite unfold_Str_nth : streamcalc.

(** ** Str prefix

  Returns a [list] of the first [n] elements of a given stream [sigma].

  *** Definition *)

(* {STR_PREFIX} *)
Fixpoint Str_prefix (n : nat) (sigma : Stream nat) : list nat :=
  match n with
    | 0 => []
    | S n' => sigma(0) :: (Str_prefix n' sigma`)
  end.
(* {END} *)
Hint Unfold Str_prefix : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_Str_prefix_base_case :
  forall (sigma : Stream nat),
    Str_prefix 0 sigma = nil.
Proof.
  intro sigma.
  unfold Str_prefix.
  reflexivity.
Qed.
Hint Rewrite unfold_Str_prefix_base_case : streamcalc.

Lemma unfold_Str_prefix_induction_case :
  forall (n' : nat) (sigma : Stream nat),
    Str_prefix (S n') sigma = (sigma(0)) :: (Str_prefix n' (sigma`)).
Proof.
  intros n' sigma.
  unfold Str_prefix; fold @Str_prefix.
  reflexivity.
Qed.
Hint Rewrite unfold_Str_prefix_induction_case : streamcalc.

(** * Stream equality *)

(** ** Bisimilarity

  How we would usually define bisimilarity:
  [[
(* {BISIMILARITY_TRADITIONAL} *)
CoInductive bisimilarity (sigma tau : Stream nat) : Prop :=
  bisimilar : sigma(0) = tau(0) ->
                sigma` ~ tau` ->
                sigma ~ tau
where "sigma ~ tau" := (Bisimilarity sigma tau).
(* {END} *)
  ]]
  Bisimilarity using [paco]: *)

(** ** Bisimilarity gen

  *** Definition *)

(* {BISIMILARITY_GEN} *)
Inductive bisimilarity_gen bisimilarity :
  Stream nat -> Stream nat -> Prop :=
  | _bisimilarity_gen :
      forall (sigma tau : Stream nat)
        (R_initial_values : sigma(0) = tau(0))
        (R_stream_derivatives : (bisimilarity (sigma`) (tau`) : Prop)),
        bisimilarity_gen bisimilarity sigma tau.
(* {END} *)
Hint Constructors bisimilarity_gen : streamcalc.

(** *** Properties *)

Lemma bisimilarity_gen_is_monotone : monotone2 bisimilarity_gen.
Proof.
  unfold monotone2.
  intros sigma tau r R_bisimilarity IN LE.
  inversion_clear IN.
  apply _bisimilarity_gen.

  Case "initial value".
  exact R_initial_values.

  Case "stream derivative".
  exact (LE (sigma`) (tau`) R_stream_derivatives).
Qed.
Hint Resolve bisimilarity_gen_is_monotone : paco.

(** Bisimilarity

  *** Definition *)

(* {BISIMILARITY} *)
Definition bisimilarity (sigma tau : Stream nat) : Prop :=
  paco2 bisimilarity_gen bot2 sigma tau.
Infix "~" := bisimilarity (at level 70, no associativity).
(* {END} *)
Hint Unfold bisimilarity : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_bisimilarity :
  forall (sigma tau : Stream nat),
  bisimilarity sigma tau = paco2 bisimilarity_gen bot2 sigma tau.
Proof.
  intros sigma tau.
  unfold bisimilarity.
  reflexivity.
Qed.
Hint Rewrite unfold_bisimilarity : streamcalc.

(** ** Coinduction tactics *)

(* {BISIMILAR_TACTIC} *)
Ltac bisimilar :=
  pfold;
  apply _bisimilarity_gen;
  [ idtac | right ].
(* {END} *)

Ltac bisimilar_l :=
  pfold;
  apply _bisimilarity_gen;
  [ idtac | left ].

(* {COINDUCTION_TACTIC} *)
Ltac coinduction proof :=
  pcofix proof;
  intros;
  bisimilar;
  [ clear proof | try (apply proof; clear proof) ].
(* {END} *)

(** ** Proof of the bisimulation principle *)

(* {BISIMULATION} *)
Definition bisimulation (R : relation (Stream nat)) : Prop :=
  forall (sigma tau : Stream nat),
    R sigma tau -> sigma(0) = tau(0) /\ R sigma` tau`.
(* {END} *)
Hint Unfold bisimulation : streamcalc.

Lemma unfold_bisimulation :
  forall (R : relation (Stream nat)),
    bisimulation R = forall (sigma tau : Stream nat),
                       R sigma tau -> sigma(0) = tau(0) /\ R (sigma`) (tau`).
Proof.
  intro R.
  unfold bisimulation.
  reflexivity.
Qed.
Hint Rewrite unfold_bisimulation : streamcalc.

(* {BISIMILARITY_IS_A_BISIMULATION} *)
Lemma bisimilarity_is_a_bisimulation :
  bisimulation bisimilarity.
(* {END} *)
Proof.
  rewrite -> unfold_bisimulation.
  (*
  (* {BISIMILARITY_UNFOLDED} *)
     forall sigma tau : Stream nat,
       sigma ~ tau -> sigma(0) = tau(0) /\ sigma ` ~ tau `
   (* {END} *)
  *)

  intros sigma tau H_bisimilarity.
  (* pdestruct H := punfold H; destruct H; pclearbot *)
  pdestruct H_bisimilarity.
  split.

  Case "initial value".
  exact R_initial_values.

  Case "stream derivative".
  rewrite <- unfold_bisimilarity in R_stream_derivatives.
  exact R_stream_derivatives.
Qed.
Hint Resolve bisimilarity_is_a_bisimulation : streamcalc.

(* {BISIMULATION_IMPLIES_BISIMILARITY} *)
Lemma bisimulation_implies_bisimilarity :
  forall (R : relation (Stream nat)),
    bisimulation R -> forall (sigma tau : Stream nat), R sigma tau -> sigma ~ tau.
(* {END} *)
Proof.
  intros R H_bisim_R.
  pcofix coIH.
  intros sigma tau H_bisim_sigma_tau.
  bisimilar.

  Case "initial value".
  rewrite -> unfold_bisimulation in H_bisim_R.
  apply H_bisim_R in H_bisim_sigma_tau.
  destruct H_bisim_sigma_tau as [ H_hd_sigma_eq_hd_tau H_bisim_sigma_tl_tau_tl ].
  exact H_hd_sigma_eq_hd_tau.

  Case "stream derivative".
  apply (coIH sigma` tau`).
  rewrite -> unfold_bisimulation in H_bisim_R.
  apply H_bisim_R in H_bisim_sigma_tau.
  destruct H_bisim_sigma_tau as [ H_hd_sigma_eq_hd_tau H_bisim_sigma_tl_tau_tl ].
  exact H_bisim_sigma_tl_tau_tl.
Qed.
Hint Resolve bisimulation_implies_bisimilarity : streamcalc.

(* {BISIMULATION_PRINCIPLE} *)
Theorem bisimulation_principle :
  forall (sigma tau : Stream nat),
    sigma ~ tau <-> exists (R : relation (Stream nat)), bisimulation R /\ R sigma tau.
(* {END} *)
Proof.
  intros sigma tau.
  split.

  Case "->".
  intros H_bisim_sigma_tau.
  exists bisimilarity.
  split; [ apply bisimilarity_is_a_bisimulation | apply H_bisim_sigma_tau ].

  Case "<-".
  intros [ R [ H_bisimulation H_R_sigma_tau ] ].
  apply (bisimulation_implies_bisimilarity R).
  exact H_bisimulation.
  exact H_R_sigma_tau.
Qed.
Hint Resolve bisimulation_principle : streamcalc.

(** ** Equivalence proof of [bisimilarity] *)

(* {BISIMILARITY_IS_REFLEXIVE} *)
Theorem bisimilarity_is_reflexive :
  forall (sigma : Stream nat),
    sigma ~ sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intro sigma.
  bisimilar.

  Case "initial value".
  reflexivity.

  Case "stream derivative".
  exact (coIH sigma`).

  Restart.

  coinduction coIH; reflexivity.
Qed.
Hint Resolve bisimilarity_is_reflexive : streamcalc.

(* {BISIMILARITY_IS_SYMMETRIC} *)
Theorem bisimilarity_is_symmetric :
  forall (sigma tau : Stream nat),
    sigma ~ tau -> tau ~ sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau H_bisim_sigma_tau.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  bisimilar.

  Case "initial value".
  symmetry.
  exact R_initial_values.

  Case "stream derivative".
  apply (coIH (sigma`) (tau`)).
  exact R_stream_derivatives.
Qed.
Hint Resolve bisimilarity_is_symmetric : streamcalc.

(* {BISIMILARITY_IS_TRANSITIVE} *)
Theorem bisimilarity_is_transitive :
  forall (sigma tau rho : Stream nat),
    sigma ~ tau -> tau ~ rho -> sigma ~ rho.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau rho H_bisim_sigma_tau H_bisim_tau_rho.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives;
    rename R_initial_values into R_initial_values_sigma_tau,
           R_stream_derivatives into R_stream_derivatives_sigma_tau.
  pdestruct H_bisim_tau_rho;
    rewrite <- unfold_bisimilarity in R_stream_derivatives;
    rename tau into rho, sigma0 into tau,
           R_initial_values into R_initial_values_tau_rho,
           R_stream_derivatives into R_stream_derivatives_tau_rho.
  bisimilar.

  Case "initial value".
  rewrite -> R_initial_values_sigma_tau.
  rewrite -> R_initial_values_tau_rho.
  reflexivity.

  Case "stream derivative".
  exact (coIH (sigma`) (tau`) (rho`)
              R_stream_derivatives_sigma_tau
              R_stream_derivatives_tau_rho).
Qed.
Hint Resolve bisimilarity_is_transitive : streamcalc.

(* {BISIMILAR_EQUIVALENCE} *)
Global Instance bisimilar_equivalence :
  Equivalence bisimilarity.
(* {END} *)
Proof.
  apply Build_Equivalence.

  Case "Reflexive Bisimilarity".
  unfold Reflexive.
  intro sigma.
  exact (bisimilarity_is_reflexive sigma).

  Case "Symmetric Bisimilarity".
  unfold Symmetric.
  intros sigma tau.
  exact (bisimilarity_is_symmetric sigma tau).

  Case "Transitive Bisimilarity".
  unfold Transitive.
  intros sigma tau rho.
  exact (bisimilarity_is_transitive sigma tau rho).
Qed.

(** *** Proofs that [Cons], [hd] and [tl] respect [bisimilarity]

  Proving that a function is [Proper] with respect to [bisimilarity], permits us
  to use it with the [rewrite] tactic. *)

(* {CONS_PROPER} *)
Global Instance Cons_proper :
  Proper (eq ==> bisimilarity ==> bisimilarity) (@Cons nat).
(* {END} *)
Proof.
  unfold Proper; unfold respectful.
  intros s t H_s_eq_t sigma tau H_bisim_sigma_tau.
  rewrite -> H_s_eq_t; clear H_s_eq_t.
  bisimilar_l.

  Case "initial value".
  rewrite ->2 initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite <- unfold_bisimilarity.
  rewrite ->2 stream_derivative.
  exact H_bisim_sigma_tau.
Qed.

(* {HD_PROPER} *)
Global Instance hd_proper :
  Proper (bisimilarity ==> eq) (@hd nat).
(* {END} *)
Proof.
  unfold Proper; unfold respectful.
  intros sigma tau H_bisim_sigma_tau.
  pdestruct H_bisim_sigma_tau.
  exact R_initial_values.
Qed.

(* {TL_PROPER} *)
Global Instance tl_proper :
  Proper (bisimilarity ==> bisimilarity) (@tl nat).
(* {END} *)
Proof.
  unfold Proper; unfold respectful.
  intros sigma tau H_bisim_sigma_tau.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  exact R_stream_derivatives.
Qed.

(** ** Proof that two streams are bisimilar iff they are element-wise equal *)

(* {BISIMILARITY_IMPLIES_STR_NTH} *)
Lemma bisimilarity_implies_Str_nth :
  forall (n : nat) (sigma tau : Stream nat),
    sigma ~ tau -> Str_nth n sigma = Str_nth n tau.
(* {END} *)
Proof.
  unfold Str_nth.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros sigma tau H_bisim_sigma_tau.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  rewrite ->2 unfold_Str_nth_tl_base_case.
  exact R_initial_values.

  Case "n = S n'".
  intros s t H_bisim_sigma_tau.
  apply (IH_n' (s`) (t`)).
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  exact R_stream_derivatives.
Qed.
Hint Resolve bisimilarity_implies_Str_nth : streamcalc.

(* {STR_NTH_IMPLIES_BISIMILARITY} *)
Lemma Str_nth_implies_bisimilarity :
  forall (sigma tau : Stream nat),
    (forall (n : nat), Str_nth n sigma = Str_nth n tau) -> sigma ~ tau.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau H_Str_nth_n_sigma_eq_Str_nth_n_tau.
  bisimilar.

  Case "initial value".
  exact (H_Str_nth_n_sigma_eq_Str_nth_n_tau 0).

  Case "stream derivative".
  apply (coIH (sigma`) (tau`)).
  intro n'.
  exact (H_Str_nth_n_sigma_eq_Str_nth_n_tau (S n')).
Qed.
Hint Resolve Str_nth_implies_bisimilarity : streamcalc.

(* {BISIMILARITY_IFF_STR_NTH} *)
Theorem bisimilarity_iff_Str_nth :
  forall (sigma tau : Stream nat),
    sigma ~ tau <-> (forall (n : nat), Str_nth n sigma = Str_nth n tau).
(* {END} *)
Proof.
  split.

  Case "->".
  intros H_bisim_sigma_tau n.
  exact (bisimilarity_implies_Str_nth n sigma tau H_bisim_sigma_tau).

  Case "<-".
  intros H.
  exact (Str_nth_implies_bisimilarity sigma tau H).
Qed.
Hint Resolve bisimilarity_iff_Str_nth : streamcalc.

(** ** Proof that two streams are bisimilar iff all their tails are bisimilar *)

(* {BISIMILARITY_IMPLIES_STR_NTH_TL} *)
Lemma bisimilarity_implies_Str_nth_tl :
  forall (n : nat) (sigma tau : Stream nat),
    sigma ~ tau -> Str_nth_tl n sigma ~ Str_nth_tl n tau.
(* {END} *)
Proof.
  pcofix coIH.
  intros n sigma tau H_bisim_sigma_tau.
  bisimilar.

  Case "initial value".
  rewrite <-2 unfold_Str_nth.
  apply bisimilarity_implies_Str_nth.
  exact H_bisim_sigma_tau.

  Case "stream derivative".
  rewrite ->2 tl_nth_tl.
  pdestruct H_bisim_sigma_tau.
  exact (coIH n (sigma`) (tau`) R_stream_derivatives).
Qed.
Hint Resolve bisimilarity_implies_Str_nth_tl : streamcalc.

(*
(* {TL_NTH_TL} *)
Lemma tl_nth_tl :
  forall (n : nat) (sigma : Stream nat),
    (Str_nth_tl n sigma)` = Str_nth_tl n sigma`.
(* {END} *)
*)

(* {STR_NTH_TL_IMPLIES_BISIMILARITY} *)
Lemma Str_nth_tl_implies_bisimilarity :
  forall (sigma tau : Stream nat),
    (forall (n : nat), Str_nth_tl n sigma ~ Str_nth_tl n tau) -> sigma ~ tau.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau H_bisim_sigma_tau.
  bisimilar.

  Case "initial value".
  specialize (H_bisim_sigma_tau 0).
  unfold Str_nth_tl in H_bisim_sigma_tau.
  pdestruct H_bisim_sigma_tau.
  exact R_initial_values.

  Case "stream derivative".
  apply (coIH sigma` tau`).
  intro n.
  rewrite <-2 tl_nth_tl.
  rewrite -> (H_bisim_sigma_tau n).
  reflexivity.
Qed.
Hint Resolve Str_nth_implies_bisimilarity : streamcalc.

(* {BISIMILARITY_IFF_STR_NTH_TL} *)
Theorem bisimilarity_iff_Str_nth_tl :
  forall (sigma tau : Stream nat),
    sigma ~ tau <-> (forall (n : nat), Str_nth_tl n sigma ~ Str_nth_tl n tau).
(* {END} *)
Proof.
  split.

  Case "->".
  intros H_bisim_sigma_tau n.
  exact (bisimilarity_implies_Str_nth_tl n sigma tau H_bisim_sigma_tau).

  Case "<-".
  intros H.
  exact (Str_nth_tl_implies_bisimilarity sigma tau H).
Qed.
Hint Resolve bisimilarity_iff_Str_nth_tl : streamcalc.

(** ** Proof that two streams are bisimilar iff all their prefixes are equal *)

(* {BISIMILARITY_IMPLIES_STR_PREFIX} *)
Lemma bisimilarity_implies_Str_prefix :
  forall (n : nat) (sigma tau : Stream nat),
    sigma ~ tau -> Str_prefix n sigma = Str_prefix n tau.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros sigma tau H.
  rewrite ->2 unfold_Str_prefix_base_case.
  reflexivity.

  Case "n = S n'".
  intros sigma tau H.
  rewrite ->2 unfold_Str_prefix_induction_case.
  pinversion H; subst;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  rewrite -> R_initial_values.
  f_equal.
  exact (IH_n' (sigma`) (tau`) R_stream_derivatives).
Qed.
Hint Rewrite bisimilarity_implies_Str_prefix : streamcalc.

(* {STR_PREFIX_IMPLIES_BISIMILARITY} *)
Lemma Str_prefix_implies_bisimilarity :
  forall (sigma tau : Stream nat),
    (forall (n : nat), Str_prefix n sigma = Str_prefix n tau) -> sigma ~ tau.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau H_Str_prefix_sigma_tau.
  bisimilar.

  Case "initial value".
  specialize (H_Str_prefix_sigma_tau 1).
  rewrite ->2 unfold_Str_prefix_induction_case in H_Str_prefix_sigma_tau.
  rewrite ->2 unfold_Str_prefix_base_case in H_Str_prefix_sigma_tau.
  inversion_clear H_Str_prefix_sigma_tau.
  reflexivity.

  Case "stream derivative".
  apply (coIH sigma` tau`).
  intro n'.
  specialize (H_Str_prefix_sigma_tau (S n')).
  inversion_clear H_Str_prefix_sigma_tau.
  reflexivity.
Qed.
Hint Resolve Str_prefix_implies_bisimilarity : streamcalc.

(* {BISIMILARITY_IFF_STR_PREFIX} *)
Theorem bisimilarity_iff_Str_prefix :
  forall (sigma tau : Stream nat),
    sigma ~ tau <-> (forall (n : nat), Str_prefix n sigma = Str_prefix n tau).
(* {END} *)
Proof.
  split.

  Case "->".
  intros H_bisim_sigma_tau n.
  exact (bisimilarity_implies_Str_prefix n sigma tau H_bisim_sigma_tau).

  Case "<-".
  intro H.
  exact (Str_prefix_implies_bisimilarity sigma tau H).
Qed.
Hint Resolve bisimilarity_implies_Str_prefix : streamcalc.

(** ** Proofs that [Str_nth], [Str_nth_tl] and [Str_prefix] all respect
  bisimilarity *)

Global Instance Str_nth_tl_proper :
    Proper (eq ==> bisimilarity ==> bisimilarity) (@Str_nth_tl nat).
Proof.
  unfold Proper; unfold respectful.
  intros x y H_x_eq_y sigma tau H_bisim_sigma_tau.
  rewrite <- H_x_eq_y.
  exact (bisimilarity_implies_Str_nth_tl x sigma tau H_bisim_sigma_tau).
Qed.

Global Instance Str_nth_proper :
  forall (n : nat),
    Proper (bisimilarity ==> eq) (Str_nth n).
Proof.
  unfold Proper; unfold respectful.
  intros n sigma tau H_bisim_sigma_tau.
  exact (bisimilarity_implies_Str_nth n sigma tau H_bisim_sigma_tau).
Qed.

Global Instance Str_prefix_proper :
  forall (n : nat),
    Proper (bisimilarity ==> eq) (Str_prefix n).
Proof.
  unfold Proper; unfold respectful.
  intros n sigma tau H_bisim_sigma_tau.
  exact (bisimilarity_implies_Str_prefix n sigma tau H_bisim_sigma_tau).
Qed.

(** * Stream constructors *)

(** ** Make stream nat

  *** Definition *)

(* {MAKE_STREAM} *)
CoFixpoint make_stream (f : nat -> nat) (n : nat) : Stream nat :=
  n ::: make_stream f (f n).
(* {END} *)
Hint Unfold make_stream : streamcalc.

(** *** Unfolding Lemmas *)

Lemma unfold_make_stream :
  forall (f : nat -> nat) (n : nat),
    make_stream f n = n ::: make_stream f (f n).
Proof.
  intros f n.
  rewrite -> (unfold_Stream (make_stream f n)).
  unfold make_stream at 1; fold make_stream.
  reflexivity.
Qed.
Hint Rewrite unfold_make_stream : streamcalc.

Lemma make_stream_initial_value :
  forall (f : nat -> nat) (n : nat),
    (make_stream f n)(0) = n.
Proof.
  intros f n.
  rewrite -> initial_value.
  rewrite -> unfold_make_stream.
  reflexivity.
Qed.
Hint Rewrite make_stream_initial_value : streamcalc.

Lemma make_stream_stream_derivative :
  forall (f : nat -> nat) (n : nat),
    (make_stream f n)` = make_stream f (f n).
Proof.
  intros f n.
  rewrite -> stream_derivative.
  rewrite -> unfold_make_stream.
  reflexivity.
Qed.
Hint Rewrite make_stream_stream_derivative : streamcalc.

(** ** Stream constant

  *** Definition *)

(* {STREAM_CONSTANT} *)
Definition stream_constant (c : nat) : Stream nat :=
  make_stream (fun x : nat => x) c.
Notation "# c" := (stream_constant c) (at level 4, left associativity).
(* {END} *)
Hint Unfold stream_constant : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_constant :
  forall (c : nat),
    #c = #c(0) ::: #c`.
Proof.
  intro c.
  unfold stream_constant at 1.
  rewrite -> (decompose_Stream (make_stream _ c)).
  rewrite -> make_stream_initial_value.
  rewrite -> make_stream_stream_derivative.

  unfold stream_constant.
  rewrite -> make_stream_initial_value.
  rewrite -> make_stream_stream_derivative.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_constant : streamcalc.

Lemma stream_constant_initial_value :
  forall (c : nat),
    #c(0) = c.
Proof.
  intro c.
  unfold stream_constant.
  rewrite -> make_stream_initial_value.
  reflexivity.
Qed.
Hint Rewrite stream_constant_initial_value : streamcalc.

Lemma stream_constant_stream_derivative :
  forall (c : nat),
    #c` = #c.
Proof.
  intro c.
  unfold stream_constant.
  rewrite -> make_stream_stream_derivative.
  reflexivity.
Qed.
Hint Rewrite stream_constant_stream_derivative : streamcalc.

(** ** Stream successor

  *** Definition *)

(* {STREAM_SUCCESSOR} *)
Definition stream_successor (i : nat) : Stream nat :=
  make_stream S i.
(* {END} *)
Hint Unfold stream_successor : streamcalc.

Lemma unfold_stream_successor :
  forall (i : nat), stream_successor i = i ::: stream_successor (S i).
Proof.
  intro i.
  rewrite -> (unfold_Stream (stream_successor i)).
  unfold stream_successor.
  unfold make_stream.
  fold make_stream.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_successor : streamcalc.

Lemma stream_successor_initial_value :
  forall (i : nat), (stream_successor i)(0) = i.
Proof.
  intro i.
  rewrite -> unfold_stream_successor.
  rewrite -> initial_value.
  reflexivity.
Qed.
Hint Rewrite stream_successor_initial_value : streamcalc.

Lemma stream_successor_stream_derivative :
  forall (i : nat), (stream_successor i)` = stream_successor (S i).
Proof.
  intro i.
  rewrite -> unfold_stream_successor.
  rewrite -> stream_derivative.
  reflexivity.
Qed.
Hint Rewrite stream_successor_stream_derivative : streamcalc.

(** * Stream operators *)

(** ** Stream map

  *** Definition *)

(* {STREAM_MAP} *)
CoFixpoint stream_map (f : nat -> nat)
           (sigma : Stream nat) : Stream nat :=
  f sigma(0) ::: stream_map f sigma`.
(* {END} *)
Hint Unfold stream_map : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_map :
  forall (f : nat -> nat) (sigma : Stream nat),
    stream_map f sigma = f sigma(0) ::: stream_map f sigma`.
Proof.
  intros f sigma.
  rewrite -> (unfold_Stream (stream_map f sigma)).
  unfold stream_map; fold stream_map.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_map : streamcalc.

Lemma stream_map_initial_value :
  forall (f : nat -> nat) (sigma : Stream nat),
    (stream_map f sigma)(0) = f sigma(0).
Proof.
  intros f sigma.
  rewrite -> initial_value.
  rewrite -> unfold_stream_map.
  reflexivity.
Qed.
Hint Rewrite stream_map_initial_value : streamcalc.

Lemma stream_map_stream_derivative :
  forall (f : nat -> nat) (sigma : Stream nat),
    (stream_map f sigma)` = stream_map f sigma`.
Proof.
  intros f sigma.
  rewrite -> stream_derivative.
  rewrite -> unfold_stream_map.
  reflexivity.
Qed.
Hint Rewrite stream_map_stream_derivative : streamcalc.

(** *** [stream_map] preserves [bisimilarity] *)

Global Instance stream_map_proper :
  forall (f : nat -> nat),
    Proper (bisimilarity ==> bisimilarity) (stream_map f).
Proof.
  unfold Proper; unfold respectful.
  pcofix coIH.
  intros f sigma tau H_bisim_sigma_tau.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  bisimilar.

  Case "initial value".
  rewrite ->2 stream_map_initial_value.
  rewrite -> R_initial_values.
  reflexivity.

  Case "stream derivative".
  exact (coIH f (sigma`) (tau`) R_stream_derivatives).
Qed.

(** ** Scalar Multiplication

  *** Definition *)

(* {STREAM_SCALAR_MULTIPLICATION} *)
Definition stream_scalar_multiplication (k : nat)
           (sigma : Stream nat) : Stream nat :=
  stream_map (mult k) sigma.
Notation "k n* sigma" := (stream_scalar_multiplication k sigma)
                       (at level 40, left associativity).
(* {END} *)
Hint Unfold stream_scalar_multiplication : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_scalar_multiplication :
  forall (k : nat) (sigma : Stream nat),
    (k n* sigma) = k * sigma(0) ::: k n* (sigma`).
Proof.
  intros k sigma.
  rewrite -> (unfold_Stream (k n* sigma)).
  unfold stream_scalar_multiplication.
  rewrite -> unfold_stream_map.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_scalar_multiplication : streamcalc.

Lemma stream_scalar_multiplication_initial_value :
  forall (k : nat) (sigma : Stream nat),
    (k n* sigma)(0) = k * sigma(0).
Proof.
  intros k sigma.
  rewrite -> initial_value.
  rewrite -> unfold_stream_scalar_multiplication.
  reflexivity.
Qed.
Hint Rewrite stream_scalar_multiplication_initial_value : streamcalc.

Lemma stream_scalar_multiplication_stream_derivative :
  forall (k : nat) (sigma : Stream nat),
    (k n* sigma)` = k n* (sigma`).
Proof.
  intros k sigma.
  rewrite -> stream_derivative.
  rewrite -> unfold_stream_scalar_multiplication.
  reflexivity.
Qed.
Hint Rewrite stream_scalar_multiplication_stream_derivative : streamcalc.

(** *** [stream_scalar_multiplication] preserves [bisimilarity] *)

Global Instance stream_scalar_multiplication_proper :
  Proper (eq ==> bisimilarity ==> bisimilarity) stream_scalar_multiplication.
Proof.
  unfold Proper; unfold respectful.
  intros s t H_s_eq_t sigma tau H_bisim_sigma_tau.
  rewrite -> H_s_eq_t; clear H_s_eq_t.
  apply (stream_map_proper (mult t)).
  exact H_bisim_sigma_tau.
Qed.

(** ** Stream zip

  *** Definition *)

(* {STREAM_ZIP} *)
CoFixpoint stream_zip (f : nat -> nat -> nat)
           (sigma tau : Stream nat) : Stream nat :=
  f sigma(0) tau(0) ::: stream_zip f sigma` tau`.
(* {END} *)
Hint Unfold stream_zip : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_zip :
  forall (f : nat -> nat -> nat) (sigma tau : Stream nat),
    stream_zip f sigma tau = f sigma(0) tau(0) ::: stream_zip f sigma` tau`.
Proof.
  intros f sigma tau.
  rewrite -> (unfold_Stream (stream_zip f sigma tau)).
  unfold stream_zip; fold stream_zip.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_zip : streamcalc.

Lemma stream_zip_initial_value :
  forall (f : nat -> nat -> nat) (sigma tau : Stream nat),
    (stream_zip f sigma tau)(0) = f sigma(0) tau(0).
Proof.
  intros f sigma tau.
  rewrite -> initial_value.
  rewrite -> unfold_stream_zip.
  reflexivity.
Qed.
Hint Rewrite stream_zip_initial_value : streamcalc.

Lemma stream_zip_stream_derivative :
  forall (f : nat -> nat -> nat) (sigma tau : Stream nat),
    (stream_zip f sigma tau)` = stream_zip f sigma` tau`.
Proof.
  intros f sigma tau.
  rewrite -> stream_derivative.
  rewrite -> unfold_stream_zip.
  reflexivity.
Qed.
Hint Rewrite stream_zip_stream_derivative.

(** *** [stream_zip] preserves [bisimilarity] *)

Global Instance stream_zip_proper :
  forall (f : nat -> nat -> nat),
    Proper (bisimilarity ==> bisimilarity ==> bisimilarity) (stream_zip f).
Proof.
  unfold Proper; unfold respectful.
  pcofix coIH.
  intros f sigma tau H_bisim_sigma_tau rho upsilon H_bisim_rho_upsilon.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives;
    rename R_initial_values into R_initial_values_sigma_tau,
           R_stream_derivatives into R_stream_derivatives_sigma_tau.
  pdestruct H_bisim_rho_upsilon;
    rewrite <- unfold_bisimilarity in R_stream_derivatives;
    rename sigma0 into rho, tau0 into upsilon,
           R_initial_values into R_initial_values_rho_upsilon,
           R_stream_derivatives into R_stream_derivatives_rho_upsilon.
  bisimilar.

  Case "initial value".
  rewrite ->2 stream_zip_initial_value.
  rewrite -> R_initial_values_sigma_tau.
  rewrite -> R_initial_values_rho_upsilon.
  reflexivity.

  Case "stream derivative".
  rewrite ->2 stream_zip_stream_derivative.
  exact (coIH f (sigma`) (tau`) R_stream_derivatives_sigma_tau
                (rho`) (upsilon`) R_stream_derivatives_rho_upsilon).
Qed.

(** ** Stream sum

  *** Definition *)

(* {STREAM_SUM} *)
Definition stream_sum (sigma tau : Stream nat) : Stream nat :=
  stream_zip plus sigma tau.
Infix "s+" := stream_sum (at level 50, left associativity).
(* {END} *)
Hint Unfold stream_sum : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_sum :
  forall (sigma tau : Stream nat),
    (sigma s+ tau) = sigma(0) + tau(0) ::: (sigma`) s+ (tau`).
Proof.
  intros sigma tau.
  unfold stream_sum.
  rewrite -> unfold_stream_zip.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_sum : streamcalc.

Lemma stream_sum_initial_value :
  forall (sigma tau : Stream nat),
    (sigma s+ tau)(0) = sigma(0) + tau(0).
Proof.
  intros sigma tau.
  rewrite -> initial_value.
  rewrite -> unfold_stream_sum.
  reflexivity.
Qed.
Hint Rewrite stream_sum_initial_value : streamcalc.

Lemma stream_sum_stream_derivative :
  forall (sigma tau : Stream nat),
    (sigma s+ tau)` = (sigma`) s+ (tau`).
Proof.
  intros sigma tau.
  rewrite -> stream_derivative.
  rewrite -> unfold_stream_sum.
  reflexivity.
Qed.
Hint Rewrite stream_sum_stream_derivative : streamcalc.

(** *** [stream_sum] preserves [bisimilarity] *)

Global Instance stream_sum_proper :
  Proper (bisimilarity ==> bisimilarity ==> bisimilarity) stream_sum.
Proof.
  unfold stream_sum.
  exact (stream_zip_proper plus).
Qed.

(** ** Stream product

  *** Definition *)

(* {STREAM_PRODUCT} *)
Definition stream_product (sigma tau : Stream nat) : Stream nat :=
  stream_zip mult sigma tau.
Infix "s*" := stream_product (at level 40, left associativity).
(* {END} *)
Hint Unfold stream_product : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_product :
  forall (sigma tau : Stream nat),
    (sigma s* tau) = sigma(0) * tau(0) ::: (sigma`) s* (tau`).
Proof.
  intros sigma tau.
  unfold stream_product.
  rewrite -> unfold_stream_zip.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_product : streamcalc.

Lemma stream_product_initial_value :
  forall (sigma tau : Stream nat),
    (sigma s* tau)(0) = sigma(0) * tau(0).
Proof.
  intros sigma tau.
  rewrite -> initial_value.
  rewrite -> unfold_stream_product.
  reflexivity.
Qed.
Hint Rewrite stream_product_initial_value : streamcalc.

Lemma stream_product_stream_derivative :
  forall (sigma tau : Stream nat),
    (sigma s* tau)` = (sigma`) s* (tau`).
Proof.
  intros sigma tau.
  rewrite -> stream_derivative.
  rewrite -> unfold_stream_product.
  reflexivity.
Qed.
Hint Rewrite stream_product_stream_derivative.

(** *** Proper *)

Global Instance stream_product_proper :
  Proper (bisimilarity ==> bisimilarity ==> bisimilarity) stream_product.
Proof.
  unfold stream_product.
  exact (stream_zip_proper mult).
Qed.

(** ** Stream exponentiation

  *** Definition *)

(* {STREAM_EXPONENTIATION} *)
Fixpoint stream_exponentiation (n : nat) (sigma : Stream nat) : Stream nat :=
  match n with
    | 0 => #1
    | S n' => sigma s* (stream_exponentiation n' sigma)
  end.
Notation "sigma s^ n" := (stream_exponentiation n sigma) (at level 31, left associativity).
(* {END} *)
Hint Unfold stream_exponentiation : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_exponentiation_base_case :
  forall (sigma : Stream nat),
    sigma s^ 0 = #1.
Proof.
  intro sigma.
  unfold stream_exponentiation.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_exponentiation_base_case : streamcalc.

Lemma unfold_stream_exponentiation_induction_case :
  forall (n' : nat) (sigma : Stream nat),
    sigma s^ S n' = sigma s* (sigma s^ n').
Proof.
  intros n' sigma.
  unfold stream_exponentiation; fold stream_exponentiation.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_exponentiation_induction_case : streamcalc.

Lemma stream_exponentiation_initial_value_base_case :
  forall (sigma : Stream nat),
    (sigma s^ 0)(0) = 1.
Proof.
  intro sigma.
  rewrite -> unfold_stream_exponentiation_base_case.
  rewrite -> stream_constant_initial_value.
  reflexivity.
Qed.
Hint Rewrite stream_exponentiation_initial_value_base_case : streamcalc.

Lemma stream_exponentiation_initial_value_induction_case :
  forall (n' : nat) (sigma : Stream nat),
    (sigma s^ S n')(0) = sigma(0) * (sigma s^ n')(0).
Proof.
  intros n' sigma.
  rewrite -> unfold_stream_exponentiation_induction_case.
  rewrite -> stream_product_initial_value.
  reflexivity.
Qed.
Hint Rewrite stream_exponentiation_initial_value_induction_case : streamcalc.

Lemma stream_exponentiation_initial_value :
  forall (n : nat) (sigma : Stream nat),
    (sigma s^ n)(0) = sigma(0) ^ n.
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intro sigma.
  rewrite -> stream_exponentiation_initial_value_base_case.
  rewrite -> unfold_power_base_case.
  reflexivity.

  Case "n = S n'".
  intro sigma.
  rewrite -> stream_exponentiation_initial_value_induction_case.
  rewrite -> unfold_power_induction_case.
  rewrite -> (IH_n' sigma).
  reflexivity.
Qed.
Hint Rewrite stream_exponentiation_initial_value : streamcalc.

Lemma stream_exponentiation_stream_derivative_base_case :
  forall (sigma : Stream nat),
    (sigma s^ 0)` = #1.
Proof.
  intro sigma.
  rewrite -> unfold_stream_exponentiation_base_case.
  rewrite -> stream_constant_stream_derivative.
  reflexivity.
Qed.
Hint Rewrite stream_exponentiation_stream_derivative_base_case.

Lemma stream_exponentiation_stream_derivative_induction_case :
  forall (n' : nat) (sigma : Stream nat),
    (sigma s^ S n')` = sigma` s* (sigma s^ n')`.
Proof.
  intros n' sigma.
  rewrite -> unfold_stream_exponentiation_induction_case.
  rewrite -> stream_product_stream_derivative.
  reflexivity.
Qed.
Hint Rewrite stream_exponentiation_stream_derivative_induction_case : streamcalc.

Lemma stream_exponentiation_stream_derivative :
  forall (n : nat) (sigma : Stream nat),
    (sigma s^ n)` = sigma` s^ n.
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intro sigma.
  rewrite ->2 unfold_stream_exponentiation_base_case.
  rewrite -> stream_constant_stream_derivative.
  reflexivity.

  Case "n = S n'".
  intro sigma.
  rewrite -> stream_exponentiation_stream_derivative_induction_case.
  rewrite -> unfold_stream_exponentiation_induction_case.
  rewrite -> (IH_n' sigma).
  reflexivity.
Qed.
Hint Rewrite stream_exponentiation_stream_derivative : streamcalc.

(** *** [stream_exponentiation] preserves [bisimilarity] *)

Global Instance stream_exponentiation_proper :
  Proper (eq ==> bisimilarity ==> bisimilarity) stream_exponentiation.
Proof.
  unfold Proper; unfold respectful.
  intros n m H_eq_n_m sigma tau H_bisim_sigma_tau; subst; revert m sigma tau H_bisim_sigma_tau.
  pcofix coIH.
  intros m sigma tau H_bisim_sigma_tau.
  bisimilar.

  Case "initial value".
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  rewrite ->2 stream_exponentiation_initial_value.
  rewrite -> R_initial_values.
  reflexivity.

  Case "stream derivative".
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  rewrite ->2 stream_exponentiation_stream_derivative.
  exact (coIH m sigma` tau` R_stream_derivatives).
Qed.

(** ** Stream partial sums acc

  *** Definition *)

(* {STREAM_PARTIAL_SUMS_ACC} *)
CoFixpoint stream_partial_sums_acc (a : nat)
           (sigma : Stream nat) : Stream nat :=
  sigma(0) + a ::: stream_partial_sums_acc (sigma(0) + a) sigma`.
(* {END} *)
Hint Unfold stream_partial_sums_acc : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_partial_sums_acc :
  forall (a : nat) (sigma : Stream nat),
    stream_partial_sums_acc a sigma =
    sigma(0) + a ::: stream_partial_sums_acc (sigma(0) + a) (sigma`).
Proof.
  intros a sigma.
  rewrite -> (unfold_Stream (stream_partial_sums_acc a sigma)).
  unfold stream_partial_sums_acc; fold stream_partial_sums_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_partial_sums_acc : streamcalc.

Lemma stream_partial_sums_acc_initial_value :
  forall (a : nat) (sigma : Stream nat),
    (stream_partial_sums_acc a sigma)(0) = sigma(0) + a.
Proof.
  intros a sigma.
  rewrite -> initial_value.
  rewrite -> unfold_stream_partial_sums_acc.
  reflexivity.
Qed.
Hint Rewrite stream_partial_sums_acc_initial_value : streamcalc.

Lemma stream_partial_sums_acc_stream_derivative :
  forall (a : nat) (sigma : Stream nat),
    (stream_partial_sums_acc a sigma)` = stream_partial_sums_acc (sigma(0) + a) sigma`.
Proof.
  intros a sigma.
  rewrite -> stream_derivative.
  rewrite -> unfold_stream_partial_sums_acc.
  reflexivity.
Qed.
Hint Rewrite stream_partial_sums_acc_stream_derivative : streamcalc.

(* {STREAM_PARTIAL_SUMS_ACC_STREAM_DERIVATIVE_BISIM_AUX} *)
Lemma stream_partial_sums_acc_stream_derivative_bisim_aux :
  forall (a i : nat) (sigma : Stream nat),
    stream_partial_sums_acc (i + a) sigma` ~ (stream_partial_sums_acc a sigma`) s+ #i.
(* {END} *)
Proof.
  pcofix coIH.
  intros a i sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> stream_sum_initial_value.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> stream_constant_initial_value.
  rewrite <- plus_assoc.
  rewrite -> (plus_comm a i).
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  rewrite -> (plus_comm ((sigma`)(0)) (i + a)).
  rewrite <- (plus_assoc i a ((sigma`)(0))).
  rewrite -> (plus_comm a ((sigma`)(0))).
  exact (coIH ((sigma`)(0) + a) i (sigma`)).
Qed.
Hint Rewrite stream_partial_sums_acc_stream_derivative_bisim_aux : streamcalc.

(* {STREAM_PARTIAL_SUMS_ACC_STREAM_DERIVATIVE_BISIM} *)
Lemma stream_partial_sums_acc_stream_derivative_bisim :
  forall (sigma : Stream nat),
    (stream_partial_sums_acc 0 sigma)` ~ (stream_partial_sums_acc 0 sigma`) s+ #(sigma(0)).
(* {END} *)
Proof.
  intro sigma.
  rewrite -> (stream_partial_sums_acc_stream_derivative 0 sigma).
  exact (stream_partial_sums_acc_stream_derivative_bisim_aux 0 (sigma(0)) sigma).
Qed.
Hint Rewrite stream_partial_sums_acc_stream_derivative_bisim : streamcalc.

(** *** [stream_partial_sums_acc] preserves [bisimilarity] *)

Global Instance stream_partial_sums_acc_proper :
  Proper (eq ==> bisimilarity ==> bisimilarity) stream_partial_sums_acc.
Proof.
  unfold Proper; unfold respectful.
  pcofix coIH.
  intros x y H_x_eq_y sigma tau H_bisim_sigma_tau.
  rewrite -> H_x_eq_y; clear H_x_eq_y.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  bisimilar.

  Case "initial value".
  rewrite ->2 stream_partial_sums_acc_initial_value.
  rewrite -> R_initial_values.
  reflexivity.

  Case "stream derivative".
  rewrite ->2 stream_partial_sums_acc_stream_derivative.
  rewrite -> R_initial_values.
  exact (coIH (tau(0) + y) (tau(0) + y) eq_refl
              (sigma`) (tau`) R_stream_derivatives).
Qed.

(** ** Stream partial sums

  *** Definition *)

(* {STREAM_PARTIAL_SUMS} *)
Definition stream_partial_sums (sigma : Stream nat) : Stream nat :=
  stream_partial_sums_acc 0 sigma.
(* {END} *)
Hint Unfold stream_partial_sums : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_stream_partial_sums :
  forall (sigma : Stream nat),
    stream_partial_sums sigma = stream_partial_sums_acc 0 sigma.
Proof.
  intro sigma.
  unfold stream_partial_sums.
  reflexivity.
Qed.
Hint Rewrite unfold_stream_partial_sums : streamcalc.

Lemma stream_partial_sums_initial_value :
  forall (sigma : Stream nat),
    (stream_partial_sums sigma)(0) = sigma(0).
Proof.
  intro sigma.
  rewrite -> initial_value.
  rewrite -> unfold_stream_partial_sums.
  rewrite -> unfold_stream_partial_sums_acc.
  rewrite -> plus_0_r.
  reflexivity.
Qed.
Hint Rewrite stream_partial_sums_initial_value : streamcalc.

(* {STREAM_PARTIAL_SUMS_STREAM_DERIVATIVE_BISIM} *)
Lemma stream_partial_sums_stream_derivative_bisim :
  forall (sigma : Stream nat),
    (stream_partial_sums sigma)` ~ (stream_partial_sums sigma`) s+ #(sigma(0)).
(* {END} *)
Proof.
  intro sigma.
  rewrite -> unfold_stream_partial_sums.
  exact (stream_partial_sums_acc_stream_derivative_bisim sigma).
Qed.
Hint Rewrite stream_partial_sums_stream_derivative_bisim : streamcalc.

(** *** [stream_partial_sums] preserves [bisimilarity] *)

Global Instance stream_partial_sums_proper :
  Proper (bisimilarity ==> bisimilarity) stream_partial_sums.
Proof.
  unfold stream_partial_sums.
  apply stream_partial_sums_acc_proper.
  reflexivity.
Qed.

(** * Stream Properties *)

(** ** Str nth *)

Lemma Str_nth_0 :
  forall (sigma : Stream nat),
    Str_nth 0 sigma = sigma(0).
Proof.
  intro n'.
  rewrite -> unfold_Str_nth.
  rewrite -> Str_nth_tl_initial_value_case_i_eq_0.
  reflexivity.
Qed.
Hint Rewrite Str_nth_0 : streamcalc.

Lemma Str_nth_S_n :
  forall (n' : nat) (sigma : Stream nat),
    Str_nth (S n') sigma = Str_nth n' sigma`.
Proof.
  intros n' sigma.
  rewrite -> unfold_Str_nth.
  rewrite -> Str_nth_tl_initial_value_case_i_gt_0.
  rewrite <- unfold_Str_nth.
  reflexivity.
Qed.
Hint Rewrite Str_nth_S_n : streamcalc.

(* {NTH_AND_STR_NTH} *)
Lemma nth_and_Str_nth :
  forall (n m : nat) (sigma : Stream nat),
    n < m ->
    nth n (Str_prefix m sigma) 0 =
    Str_nth n sigma.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  case m as [ | m' ].

  SCase "m = 0".
  intros sigma H_absurd.
  inversion H_absurd.

  SCase "m = S m'".
  intros sigma H_0_lt_S_m'.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> Str_nth_0.
  reflexivity.

  Case "n = S n'".
  case m as [ | m' ].

  SCase "m = 0".
  intros sigma H_absurd.
  inversion H_absurd.

  SCase "m = S m'".
  intros sigma H_S_n'_S_m'.

  rewrite -> Str_nth_S_n.

  assert (H_hypothesis_helper: n' < m').
    apply lt_S_n.
    exact H_S_n'_S_m'.

  rewrite <- (IH_n' m' sigma` H_hypothesis_helper);
    clear H_hypothesis_helper.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_nth_induction_case_cons.
  reflexivity.
Qed.
Hint Rewrite nth_and_Str_nth : streamcalc.

(* {STR_NTH_STREAM_MAP} *)
Lemma Str_nth_stream_map :
  forall (i : nat) (sigma : Stream nat) (f : nat -> nat),
    Str_nth i (stream_map f sigma) = f (Str_nth i sigma).
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros sigma f.
  rewrite ->2 Str_nth_0.
  rewrite -> stream_map_initial_value.
  reflexivity.

  Case "i = S i'".
  intros sigma f.
  rewrite ->2 Str_nth_S_n.
  rewrite -> stream_map_stream_derivative.
  rewrite -> IH_i'.
  reflexivity.
Qed.
Hint Rewrite Str_nth_stream_map : streamcalc.

(* {STR_NTH_STREAM_ZIP} *)
Lemma Str_nth_stream_zip :
  forall (i : nat) (sigma tau : Stream nat) (f : nat -> nat -> nat),
    Str_nth i (stream_zip f sigma tau) = f (Str_nth i sigma) (Str_nth i tau).
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros sigma tau f.
  rewrite ->3 Str_nth_0.
  rewrite -> stream_zip_initial_value.
  reflexivity.

  Case "i = S i'".
  intros sigma tau f.
  rewrite ->3 Str_nth_S_n.
  exact (IH_i' sigma` tau` f).
Qed.
Hint Rewrite Str_nth_stream_zip : streamcalc.

(* {STR_NTH_STREAM_CONSTANT} *)
Lemma Str_nth_stream_constant :
  forall (i n : nat),
    Str_nth i #n = n.
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intro n.
  rewrite -> unfold_Str_nth.
  rewrite -> Str_nth_tl_initial_value_case_i_eq_0.
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "i = S i'".
  intro n.
  rewrite -> unfold_Str_nth.
  rewrite -> Str_nth_tl_initial_value_case_i_gt_0.
  rewrite -> stream_constant_stream_derivative.
  exact (IH_i' n).
Qed.
Hint Rewrite Str_nth_stream_constant : streamcalc.

(* {STR_NTH_STREAM_SUCCESSOR} *)
Lemma Str_nth_stream_successor :
  forall (i n : nat),
    Str_nth i (stream_successor n) = n + i.
(* {END} *)
Proof.
  induction i as [ | i' IH_i' ].

  Case "i  = 0".
  intro n.
  rewrite -> unfold_Str_nth.
  rewrite -> Str_nth_tl_initial_value_case_i_eq_0.
  rewrite -> stream_successor_initial_value.
  rewrite -> plus_0_r.
  reflexivity.

  Case "i = S i'".
  intro n.
  rewrite -> unfold_Str_nth.
  rewrite -> Str_nth_tl_initial_value_case_i_gt_0.
  rewrite -> stream_successor_stream_derivative.
  rewrite <- unfold_Str_nth.
  rewrite -> (IH_i' (S n)).
  rewrite -> plus_Sn_m.
  rewrite <- plus_n_Sm.
  reflexivity.
Qed.
Hint Rewrite Str_nth_stream_successor : streamcalc.

(* {STR_NTH_STREAM_EXPONENTIATION} *)
Lemma Str_nth_stream_exponentiation :
  forall (n i : nat) (sigma : Stream nat),
    Str_nth i (sigma s^ n) = (Str_nth i sigma) ^ n.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros i sigma.
  rewrite -> unfold_stream_exponentiation_base_case.
  rewrite -> unfold_power_base_case.
  rewrite -> Str_nth_stream_constant.
  reflexivity.

  Case "n = S n'".
  intros i sigma.
  rewrite -> unfold_stream_exponentiation_induction_case.
  rewrite -> unfold_power_induction_case.
  rewrite <- (IH_n' i sigma).
  unfold stream_product.
  exact (Str_nth_stream_zip i sigma (sigma s^ n') mult).
Qed.
Hint Rewrite Str_nth_stream_exponentiation : streamcalc.

(* ** Str nth tl *)

Lemma Str_nth_tl_1 :
  forall (sigma : Stream nat),
    Str_nth_tl 1 sigma = sigma`.
Proof.
  intros sigma.
  unfold Str_nth_tl.
  reflexivity.
Qed.
Hint Rewrite Str_nth_tl_1 : streamcalc.

Lemma Str_nth_tl_stream_zip :
  forall (i : nat) (sigma tau : Stream nat) (f : nat -> nat -> nat),
    Str_nth_tl i (stream_zip f sigma tau) ~
    stream_zip f (Str_nth_tl i sigma) (Str_nth_tl i tau).
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros sigma tau f.
  unfold Str_nth_tl.
  reflexivity.

  Case "i = S i'".
  intros sigma tau f.
  rewrite ->3 unfold_Str_nth_tl_induction_case.
  exact (IH_i' (sigma`) (tau`) f).
Qed.
Hint Rewrite Str_nth_tl_stream_zip : streamcalc.
Hint Resolve Str_nth_tl_stream_zip : streamcalc.

Lemma Str_nth_tl_stream_constant :
  forall (i : nat),
    Str_nth_tl i #0 ~ #0.
Proof.
  pcofix coIH.
  intro i.
  bisimilar.

  Case "initial value".
  rewrite <- unfold_Str_nth.
  rewrite -> Str_nth_stream_constant.
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  case i as [ | i' ].

  SCase "i = 0".
  rewrite -> Str_nth_tl_stream_derivative_case_i_eq_0.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH 0).

  SCase "i = S i'".
  rewrite -> Str_nth_tl_stream_derivative_case_i_gt_0.
  rewrite ->2 stream_constant_stream_derivative.
  exact (coIH i').
Qed.
Hint Rewrite Str_nth_tl_stream_constant : streamcalc.

(** ** Str_Prefix *)

(* {STR_PREFIX_LENGTH} *)
Lemma Str_prefix_length :
  forall (n : nat) (sigma : Stream nat),
    length (Str_prefix n sigma) = n.
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intro sigma.
  rewrite -> unfold_Str_prefix_base_case.
  rewrite -> unfold_length_base_case.
  reflexivity.

  Case "n = S n'".
  intro sigma.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> unfold_length_induction_case.
  rewrite -> (IH_n' sigma`).
  reflexivity.
Qed.
Hint Rewrite Str_prefix_length : streamcalc.

(* {STR_PREFIX_STREAM_PARTIAL_SUMS_ACC_EQ_LIST_PARTIAL_SUMS_ACC} *)
Lemma Str_prefix_stream_partial_sums_acc_eq_list_partial_sums_acc :
  forall (n a : nat) (sigma : Stream nat),
    Str_prefix n (stream_partial_sums_acc a sigma) =
    list_partial_sums_acc a (Str_prefix n sigma).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros a sigma.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> unfold_list_partial_sums_acc_base_case.
  reflexivity.

  Case "n = S n'".
  intros a sigma.
  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  f_equal.
  exact (IH_n' (sigma(0) + a) sigma`).
Qed.
Hint Rewrite Str_prefix_stream_partial_sums_acc_eq_list_partial_sums_acc : streamcalc.

(* {STR_PREFIX_STREAM_PARTIAL_SUMS_EQ_LIST_PARTIAL_SUMS} *)
Corollary Str_prefix_stream_partial_sums_eq_list_partial_sums :
  forall (n : nat) (sigma : Stream nat),
    Str_prefix n (stream_partial_sums sigma) =
    list_partial_sums (Str_prefix n sigma).
(* {END} *)
Proof.
  intros n sigma.
  rewrite -> unfold_list_partial_sums.
  rewrite -> unfold_stream_partial_sums.
  exact (Str_prefix_stream_partial_sums_acc_eq_list_partial_sums_acc n 0 sigma).
Qed.
Hint Rewrite Str_prefix_stream_partial_sums_eq_list_partial_sums : streamcalc.

Lemma Str_prefix_split_with_Str_nth :
  forall (n : nat) (sigma : Stream nat),
    Str_prefix (S n) sigma =
    (Str_prefix n sigma) ++ [(Str_nth n sigma)].
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intro sigma.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite ->2 unfold_Str_prefix_base_case.
  rewrite -> app_nil_l.
  rewrite -> Str_nth_0.
  reflexivity.

  Case "n = S n'".
  intro sigma.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> (IH_n' sigma`).
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> Str_nth_S_n.
  rewrite <- app_comm_cons.
  reflexivity.
Qed.
Hint Rewrite Str_prefix_split_with_Str_nth : streamcalc.

(* {STR_PREFIX_STREAM_ZIP} *)
Lemma Str_prefix_stream_zip :
  forall (n : nat) (sigma tau : Stream nat) (f : nat -> nat -> nat),
    Str_prefix n (stream_zip f sigma tau) =
    list_zip f (Str_prefix n sigma) (Str_prefix n tau).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros sigma tau f.
  rewrite ->3 unfold_Str_prefix_base_case.
  rewrite -> unfold_list_zip_base_case_nil.
  reflexivity.

  Case "n = S n'".
  intros sigma tau f.
  rewrite -> unfold_Str_prefix_induction_case.
  rewrite -> stream_zip_stream_derivative.
  rewrite -> IH_n'.
  rewrite -> stream_zip_initial_value.

  rewrite ->2 unfold_Str_prefix_induction_case.
  rewrite -> unfold_list_zip_induction_case_cons.
  reflexivity.
Qed.
Hint Rewrite Str_prefix_stream_zip : streamcalc.

(* {STR_PREFIX_AND_REMOVELAST} *)
Lemma Str_prefix_and_removelast :
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
Hint Rewrite Str_prefix_and_removelast : streamcalc.

(** ** Stream constant *)

(* {STREAM_CONSTANT_SUM} *)
Lemma stream_constant_sum :
  forall (n m : nat),
    (#n) s+ (#m) ~ #(n + m).
(* {END} *)
Proof.
  pcofix coIH.
  intros n m.
  bisimilar.

  Case "initial value".
  rewrite -> stream_sum_initial_value.
  rewrite ->3 stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_sum_stream_derivative.
  rewrite ->3 stream_constant_stream_derivative.
  exact (coIH n m).
Qed.
Hint Rewrite stream_constant_sum : streamcalc.

(* {STREAM_CONSTANT_STREAM_MAP} *)
Lemma stream_constant_stream_map :
  forall (n : nat) (f : nat -> nat),
    #(f n) ~ stream_map f #n.
(* {END} *)
Proof.
  pcofix coIH.
  intros n f.
  bisimilar.

  Case "initial value".
  rewrite -> stream_constant_initial_value.
  rewrite -> stream_map_initial_value.
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_constant_stream_derivative.
  rewrite -> stream_map_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH n f).
Qed.
Hint Rewrite stream_constant_stream_map : streamcalc.

(* {STREAM_CONSTANT_STREAM_ZIP} *)
Lemma stream_constant_stream_zip :
  forall (n m : nat) (f : nat -> nat -> nat),
    #(f n m) ~ stream_zip f #n #m.
(* {END} *)
Proof.
  pcofix coIH.
  intros n m f.
  bisimilar.

  Case "initial value".
  rewrite -> stream_constant_initial_value.
  rewrite -> stream_zip_initial_value.
  rewrite ->2 stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_constant_stream_derivative.
  rewrite -> stream_zip_stream_derivative.
  rewrite ->2 stream_constant_stream_derivative.
  exact (coIH n m f).
Qed.
Hint Rewrite stream_constant_stream_zip : streamcalc.

(** ** Stream successor *)

Lemma stream_successor_sum :
  forall (n m : nat),
    stream_successor (n + m) ~ #n s+ (stream_successor m).
Proof.
  pcofix coIH.
  intros n m.
  bisimilar.

  Case "initial value".
  rewrite -> stream_sum_initial_value.
  rewrite ->2 stream_successor_initial_value.
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_successor_stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  rewrite -> stream_successor_stream_derivative.
  rewrite -> plus_n_Sm.
  exact (coIH n (S m)).
Qed.
Hint Rewrite stream_successor_sum : streamcalc.

Lemma stream_successor_stream_derivative_bisim :
  forall (n : nat),
    (stream_successor n)` ~ #1 s+ (stream_successor n).
Proof.
  intro n.
  rewrite -> stream_successor_stream_derivative.
  rewrite <- NPeano.Nat.add_1_l.
  rewrite -> stream_successor_sum.
  reflexivity.
Qed.
Hint Rewrite stream_successor_stream_derivative_bisim : streamcalc.

(** ** Stream sum *)

(* {STREAM_SUM_COMM} *)
Lemma stream_sum_comm :
  forall (sigma tau : Stream nat),
    sigma s+ tau ~ tau s+ sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau.
  bisimilar.

  Case "initial value".
  rewrite ->2 stream_sum_initial_value.
  exact (plus_comm sigma(0) tau(0)).

  Case "stream derivative".
  rewrite ->2 stream_sum_stream_derivative.
  exact (coIH (sigma`) (tau`)).
Qed.
Hint Rewrite stream_sum_comm : streamcalc.

(* {STREAM_SUM_ASSOC} *)
Lemma stream_sum_assoc :
  forall (sigma tau rho : Stream nat),
    sigma s+ (tau s+ rho) ~ sigma s+ tau s+ rho.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau rho.
  bisimilar.

  Case "initial value".
  rewrite ->4 stream_sum_initial_value.
  exact (plus_assoc sigma(0) tau(0) rho(0)).

  Case "stream derivative".
  rewrite ->4 stream_sum_stream_derivative.
  exact (coIH (sigma`) (tau`) (rho`)).
Qed.
Hint Rewrite stream_sum_assoc : streamcalc.

(* {STREAM_SUM_O_R} *)
Lemma stream_sum_0_r :
  forall (sigma : Stream nat),
    sigma s+ #0 ~ sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intro sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_sum_initial_value.
  rewrite -> stream_constant_initial_value.
  exact (plus_0_r sigma(0)).

  Case "stream derivative".
  rewrite -> stream_sum_stream_derivative.
  exact (coIH (sigma`)).
Qed.
Hint Rewrite stream_sum_0_r : streamcalc.

(* {STREAM_SUM_O_L} *)
Lemma stream_sum_0_l :
  forall (sigma : Stream nat),
    #0 s+ sigma ~ sigma.
(* {END} *)
Proof.
  intro sigma.
  rewrite -> stream_sum_comm.
  exact (stream_sum_0_r sigma).
Qed.
Hint Rewrite stream_sum_0_l : streamcalc.

Lemma stream_sum_same_addend_r :
  forall (sigma tau rho : Stream nat),
    sigma ~ tau -> (sigma s+ rho) ~ (tau s+ rho).
Proof.
  pcofix coIH.
  intros sigma tau rho H_bisim_sigma_tau.
  bisimilar.

  Case "initial value".
  rewrite ->2 stream_sum_initial_value.
  rewrite -> H_bisim_sigma_tau.
  reflexivity.

  Case "stream derivative".
  rewrite ->2 stream_sum_stream_derivative.
  pdestruct H_bisim_sigma_tau;
    rewrite <- unfold_bisimilarity in R_stream_derivatives.
  exact (coIH (sigma`) (tau`) (rho`) R_stream_derivatives).
Qed.
Hint Rewrite stream_sum_same_addend_r : streamcalc.

Lemma stream_sum_same_addend_l :
  forall (sigma tau rho : Stream nat),
    sigma ~ tau -> (rho s+ sigma) ~ (rho s+ tau).
Proof.
  intros sigma tau rho H_bisim_sigma_tau.
  rewrite -> (stream_sum_comm rho sigma).
  rewrite -> (stream_sum_comm rho tau).
  exact (stream_sum_same_addend_r sigma tau rho H_bisim_sigma_tau).
Qed.
Hint Rewrite stream_sum_same_addend_l : streamcalc.

(* {STREAM_SUM_PERMUTE} *)
Lemma stream_sum_permute :
  forall (sigma tau rho : Stream nat),
    sigma s+ (tau s+ rho) ~ tau s+ (sigma s+ rho).
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau rho.
  bisimilar.

  Case "initial value".
  rewrite ->4 stream_sum_initial_value.
  rewrite -> plus_permute.
  reflexivity.

  Case "stream derivative".
  rewrite ->4 stream_sum_stream_derivative.
  exact (coIH (sigma`) (tau`) (rho`)).
Qed.
Hint Rewrite stream_sum_permute : streamcalc.

(** ** Stream product *)

(* {STREAM_PRODUCT_COMM} *)
Lemma stream_product_comm :
  forall (sigma tau : Stream nat),
    sigma s* tau ~ tau s* sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau.
  bisimilar.

  Case "initial value".
  rewrite ->2 stream_product_initial_value.
  exact (mult_comm sigma(0) tau(0)).

  Case "stream derivative".
  rewrite ->2 stream_product_stream_derivative.
  exact (coIH (sigma`) (tau`)).
Qed.
Hint Rewrite stream_product_comm : streamcalc.

(* {STREAM_PRODUCT_ASSOC} *)
Lemma stream_product_assoc :
  forall (sigma tau rho : Stream nat),
    sigma s* (tau s* rho) ~ sigma s* tau s* rho.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau rho.
  bisimilar.

  Case "initial value".
  rewrite ->4 stream_product_initial_value.
  exact (mult_assoc sigma(0) tau(0) rho(0)).

  Case "stream derivative".
  rewrite ->4 stream_product_stream_derivative.
  exact (coIH (sigma`) (tau`) (rho`)).
Qed.
Hint Rewrite stream_product_assoc : streamcalc.

(* {STREAM_PRODUCT_1_R} *)
Lemma stream_product_1_r :
  forall (sigma : Stream nat),
    sigma s* #1 ~ sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intro sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_product_initial_value.
  rewrite -> stream_constant_initial_value.
  exact (mult_1_r sigma(0)).

  Case "stream derivative".
  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH (sigma`)).
Qed.
Hint Rewrite stream_product_1_r : streamcalc.

(* {STREAM_PRODUCT_1_L} *)
Lemma stream_product_1_l :
  forall (sigma : Stream nat),
    #1 s* sigma ~ sigma.
(* {END} *)
Proof.
  intro sigma.
  rewrite -> stream_product_comm.
  exact (stream_product_1_r sigma).
Qed.
Hint Rewrite stream_product_1_l : streamcalc.

(* {STREAM_PRODUCT_0_R} *)
Lemma stream_product_0_r :
  forall (sigma : Stream nat),
    sigma s* #0 ~ #0.
(* {END} *)
Proof.
  pcofix coIH.
  intro sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_product_initial_value.
  rewrite -> stream_constant_initial_value.
  exact (mult_0_r sigma(0)).

  Case "stream derivative".
  rewrite -> stream_product_stream_derivative.
  exact (coIH (sigma`)).
Qed.
Hint Rewrite stream_product_0_r : streamcalc.

(* {STREAM_PRODUCT_0_L} *)
Lemma stream_product_0_l :
  forall (sigma : Stream nat),
    #0 s* sigma ~ #0.
(* {END} *)
Proof.
  intro sigma.
  rewrite -> stream_product_comm.
  exact (stream_product_0_r sigma).
Qed.
Hint Rewrite stream_product_0_l : streamcalc.

(* {STREAM_PRODUCT_DISTR_L} *)
Lemma stream_product_distr_l :
  forall (sigma tau rho : Stream nat),
    sigma s* (tau s+ rho) ~ (sigma s* tau) s+ (sigma s* rho).
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau rho.
  bisimilar.

  Case "initial value".
  rewrite -> stream_product_initial_value.
  rewrite -> stream_sum_initial_value.

  rewrite -> stream_sum_initial_value.
  rewrite -> stream_product_initial_value.
  rewrite -> stream_product_initial_value.
  exact (mult_plus_distr_l sigma(0) tau(0) rho(0)).

  Case "stream derivative".
  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_sum_stream_derivative.

  rewrite -> stream_sum_stream_derivative.
  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_product_stream_derivative.
  exact (coIH (sigma`) (tau`) (rho`)).
Qed.
Hint Rewrite stream_product_distr_l : streamcalc.

(* {STREAM_PRODUCT_DISTR_R} *)
Lemma stream_product_distr_r :
  forall (sigma tau rho : Stream nat),
    (sigma s+ tau) s* rho ~ sigma s* rho s+ tau s* rho.
(* {END} *)
Proof.
  intros sigma tau rho.
  rewrite -> (stream_product_comm (sigma s+ tau) rho).
  rewrite -> (stream_product_comm sigma rho).
  rewrite -> (stream_product_comm tau rho).
  exact (stream_product_distr_l rho sigma tau).
Qed.
Hint Rewrite stream_product_distr_r : streamcalc.

(* {STREAM_PRODUCT_PERMUTE} *)
Lemma stream_product_permute :
  forall (sigma tau rho : Stream nat),
    sigma s* (tau s* rho) ~ tau s* (sigma s* rho).
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau rho.
  bisimilar.

  Case "initial value".
  rewrite ->4 stream_product_initial_value.
  rewrite -> (mult_comm sigma(0) (tau(0) * rho(0))).
  rewrite <- mult_assoc.
  rewrite -> (mult_comm rho(0) sigma(0)).
  reflexivity.

  Case "stream derivative".
  rewrite ->4 stream_product_stream_derivative.
  exact (coIH (sigma`) (tau`) (rho`)).
Qed.
Hint Rewrite stream_product_permute : streamcalc.

(** ** Stream exponentiation *)

Lemma stream_exponentiation_1 :
  forall (sigma : Stream nat),
    sigma s^ 1 ~ sigma.
Proof.
  intros sigma.
  rewrite -> unfold_stream_exponentiation_induction_case.
  rewrite -> unfold_stream_exponentiation_base_case.
  rewrite -> stream_product_1_r.
  reflexivity.
Qed.
Hint Rewrite stream_exponentiation_1 : streamcalc.

(** ** Stream scalar multiplication *)

(* {STREAM_SCALAR_MULTIPLICATION_STREAM_COMM} *)
Lemma stream_scalar_multiplication_stream_comm :
  forall (k : nat) (sigma tau : Stream nat),
    k n* sigma s* tau ~ sigma s* (k n* tau).
(* {END} *)
Proof.
  pcofix coIH.
  intros k sigma tau.
  bisimilar.

  Case "initial value".
  rewrite -> stream_product_initial_value.
  rewrite -> stream_scalar_multiplication_initial_value.

  rewrite -> stream_product_initial_value.
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite -> (mult_comm k sigma(0)).
  rewrite <- mult_assoc.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_scalar_multiplication_stream_derivative.

  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_scalar_multiplication_stream_derivative.
  exact (coIH k sigma` tau`).
Qed.
Hint Rewrite stream_scalar_multiplication_stream_comm : streamcalc.

(* {STREAM_SCALAR_MULTIPLICATION_STREAM_ASSOC} *)
Lemma stream_scalar_multiplication_stream_assoc :
  forall (k : nat) (sigma tau : Stream nat),
    k n* (sigma s* tau) ~ k n* sigma s* tau.
(* {END} *)
Proof.
  pcofix coIH.
  intros k sigma tau.
  bisimilar.

  Case "initial value".
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite -> stream_product_initial_value.

  rewrite -> stream_product_initial_value.
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite <- mult_assoc.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_scalar_multiplication_stream_derivative.
  rewrite -> stream_product_stream_derivative.

  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_scalar_multiplication_stream_derivative.
  exact (coIH k sigma` tau`).
Qed.
Hint Rewrite stream_scalar_multiplication_stream_assoc : streamcalc.

(* {STREAM_SCALAR_MULTIPLICATION_1_L} *)
Lemma stream_scalar_multiplication_1_l :
  forall (sigma : Stream nat),
    1 n* sigma ~ sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intro sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite -> mult_1_l.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_scalar_multiplication_stream_derivative.
  exact (coIH sigma`).
Qed.
Hint Rewrite stream_scalar_multiplication_1_l : streamcalc.

(* {STREAM_SCALAR_MULTIPLICATION_0_L} *)
Lemma stream_scalar_multiplication_0_l :
  forall (sigma : Stream nat),
    0 n* sigma ~ #0.
(* {END} *)
Proof.
  pcofix coIH.
  intro sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite -> mult_0_l.
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_scalar_multiplication_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH sigma`).
Qed.
Hint Rewrite stream_scalar_multiplication_0_l : streamcalc.

(* {STREAM_SCALAR_MULTIPLICATION_SUM_DIST_L} *)
Lemma stream_scalar_multiplication_sum_dist_l :
  forall (k : nat) (sigma tau : Stream nat),
    k n* (sigma s+ tau) ~ (k n* sigma) s+ (k n* tau).
(* {END} *)
Proof.
  pcofix coIH.
  intros k sigma tau.
  bisimilar.

  Case "initial value".
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite -> stream_sum_initial_value.
  rewrite -> mult_plus_distr_l.

  rewrite -> stream_sum_initial_value.
  rewrite ->2 stream_scalar_multiplication_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_scalar_multiplication_stream_derivative.
  rewrite -> (stream_sum_stream_derivative (k n* sigma) (k n* tau)).
  exact (coIH k sigma` tau`).
Qed.
Hint Rewrite stream_scalar_multiplication_sum_dist_l : streamcalc.

(* {STREAM_SCALAR_MULTIPLICATION_PLUS_DIST_R} *)
Lemma stream_scalar_multiplication_plus_dist_r :
  forall (k l : nat) (sigma : Stream nat),
    (k + l) n* sigma ~ (k n* sigma) s+ (l n* sigma).
(* {END} *)
Proof.
  pcofix coIH.
  intros k l sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite -> mult_plus_distr_r.

  rewrite -> stream_sum_initial_value.
  rewrite ->2 stream_scalar_multiplication_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_scalar_multiplication_stream_derivative.

  rewrite -> stream_sum_stream_derivative.
  rewrite ->2 stream_scalar_multiplication_stream_derivative.
  exact (coIH k l sigma`).
Qed.
Hint Rewrite stream_scalar_multiplication_plus_dist_r : streamcalc.

(* {RELATION_BETWEEN_MULT_AND_STREAM_SCALAR_MULTIPLICATION} *)
Lemma relation_between_mult_and_stream_scalar_multiplication :
  forall (k l : nat) (sigma : Stream nat),
    (k * l) n* sigma ~ k n* (l n* sigma).
(* {END} *)
Proof.
  pcofix coIH.
  intros k l sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite ->2 stream_scalar_multiplication_initial_value.
  rewrite <- mult_assoc.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_scalar_multiplication_stream_derivative.

  rewrite ->2 stream_scalar_multiplication_stream_derivative.
  exact (coIH k l sigma`).
Qed.
Hint Rewrite relation_between_mult_and_stream_scalar_multiplication : streamcalc.

(* {STREAM_SCALAR_MULTIPLICATION_STREAM_PRODUCT_STREAM_CONSTANT} *)
Lemma stream_scalar_multiplication_stream_product_stream_constant :
  forall (k : nat) (sigma : Stream nat),
    (k n* sigma) ~ #k s* sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intros k sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_scalar_multiplication_initial_value.
  rewrite -> stream_product_initial_value.
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_scalar_multiplication_stream_derivative.
  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  exact (coIH k sigma`).
Qed.
Hint Rewrite stream_scalar_multiplication_stream_product_stream_constant : streamcalc.

(* {STREAM_SCALAR_MULTIPLICATION_SPLIT_STREAM_CONSTANT} *)
Corollary stream_scalar_multiplication_split_stream_constant :
  forall (k : nat),
    #k ~ k n* #1.
(* {END} *)
Proof.
  intro k.
  symmetry.
  rewrite <- (stream_product_1_r #k).
  exact (stream_scalar_multiplication_stream_product_stream_constant k #1).
Qed.
Hint Rewrite stream_scalar_multiplication_split_stream_constant : streamcalc.

(** ** Successive Powers

  *** Definition *)

(* {SUCCESSIVE_POWERS} *)
CoFixpoint successive_powers (b e : nat) : Stream nat :=
  (S b) ^ e ::: successive_powers (S b) e.
(* {END} *)
Hint Unfold successive_powers : streamcalc.

(** *** Unfolding lemmas *)

Lemma unfold_successive_powers :
  forall (b e : nat),
    successive_powers b e = (S b) ^ e ::: successive_powers (S b) e.
Proof.
  intros b e.
  rewrite -> (unfold_Stream (successive_powers b e)).
  unfold successive_powers; fold successive_powers.
  reflexivity.
Qed.
Hint Rewrite unfold_successive_powers : streamcalc.

Lemma successive_powers_initial_value :
  forall (b e : nat),
    (successive_powers b e)(0) = (S b) ^ e.
Proof.
  intros b e.
  rewrite -> initial_value.
  rewrite -> unfold_successive_powers.
  reflexivity.
Qed.
Hint Rewrite successive_powers_initial_value : streamcalc.

Lemma successive_powers_stream_derivative :
  forall (b e : nat),
    (successive_powers b e)` = successive_powers (S b) e.
Proof.
  intros b e.
  rewrite -> stream_derivative.
  rewrite -> unfold_successive_powers.
  reflexivity.
Qed.
Hint Rewrite successive_powers_stream_derivative : streamcalc.

(** *** Properties *)

Lemma Str_nth_successive_powers :
  forall (i b e : nat),
    Str_nth i (successive_powers b e) =
    S (i + b) ^ e.
Proof.
  induction i as [ | i' IH_i' ].

  Case "i = 0".
  intros b e.
  rewrite -> Str_nth_0.
  rewrite -> successive_powers_initial_value.
  rewrite -> plus_0_l.
  reflexivity.

  Case "i = S i'".
  intros b e.
  rewrite -> Str_nth_S_n.
  rewrite -> successive_powers_stream_derivative.
  rewrite -> (IH_i' (S b) e).
  rewrite <- plus_n_Sm.
  rewrite -> plus_Sn_m.
  reflexivity.
Qed.
Hint Rewrite Str_nth_successive_powers : streamcalc.

(** ** Stream partial sums acc *)

(* {STREAM_PARTIAL_SUMS_ACC_SUM_AUX} *)
Lemma stream_partial_sums_acc_sum_aux :
  forall (sigma tau : Stream nat) (a b i j : nat),
    stream_partial_sums_acc ((i + a) + (j + b)) (sigma s+ tau) ~
                     stream_partial_sums_acc (i + a) sigma s+
                     stream_partial_sums_acc (j + b) tau.
(* {END} *)
Proof.
  pcofix coIH.
  intros sigma tau a b i j.
  bisimilar.

  Case "initial value".
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> stream_sum_initial_value.

  rewrite -> stream_sum_initial_value.
  rewrite ->2 stream_partial_sums_acc_initial_value.

  rewrite <-4 plus_assoc.
  rewrite -> (plus_comm tau(0) (i + (a + (j + b)))).
  rewrite <-3 plus_assoc.
  rewrite -> (plus_comm tau(0) (j + b)).
  rewrite <- plus_assoc.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_sum_stream_derivative.
  rewrite -> (unfold_stream_partial_sums_acc (i + a + (j + b)) (sigma s+ tau)).
  rewrite -> (unfold_stream_partial_sums_acc (i + a) sigma).
  rewrite -> (unfold_stream_partial_sums_acc (j + b) tau).
  rewrite ->6 stream_derivative, <- 3 stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite -> stream_sum_initial_value.
  rewrite <-2 plus_assoc.

  rewrite -> (plus_permute (sigma(0)) i a).
  rewrite -> (plus_permute (tau(0)) j b).

  rewrite -> (plus_permute tau(0) i (a + (j + b))).
  rewrite -> (plus_permute tau(0) a (j + b)).
  rewrite -> (plus_permute tau(0) j b).

  rewrite -> (plus_permute sigma(0) i (a + _)).
  rewrite ->2 plus_assoc.
  rewrite <- (plus_assoc i sigma(0) a).
  exact (coIH (sigma`) (tau`) (sigma(0) + a) (tau(0) + b) i j).
Qed.
Hint Rewrite stream_partial_sums_acc_sum_aux : streamcalc.

(* {STREAM_PARTIAL_SUMS_ACC_SUM} *)
Lemma stream_partial_sums_acc_sum :
  forall (sigma tau : Stream nat),
    stream_partial_sums_acc 0 (sigma s+ tau) ~
    stream_partial_sums_acc 0 sigma s+ stream_partial_sums_acc 0 tau.
(* {END} *)
Proof.
  intros sigma tau.
  exact (stream_partial_sums_acc_sum_aux sigma tau 0 0 0 0).
Qed.
Hint Rewrite stream_partial_sums_acc_sum : streamcalc.

(* {STREAM_PARTIAL_SUMS_ACC_STREAM_CONSTANT_ASSOC} *)
Lemma stream_partial_sums_acc_stream_constant_assoc :
  forall (a n : nat) (sigma : Stream nat),
    stream_partial_sums_acc (#n(0) * a) (#n s* sigma) ~
    #n s* stream_partial_sums_acc a sigma.
(* {END} *)
Proof.
  pcofix coIH.
  intros a n sigma.
  bisimilar.

  Case "initial value".
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite ->2 stream_product_initial_value.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> mult_plus_distr_l.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> stream_product_initial_value.
  rewrite -> stream_product_stream_derivative.
  rewrite -> stream_constant_stream_derivative.
  rewrite <-  mult_plus_distr_l.
  exact (coIH (sigma(0) + a) n (sigma`)).
Qed.
Hint Rewrite stream_partial_sums_acc_stream_constant_assoc : streamcalc.

(* {STREAM_PARTIAL_SUMS_ACC_0} *)
Lemma stream_partial_sums_acc_0 :
  forall (a : nat), stream_partial_sums_acc a #0 ~ #a.
(* {END} *)
Proof.
  pcofix coIH.
  intro a.
  bisimilar.

  Case "initial value".
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite ->2 stream_constant_initial_value.
  rewrite -> plus_0_l.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> stream_constant_initial_value.
  rewrite -> plus_0_l.
  rewrite ->2 stream_constant_stream_derivative.
  exact (coIH a).
Qed.
Hint Rewrite stream_partial_sums_acc_0 : streamcalc.

(** ** Stream partial sums *)

(* {STREAM_PARTIAL_SUMS_SUM} *)
Lemma stream_partial_sums_sum :
  forall (sigma tau : Stream nat),
    stream_partial_sums (sigma s+ tau) ~
    (stream_partial_sums sigma) s+ (stream_partial_sums tau).
(* {END} *)
Proof.
  intros sigma tau.
  rewrite -> unfold_stream_partial_sums.
  exact (stream_partial_sums_acc_sum sigma tau).
Qed.
Hint Rewrite stream_partial_sums_sum : streamcalc.

(* {STREAM_PARTIAL_SUMS_STREAM_CONSTANT_ASSOC} *)
Lemma stream_partial_sums_stream_constant_assoc :
  forall (n : nat) (sigma : Stream nat),
    stream_partial_sums (#n s* sigma) ~ #n s* stream_partial_sums sigma.
(* {END} *)
Proof.
  intros n sigma.
  rewrite -> unfold_stream_partial_sums.

  assert (H_helper: stream_partial_sums_acc 0 (#n s* sigma) ~
                    stream_partial_sums_acc (#n(0) * 0) (#n s* sigma)).
    rewrite -> mult_0_r; reflexivity.
  rewrite -> H_helper; clear H_helper.

  exact (stream_partial_sums_acc_stream_constant_assoc 0 n sigma).
Qed.
Hint Rewrite stream_partial_sums_stream_constant_assoc : streamcalc.

(* {STREAM_PARTIAL_SUMS_ACC_STREAM_CONSTANT_PLUS_STREAM_PARTIAL_SUMS} *)
Lemma stream_partial_sums_acc_stream_constant_plus_stream_partial_sums :
  forall (a : nat) (sigma : Stream nat),
    stream_partial_sums_acc a sigma ~ #a s+ (stream_partial_sums sigma).
(* {END} *)
Proof.
  intros a sigma; apply Str_nth_implies_bisimilarity; intros n.
  revert a sigma; induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros a sigma.
  rewrite ->2 unfold_Str_nth.
  rewrite ->2 Str_nth_tl_initial_value_case_i_eq_0.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> stream_sum_initial_value.
  rewrite -> stream_partial_sums_initial_value.
  rewrite -> stream_constant_initial_value.
  rewrite -> plus_comm.
  reflexivity.

  Case "n = S n'".
  intros a sigma.
  rewrite ->2 unfold_Str_nth.
  rewrite ->2 Str_nth_tl_initial_value_case_i_gt_0.
  rewrite <-2 unfold_Str_nth.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> stream_sum_stream_derivative.
  rewrite -> stream_partial_sums_acc_stream_derivative_bisim_aux.
  rewrite -> stream_partial_sums_stream_derivative_bisim.
  unfold stream_sum.
  rewrite -> Str_nth_stream_zip.
  rewrite -> IH_n'.
  unfold stream_sum.
  rewrite ->3 Str_nth_stream_zip.
  rewrite <- plus_assoc.
  rewrite -> stream_constant_stream_derivative.
  reflexivity.
Qed.
Hint Rewrite stream_partial_sums_acc_stream_constant_plus_stream_partial_sums : streamcalc.

(* {STREAM_PARTIAL_SUMS_0} *)
Lemma stream_partial_sums_0 :
  stream_partial_sums #0 ~ #0.
(* {END} *)
Proof.
  unfold stream_partial_sums.
  pcofix coIH.
  bisimilar.

  Case "initial value".
  rewrite -> stream_constant_initial_value.
  rewrite -> stream_partial_sums_acc_initial_value.
  rewrite -> plus_0_r.
  rewrite -> stream_constant_initial_value.
  reflexivity.

  Case "stream derivative".
  rewrite -> stream_constant_stream_derivative.
  rewrite -> stream_partial_sums_acc_stream_derivative.
  rewrite -> plus_0_r.
  rewrite -> stream_constant_stream_derivative.
  exact coIH.
Qed.
Hint Rewrite stream_partial_sums_0 : streamcalc.
