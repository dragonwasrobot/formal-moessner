(* Power.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Power *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.

(* Own modules *)
Require Import Cases.

(** ** Preliminary *)

(*
(* {NATS} *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.
(* {END} *)
*)

(*
(* {NAT_RECT} *)
nat_rect : forall P : nat -> Type,
  P O ->
  (forall (n : nat), P n -> P (S n)) ->
  (forall (n : nat), P n).
(* {END} *)
*)

(*
(* {EQ} *)
Inductive eq (A : Type) (x : A) : A -> Prop :=
| eq_refl : x = x
(* {END} *)
*)

(** ** Power

  *** Definition *)

(* {POWER} *)
Fixpoint power (e b : nat) : nat :=
  match e with
    | O => 1
    | S e' => b * (b ^ e')
  end
  where "b ^ e" := (power e b).
(* {END} *)
Hint Unfold power : power.

(** *** Unfolding lemmas *)

(* {UNFOLD_POWER_BASE_CASE} *)
Lemma unfold_power_base_case :
  forall b : nat,
    b ^ 0 = 1.
(* {END} *)
Proof.
  intro b.
  unfold power.
  reflexivity.
Qed.
Hint Rewrite unfold_power_base_case : power.

(* {UNFOLD_POWER_INDUCTION_CASE} *)
Lemma unfold_power_induction_case :
  forall b e' : nat,
    b ^ (S e') = b * (b ^ e').
(* {END} *)
Proof.
  intros b e'.
  unfold power.
  reflexivity.
Qed.
Hint Rewrite unfold_power_induction_case : power.

(** *** Properties *)

Lemma power_b_1 :
  forall (b : nat),
    b ^ 1 = b.
Proof.
  intro b.
  rewrite -> unfold_power_induction_case.
  rewrite -> unfold_power_base_case.
  rewrite -> mult_1_r.
  reflexivity.
Qed.
Hint Rewrite power_b_1 : power.

Lemma power_1_e :
  forall (e : nat),
    1 ^ e = 1.
Proof.
  induction e as [ | e' IH_e' ].

  Case "e = 0".
  rewrite -> unfold_power_base_case.
  reflexivity.

  Case "e = S e'".
  rewrite -> unfold_power_induction_case.
  rewrite -> IH_e'.
  rewrite -> mult_1_l.
  reflexivity.
Qed.
Hint Rewrite power_1_e : power.

Lemma power_0_e :
  forall (e' : nat),
    0 ^ (S e') = 0.
Proof.
  intro e'.
  rewrite -> unfold_power_induction_case.
  rewrite -> mult_0_l.
  reflexivity.
Qed.
Hint Rewrite power_0_e : power.

Lemma power_distributivity :
  forall (b e1 e2 : nat),
    b ^ (e1 + e2) = (b ^ e1) * (b ^ e2).
Proof.
  intro b.
  case e1 as [ | e1' ].

  Case "e1 = 0".
  case e2 as [ | e2' ].

  SCase "e2 = 0".
  rewrite -> plus_0_l.
  rewrite -> unfold_power_base_case.
  rewrite -> mult_1_r.
  reflexivity.

  SCase "e2 = S e2'".
  rewrite -> plus_0_l.
  rewrite -> unfold_power_induction_case.
  rewrite -> unfold_power_base_case.
  rewrite -> mult_1_l.
  reflexivity.

  Case "e1 = S e1'".
  induction e2 as [ | e2' IH_e2' ].

  SCase "e2 = 0".
  rewrite -> plus_0_r.
  rewrite -> unfold_power_induction_case.
  rewrite -> unfold_power_base_case.
  rewrite -> mult_1_r.
  reflexivity.

  SCase "e2 = S e2'".
  rewrite <- plus_n_Sm.
  rewrite -> unfold_power_induction_case.
  rewrite -> IH_e2'.
  rewrite ->2 unfold_power_induction_case.
  rewrite <-2 mult_assoc.
  rewrite -> mult_comm.
  rewrite <- mult_assoc.
  rewrite -> (mult_comm b (b ^ e2')).
  rewrite <- mult_assoc.
  reflexivity.
Qed.
Hint Rewrite power_distributivity : power.

Lemma power_e_identity :
  forall (b e1 e2 : nat),
    (b ^ e1) ^ e2 = b ^ (e1 * e2).
Proof.
  intro b.
  case e1 as [ | e1' ].

  Case "e1 = 0".
  case e2 as [ | e2' ].

  SCase "e2 = 0".
  rewrite -> mult_0_r.
  rewrite ->2 unfold_power_base_case.
  reflexivity.

  SCase "e2 = S e2'".
  rewrite -> mult_0_l.
  rewrite -> unfold_power_base_case.
  rewrite -> unfold_power_induction_case.
  rewrite -> power_1_e.
  rewrite -> mult_1_r.
  reflexivity.

  Case "e1 = S e1'".
  induction e2 as [ | e2' IH_e2' ].

  SCase "e2 = 0".
  rewrite -> mult_0_r.
  rewrite ->2 unfold_power_base_case.
  reflexivity.

  SCase "e2 = S e2'".
  rewrite -> mult_succ_r.
  rewrite -> power_distributivity.
  rewrite <- IH_e2'.
  rewrite <- mult_comm.
  rewrite <- unfold_power_induction_case.
  reflexivity.
Qed.
Hint Rewrite power_e_identity : power.

Lemma power_distribution_identity :
  forall (b1 b2 e : nat),
    (b1 * b2) ^ e = (b1 ^ e) * (b2 ^ e).
Proof.
  intros b1 b2.
  induction e as [ | e' IH_e' ].

  Case "e = 0".
  rewrite ->3 unfold_power_base_case.
  rewrite -> mult_1_r.
  reflexivity.

  Case "e = S e'".
  rewrite -> unfold_power_induction_case.
  rewrite -> IH_e'.
  rewrite ->2 unfold_power_induction_case.
  rewrite <-2 mult_assoc.
  rewrite -> (mult_comm b2 _).
  rewrite <- mult_assoc.
  rewrite -> (mult_comm b2 _).
  reflexivity.
Qed.
Hint Rewrite power_distribution_identity : power.