(* PascalsTriangle.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * Pascal's triangle *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.

(* Own modules *)
Require Import Cases.
Require Import BinomialCoefficients.

(** * Pascal's triangle *)

(** ** Entry

  An [Entry] is an entry in a triangle, e.g. Pascal's or Long's, having arguments:
  [row], [column], [value]. *)

(* {ENTRY} *)
Inductive Entry : Type :=
  | entry : nat -> nat -> nat -> Entry.
(* {END} *)
Hint Constructors Entry : pascal.

(** ** Pascal

  A formalization of the entries of Pascal's triangle.

 *** Definition *)

(* {PASCAL} *)
Inductive Pascal : Entry -> Prop :=
| pascal_base_n_0 : forall (n : nat), (Pascal (entry n 0 1))
| pascal_base_n_n : forall (n : nat), 0 < n -> (Pascal (entry n n 1))
| pascal_base_n_lt_k : forall (n k : nat), n < k -> (Pascal (entry n k 0))
| pascal_inductive_S_n' : forall (n' k' r'' r' r : nat),
                 r = r'' + r' ->
                 (Pascal (entry n' k' r'')) ->
                 (Pascal (entry n' (S k') r')) ->
                 (Pascal (entry (S n') (S k') r)).
(* {END} *)
Hint Constructors Pascal : pascal.

(*
(* {PASCAL_BASE_CASES} *)
| pascal_base_n_0 : forall (n : nat), (Pascal (entry n 0 1))
| pascal_base_n_n : forall (n : nat), 0 < n -> (Pascal (entry n n 1))
| pascal_base_n_lt_k : forall (n k : nat), n < k -> (Pascal (entry n k 0))
(* {END} *)
*)

(*
(* {PASCAL_INDUCTIVE_CASE} *)
| pascal_inductive_S_n' : forall (n' k' r'' r' r : nat),
                 r = r'' + r' ->
                 (Pascal (entry n' k' r'')) ->
                 (Pascal (entry n' (S k') r')) ->
                 (Pascal (entry (S n') (S k') r)).
(* {END} *)
*)

(* *** Equivalence of [binomial_coefficient] and [Pascal] *)

(* {BINOMIAL_COEFFICIENT_IMPLIES_PASCAL} *)
Lemma binomial_coefficient_implies_Pascal :
  forall (n k v : nat),
    v = C(n, k) -> Pascal (entry n k v).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  case k as [ | k' ].

  SCase "k = 0".
  intros v H; rewrite -> H; clear H v.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  exact (pascal_base_n_0 0).

  SCase "k = S k'".
  intros v H; rewrite -> H; clear H v.
  rewrite -> unfold_binomial_coefficient_base_case_0_S_k'.
  exact (pascal_base_n_lt_k 0 (S k') (lt_0_Sn k')).

  Case "n = S n'".
  case k as [ | k' ].

  SCase "k = 0".
  intros v H; rewrite -> H; clear H v.
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  exact (pascal_base_n_0 (S n')).

  SCase "k = S k'".
  intros v H; rewrite -> H; clear H v.
  rewrite -> unfold_binomial_coefficient_induction_case_S_n'_S_k'.
  apply (pascal_inductive_S_n' n' k'
                               (binomial_coefficient n' k')
                               (binomial_coefficient n' (S k'))).

  SSCase "r = r'' + r'".
  rewrite -> plus_comm.
  reflexivity.

  SSCase "(Pascal (entry n' k' r''))".
  apply (IH_n' k' (binomial_coefficient n' k')).
  reflexivity.

  SSCase "(Pascal (entry (S n') (S k') r))".
  apply (IH_n' (S k') (binomial_coefficient n' (S k'))).
  reflexivity.
Qed.
Hint Resolve binomial_coefficient_implies_Pascal : pascal.

(* {PASCAL_IMPLIES_BINOMIAL_COEFFICIENT} *)
Lemma Pascal_implies_binomial_coefficient :
  forall (n k v : nat),
    Pascal (entry n k v) -> v = C(n, k).
(* {END} *)
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intros k v H_Pascal_0_k_v.
  inversion_clear H_Pascal_0_k_v.

  SCase "1 = C(0, 0)".
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  reflexivity.

  SCase "1 = C(0, 0)".
  rename H into H_absurd.
  inversion H_absurd.

  SCase "0 = C(0, k)".
  rename H into H_0_lt_k.
  rewrite -> (binomial_coefficient_n_lt_k_implies_0 0 k H_0_lt_k).
  reflexivity.

  Case "n = S n'".
  intros k v H_Pascal_S_n'_k_v.
  inversion_clear H_Pascal_S_n'_k_v.

  SCase "1 = C(S n', 0)".
  rewrite -> unfold_binomial_coefficient_base_case_n_0.
  reflexivity.

  SCase "1 = C(S n', S n')".
  rewrite -> binomial_coefficient_n_eq_k_implies_1.
  reflexivity.

  SCase "0 = C(S n', k)".
  rename H into H_S_n'_lt_k.
  rewrite -> (binomial_coefficient_n_lt_k_implies_0 (S n') k H_S_n'_lt_k).
  reflexivity.

  SCase "v = C(S n', S k')".
  rename H0 into H_Pascal_n'_k'_r'', H1 into H_Pascal_n'_S_k'_r';
    rewrite -> H; clear H v.
  rewrite -> unfold_binomial_coefficient_induction_case_S_n'_S_k'.
  rewrite -> (IH_n' k' r'' H_Pascal_n'_k'_r'').
  rewrite -> (IH_n' (S k') r' H_Pascal_n'_S_k'_r').
  rewrite -> plus_comm.
  reflexivity.
Qed.
Hint Resolve Pascal_implies_binomial_coefficient : pascal.

(* {PASCAL_IFF_BINOMIAL_COEFFICIENT} *)
Theorem Pascal_iff_binomial_coefficient :
  forall (n k v : nat),
    Pascal (entry n k v) <-> v = C(n, k).
(* {END} *)
Proof.
  intros n k v.
  split.

  Case "Pascal (entry n k v) -> v = C(n, k)".
  exact (Pascal_implies_binomial_coefficient n k v).

  Case "v = C(n, k) -> Pascal (entry n k v)".
  exact (binomial_coefficient_implies_Pascal n k v).
Qed.
Hint Resolve Pascal_iff_binomial_coefficient : pascal.

(* {PASCAL_IS_SYMMETRIC} *)
Theorem Pascal_is_symmetric :
  forall (n k v : nat),
    k <= n ->
    (Pascal (entry n k v) <->
     Pascal (entry n (n - k) v)).
(* {END} *)
Proof.
  intros n k v H_k_le_n.
  split.

  Case "->".
  intro H_Pascal_n_k_v.
  rewrite -> (Pascal_iff_binomial_coefficient n (n - k) v).
  rewrite -> (Pascal_iff_binomial_coefficient n k v) in H_Pascal_n_k_v.
  rewrite -> H_Pascal_n_k_v; clear H_Pascal_n_k_v v.
  exact (binomial_coefficient_is_symmetric n k H_k_le_n).

  Case "<-".
  intro H_Pascal_n_nk_v.
  rewrite -> (Pascal_iff_binomial_coefficient n k v).
  rewrite -> (Pascal_iff_binomial_coefficient n (n - k) v) in H_Pascal_n_nk_v.
  rewrite -> H_Pascal_n_nk_v; clear H_Pascal_n_nk_v v.
  symmetry.
  exact (binomial_coefficient_is_symmetric n k H_k_le_n).
Qed.
Hint Resolve Pascal_is_symmetric : pascal.

(* {PASCAL_IS_SYMMETRIC_ALT} *)
Theorem Pascal_is_symmetric_alt :
  forall (n k v : nat),
    Pascal (entry (n + k) n v) <->
    Pascal (entry (k + n) k v).
(* {END} *)
Proof.
  intros n k v.
  split.

  Case "->".
  intro H_Pascal_nk_n_v.
  rewrite -> (Pascal_iff_binomial_coefficient (k + n) k v).
  rewrite -> (Pascal_iff_binomial_coefficient (n + k) n v) in H_Pascal_nk_n_v.
  rewrite -> H_Pascal_nk_n_v; clear H_Pascal_nk_n_v v.
  exact (binomial_coefficient_is_symmetric_alt n k).

  Case "<-".
  intro H_Pascal_nk_k_v.
  rewrite -> (Pascal_iff_binomial_coefficient (n + k) n v).
  rewrite -> (Pascal_iff_binomial_coefficient (k + n) k v) in H_Pascal_nk_k_v.
  rewrite -> H_Pascal_nk_k_v; clear H_Pascal_nk_k_v v.
  symmetry.
  exact (binomial_coefficient_is_symmetric_alt n k).
Qed.
Hint Resolve Pascal_is_symmetric_alt : pascal.

(** ** Rotated Pascal

  *** Definition *)

(* {ROTATED_PASCAL} *)
Inductive Rotated_Pascal : Entry -> Prop :=
| rotated_pascal_base_r_0 :
    forall (r : nat), (Rotated_Pascal (entry r 0 1))
| rotated_pascal_base_0_c :
    forall (c : nat), 0 < c -> (Rotated_Pascal (entry 0 c 1))
| rotated_pascal_induction_r_c :
    forall (r' c' v'' v' v : nat),
      v = v'' + v' ->
      (Rotated_Pascal (entry (S r') c' v'')) ->
      (Rotated_Pascal (entry r' (S c') v'))  ->
      (Rotated_Pascal (entry (S r') (S c') v)).
(* {END} *)
Hint Constructors Rotated_Pascal : pascal.

(** *** Equivalence of Rotated binomial coefficient and Pascal triangle *)

(* {ROTATED_BINOMIAL_COEFFICIENT_IMPLIES_ROTATED_PASCAL} *)
Lemma rotated_binomial_coefficient_implies_Rotated_Pascal :
  forall (r c v : nat),
    v = R(r,c) -> Rotated_Pascal (entry r c v).
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  case c as [ | c' ].

  SCase "c = 0".
  intros v H; rewrite -> H; clear H v.
  exact (rotated_pascal_base_r_0 0).

  SCase "c = S c'".
  intros v H; rewrite -> H; clear H v.
  exact (rotated_pascal_base_0_c (S c') (lt_0_Sn c')).

  Case "r = S r'".
  induction c as [ | c' IH_c' ].

  SCase "c = 0".
  intros v H; rewrite -> H; clear H v.
  rewrite -> unfold_rotated_binomial_coefficient.
  rewrite -> plus_0_l.
  rewrite -> binomial_coefficient_n_eq_k_implies_1.
  exact (rotated_pascal_base_r_0 (S r')).

  SCase "c = S c'".
  intros v H; rewrite -> H; clear H v.
  apply (rotated_pascal_induction_r_c r' c'
                                      R(S r', c')
                                      R(r', S c')
                                      R(S r', S c')).

  SSCase "R(S r', S c') = R(S r', c') + R(r', S c')".
  rewrite -> unfold_rotated_binomial_coefficient_induction_case_S_r'_S_c'.
  reflexivity.

  SSCase "Rotated_Pascal (entry (S r') c' R(S r', c')".
  apply (IH_c' (R(S r', c'))).
  reflexivity.

  SSCase "Rotated_Pascal (entry r' (S c') R(r', S c'))".
  apply (IH_r' (S c') R(r', S c')).
  reflexivity.
Qed.
Hint Resolve rotated_binomial_coefficient_implies_Rotated_Pascal : pascal.

(* {ROTATED_PASCAL_IMPLIES_ROTATED_BINOMIAL_COEFFICIENT} *)
Lemma Rotated_Pascal_implies_rotated_binomial_coefficient :
  forall (r c v : nat),
    Rotated_Pascal (entry r c v) -> v = R(r, c).
(* {END} *)
Proof.
  induction r as [ | r' IH_r' ].

  Case "r = 0".
  intros c v H_Rotated_Pascal_0_c_v.
  inversion_clear H_Rotated_Pascal_0_c_v.

  SCase "1 = R(0, 0)".
  rewrite -> unfold_rotated_binomial_coefficient_base_case_r_0.
  reflexivity.

  SCase "1 = R(0, c)".
  inversion_clear H.

  SSCase "1 = R(0, 1)".
  rewrite -> (unfold_rotated_binomial_coefficient_base_case_0_c
                1 (lt_0_Sn 0)).
  reflexivity.

  SSCase "1 = R(0 (S c')".
  rename m into c'.
  rewrite -> (unfold_rotated_binomial_coefficient_base_case_0_c
                (S c') (lt_0_Sn c')).
  reflexivity.

  Case "r = S r'".
  induction c as [ | c' IH_c' ].

  SCase "c = 0".
  intros v H_Rotated_Pascal_S_r'_0.
  inversion_clear H_Rotated_Pascal_S_r'_0.
  rewrite -> unfold_rotated_binomial_coefficient_base_case_r_0.
  reflexivity.

  SCase "c = S c'".
  intros v H_Rotated_Pascal_S_r'_S_c'_v.
  inversion_clear H_Rotated_Pascal_S_r'_S_c'_v;
  rename H0 into H_Rotated_Pascal_S_r'_c'_v'',
         H1 into H_Rotated_Pascal_r'_S_c'_v';
    rewrite -> H; clear H v.
  rewrite -> (IH_r' (S c') v' H_Rotated_Pascal_r'_S_c'_v').
  rewrite -> (IH_c' v'' H_Rotated_Pascal_S_r'_c'_v'').
  rewrite -> unfold_rotated_binomial_coefficient_induction_case_S_r'_S_c'.
  reflexivity.
Qed.
Hint Resolve Rotated_Pascal_implies_rotated_binomial_coefficient : pascal.

(* {ROTATED_PASCAL_IFF_ROTATED_BINOMIAL_COEFFICIENT} *)
Theorem Rotated_Pascal_iff_rotated_binomial_coefficient :
  forall (r c v : nat),
    Rotated_Pascal (entry r c v) <-> v = R(r, c).
(* {END} *)
Proof.
  intros r c v.
  split.

  Case "Rotated_Pascal (entry r c v) -> v = R(r, c)".
  exact (Rotated_Pascal_implies_rotated_binomial_coefficient r c v).

  Case "v = R(r, c) -> Rotated_Pascal (entry r c v)".
  exact (rotated_binomial_coefficient_implies_Rotated_Pascal r c v).
Qed.
Hint Resolve Rotated_Pascal_implies_rotated_binomial_coefficient : pascal.

(* {ROTATED_PASCAL_IS_SYMMETRIC} *)
Theorem Rotated_Pascal_is_symmetric :
  forall (r c v : nat),
    Rotated_Pascal (entry r c v) <->
    Rotated_Pascal (entry c r v).
(* {END} *)
Proof.
  intros r c v.
  split.

  Case "->".
  intro H_Rotated_Pascal_r_c_v.
  rewrite -> (Rotated_Pascal_iff_rotated_binomial_coefficient c r v).
  rewrite -> (Rotated_Pascal_iff_rotated_binomial_coefficient r c v)
    in H_Rotated_Pascal_r_c_v.
  rewrite -> H_Rotated_Pascal_r_c_v; clear H_Rotated_Pascal_r_c_v.
  exact (rotated_binomial_coefficient_is_symmetric r c).

  Case "<-".
  intro H_Rotated_Pascal_c_r_v.
  rewrite -> (Rotated_Pascal_iff_rotated_binomial_coefficient r c v).
  rewrite -> (Rotated_Pascal_iff_rotated_binomial_coefficient c r v)
    in H_Rotated_Pascal_c_r_v.
  rewrite -> H_Rotated_Pascal_c_r_v; clear H_Rotated_Pascal_c_r_v.
  exact (rotated_binomial_coefficient_is_symmetric c r).
Qed.
Hint Resolve Rotated_Pascal_is_symmetric : pascal.

(** *** Equivalence of Rotated Pascal and Pascal *)

(* {ROTATED_PASCAL_IMPLIES_PASCAL} *)
Corollary Rotated_Pascal_implies_Pascal :
  forall (r c v : nat),
    Rotated_Pascal (entry r c v) ->
    Pascal (entry (r + c) c v).
(* {END} *)
Proof.
  intros r c v H_Rotated_Pascal.
  apply (binomial_coefficient_implies_Pascal (r + c) c v).
  rewrite <- unfold_rotated_binomial_coefficient.
  rewrite -> rotated_binomial_coefficient_is_symmetric.
  apply (Rotated_Pascal_implies_rotated_binomial_coefficient r c v).
  exact H_Rotated_Pascal.
Qed.
Hint Resolve Rotated_Pascal_implies_Pascal : pascal.

(* {PASCAL_IMPLIES_ROTATED_PASCAL} *)
Corollary Pascal_implies_Rotated_Pascal :
  forall (n k v : nat),
    Pascal (entry (n + k) k v) ->
    Rotated_Pascal (entry n k v).
(* {END} *)
Proof.
  intros n k v H_Pascal.
  apply (rotated_binomial_coefficient_implies_Rotated_Pascal n k v).
  rewrite -> rotated_binomial_coefficient_is_symmetric.
  rewrite -> unfold_rotated_binomial_coefficient.
  apply (Pascal_implies_binomial_coefficient (n + k) k v).
  exact H_Pascal.
Qed.
Hint Resolve Pascal_implies_Rotated_Pascal : pascal.

(* {ROTATED_PASCAL_IFF_PASCAL} *)
Theorem Rotated_Pascal_iff_Pascal :
  forall (n k v : nat),
    Rotated_Pascal (entry n k v) <->
    Pascal (entry (n + k) k v).
(* {END} *)
Proof.
  intros n k v.
  split.

  Case "->".
  exact (Rotated_Pascal_implies_Pascal n k v).

  Case "<-".
  exact (Pascal_implies_Rotated_Pascal n k v).
Qed.
Hint Resolve Rotated_Pascal_iff_Pascal : pascal.