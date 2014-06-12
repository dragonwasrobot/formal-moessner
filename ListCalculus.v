(* ListCalculus.v *)
(* author: Peter Urbak *)
(* version: 2014-06-02 *)

(** * List calculus

  This module defines a small calculus over the [list nat] type with the
  following selectors:

  - [hd]
  - [tl]
  - [nth]
  - [last]
  - [removelast]
  - [app]
  - [length]
  - [rev]

  constructors:

  - [make_list]
  - [list_constant]
  - [list_successor]

  and operators:

  - [list_map]
  - [list_scalar_mult]
  - [list_exponentiation]
  - [list_zip]
  - [list_sum]
  - [list_product]
  - [list_partial_sums_acc]
  - [list_partial_sums]
*)

(** * Preliminaries *)

(** ** Requirements *)

(* Standard library *)
Require Import Arith.
Require Export List.
Export ListNotations. (* enable [ ] and [ a ; b ; c] notation *)

(* Own modules *)
Require Import Cases.
Require Export Power.

(** * List basics *)

(** ** List type *)

(** ** List

  *** Definition *)

(*
(* {LIST} *)
Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.
(* {END} *)

(* {NOTATION} *)
Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
(* {END} *)
*)

(** ** List selectors *)

(** ** Hd

  *** Definition *)

(*
(* {HD} *)
Definition hd {A : Type} (d : A) (xs : list A) :=
  match xs with
    | [] => d
    | x :: _ => x
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_list_head :
  forall (d : nat) (xs : list nat),
    hd d xs = match xs with
               | [] => d
               | x :: _ => x
              end.
Proof.
  intros d xs.
  unfold hd.
  reflexivity.
Qed.
Hint Rewrite unfold_list_head : listcalc.

(** ** Tl

  *** Definition *)

(*
(* {TL} *)
Definition tl {A : Type} (xs : list A) :=
  match xs with
    | [] => []
    | _ :: xs' => xs'
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_list_tail :
  forall (xs : list nat),
    tl xs = match xs with
              | [] => []
              | _ :: xs' => xs'
            end.
Proof.
  intro xs.
  unfold tl.
  reflexivity.
Qed.
Hint Rewrite unfold_list_tail : listcalc.

(** ** Nth

 *** Definition *)

(*
(* {NTH} *)
Fixpoint nth {A : Type} (n : nat) (xs: list A) (d : A) : A :=
  match n, xs with
    | O, x :: xs' => x
    | O, [] => d
    | S n', [] => d
    | S n', x :: xs => nth n' xs' d
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_nth_base_case_nil :
  forall (A : Type) (d : A),
    nth 0 [] d = d.
Proof.
  intros A d.
  unfold nth.
  reflexivity.
Qed.
Hint Rewrite unfold_nth_base_case_nil : listcalc.

Lemma unfold_nth_base_case_cons :
  forall (A : Type) (d x : A) (xs' : list A),
    nth 0 (x :: xs') d = x.
Proof.
  intros A d x xs'.
  unfold nth.
  reflexivity.
Qed.
Hint Rewrite unfold_nth_base_case_cons : listcalc.

Lemma unfold_nth_induction_case_nil :
  forall (A : Type) (n' : nat) (d : A),
    nth (S n') [] d = d.
Proof.
  intros A n' d.
  unfold nth.
  reflexivity.
Qed.
Hint Rewrite unfold_nth_induction_case_nil : listcalc.

Lemma unfold_nth_induction_case_cons :
  forall (A : Type) (n' : nat) (d x : A) (xs' : list A),
    nth (S n') (x :: xs') d = nth n' xs' d.
Proof.
  intros A n' d x xs'.
  unfold nth.
  reflexivity.
Qed.
Hint Rewrite unfold_nth_induction_case_cons : listcalc.

(** *** Properties *)

Lemma nth_n_nil :
  forall (A : Type) (n : nat) (d : A),
    nth n [] d = d.
Proof.
  intros A n d.
  case n as [ | n' ].

  Case "n = 0".
  rewrite -> unfold_nth_base_case_nil.
  reflexivity.

  Case "n = S n'".
  rewrite -> unfold_nth_induction_case_nil.
  reflexivity.
Qed.
Hint Rewrite nth_n_nil : listcalc.

(** ** Last

  *** Definition *)

(*
(* {LAST} *)
Fixpoint last {A : Type} (xs: list A) (d : A) : A :=
  match xs with
    | [] => d
    | [x] => x
    | x :: xs => last xs d
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_last_base_case_nil :
  forall (A : Type) (d : A),
    last [] d = d.
Proof.
  intros A d.
  unfold last.
  reflexivity.
Qed.
Hint Rewrite unfold_last_base_case_nil : listcalc.

Lemma unfold_last_base_case_cons :
  forall (A : Type) (x d : A),
    last [x] d = x.
Proof.
  intros A x d.
  unfold last.
  reflexivity.
Qed.
Hint Rewrite unfold_last_base_case_cons : listcalc.

Lemma unfold_last_induction_case :
  forall (A : Type) (x x' d : A) (xs'' : list A),
    last (x :: x' :: xs'') d = last (x' :: xs'') d.
Proof.
  intros A x x' d xs''.
  unfold last; fold last.
  reflexivity.
Qed.
Hint Rewrite unfold_last_induction_case : listcalc.

(** *** Properties *)

Lemma last_cons :
  forall (x d : nat) (xs' : list nat),
    length xs' > 0 ->
    last (x :: xs') d = last xs' d.
Proof.
  intros x d.
  case xs' as [ | x' xs'' ].

  Case "xs' = []".
  intro H_absurd; inversion H_absurd.

  Case "xs' = x' :: xs''".
  intros _.
  rewrite -> unfold_last_induction_case.
  reflexivity.
Qed.
Hint Resolve last_cons : listcalc.

(** ** Remove last

  *** Definition *)

(*
(* {REMOVELAST} *)
Fixpoint removelast {A : Type} (xs : list A) : list A :=
  match xs with
    | [] => []
    | [x] => []
    | x :: xs => x :: removelast xs
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_removelast_base_case_nil :
  forall (A : Type),
    removelast ([] : list A) = ([] : list A).
Proof.
  intro A.
  unfold removelast.
  reflexivity.
Qed.
Hint Rewrite unfold_removelast_base_case_nil : listcalc.

Lemma unfold_removelast_base_case_cons :
  forall (A : Type) (x : A),
    removelast [x] = [].
Proof.
  intros A x.
  unfold removelast.
  reflexivity.
Qed.
Hint Rewrite unfold_removelast_base_case_cons : listcalc.

Lemma unfold_removelast_induction_case :
  forall (A : Type) (x x' : A) (xs'' : list A),
    removelast (x :: x' :: xs'') = x :: removelast (x' :: xs'').
Proof.
  intros A x x' xs''.
  unfold removelast.
  reflexivity.
Qed.
Hint Rewrite unfold_removelast_induction_case : listcalc.

(** ** App

  *** Definition *)

(*
(* {APP} *)
Fixpoint app {A : Type} (xs ys : list A) : list A :=
  match xs with
    | [] => ys
    | x :: xs' => x :: app xs' ys
  end.
Infix "++" := app (right associativity, at level 60) : list_scope.
(* {END} *)
*)

(** ** Length

  *** Definition *)

(*
(* {LENGTH} *)
Fixpoint length {A : Type} (xs : list A) : nat :=
  match xs with
   | [] => O
   | _ :: xs' => S (length xs')
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_length_base_case :
  length ([] : list nat) = 0.
Proof.
  unfold length.
  reflexivity.
Qed.
Hint Rewrite unfold_length_base_case : listcalc.

Lemma unfold_length_induction_case :
  forall (x : nat) (xs' : list nat),
    length (x :: xs') = S (length xs').
Proof.
  intros x xs'.
  unfold length.
  reflexivity.
Qed.
Hint Rewrite unfold_length_induction_case : listcalc.

(** *** Properties *)

Lemma length_nil_0 :
  forall (xs : list nat),
    length xs = 0 ->
    xs = [].
Proof.
  case xs as [ | x xs' ].

  Case "xs = []".
  intro H_length_nil_eq_0.
  reflexivity.

  Case "xs = x :: xs'".
  intro H_absurd; inversion H_absurd.
Qed.
Hint Rewrite length_nil_0 : listcalc.

Lemma length_implies_last_index :
  forall (n d : nat) (xs : list nat),
    length xs = (S n) ->
    last xs d = nth n xs d.
Proof.
  induction n as [ | n' IH_n' ].

  Case "n = 0".
  intro d.
  case xs as [ | x xs' ].

  SCase "xs = []".
  intro H_absurd; inversion H_absurd.

  SCase "xs = x :: xs'".
  intro H_length_x_xs'_eq_1.
  rewrite -> unfold_nth_base_case_cons.
  inversion H_length_x_xs'_eq_1;
    rename H0 into H_length_xs'_eq_0.
  rewrite -> (length_nil_0 xs' H_length_xs'_eq_0).
  rewrite -> unfold_last_base_case_cons.
  reflexivity.

  Case "n = S n'".
  intro d.
  case xs as [ | x xs' ].

  SCase "xs = []".
  intro H_absurd; inversion H_absurd.

  SCase "xs = x :: xs'".
  intro H_length_x_xs'_eq_S_S_n'.
  rewrite -> unfold_nth_induction_case_cons.
  inversion H_length_x_xs'_eq_S_S_n';
   rename H0 into H_length_xs'_eq_S_n'.
  rewrite <- (IH_n' d xs' H_length_xs'_eq_S_n').
  rewrite -> last_cons;
    [ reflexivity | rewrite -> H_length_xs'_eq_S_n'; apply gt_Sn_O ].
Qed.
Hint Resolve length_implies_last_index : listcalc.

(** ** Rev

  ** Definition *)

(*
(* {REV} *)
Fixpoint rev {A : Type} (xs : list A) : list A :=
  match xs with
    | [] => []
    | x :: xs' => rev xs' ++ [x]
  end.
(* {END} *)
*)

(** *** Unfolding lemmas *)

Lemma unfold_rev_base_case :
  forall (A : Type),
    rev ([] : list A) = [].
Proof.
  intro A.
  unfold rev.
  reflexivity.
Qed.
Hint Rewrite unfold_rev_base_case : listcalc.

Lemma unfold_rev_induction_case :
  forall (A : Type) (x : A) (xs' : list A),
    rev (x :: xs') = rev xs' ++ [x].
Proof.
  intros A x xs'.
  unfold rev; fold rev.
  reflexivity.
Qed.
Hint Rewrite unfold_rev_induction_case : listcalc.

(** *** Properties *)

(* {NTH_REV_EQ_LAST} *)
Lemma nth_rev_eq_last :
  forall (xs : list nat) (d : nat),
    nth 0 (rev xs) d =
    last xs d.
(* {END} *)
Proof.
  induction xs as [ | x xs' IH_xs' ].

  Case "xs = []".
  intro d.
  rewrite -> unfold_last_base_case_nil.
  rewrite -> unfold_rev_base_case.
  rewrite -> unfold_nth_base_case_nil.
  reflexivity.

  Case "xs = x :: xs'".
  intro d.
  case xs' as [ | x' xs'' ].

  SCase "xs' = []".
  rewrite -> unfold_last_base_case_cons.
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_rev_base_case.
  rewrite -> app_nil_l.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.

  SCase "xs' = x' :: xs''".
  rewrite -> unfold_rev_induction_case.
  rewrite -> unfold_last_induction_case.
  rewrite <- (IH_xs' d).
  rewrite -> unfold_rev_induction_case.
  rewrite -> app_nth1;
    [ idtac |
      rewrite -> app_length;
        rewrite -> unfold_length_induction_case;
        rewrite -> unfold_length_base_case;
        rewrite -> plus_comm;
        apply lt_0_Sn ].
  reflexivity.
Qed.
Hint Rewrite nth_rev_eq_last : listcalc.

(** ** List constructors *)

(** ** Make list

  *** Definition *)

(* {MAKE_LIST} *)
Fixpoint make_list (n i : nat) (f : nat -> nat) : list nat :=
  match n with
    | 0 => []
    | S n' => i :: (make_list n' (f i) f)
  end.
(* {END} *)
Hint Unfold make_list : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_make_list_base_case :
  forall (i : nat) (f : nat -> nat),
    make_list 0 i f = [].
Proof.
  intros i f.
  unfold make_list.
  reflexivity.
Qed.
Hint Rewrite unfold_make_list_base_case : listcalc.

Lemma unfold_make_list_induction_case :
  forall (n' i : nat) (f : nat -> nat),
    make_list (S n') i f = i :: (make_list n' (f i) f).
Proof.
  intros n' i f.
  unfold make_list; fold make_list.
  reflexivity.
Qed.
Hint Rewrite unfold_make_list_induction_case : listcalc.

(** *** List constant

  *** Definition *)

(* {LIST_CONSTANT} *)
Definition list_constant (n c : nat) : list nat :=
  make_list n c (fun x : nat => x).
(* {END} *)
Hint Unfold list_constant : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_constant_base_case :
  forall (c : nat),
    list_constant 0 c = [].
Proof.
  intro c.
  unfold list_constant.
  rewrite -> unfold_make_list_base_case.
  reflexivity.
Qed.
Hint Rewrite unfold_list_constant_base_case : listcalc.

Lemma unfold_list_constant_induction_case :
  forall (c n' : nat),
    list_constant (S n') c = c :: (list_constant n' c).
Proof.
  intros c n'.
  unfold list_constant.
  rewrite -> unfold_make_list_induction_case.
  reflexivity.
Qed.
Hint Rewrite unfold_list_constant_induction_case : listcalc.

(** List successor *)

(* {LIST_SUCCESSOR} *)
Definition list_successor (n i : nat) : list nat :=
  make_list n i S.
(* {END} *)
Hint Unfold list_successor : listcalc.

Lemma unfold_list_successor_base_case :
  forall (i : nat),
    list_successor 0 i = [].
Proof.
  intro i.
  unfold list_successor.
  rewrite -> unfold_make_list_base_case.
  reflexivity.
Qed.
Hint Rewrite unfold_list_successor_base_case : listcalc.

Lemma unfold_list_successor_induction_case :
  forall (n' i : nat),
    list_successor (S n') i = i :: (list_successor n' (S i)).
Proof.
  intros n' i.
  unfold list_successor.
  rewrite -> unfold_make_list_induction_case.
  reflexivity.
Qed.
Hint Rewrite unfold_list_successor_induction_case : listcalc.

(** * List operators *)

(** ** List map

  *** Definition *)

(* {LIST_MAP} *)
Fixpoint list_map (f : nat -> nat) (xs : list nat) : list nat :=
  match xs with
    | [] => xs
    | x :: xs' => (f x) :: (list_map f xs')
  end.
(* {END} *)
Hint Unfold list_map : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_map_base_case :
  forall (f : nat -> nat),
    list_map f [] = [].
Proof.
  intro f.
  unfold list_map.
  reflexivity.
Qed.
Hint Rewrite unfold_list_map_base_case : listcalc.

Lemma unfold_list_map_induction_case :
  forall (x : nat) (xs' : list nat) (f : nat -> nat),
    list_map f (x :: xs') = (f x) :: (list_map f xs').
Proof.
  intros x xs' f.
  unfold list_map; fold list_map.
  reflexivity.
Qed.
Hint Rewrite unfold_list_map_induction_case : listcalc.

(** ** List scalar multiplication

  *** Definition *)

(* {LIST_SCALAR_MULTIPLICATION} *)
Definition list_scalar_multiplication (k : nat)
           (xs : list nat) : list nat :=
  list_map (mult k) xs.
Notation "k ls* xs" := (list_scalar_multiplication k xs)
                         (at level 40, left associativity).
(* {END} *)
Hint Unfold list_scalar_multiplication : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_scalar_multiplication :
  forall (k : nat) (xs : list nat),
    list_scalar_multiplication k xs = list_map (mult k) xs.
Proof.
  intros k xs.
  unfold list_scalar_multiplication.
  reflexivity.
Qed.
Hint Rewrite unfold_list_scalar_multiplication : listcalc.

Lemma unfold_list_scalar_multiplication_base_case :
  forall (k : nat),
    k ls* [] = [].
Proof.
  intro k.
  unfold list_scalar_multiplication.
  exact (unfold_list_map_base_case (mult k)).
Qed.
Hint Rewrite unfold_list_scalar_multiplication_base_case : listcalc.

Lemma unfold_list_scalar_multiplication_induction_case :
  forall (k x : nat) (xs' : list nat),
    k ls* (x :: xs') = (k * x) :: (k ls* xs').
Proof.
  intros k x xs'.
  unfold list_scalar_multiplication.
  exact (unfold_list_map_induction_case x xs' (mult k)).
Qed.
Hint Rewrite unfold_list_scalar_multiplication_induction_case : listcalc.

(** ** List exponentiation

  *** Definition *)

(* {LIST_EXPONENTIATION} *)
Definition list_exponentiation (n : nat) (xs : list nat) : list nat :=
  list_map (power n) xs.
Notation "xs l^ n" := (list_exponentiation n xs)
                        (at level 31, left associativity).
(* {END} *)
Hint Unfold list_exponentiation : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_exponentiation :
  forall (n : nat) (xs : list nat),
    list_exponentiation n xs = list_map (power n) xs.
Proof.
  intros n xs.
  unfold list_exponentiation.
  reflexivity.
Qed.
Hint Rewrite unfold_list_exponentiation : listcalc.

Lemma unfold_list_exponentiation_base_case :
  forall (n : nat),
    [] l^ n = [].
Proof.
  intro n.
  unfold list_exponentiation.
  rewrite -> unfold_list_map_base_case.
  reflexivity.
Qed.
Hint Rewrite unfold_list_exponentiation_base_case : listcalc.

Lemma unfold_list_exponentiation_induction_case :
  forall (n x : nat) (xs' : list nat),
    (x :: xs') l^ n = (x ^ n) :: (xs' l^ n).
Proof.
  intros n x xs'.
  unfold list_exponentiation.
  rewrite -> unfold_list_map_induction_case.
  reflexivity.
Qed.
Hint Rewrite unfold_list_exponentiation_induction_case : listcalc.

(** ** List zip

  *** Definition *)

(* {LIST_ZIP} *)
Fixpoint list_zip (f : nat -> nat -> nat)
         (xs ys : list nat) : list nat :=
  match xs, ys with
    | xs, [] => xs
    | [], ys => ys
    | x :: xs', y :: ys' => (f x y) :: (list_zip f xs' ys')
  end.
(* {END} *)
Hint Unfold list_zip : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_zip_base_case_nil :
  forall (f : nat -> nat -> nat),
    list_zip f [] [] = [].
Proof.
  intro f.
  unfold list_zip.
  reflexivity.
Qed.
Hint Rewrite unfold_list_zip_base_case_nil : listcalc.

Lemma unfold_list_zip_base_case_cons :
  forall (y : nat) (ys' : list nat) (f : nat -> nat -> nat),
    list_zip f [] (y :: ys') = (y :: ys').
Proof.
  intros y ys' f.
  unfold list_zip.
  reflexivity.
Qed.
Hint Rewrite unfold_list_zip_base_case_cons : listcalc.

Lemma unfold_list_zip_induction_case_nil :
  forall (x : nat) (xs' : list nat) (f : nat -> nat -> nat),
    list_zip f (x :: xs') [] = (x :: xs').
Proof.
  intros x xs' f.
  unfold list_zip.
  reflexivity.
Qed.
Hint Rewrite unfold_list_zip_induction_case_nil : listcalc.

Lemma unfold_list_zip_induction_case_cons :
  forall (x y : nat) (xs' ys' : list nat) (f : nat -> nat -> nat),
    list_zip f (x :: xs') (y :: ys') = (f x y) :: (list_zip f xs' ys').
Proof.
  intros x y xs' ys' f.
  unfold list_zip; fold list_zip.
  reflexivity.
Qed.
Hint Rewrite unfold_list_zip_induction_case_cons : listcalc.

(** ** List sum

  *** Definition *)

(* {LIST_SUM} *)
Definition list_sum (xs ys : list nat) : list nat :=
  list_zip plus xs ys.
Infix "l+" := list_sum (at level 50, left associativity).
(* {END} *)
Hint Unfold list_sum : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_sum :
  forall (xs ys : list nat),
    xs l+ ys = list_zip plus xs ys.
Proof.
  intros xs ys.
  unfold list_sum.
  reflexivity.
Qed.
Hint Rewrite unfold_list_sum : listcalc.

Lemma unfold_list_sum_base_case_nil :
  [] l+ [] = [].
Proof.
  unfold list_sum.
  exact (unfold_list_zip_base_case_nil plus).
Qed.
Hint Rewrite unfold_list_sum_base_case_nil : listcalc.

Lemma unfold_list_sum_base_case_cons :
  forall (y : nat) (ys' : list nat),
    [] l+ (y :: ys') = (y :: ys').
Proof.
  intros y ys'.
  unfold list_sum.
  exact (unfold_list_zip_base_case_cons y ys' plus).
Qed.
Hint Rewrite unfold_list_sum_base_case_cons : listcalc.

Lemma unfold_list_sum_induction_case_nil :
  forall (x : nat) (xs' : list nat),
    (x :: xs') l+ [] = (x :: xs').
Proof.
  intros x xs'.
  unfold list_sum.
  exact (unfold_list_zip_induction_case_nil x xs' plus).
Qed.
Hint Rewrite unfold_list_sum_induction_case_nil : listcalc.

Lemma unfold_list_sum_induction_case_cons :
  forall (x y : nat) (xs' ys' : list nat),
    (x :: xs') l+ (y :: ys') = (x + y) :: (xs' l+ ys').
Proof.
  intros x y xs' ys'.
  unfold list_sum.
  exact (unfold_list_zip_induction_case_cons x y xs' ys' plus).
Qed.
Hint Rewrite unfold_list_sum_induction_case_cons : listcalc.

(** ** List product

  *** Definition *)

(* {LIST_PRODUCT} *)
Definition list_product (xs ys : list nat) : list nat :=
  list_zip mult xs ys.
Infix "l*" := list_product (at level 40, left associativity).
(* {END} *)
Hint Unfold list_product : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_product :
  forall (xs ys : list nat),
    xs l* ys = list_zip mult xs ys.
Proof.
  intros xs ys.
  unfold list_product.
  reflexivity.
Qed.
Hint Rewrite unfold_list_product : listcalc.

Lemma unfold_list_product_base_case_nil :
  [] l* [] = [].
Proof.
  unfold list_product.
  exact (unfold_list_zip_base_case_nil mult).
Qed.
Hint Rewrite unfold_list_product_base_case_nil : listcalc.

Lemma unfold_list_product_base_case_cons :
  forall (y : nat) (ys' : list nat),
    [] l* (y :: ys') = (y :: ys').
Proof.
  intros y ys'.
  unfold list_product.
  exact (unfold_list_zip_base_case_cons y ys' mult).
Qed.
Hint Rewrite unfold_list_product_base_case_cons : listcalc.

Lemma unfold_list_product_induction_case_nil :
  forall (x : nat) (xs' : list nat),
    (x :: xs') l* [] = (x :: xs').
Proof.
  intros x xs'.
  unfold list_product.
  exact (unfold_list_zip_induction_case_nil x xs' mult).
Qed.
Hint Rewrite unfold_list_product_induction_case_nil : listcalc.

Lemma unfold_list_product_induction_case_cons :
  forall (x y : nat) (xs' ys' : list nat),
    (x :: xs') l* (y :: ys') = (x * y) :: (xs' l* ys').
Proof.
  intros x y xs' ys'.
  unfold list_product.
  exact (unfold_list_zip_induction_case_cons x y xs' ys' mult).
Qed.
Hint Rewrite unfold_list_product_induction_case_cons : listcalc.

(** ** List partial sums acc

  *** Definition *)

(* {LIST_PARTIAL_SUMS_ACC} *)
Fixpoint list_partial_sums_acc (a : nat) (xs : list nat) : list nat :=
  match xs with
    | [] => []
    | x :: xs' => (x + a) :: (list_partial_sums_acc (x + a) xs')
  end.
(* {END} *)
Hint Unfold list_partial_sums_acc : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_partial_sums_acc_base_case :
  forall (a : nat),
    list_partial_sums_acc a [] = [].
Proof.
  intro a.
  unfold list_partial_sums_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_list_partial_sums_acc_base_case : listcalc.

Lemma unfold_list_partial_sums_acc_induction_case :
  forall (a x : nat) (xs' : list nat),
    list_partial_sums_acc a (x :: xs') =
    (x + a) :: (list_partial_sums_acc (x + a) xs').
Proof.
  intros a x xs'.
  unfold list_partial_sums_acc; fold list_partial_sums_acc.
  reflexivity.
Qed.
Hint Rewrite unfold_list_partial_sums_acc_induction_case : listcalc.

(** *** Properties *)

Lemma nth_list_partial_sums_acc :
  forall (xs : list nat) (a d : nat),
    length xs > 0 ->
    nth 0 (list_partial_sums_acc a xs) d =
    (nth 0 xs d) + a.
Proof.
  induction xs as [ | x xs' IH_xs' ].

  Case "xs = []".
  intros a d H_absurd.
  inversion H_absurd.

  Case "xs = x :: xs'".
  intros a d H_length_x_xs'_gt_0.
  rewrite -> unfold_list_partial_sums_acc_induction_case.
  rewrite -> unfold_nth_base_case_cons.
  rewrite -> unfold_nth_base_case_cons.
  reflexivity.
Qed.
Hint Rewrite nth_list_partial_sums_acc : listcalc.

(** *** List partial sums

  *** Definition *)

(* {LIST_PARTIAL_SUMS} *)
Definition list_partial_sums (xs : list nat) : list nat :=
  list_partial_sums_acc 0 xs.
(* {END} *)
Hint Unfold list_partial_sums : listcalc.

(** *** Unfolding lemmas *)

Lemma unfold_list_partial_sums :
  forall (xs : list nat),
    list_partial_sums xs = list_partial_sums_acc 0 xs.
Proof.
  intro xs.
  unfold list_partial_sums.
  reflexivity.
Qed.
Hint Rewrite unfold_list_partial_sums : listcalc.

(** *** Properties *)

Lemma nth_list_partial_sums :
  forall (xs : list nat) (d : nat),
    length xs > 0 ->
    nth 0 (list_partial_sums xs) d =
    (nth 0 xs d).
Proof.
  intros xs d H_length_xs_gt_0.
  rewrite -> unfold_list_partial_sums.
  rewrite <- plus_0_r.
  exact (nth_list_partial_sums_acc xs 0 d H_length_xs_gt_0).
Qed.
Hint Rewrite nth_list_partial_sums : listcalc.