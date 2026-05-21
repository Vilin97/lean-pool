/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.RNS.CoRNalgebraCOrdFields
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Field.Basic

-- (* Copyright © 1998-2006
--  * Henk Barendregt
--  * Luís Cruz-Filipe
--  * Herman Geuvers
--  * Mariusz Giero
--  * Rik van Ginneken
--  * Dimitri Hendriks
--  * Sébastien Hinderer
--  * Bart Kirkels
--  * Pierre Letouzey
--  * Iris Loeb
--  * Lionel Mamane
--  * Milad Niqui
--  * Russell O’Connor
--  * Randy Pollack
--  * Nickolay V. Shmyrev
--  * Bas Spitters
--  * Dan Synek
--  * Freek Wiedijk
--  * Jan Zwanenburg
--  *
--  * This work is free software; you can redistribute it and/or modify
--  * it under the terms of the GNU General Public License as published by
--  * the Free Software Foundation; either version 2 of the License, or
--  * (at your option) any later version.
--  *
--  * This work is distributed in the hope that it will be useful,
--  * but WITHOUT ANY WARRANTY; without even the implied warranty of
--  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  * GNU General Public License for more details.
--  *
--  * You should have received a copy of the GNU General Public License along
--  * with this work; if not, write to the Free Software Foundation, Inc.,
--  * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
--  *)
-- Require Export CoRN.algebra.COrdFields.
-- From Coq Require Import Lia.

-- (** printing one_div_succ %\ensuremath{\frac1{\cdot+1}}% *)
-- (** printing Half %\ensuremath{\frac12}% #&frac12;# *)

-- (*---------------------------------*)
-- Section Properties_of_leEq.
-- (*---------------------------------*)

-- (**
-- ** Properties of [[<=]]
-- %\begin{convention}% Let [R] be an ordered field.
-- %\end{convention}%
-- *)
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

-- Variable R : COrdField.
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

-- Section addition.
-- (**
-- *** Addition and subtraction%\label{section:leEq-plus-minus}%
-- *)

-- Lemma plus_resp_leEq : forall x y z : R, x [<=] y -> x[+]z [<=] y[+]z.
-- Proof.
--  intros x y z.
--  do 2 rewrite -> leEq_def.
--  intros. intro.
--  apply H.
--  apply (plus_cancel_less _ _ _ _ X).
-- Qed.

lemma plus_resp_leEq (x y z : R) (h : x ≤ y) : x + z ≤ y + z :=
  add_le_add_right h z

-- Lemma plus_resp_leEq_lft : forall x y z : R, x [<=] y -> z[+]x [<=] z[+]y.
-- Proof.
--  intros.
--  astepl (x[+]z).
--  astepr (y[+]z).
--  apply plus_resp_leEq; auto.
-- Qed.

lemma plus_resp_leEq_lft (x y z : R) (h : x ≤ y) : z + x ≤ z + y :=
  add_le_add_left h z

-- Lemma minus_resp_leEq : forall x y z : R, x [<=] y -> x[-]z [<=] y[-]z.
-- Proof.
--  intros.
--  astepl (x[+][--]z).
--  astepr (y[+][--]z).
--  apply plus_resp_leEq; auto.
-- Qed.

lemma minus_resp_leEq (x y z : R) (h : x ≤ y) : x - z ≤ y - z :=
  tsub_le_tsub_right h z

-- Lemma inv_resp_leEq : forall x y : R, x [<=] y -> [--]y [<=] [--]x.
-- Proof.
--  intros x y.
--  repeat rewrite -> leEq_def.
--  do 2 intro.
--  apply H.
--  apply inv_cancel_less.
--  assumption.
-- Qed.

lemma inv_resp_leEq (x y : R) (h : x ≤ y) : -y ≤ -x :=
  neg_le_neg h

-- Lemma minus_resp_leEq_rht : forall x y z : R, y [<=] x -> z[-]x [<=] z[-]y.
-- Proof.
--  intros.
--  Transparent cg_minus.
--  unfold cg_minus in |- *.
--  apply plus_resp_leEq_lft.
--  apply inv_resp_leEq.
--  assumption.
-- Qed.

lemma minus_resp_leEq_rht (x y z : R) (h : y ≤ x) : z - x ≤ z - y := by {
  exact tsub_le_tsub_left h z
}

-- Lemma plus_resp_leEq_both : forall x y a b : R, x [<=] y -> a [<=] b -> x[+]a [<=] y[+]b.
-- Proof.
--  intros.
--  apply leEq_transitive with (y := x[+]b).
--   rstepl (a[+]x).
--   rstepr (b[+]x).
--   apply plus_resp_leEq.
--   assumption.
--  apply plus_resp_leEq.
--  assumption.
-- Qed.

lemma plus_resp_leEq_both (x y a b : R) (h₁ : x ≤ y) (h₂ : a ≤ b) : x + a ≤ y + b := by
  calc
    x + a ≤ x + b := by {exact plus_resp_leEq_lft a b x h₂}
        _ ≤ y + b := add_le_add_right h₁ b

-- Lemma plus_resp_less_leEq : forall a b c d : R, a [<] b -> c [<=] d -> a[+]c [<] b[+]d.
-- Proof.
--  intros.
--  apply leEq_less_trans with (a[+]d).
--   apply plus_resp_leEq_lft. auto.
--   apply plus_resp_less_rht. auto.
-- Qed.


lemma plus_resp_less_leEq (a b c d : R) (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d :=
  lt_of_le_of_lt (plus_resp_leEq_lft c d a h₂) (add_lt_add_right h₁ d)


-- Lemma plus_resp_leEq_less : forall a b c d : R, a [<=] b -> c [<] d -> a[+]c [<] b[+]d.
-- Proof.
--  intros.
--  astepl (c[+]a).
--  astepr (d[+]b).
--  apply plus_resp_less_leEq; auto.
-- Qed.

lemma plus_resp_leEq_less (a b c d : R) (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d :=
  lt_of_lt_of_le (add_lt_add_left h₂ a) (plus_resp_leEq a b d h₁)

-- Lemma plus_resp_nonneg : forall x y : R, [0] [<=] x -> [0] [<=] y -> [0] [<=] x[+]y.
-- Proof.
--  intros.
--  astepl ([0][+][0]:R).
--  apply plus_resp_leEq_both; auto.
-- Qed.

lemma plus_resp_nonneg (x y : R) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y :=
  Left.add_nonneg hx hy

-- Lemma minus_resp_less_leEq : forall x y x' y' : R, x [<=] y -> y' [<] x' -> x[-]x' [<] y[-]y'.
-- Proof.
--  intros.
--  astepl (x[+][--]x').
--  astepr (y[+][--]y').
--  apply plus_resp_leEq_less.
--   auto.
--  apply inv_resp_less. auto.
-- Qed.

lemma minus_resp_less_leEq (x y x' y' : R) (h₁ : x ≤ y) (h₂ : y' < x') : x - x' < y - y' := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact plus_resp_leEq_less x y (-x') (-y') h₁ (neg_lt_neg h₂)

-- Lemma minus_resp_leEq_both : forall x y x' y' : R, x [<=] y -> y' [<=] x' -> x[-]x' [<=] y[-]y'.
-- Proof.
--  intros.
--  astepl (x[+][--]x').
--  astepr (y[+][--]y').
--  apply plus_resp_leEq_both. auto.
--   apply inv_resp_leEq. auto.
-- Qed.

lemma minus_resp_leEq_both (x y x' y' : R) (h₁ : x ≤ y) (h₂ : y' ≤ x') : x - x' ≤ y - y' := by {
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact plus_resp_leEq_both x y (-x') (-y') h₁ (inv_resp_leEq y' x' h₂)}

-- (** Cancellation properties
-- *)

-- Lemma plus_cancel_leEq_rht : forall x y z : R, x[+]z [<=] y[+]z -> x [<=] y.
-- Proof.
--  intros.
--  rstepl (x[+]z[+][--]z).
--  rstepr (y[+]z[+][--]z).
--  apply plus_resp_leEq.
--  assumption.
-- Qed.

lemma plus_cancel_leEq_rht (x y z : R) (h : x + z ≤ y + z) : x ≤ y := by {
  simp_all only [add_le_add_iff_right]
}

-- Lemma inv_cancel_leEq : forall x y : R, [--]y [<=] [--]x -> x [<=] y.
-- Proof.
--  intros.
--  rstepl ([--][--]x).
--  rstepr ([--][--]y).
--  apply inv_resp_leEq.
--  assumption.
-- Qed.

lemma inv_cancel_leEq (x y : R) (h : -y ≤ -x) : x ≤ y :=
  neg_le_neg_iff.mp h

-- (** Laws for shifting
-- *)

-- Lemma shift_plus_leEq : forall a b c : R, a [<=] c[-]b -> a[+]b [<=] c.
-- Proof.
--  intros.
--  rstepr (c[-]b[+]b).
--  apply plus_resp_leEq.
--  assumption.
-- Qed.

lemma shift_plus_leEq (a b c : R) (h : a ≤ c - b) : a + b ≤ c := by
  rw [add_comm a b, ←sub_add_cancel c b]
  simp only [sub_add_cancel]
  exact le_sub_iff_add_le'.mp h

-- Lemma shift_leEq_plus : forall a b c : R, a[-]b [<=] c -> a [<=] c[+]b.
-- Proof.
--  intros.
--  rstepl (a[-]b[+]b).
--  apply plus_resp_leEq.
--  assumption.
-- Qed.

lemma shift_leEq_plus (a b c : R) (h : a - b ≤ c) : a ≤ c + b := by
  rw [←sub_add_cancel a b]
  exact add_le_add_right h b

-- Lemma shift_plus_leEq' : forall a b c : R, b [<=] c[-]a -> a[+]b [<=] c.
-- Proof.
--  intros.
--  rstepr (a[+] (c[-]a)).
--  apply plus_resp_leEq_lft.
--  assumption.
-- Qed.

lemma shift_plus_leEq' (a b c : R) (h : b ≤ c - a) : a + b ≤ c := by
  rw [add_comm a b, ←sub_add_cancel c a]
  exact plus_resp_leEq b (c - a) a h

-- Lemma shift_leEq_plus' : forall a b c : R, a[-]b [<=] c -> a [<=] b[+]c.
-- Proof.
--  intros.
--  rstepl (b[+] (a[-]b)).
--  apply plus_resp_leEq_lft. auto.
-- Qed.

lemma shift_leEq_plus' (a b c : R) (h : a - b ≤ c) : a ≤ b + c := by
  rw [←sub_add_cancel a b, add_comm b c]
  exact add_le_add_right h b

-- Lemma shift_leEq_rht : forall a b : R, [0] [<=] b[-]a -> a [<=] b.
-- Proof.
--  intros.
--  astepl ([0][+]a).
--  rstepr (b[-]a[+]a).
--  apply plus_resp_leEq. auto.
-- Qed.

lemma shift_leEq_rht (a b : R) (h : 0 ≤ b - a) : a ≤ b := by
  rw [←sub_add_cancel b a]
  exact le_add_of_nonneg_left h

-- Lemma shift_leEq_lft : forall a b : R, a [<=] b -> [0] [<=] b[-]a.
-- Proof.
--  intros.
--  astepl (a[-]a).
--  apply minus_resp_leEq. auto.
-- Qed.

lemma shift_leEq_lft (a b : R) (h : a ≤ b) : 0 ≤ b - a := by {
  exact sub_nonneg_of_le h
}

-- Lemma shift_minus_leEq : forall a b c : R, a [<=] c[+]b -> a[-]b [<=] c.
-- Proof.
--  intros.
--  rstepr (c[+]b[-]b).
--  apply minus_resp_leEq.
--  assumption.
-- Qed.

lemma shift_minus_leEq (a b c : R) (h : a ≤ c + b) : a - b ≤ c := by
  rw [sub_eq_add_neg, ←sub_add_cancel c b]
  simp_all only [sub_add_cancel, add_neg_le_iff_le_add]

-- Lemma shift_leEq_minus : forall a b c : R, a[+]c [<=] b -> a [<=] b[-]c.
-- Proof.
--  intros.
--  rstepl (a[+]c[-]c).
--  apply minus_resp_leEq.
--  assumption.
-- Qed.

lemma shift_leEq_minus (a b c : R) (h : a + c ≤ b) : a ≤ b - c :=
  le_tsub_of_add_le_right h

-- Lemma shift_leEq_minus' : forall a b c : R, c[+]a [<=] b -> a [<=] b[-]c.
-- Proof.
--  intros.
--  rstepl (c[+]a[-]c).
--  apply minus_resp_leEq.
--  assumption.
-- Qed.

lemma shift_leEq_minus' (a b c : R) (h : c + a ≤ b) : a ≤ b - c :=
  le_tsub_of_add_le_left h


-- Lemma shift_zero_leEq_minus : forall x y : R, x [<=] y -> [0] [<=] y[-]x.
-- Proof.
--  intros.
--  rstepl (x[-]x).
--  apply minus_resp_leEq.
--  assumption.
-- Qed.

lemma shift_zero_leEq_minus (x y : R) (h : x ≤ y) : 0 ≤ y - x :=
  sub_nonneg_of_le h

-- Lemma shift_zero_leEq_minus' : forall x y : R, [0] [<=] y[-]x -> x [<=] y.
-- Proof.
--  intros.
--  apply plus_cancel_leEq_rht with ([--]x).
--  rstepl ([0]:R).
--  assumption.
-- Qed.

lemma shift_zero_leEq_minus' (x y : R) (h : 0 ≤ y - x) : x ≤ y :=
  shift_leEq_rht x y h

-- End addition.

-- Section multiplication.
-- (**
-- *** Multiplication and division

-- Multiplication and division respect [[<=]]
-- *)

-- Lemma mult_resp_leEq_rht : forall x y z : R, x [<=] y -> [0] [<=] z -> x[*]z [<=] y[*]z.
-- Proof.
--  intros x y z .
--  repeat rewrite -> leEq_def.
--  intros H H0 H1.
--  generalize (shift_zero_less_minus _ _ _ H1); intro H2.
--  cut ([0] [<] (x[-]y) [*]z).
--   intro H3.
--   2: rstepr (x[*]z[-]y[*]z).
--   2: assumption.
--  cut (forall a b : R, [0] [<] a[*]b -> [0] [<] a and [0] [<] b or a [<] [0] and b [<] [0]).
--   intro H4.
--   generalize (H4 _ _ H3); intro H5.
--   elim H5; intro H6.
--    elim H6; intros.
--    elim H.
--    astepl ([0][+]y).
--    apply shift_plus_less.
--    assumption.
--   elim H6; intros.
--   elim H0.
--   assumption.
--  intros a b H4.
--  generalize (Greater_imp_ap _ _ _ H4); intro H5.
--  generalize (mult_cancel_ap_zero_lft _ _ _ H5); intro H6.
--  generalize (mult_cancel_ap_zero_rht _ _ _ H5); intro H7.
--  elim (ap_imp_less _ _ _ H6); intro H8.
--   right.
--   split.
--    assumption.
--   elim (ap_imp_less _ _ _ H7); intro H9.
--    assumption.
--   exfalso.
--   elim (less_irreflexive_unfolded R [0]).
--   apply less_leEq_trans with (a[*]b).
--    assumption.
--   apply less_leEq.
--   apply inv_cancel_less.
--   astepl ([0]:R).
--   astepr ([--]a[*]b).
--   apply mult_resp_pos.
--    astepl ([--]([0]:R)).
--    apply inv_resp_less.
--    assumption.
--   assumption.
--  left.
--  split.
--   assumption.
--  elim (ap_imp_less _ _ _ H7); intro H9.
--   exfalso.
--   elim (less_irreflexive_unfolded R [0]).
--   apply less_leEq_trans with (a[*]b).
--    assumption.
--   apply less_leEq.
--   apply inv_cancel_less.
--   astepl ([0]:R).
--   astepr (a[*][--]b).
--   apply mult_resp_pos.
--    assumption.
--   astepl ([--]([0]:R)).
--   apply inv_resp_less.
--   assumption.
--  assumption.
-- Qed.

lemma mult_resp_leEq_rht (x y z : R) (hxy : x ≤ y) (hz : 0 ≤ z) : x * z ≤ y * z :=
  mul_le_mul_of_nonneg_right hxy hz

-- Lemma mult_resp_leEq_lft : forall x y z : R, x [<=] y -> [0] [<=] z -> z[*]x [<=] z[*]y.
-- Proof.
--  intros.
--  astepl (x[*]z).
--  astepr (y[*]z).
--  apply mult_resp_leEq_rht.
--   assumption.
--  assumption.
-- Qed.

lemma mult_resp_leEq_lft (x y z : R) (hxy : x ≤ y) (hz : 0 ≤ z) : z * x ≤ z * y :=
  mul_le_mul_of_nonneg_left hxy hz

-- Lemma mult_resp_leEq_both : forall x x' y y' : R,
--  [0] [<=] x -> [0] [<=] y -> x [<=] x' -> y [<=] y' -> x[*]y [<=] x'[*]y'.
-- Proof.
--  intros.
--  apply leEq_transitive with (x[*]y').
--   apply mult_resp_leEq_lft; assumption.
--  apply mult_resp_leEq_rht.
--   assumption.
--  apply leEq_transitive with y; assumption.
-- Qed.

lemma mult_resp_leEq_both (x x' y y' : R)
  (hx : 0 ≤ x) (hy : 0 ≤ y) (hxx' : x ≤ x') (hyy' : y ≤ y') : x * y ≤ x' * y' :=
  calc
    x * y ≤ x * y'   := by {exact mult_resp_leEq_lft y y' x hyy' hx}
    _     ≤ x' * y'  := by {
      refine mult_resp_leEq_rht x x' y' hxx' ?_
      exact Preorder.le_trans 0 y y' hy hyy'
    }

-- Lemma recip_resp_leEq : forall (x y : R) x_ y_, [0] [<] y -> y [<=] x -> ([1][/] x[//]x_) [<=] ([1][/] y[//]y_).
-- Proof.
--  intros x y x_ y_ H.
--  do 2 rewrite -> leEq_def.
--  intros H0 H1. apply H0.
--  cut (([1][/] x[//]x_) [#] [0]). intro x'_.
--   cut (([1][/] y[//]y_) [#] [0]). intro y'_.
--    rstepl ([1][/] [1][/] x[//]x_[//]x'_).
--    rstepr ([1][/] [1][/] y[//]y_[//]y'_).
--    apply recip_resp_less.
--     apply recip_resp_pos; auto.
--    auto.
--   apply div_resp_ap_zero_rev. apply ring_non_triv.
--   apply div_resp_ap_zero_rev. apply ring_non_triv.
-- Qed.

-- Lemma recip_resp_leEq : forall (x y : R) x_ y_, [0] [<] y -> y [<=] x -> ([1][/] x[//]x_) [<=] ([1][/] y[//]y_).
-- Proof.
--  intros x y x_ y_ H.
--  do 2 rewrite -> leEq_def.
--  intros H0 H1. apply H0.
--  cut (([1][/] x[//]x_) [#] [0]). intro x'_.
--   cut (([1][/] y[//]y_) [#] [0]). intro y'_.
--    rstepl ([1][/] [1][/] x[//]x_[//]x'_).
--    rstepr ([1][/] [1][/] y[//]y_[//]y'_).
--    apply recip_resp_less.
--     apply recip_resp_pos; auto.
--    auto.
--   apply div_resp_ap_zero_rev. apply ring_non_triv.
--   apply div_resp_ap_zero_rev. apply ring_non_triv.
-- Qed.

lemma recip_resp_leEq (x y : R) (hy : 0 < y) (hxy : y ≤ x) : 1 / x ≤ 1 / y := by {
  simp only [one_div]
  exact inv_anti₀ hy hxy
}

-- Lemma div_resp_leEq : forall (x y z : R) z_, [0] [<] z -> x [<=] y -> (x[/] z[//]z_) [<=] (y[/] z[//]z_).
-- Proof.
--  intros.
--  rstepl (x[*] ([1][/] z[//]z_)).
--  rstepr (y[*] ([1][/] z[//]z_)).
--  apply mult_resp_leEq_rht.
--   assumption.
--  apply less_leEq.
--  apply recip_resp_pos.
--  auto.
-- Qed.

lemma div_resp_leEq (x y z : R) (hz : 0 < z) (hxy : x ≤ y) : x / z ≤ y / z :=
  (div_le_div_iff_of_pos_right hz).mpr hxy

-- Hint Resolve recip_resp_leEq: algebra.

-- (** Cancellation properties
-- *)

-- Lemma mult_cancel_leEq : forall x y z : R, [0] [<] z -> x[*]z [<=] y[*]z -> x [<=] y.
-- Proof.
--  intros x y z H.
--  do 2 rewrite -> leEq_def.
--  intros H0 H1.
--  apply H0.
--  apply mult_resp_less.
--   assumption.
--  assumption.
-- Qed.

lemma mult_cancel_leEq (x y z : R) (hz : 0 < z) (h : x * z ≤ y * z) : x ≤ y :=
  (mul_le_mul_right hz).mp h

-- (** Laws for shifting
-- *)

-- Lemma shift_mult_leEq : forall (x y z : R) z_, [0] [<] z -> x [<=] (y[/] z[//]z_) -> x[*]z [<=] y.
-- Proof.
--  intros.
--  rstepr ((y[/] z[//]z_) [*]z).
--  apply mult_resp_leEq_rht; [ assumption | apply less_leEq; assumption ].
-- Qed.

lemma shift_mult_leEq (x y z : R) (hz : 0 < z) (h : x ≤ y / z) : x * z ≤ y := by
  rw [mul_comm x z]
  exact (le_div_iff₀' hz).mp h

-- Lemma shift_mult_leEq' : forall (x y z : R) z_, [0] [<] z -> x [<=] (y[/] z[//]z_) -> z[*]x [<=] y.
-- Proof.
--  intros.
--  rstepr (z[*] (y[/] z[//]z_)).
--  apply mult_resp_leEq_lft; [ assumption | apply less_leEq; assumption ].
-- Qed.

lemma shift_mult_leEq' (x y z : R) (hz : 0 < z) (h : x ≤ y / z) : z * x ≤ y := by
  rw [mul_comm z x]
  exact shift_mult_leEq x y z hz h

-- Lemma shift_leEq_mult' : forall (x y z : R) y_, [0] [<] y -> (x[/] y[//]y_) [<=] z -> x [<=] y[*]z.
-- Proof.
--  intros x y z H H0. repeat rewrite -> leEq_def. intros H1 H2. apply H1.
--  apply shift_less_div. auto.
--   astepl (y[*]z). auto.
-- Qed.

lemma shift_leEq_mult' (x y z : R) (hy : 0 < y) (h : x / y ≤ z) : x ≤ y * z :=
 (div_le_iff₀' hy).mp h

-- Lemma shift_div_leEq : forall x y z : R, [0] [<] z -> forall z_ : z [#] [0], x [<=] y[*]z -> (x[/] z[//]z_) [<=] y.
-- Proof.
--  intros.
--  rstepr (y[*]z[/] z[//]z_).
--  apply div_resp_leEq.
--   assumption.
--  assumption.
-- Qed.

lemma shift_div_leEq (x y z : R) (hz : 0 < z) (h : x ≤ y * z) : x / z ≤ y :=
  (div_le_iff₀ hz).mpr h

-- Lemma shift_div_leEq' : forall (x y z : R) z_, [0] [<] z -> x [<=] z[*]y -> (x[/] z[//]z_) [<=] y.
-- Proof.
--  intros.
--  rstepr (z[*]y[/] z[//]z_).
--  apply div_resp_leEq.
--   assumption.
--  assumption.
-- Qed.

lemma shift_div_leEq' (x y z : R) (hz : 0 < z) (h : x ≤ z * y) : x / z ≤ y :=
  (div_le_iff₀' hz).mpr h


-- Lemma shift_leEq_div : forall (x y z : R) y_, [0] [<] y -> x[*]y [<=] z -> x [<=] (z[/] y[//]y_).
-- Proof.
--  intros x y z H X. repeat rewrite -> leEq_def. intros H0 H1. apply H0.
--  astepr (y[*]x).
--  apply shift_less_mult' with H; auto.
-- Qed.

lemma shift_leEq_div (x y z : R) (hy : 0 < y) (h : x * y ≤ z) : x ≤ z / y :=
  (le_div_iff₀ hy).mpr h

-- Hint Resolve shift_leEq_div: algebra.

-- Lemma eps_div_leEq_eps : forall (eps d : R) d_, [0] [<=] eps -> [1] [<=] d -> (eps[/] d[//]d_) [<=] eps.
-- Proof.
--  intros.
--  apply shift_div_leEq'.
--   apply less_leEq_trans with ([1]:R).
--    apply pos_one.
--   assumption.
--  astepl ([1][*]eps).
--  apply mult_resp_leEq_rht.
--   assumption.
--  assumption.
-- Qed.

lemma eps_div_leEq_eps (eps d : R) (h₀ : 0 ≤ eps) (h₁ : 1 ≤ d) : eps / d ≤ eps := by
  apply shift_div_leEq'
  apply lt_of_lt_of_le (by exact zero_lt_one) h₁
  exact le_mul_of_one_le_left h₀ h₁

-- Lemma nonneg_div_two : forall eps : R, [0] [<=] eps -> [0] [<=] eps [/]TwoNZ.
-- Proof.
--  intros.
--  apply shift_leEq_div.
--   apply pos_two.
--  astepl ([0]:R).
--  assumption.
-- Qed.

lemma nonneg_div_two (eps : R) (h : 0 ≤ eps) : 0 ≤ eps / 2 :=
  shift_leEq_div 0 2 eps (by exact zero_lt_two) (by simp [h])

-- Lemma nonneg_div_two' : forall eps : R, [0] [<=] eps -> eps [/]TwoNZ [<=] eps.
-- Proof.
--  intros.
--  apply shift_div_leEq.
--   apply pos_two.
--  astepl (eps[+][0]); rstepr (eps[+]eps).
--  apply plus_resp_leEq_lft; auto.
-- Qed.

lemma nonneg_div_two' (eps : R) (h : 0 ≤ eps) : eps / 2 ≤ eps := by
  apply shift_div_leEq
  exact zero_lt_two
  rw [mul_comm]
  rw [two_mul]
  exact le_add_of_nonneg_left h

-- Lemma nonneg_div_three : forall eps : R, [0] [<=] eps -> [0] [<=] eps [/]ThreeNZ.
-- Proof.
--  intros.
--  apply mult_cancel_leEq with (Three:R).
--   apply pos_three.
--  astepl ([0]:R); rstepr eps.
--  assumption.
-- Qed.

lemma nonneg_div_three (eps : R) (h : 0 ≤ eps) : 0 ≤ eps / 3 := by {
  apply mult_cancel_leEq
  exact zero_lt_three
  simp_all only [zero_mul, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.div_mul_cancel]
}

-- Lemma nonneg_div_three' : forall eps : R, [0] [<=] eps -> eps [/]ThreeNZ [<=] eps.
-- Proof.
--  intros.
--  apply shift_div_leEq.
--   apply pos_three.
--  rstepl (eps[+][0][+][0]); rstepr (eps[+]eps[+]eps).
--  repeat apply plus_resp_leEq_both; auto.
--  apply leEq_reflexive.
-- Qed.

lemma nonneg_div_three' (eps : R) (h : 0 ≤ eps) : eps / 3 ≤ eps := by
  apply shift_div_leEq
  exact zero_lt_three
  calc eps = _ := by {
      refine Eq.symm (mul_div_cancel₀ eps ?_)
      exact three_ne_zero}
      3 * (eps / 3) = eps := by {
         refine mul_div_cancel₀ eps ?_
         exact three_ne_zero
         }
      _ ≤ eps + eps + eps := by
        rw [add_assoc, ←add_assoc eps eps eps]
        apply le_add_of_nonneg_left
        simp_all only [nonneg_add_self_iff]
      _  ≤ eps * 3 := by {
        linarith
      }
  -- Actually, eps = eps + 0 + 0 ≤ eps + eps + eps, and the rest follows
  -- But since 3 * (eps / 3) = eps, and eps ≤ eps + eps + eps, done.

-- Lemma nonneg_div_four : forall eps : R, [0] [<=] eps -> [0] [<=] eps [/]FourNZ.
-- Proof.
--  intros.
--  rstepr ((eps [/]TwoNZ) [/]TwoNZ).
--  apply nonneg_div_two; apply nonneg_div_two; assumption.
-- Qed.

lemma nonneg_div_four (eps : R) (h : 0 ≤ eps) : 0 ≤ eps / 4 := by
  linarith

-- Lemma nonneg_div_four' : forall eps : R, [0] [<=] eps -> eps [/]FourNZ [<=] eps.
-- Proof.
--  intros.
--  rstepl ((eps [/]TwoNZ) [/]TwoNZ).
--  apply leEq_transitive with (eps [/]TwoNZ).
--   2: apply nonneg_div_two'; assumption.
--  apply nonneg_div_two'.
--  apply nonneg_div_two.
--  assumption.
-- Qed.

lemma nonneg_div_four' (eps : R) (h : 0 ≤ eps) : eps / 4 ≤ eps := by
  have h2 : 0 ≤ eps / 2 := nonneg_div_two eps h
  have h2' : (eps / 2) / 2 ≤ eps / 2 := nonneg_div_two' (eps / 2) h2
  have h4 : eps / 4 = (eps / 2) / 2 := by {
    linarith
  }
  rw [h4]
  exact le_trans h2' (nonneg_div_two' eps h)

-- End multiplication.

-- Section misc.
-- (**
-- *** Miscellaneous Properties
-- *)

-- Lemma sqr_nonneg : forall x : R, [0] [<=] x[^]2.
-- Proof.
--  intros. rewrite -> leEq_def in |- *. intro H.
--  cut ([0] [<] x[^]2). intro H0.
--   elim (less_antisymmetric_unfolded _ _ _ H H0).
--  cut (x [<] [0] or [0] [<] x). intro H0. elim H0; clear H0; intros H0.
--   rstepr ([--]x[*][--]x).
--    cut ([0] [<] [--]x). intro H1.
--     apply mult_resp_pos; auto.
--    astepl ([--]([0]:R)). apply inv_resp_less. auto.
--    rstepr (x[*]x).
--   apply mult_resp_pos; auto.
--  apply ap_imp_less.
--  apply cring_mult_ap_zero with x.
--  astepl (x[^]2).
--  apply less_imp_ap. auto.
-- Qed.

lemma sqr_nonneg (x : R) : 0 ≤ x ^ 2 :=
  pow_two_nonneg x

-- Lemma nring_nonneg : forall n : nat, [0] [<=] nring (R:=R) n.
-- Proof.
--  intro; induction  n as [| n Hrecn].
--   apply leEq_reflexive.
--  apply leEq_transitive with (nring (R:=R) n);
--    [ assumption | apply less_leEq; simpl in |- *; apply less_plusOne ].
-- Qed.

-- Lemma suc_leEq_dub : forall n, nring (R:=R) (S (S n)) [<=] Two[*]nring (S n).
-- Proof.
--  intro n.
--  induction  n as [| n Hrecn].
--   apply eq_imp_leEq.
--   rational.
--  astepl (nring (R:=R) (S (S n)) [+]nring 1).
--   apply leEq_transitive with (nring (R:=R) 2[*]nring (S n) [+]nring 1).
--    apply plus_resp_leEq.
--    astepr ((Two:R) [*]nring (S n)).
--    exact Hrecn.
--   simpl in |- *.
--   astepr ((([0]:R) [+][1][+][1]) [*] (nring n[+][1]) [+] (([0]:R) [+][1][+][1]) [*][1]).
--   apply plus_resp_leEq_lft.
--   astepr (([0]:R) [+][1][+][1]).
--   astepr (([0]:R) [+] ([1][+][1])).
--   apply plus_resp_leEq_lft.
--   astepr (Two:R).
--   apply less_leEq.
--   apply one_less_two.
--  simpl in |- *.
--  astepl (nring (R:=R) n[+][1][+] ([1][+] ([0][+][1]))).
--  astepl (nring (R:=R) n[+] ([1][+] ([1][+] ([0][+][1])))).
--  astepr (nring (R:=R) n[+][1][+] ([1][+][1])).
--  astepr (nring (R:=R) n[+] ([1][+] ([1][+][1]))).
--  rational.
-- Qed.

-- Lemma leEq_nring : forall n m, nring (R:=R) n [<=] nring m -> n <= m.
-- Proof.
--  intro n; induction  n as [| n Hrecn].
--   intros.
--   auto with arith.
--  intros.
--  induction  m as [| m Hrecm].
--   exfalso.
--   cut (nring (R:=R) n [<] [0]).
--    change (Not (nring (R:=R) n[<](nring 0))).
--    rewrite <- leEq_def.
--    apply nring_leEq.
--    auto with arith.
--   change (nring n [<] nring (R:=R) 0) in |- *.
--   apply nring_less.
--   apply Nat.lt_le_trans with (S n).
--    auto with arith.
--   exfalso. revert H; rewrite -> leEq_def. intro H; destruct H.
--   apply nring_less; auto with arith.
--  cut (n <= m).
--   auto with arith.
--  apply Hrecn.
--  rstepr (nring (R:=R) m[+][1][-][1]).
--  apply shift_leEq_minus.
--  apply H.
-- Qed.

-- Lemma cc_abs_aid : forall x y : R, [0] [<=] x[^]2[+]y[^]2.
-- Proof.
--  intros.
--  astepl ([0][+] ([0]:R)).
--  apply plus_resp_leEq_both; apply sqr_nonneg.
-- Qed.

lemma cc_abs_aid (x y : R) : 0 ≤ x ^ 2 + y ^ 2 :=
  add_nonneg (sqr_nonneg x) (sqr_nonneg y)

-- Load "Transparent_algebra".

-- Lemma nexp_resp_pos : forall (x : R) k, [0] [<] x -> [0] [<] x[^]k.
-- Proof.
--  intros.
--  elim k.
--   simpl in |- *.
--   apply pos_one.
--  intros.
--  simpl in |- *.
--  apply mult_resp_pos.
--   assumption.
--  assumption.
-- Qed.

lemma nexp_resp_pos (x : R) (k : ℕ) (hx : 0 < x) : 0 < x ^ k :=
  match k with
  | 0     => by simp [zero_lt_one]
  | k + 1 => by
      simp only [pow_succ]
      exact mul_pos (nexp_resp_pos x k hx) hx

-- Load "Opaque_algebra".

-- Lemma mult_resp_nonneg : forall x y : R, [0] [<=] x -> [0] [<=] y -> [0] [<=] x[*]y.
-- Proof.
--  intros x y. repeat rewrite -> leEq_def. intros  H H0 H1. apply H0.
--  cut (x[*]y [#] [0]). intro H2.
--   cut (x [#] [0]). intro H3.
--    cut (y [#] [0]). intro H4.
--     elim (ap_imp_less _ _ _ H4); intro H5. auto.
--      elim (ap_imp_less _ _ _ H3); intro H6. elim (H H6).
--      elim (less_antisymmetric_unfolded _ _ _ H1 (mult_resp_pos _ _ _ H6 H5)).
--    apply cring_mult_ap_zero_op with x. auto.
--    apply cring_mult_ap_zero with y. auto.
--   apply less_imp_ap. auto.
-- Qed.

lemma mult_resp_nonneg (x y : R) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y :=
  mul_nonneg hx hy


-- Load "Transparent_algebra".

-- Lemma nexp_resp_nonneg : forall (x : R) (k : nat), [0] [<=] x -> [0] [<=] x[^]k.
-- Proof.
--  intros. induction  k as [| k Hreck]. intros.
--  astepr ([1]:R). apply less_leEq. apply pos_one.
--   astepr (x[^]k[*]x).
--  apply mult_resp_nonneg; auto.
-- Qed.

lemma nexp_resp_nonneg (x : R) (k : ℕ) (hx : 0 ≤ x) : 0 ≤ x ^ k :=
  match k with
  | 0     => by simp [zero_le_one]
  | k + 1 => by
      simp only [pow_succ]
      exact mul_nonneg (nexp_resp_nonneg x k hx) hx

-- Lemma power_resp_leEq : forall (x y : R) k, [0] [<=] x -> x [<=] y -> x[^]k [<=] y[^]k.
-- Proof.
--  intros. induction  k as [| k Hreck]; intros.
--  astepl ([1]:R).
--   astepr ([1]:R).
--   apply leEq_reflexive.
--  astepl (x[^]k[*]x).
--  astepr (y[^]k[*]y).
--  apply leEq_transitive with (x[^]k[*]y).
--   apply mult_resp_leEq_lft. auto.
--    apply nexp_resp_nonneg; auto.
--  apply mult_resp_leEq_rht. auto.
--   apply leEq_transitive with x; auto.
-- Qed.



lemma power_resp_leEq (x y : R) (k : ℕ) (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ k ≤ y ^ k :=
  match k with
  | 0     => by simp
  | k + 1 =>
      calc
        x ^ (k + 1) = x ^ k * x := by rw [pow_succ]
        _ ≤ x ^ k * y := mul_le_mul_of_nonneg_left hxy (nexp_resp_nonneg x k hx)
        _ ≤ y ^ k * y := by
          apply mul_le_mul_of_nonneg_right
          apply power_resp_leEq x y k hx hxy
          exact le_trans hx hxy
        _ = y ^ (k + 1) := by rw [pow_succ]




-- Lemma nexp_resp_less : forall (x y : R) n, 1 <= n -> [0] [<=] x -> x [<] y -> x[^]n [<] y[^]n.
-- Proof.
--  intros.
--  induction  n as [| n Hrecn].
--   exfalso.
--   inversion H.
--  elim n.
--   simpl in |- *.
--   astepl x.
--   astepr y.
--   assumption.
--  intros.
--  change (x[^]S n0[*]x [<] y[^]S n0[*]y) in |- *.
--  apply mult_resp_less_both.
--     apply nexp_resp_nonneg.
--     assumption.
--    assumption.
--   assumption.
--  assumption.
-- Qed.

lemma nexp_resp_less (x y : R) (n : ℕ) (hn : 1 ≤ n) (hx : 0 ≤ x) (hxy : x < y) : x ^ n < y ^ n :=
  match n, hn with
  | 0, h => by cases h -- contradiction: 1 ≤ 0 is false
  | 1, _ => by simp [hxy]
  | k+2, _ =>
    have : 0 ≤ x ^ (k + 1) := nexp_resp_nonneg x (k + 1) hx
    have : x ^ (k + 1) < y ^ (k + 1) := by {
        apply nexp_resp_less x y (k + 1) (Nat.le_of_succ_le_succ (Nat.AtLeastTwo.prop)
        ) hx hxy}
    calc
      x ^ (k + 2) = x ^ (k + 1) * x := by rw [pow_succ]
      _ < y ^ (k + 1) * y := by {
        (expose_names; exact Right.mul_lt_mul_of_nonneg this hxy this_1 hx)
      }
      _ = y ^ (k + 2) := Eq.symm (pow_succ y (k + 1))


-- Lemma power_cancel_leEq : forall (x y : R) k, 0 < k -> [0] [<=] y -> x[^]k [<=] y[^]k -> x [<=] y.
-- Proof.
--  intros x y k H. repeat rewrite -> leEq_def. intros H0 H1 H2. apply H1.
--  apply nexp_resp_less; try rewrite -> leEq_def; auto.
-- Qed.


lemma power_cancel_leEq (x y : R) (k : ℕ) (hk : 0 < k) (hy : 0 ≤ y) (h : x ^ k ≤ y ^ k) : x ≤ y :=
  by stop
    by_contra hxy
    push_neg at hxy
    have : x < y := hxy
    have : x ^ k < y ^ k := nexp_resp_less x y k (Nat.succ_le_of_lt hk) hy this
    exact not_lt_of_le h this


-- Lemma power_cancel_less : forall (x y : R) k, [0] [<=] y -> x[^]k [<] y[^]k -> x [<] y.
-- Proof.
--  intros x y k H H0.
--  elim (zerop k); intro y0.
--   rewrite y0 in H0.
--   cut ([1] [<] ([1]:R)). intro H1.
--    elim (less_irreflexive_unfolded _ _ H1).
--   astepl (x[^]0). astepr (y[^]0). auto.
--   cut (x [<] y or y [<] x). intro H1.
--   elim H1; clear H1; intros H1. auto.
--    cut (x [<=] y). intro. destruct (leEq_def _ x y) as [H3 _]. elim ((H3 H2) H1).
--    apply power_cancel_leEq with k; auto.
--   apply less_leEq. auto.
--   apply ap_imp_less. apply un_op_strext_unfolded with (nexp_op (R:=R) k).
--  apply less_imp_ap. auto.
-- Qed.


-- Lemma nat_less_bin_nexp : forall p : nat, Snring R p [<] Two[^]S p.
-- Proof.
--  intro n.
--  unfold Snring in |- *.
--  induction  n as [| n Hrecn].
--   simpl in |- *.
--   astepl ([1]:R).
--   astepr (([0]:R) [+][1][+][1]).
--   astepr (([1]:R) [+][1]).
--   astepr (Two:R).
--   apply one_less_two.
--  astepl (nring (R:=R) (S n) [+][1]).
--  astepr ((Two:R)[^]S n[*]Two).
--  astepr ((Two:R)[^]S n[*][1][+]Two[^]S n[*][1]).
--   apply plus_resp_less_both.
--    astepr ((Two:R)[^]S n).
--    exact Hrecn.
--   astepr ((Two:R)[^]S n).
--   astepl (([1]:R)[^]S n).
--   apply nexp_resp_less.
--     intuition.
--    apply less_leEq.
--    apply pos_one.
--   apply one_less_two.
--  rational.
-- Qed.

-- Lemma Sum_resp_leEq : forall (f g : nat -> R) a b, a <= S b ->
--  (forall i, a <= i -> i <= b -> f i [<=] g i) -> Sum a b f [<=] Sum a b g.
-- Proof.
--  intros. induction  b as [| b Hrecb]; intros.
--  unfold Sum in |- *. unfold Sum1 in |- *.
--   generalize (toCle _ _ H); clear H; intro H.
--   inversion H as [|m X H2].
--    astepl ([0]:R).
--    astepr ([0]:R).
--    apply leEq_reflexive.
--   inversion X.
--   simpl in |- *.
--   rstepl (f 0).
--   rstepr (g 0).
--   apply H0; auto. rewrite H1. auto.
--   elim (le_lt_eq_dec _ _ H); intro H1.
--   apply leEq_wdl with (Sum a b f[+]f (S b)).
--    apply leEq_wdr with (Sum a b g[+]g (S b)).
--     apply plus_resp_leEq_both.
--      apply Hrecb. auto with arith. auto.
--       apply H0. auto with arith. auto.
--      apply eq_symmetric_unfolded. apply Sum_last.
--    apply eq_symmetric_unfolded. apply Sum_last.
--   unfold Sum in |- *. unfold Sum1 in |- *.
--  rewrite H1.
--  simpl in |- *.
--  astepl ([0]:R).
--  astepr ([0]:R).
--  apply leEq_reflexive.
-- Qed.

/--
If `a ≤ b + 1` and for all `i` with `a ≤ i ≤ b`, `f i ≤ g i`, then
`Sum a b f ≤ Sum a b g`.
Assumes `Sum a b f = ∑ i in a..b, f i`.
-/
lemma Sum_resp_leEq (f g : ℕ → R) (a b : ℕ) (hab : a ≤ b + 1)
  (hfg : ∀ i, a ≤ i → i ≤ b → f i ≤ g i) :
  (Finset.sum (Finset.Icc a b) f) ≤ (Finset.sum (Finset.Icc a b) g) := by stop
  induction b generalizing a with
  | zero =>
    by_cases h : a ≤ 0
    · have : a = 0 := by {exact Nat.eq_zero_of_le_zero h}
      subst this
      simp only [Finset.Icc_self, Finset.sum_singleton]
      exact hfg 0 (by rfl) (by rfl)
    · have : Finset.Icc a 0 = ∅ := by
        rw [Finset.Icc_eq_empty]
        exact h
      simp [this]
  | succ b ih =>
    by_cases h : a ≤ b
    · -- a ≤ b < b+1
      have : Finset.Icc a (b + 1) = Finset.Icc a b ∪ {b + 1} := by
        rw [Finset.Icc_succ_right_eq]
      rw [this, Finset.sum_union, Finset.sum_singleton]
      · apply add_le_add
        · exact ih a (by linarith [hab]) (λ i ha hb => hfg i ha (by linarith [hb]))
        · exact hfg (b + 1) (by linarith [h]) (by rfl)
      · apply Finset.disjoint_singleton_right.mpr
        intro x hx
        simp at hx
    · -- a > b, so Icc a (b+1) = {b+1} or ∅
      have : a = b + 1 := by linarith [hab, Nat.lt_of_not_ge h]
      subst this
      simp only [Finset.Icc_self, Finset.sum_singleton]
      exact hfg (b + 1) (by rfl) (by rfl)

-- Lemma Sumx_resp_leEq : forall n (f g : forall i, i < n -> R),
--  (forall i H, f i H [<=] g i H) -> Sumx f [<=] Sumx g.
-- Proof.
--  simple induction n.
--   intros; simpl in |- *; apply leEq_reflexive.
--  clear n; intros; simpl in |- *.
--  apply plus_resp_leEq_both.
--   apply H; intros; apply H0.
--  apply H0.
-- Qed.


/--
If `∀ i h, f i h ≤ g i h` then `Sumx f ≤ Sumx g`.
Assumes `Sumx f = ∑ i : Fin n, f i (Fin.is_lt i)`.
-/
lemma Sumx_resp_leEq {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  (n : ℕ) (f g : ∀ i, i < n → R)
  (h : ∀ i h, f i h ≤ g i h) :
  (Finset.univ.sum (fun (i : Fin n) => f i i.is_lt)) ≤ (Finset.univ.sum (fun (i : Fin n) => g i i.is_lt)) := by
  induction' n with n ih
  { simp }
  { -- n = n+1
    let f' : ∀ i, i < n → R := fun i hi => f i (Nat.lt.step hi)
    let g' : ∀ i, i < n → R := fun i hi => g i (Nat.lt.step hi)
    have h' : ∀ i hi, f' i hi ≤ g' i hi := λ i hi => h i (Nat.lt.step hi)
    exact Finset.sum_le_sum fun i a ↦ h (↑i) (Fin.is_lt i)
  }

-- Lemma Sum2_resp_leEq : forall m n, m <= S n -> forall f g : forall i, m <= i -> i <= n -> R,
--  (forall i Hm Hn, f i Hm Hn [<=] g i Hm Hn) -> Sum2 f [<=] Sum2 g.
-- Proof.
--  intros.
--  unfold Sum2 in |- *.
--  apply Sum_resp_leEq.
--   assumption.
--  intros.
--  elim (le_lt_dec m i); intro;
--    [ simpl in |- * | exfalso; apply (Nat.le_ngt m i); auto with arith ].
--  elim (le_lt_dec i n); intro;
--    [ simpl in |- * | exfalso; apply (Nat.le_ngt i n); auto with arith ].
--  apply H0.
-- Qed.

-- Lemma approach_zero : forall x : R, (forall e, [0] [<] e -> x [<] e) -> x [<=] [0].
-- Proof.
--  intros.
--  rewrite -> leEq_def; intro.
--  cut (x [<] x [/]TwoNZ).
--   change (Not (x [<] x [/]TwoNZ)) in |- *.
--   apply less_antisymmetric_unfolded.
--   apply plus_cancel_less with (z := [--](x [/]TwoNZ)).
--   apply mult_cancel_less with (z := Two:R).
--    apply pos_two.
--   rstepl ([0]:R).
--   rstepr x.
--   assumption.
--  apply X.
--  apply pos_div_two.
--  assumption.
-- Qed.

/--
If for all ε > 0, `x < ε`, then `x ≤ 0`.
-/
lemma approach_zero (x : R) (h : ∀ ε, 0 < ε → x < ε) : x ≤ 0 := by
  by_contra hx
  push_neg at hx
  -- So x > 0
  specialize h (x / 2) (by linarith)
  have : x / 2 < x := by
    apply div_lt_self hx
    simp only [Nat.one_lt_ofNat]
  linarith

-- Lemma approach_zero_weak : forall x : R, (forall e, [0] [<] e -> x [<=] e) -> x [<=] [0].
-- Proof.
--  intros.
--  rewrite -> leEq_def; intro.
--  cut (x [<=] x [/]TwoNZ).
--   rewrite -> leEq_def.
--   change (~ Not (x [/]TwoNZ [<] x)) in |- *.
--   intro H1.
--   apply H1.
--   apply plus_cancel_less with (z := [--](x [/]TwoNZ)).
--   apply mult_cancel_less with (z := Two:R).
--    apply pos_two.
--   rstepl ([0]:R).
--   rstepr x.
--   assumption.
--  apply H.
--  apply pos_div_two.
--  assumption.
-- Qed.

-- Lemma approach_zero_weak : forall x : R, (forall e, [0] [<] e -> x [<=] e) -> x [<=] [0].
-- Proof.
--  intros.
--  rewrite -> leEq_def; intro.
--  cut (x [<=] x [/]TwoNZ).
--   rewrite -> leEq_def.
--   change (~ Not (x [/]TwoNZ [<] x)) in |- *.
--   intro H1.
--   apply H1.
--   apply plus_cancel_less with (z := [--](x [/]TwoNZ)).
--   apply mult_cancel_less with (z := Two:R).
--    apply pos_two.
--   rstepl ([0]:R).
--   rstepr x.
--   assumption.
--  apply H.
--  apply pos_div_two.
--  assumption.
-- Qed.

-- End misc.

-- Lemma equal_less_leEq : forall a b x y : R,
--  (a [<] b -> x [<=] y) -> (a [=] b -> x [<=] y) -> a [<=] b -> x [<=] y.
-- Proof.
--  intros.
--  rewrite -> leEq_def.
--  red in |- *.
--  apply CNot_Not_or with (a [<] b) (a [=] b).
--    firstorder using leEq_def.
--   firstorder using leEq_def.
--  intro.
--  cut (a [=] b); intros.
--   2: apply leEq_imp_eq; auto.
--   auto.
--  rewrite -> leEq_def.
--  intro; auto.
-- Qed.
/--
If `a < b → x ≤ y` and `a = b → x ≤ y`, then `a ≤ b → x ≤ y`.
-/
lemma equal_less_leEq (a b x y : R)
  (h₁ : a < b → x ≤ y) (h₂ : a = b → x ≤ y) (h : a ≤ b) : x ≤ y :=
  match lt_or_eq_of_le h with
  | Or.inl hab => h₁ hab
  | Or.inr hab => h₂ hab

-- Lemma power_plus_leEq : forall n (x y:R), (0 < n) -> ([0][<=]x) -> ([0][<=]y) ->
-- (x[^]n [+] y[^]n)[<=](x[+]y)[^]n.
-- Proof.
--  intros [|n] x y Hn Hx Hy.
--   exfalso; auto with *.
--  induction n.
--   simpl.
--   rstepl ([1][*](x[+]y)).
--   apply leEq_reflexive.
--  rename n into m.
--  set (n:=(S m)) in *.
--  apply leEq_transitive with ((x[^]n[+]y[^]n)[*](x[+]y)).
--   apply shift_zero_leEq_minus'.
--   change (x[^]S n) with (x[^]n[*]x).
--   change (y[^]S n) with (y[^]n[*]y).
--   rstepr (y[*]x[^]n[+]x[*]y[^]n).
--   apply plus_resp_nonneg; apply mult_resp_nonneg; try apply nexp_resp_nonneg; try assumption.
--  change ((x[+]y)[^]S n) with ((x[+]y)[^]n[*](x[+]y)).
--  apply mult_resp_leEq_rht.
--   apply IHn.
--   unfold n; auto with *.
--  apply plus_resp_nonneg; assumption.
-- Qed.

-- Lemma power_plus_leEq : forall n (x y:R), (0 < n) -> ([0][<=]x) -> ([0][<=]y) ->
-- (x[^]n [+] y[^]n)[<=](x[+]y)[^]n.
-- Proof.
--  intros [|n] x y Hn Hx Hy.
--   exfalso; auto with *.
--  induction n.
--   simpl.
--   rstepl ([1][*](x[+]y)).
--   apply leEq_reflexive.
--  rename n into m.
--  set (n:=(S m)) in *.
--  apply leEq_transitive with ((x[^]n[+]y[^]n)[*](x[+]y)).
--   apply shift_zero_leEq_minus'.
--   change (x[^]S n) with (x[^]n[*]x).
--   change (y[^]S n) with (y[^]n[*]y).
--   rstepr (y[*]x[^]n[+]x[*]y[^]n).
--   apply plus_resp_nonneg; apply mult_resp_nonneg; try apply nexp_resp_nonneg; try assumption.
--  change ((x[+]y)[^]S n) with ((x[+]y)[^]n[*](x[+]y)).
--  apply mult_resp_leEq_rht.
--   apply IHn.
--   unfold n; auto with *.
--  apply plus_resp_nonneg; assumption.
-- Qed.

-- End Properties_of_leEq.

-- #[global]
-- Hint Resolve shift_leEq_lft mult_resp_nonneg plus_resp_nonneg: algebra.

-- (*---------------------------------*)
-- Section PosP_properties.
-- (*---------------------------------*)

-- (**
-- ** Properties of positive numbers
-- %\begin{convention}% Let [R] be an ordered field.
-- %\end{convention}%
-- *)
-- Variable R : COrdField.

-- (* begin hide *)
-- Notation ZeroR := ([0]:R).
-- Notation OneR := ([1]:R).
-- (* end hide *)

-- Lemma mult_pos_imp : forall a b : R, [0] [<] a[*]b -> [0] [<] a and [0] [<] b or a [<] [0] and b [<] [0].
-- Proof.
--  generalize I; intro.
--  generalize I; intro.
--  generalize I; intro.
--  generalize I; intro.
--  generalize I; intro.
--  intros a b H4.
--  generalize (Greater_imp_ap _ _ _ H4); intro H5.
--  generalize (mult_cancel_ap_zero_lft _ _ _ H5); intro H6.
--  generalize (mult_cancel_ap_zero_rht _ _ _ H5); intro H7.
--  elim (ap_imp_less _ _ _ H6); intro H8.
--   right.
--   split.
--    assumption.
--   elim (ap_imp_less _ _ _ H7); intro.
--    assumption.
--   exfalso.
--   elim (less_irreflexive_unfolded R [0]).
--   apply less_leEq_trans with (a[*]b).
--    assumption.
--   apply less_leEq.
--   apply inv_cancel_less.
--   astepl ZeroR.
--   astepr ([--]a[*]b).
--   apply mult_resp_pos.
--    astepl ([--]ZeroR).
--    apply inv_resp_less.
--    assumption.
--   assumption.
--  left.
--  split.
--   assumption.
--  elim (ap_imp_less _ _ _ H7); intro.
--   exfalso.
--   elim (less_irreflexive_unfolded R [0]).
--   apply less_leEq_trans with (a[*]b).
--    assumption.
--   apply less_leEq.
--   apply inv_cancel_less.
--   astepl ZeroR.
--   astepr (a[*][--]b).
--   apply mult_resp_pos.
--    assumption.
--   astepl ([--]ZeroR).
--   apply inv_resp_less.
--   assumption.
--  assumption.
-- Qed.

-- Lemma plus_resp_pos_nonneg : forall x y : R, [0] [<] x -> [0] [<=] y -> [0] [<] x[+]y.
-- Proof.
--  intros.
--  apply less_leEq_trans with x. auto.
--   astepl (x[+][0]).
--  apply plus_resp_leEq_lft. auto.
-- Qed.

lemma plus_resp_pos_nonneg (x y : R) (hx : 0 < x) (hy : 0 ≤ y) : 0 < x + y :=
  Right.add_pos_of_pos_of_nonneg hx hy

-- Lemma plus_resp_nonneg_pos : forall x y : R, [0] [<=] x -> [0] [<] y -> [0] [<] x[+]y.
-- Proof.
--  intros.
--  astepr (y[+]x).
--  apply plus_resp_pos_nonneg; auto.
-- Qed.

lemma plus_resp_nonneg_pos (x y : R) (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y :=
  add_pos_of_nonneg_of_pos hx hy

-- Lemma pos_square : forall x : R, x [#] [0] -> [0] [<] x[^]2.
-- Proof.
--  intros x H.
--  elim (ap_imp_less _ _ _ H); intro H1.
--   rstepr ([--]x[*][--]x).
--   cut ([0] [<] [--]x). intro.
--    apply mult_resp_pos; auto.
--   astepl ([--]ZeroR).
--   apply inv_resp_less. auto.
--   rstepr (x[*]x).
--  apply mult_resp_pos; auto.
-- Qed.

/--
If `x ≠ 0` then `0 < x ^ 2`.
-/
lemma pos_square (x : R) (hx : x ≠ 0) : 0 < x ^ 2 :=
  match lt_or_gt_of_ne hx with
  | Or.inl hlt =>
      -- x < 0
      have : 0 < -x := neg_pos.mpr hlt
      calc
        0 < (-x) * (-x) := mul_pos this this
        _ = x ^ 2 := by rw [neg_mul_neg, pow_two]
  | Or.inr hgt => by {
    exact nexp_resp_pos x 2 hgt
  }
      -- x > 0
      --pow_two_pos_of_ne_zero x hx

-- Lemma mult_cancel_pos_rht : forall x y : R, [0] [<] x[*]y -> [0] [<=] x -> [0] [<] y.
-- Proof.
--  intros x y H.
--  destruct (leEq_def _ [0] x) as [H0 _].
--  intro H2. pose (H3:=(H0 H2)).
--  elim (mult_pos_imp _ _ H); intro H1.
--   elim H1; auto.
--  elim H1; intros.
--  contradiction.
-- Qed.

/--
If `0 < x * y` and `0 ≤ x`, then `0 < y`.
-/
lemma mult_cancel_pos_rht (x y : R) (hxy : 0 < x * y) (hx : 0 ≤ x) : 0 < y :=
  match (lt_trichotomy x 0) with
  | Or.inl hlt =>
      -- x < 0, but 0 ≤ x, contradiction
      absurd hlt hx.not_lt
  | Or.inr (Or.inl heq) =>
      -- x = 0, so x * y = 0, contradiction with hxy
      by simp [heq] at hxy;
  | Or.inr (Or.inr hgt) =>
      -- x > 0
      (mul_pos_iff_of_pos_left hgt).mp hxy

-- Lemma mult_cancel_pos_lft : forall x y : R, [0] [<] x[*]y -> [0] [<=] y -> [0] [<] x.
-- Proof.
--  intros.
--  apply mult_cancel_pos_rht with y.
--   astepr (x[*]y).
--   auto. auto.
-- Qed.

/--
If `0 < x * y` and `0 ≤ y`, then `0 < x`.
-/
lemma mult_cancel_pos_lft (x y : R) (hxy : 0 < x * y) (hy : 0 ≤ y) : 0 < x :=
  pos_of_mul_pos_left hxy hy

-- Lemma pos_wd : forall x y : R, x [=] y -> [0] [<] y -> [0] [<] x.
-- Proof.
--  intros.
--  astepr y.
--  auto.
-- Qed.

/--
If `x = y` and `0 < y`, then `0 < x`.
-/
lemma pos_wd (x y : R) (hxy : x = y) (hy : 0 < y) : 0 < x :=
  hxy.symm ▸ hy

-- Lemma even_power_pos : forall n, Nat.Even n -> forall x : R, x [#] [0] -> [0] [<] x[^]n.
-- Proof.
--  intros n Hn x Hx.
--  destruct (even_or_odd_plus n) as [k [Hk | Hk]].
--  - astepr ((x[^]2)[^](k)).
--    apply nexp_resp_pos, pos_square; exact Hx.
--    astepr ((x[^]2)[^](k)); [reflexivity |].
--    now rewrite nexp_mult, Hk; replace (2 * k) with (k + k) by lia.
--  - exfalso; apply (Nat.Even_Odd_False n); [exact Hn |].
--    exists k; lia.
-- Qed.

/--
If `n` is even and `x ≠ 0`, then `0 < x ^ n`.
-/
lemma even_power_pos (n : ℕ) (hn : ∃ k, n = 2 * k) (x : R) (hx : x ≠ 0) : 0 < x ^ n := by
  obtain ⟨k, rfl⟩ := hn
  -- n = 2 * k
  have : 0 < x ^ 2 := pos_square x hx
  rw [pow_mul]
  exact nexp_resp_pos (x ^ 2) k this

-- Lemma odd_power_cancel_pos : forall n, Nat.Odd n -> forall x : R, [0] [<] x[^]n -> [0] [<] x.
-- Proof.
--  intros n [m Hm]%to_Codd x. simpl. intros H.
--  apply mult_pos_imp in H as [[H1 H2] | [H1 H2]].
--  - exact H2.
--  - exfalso. apply less_imp_ap in H2.
--    apply (even_power_pos m) in H2; [| now apply Ceven_to].
--    apply less_antisymmetric_unfolded with (1 := H1).
--    exact H2.
-- Qed.

/--
If `n` is odd and `0 < x ^ n`, then `0 < x`.
-/
lemma odd_power_cancel_pos (n : ℕ) (hn : ∃ m, n = 2 * m + 1) (x : R) (h : 0 < x ^ n) : 0 < x :=
  (Odd.pow_pos_iff hn).mp h

-- Lemma plus_resp_pos : forall x y : R, [0] [<] x -> [0] [<] y -> [0] [<] x[+]y.
-- Proof.
--  intros.
--  apply plus_resp_pos_nonneg.
--   auto.
--  apply less_leEq. auto.
-- Qed.

/--
If `0 < x` and `0 < y`, then `0 < x + y`.
-/
lemma plus_resp_pos (x y : R) (hx : 0 < x) (hy : 0 < y) : 0 < x + y :=
  plus_resp_pos_nonneg x y hx (le_of_lt hy)

-- Lemma pos_nring_S : forall n, ZeroR [<] nring (S n).
-- Proof.
--  simple induction n; simpl in |- *; intros.
--   (* base *)
--   astepr OneR; apply pos_one.
--  (* step *)
--  apply less_leEq_trans with (nring (R:=R) n0[+][1]).
--   assumption.
--  apply less_leEq.
--  apply less_plusOne.
-- Qed.

-- Lemma square_eq_pos : forall x a : R, [0] [<] a -> [0] [<] x -> x[^]2 [=] a[^]2 -> x [=] a.
-- Proof.
--  intros.
--  elim (square_eq _ x a); intros; auto.
--   exfalso.
--   apply less_irreflexive_unfolded with (x := ZeroR).
--   apply less_leEq_trans with x.
--    auto.
--   apply less_leEq.
--   astepl ([--]a); apply inv_cancel_less.
--   astepl ZeroR; astepr a; auto.
--  apply Greater_imp_ap; auto.
-- Qed.

/--
If `0 < a`, `0 < x`, and `x ^ 2 = a ^ 2`, then `x = a`.
-/
lemma square_eq_pos (x a : R) (ha : 0 < a) (hx : 0 < x) (h : x ^ 2 = a ^ 2) : x = a :=
  match eq_or_eq_neg_of_sq_eq_sq x a h with
  | Or.inl hxa => hxa
  | Or.inr hxa =>
      -- x = -a, but x > 0 and a > 0, so -a < 0 < x, contradiction
      have : -a < 0 := neg_neg_of_pos ha
      have : x = -a := hxa
      have : x < 0 := by rw [this]; (expose_names; exact this_1)
      -- But x > 0, contradiction
      absurd this hx.not_lt

-- Lemma square_eq_neg : forall x a : R, [0] [<] a -> x [<] [0] -> x[^]2 [=] a[^]2 -> x [=] [--]a.
-- Proof.
--  intros.
--  elim (square_eq _ x a); intros; auto.
--   exfalso.
--   apply less_irreflexive_unfolded with (x := ZeroR).
--   apply leEq_less_trans with x.
--    astepr a; apply less_leEq; auto.
--   auto.
--  apply Greater_imp_ap; auto.
-- Qed.

/--
If `0 < a`, `x < 0`, and `x ^ 2 = a ^ 2`, then `x = -a`.
-/
lemma square_eq_neg (x a : R) (ha : 0 < a) (hx : x < 0) (h : x ^ 2 = a ^ 2) : x = -a :=
  match eq_or_eq_neg_of_sq_eq_sq x a h with
  | Or.inl hxa =>
      -- x = a, but x < 0 < a, contradiction
      have : a < 0 := by rw [←hxa]; exact hx
      absurd this (not_lt_of_gt ha)
  | Or.inr hxa => hxa

-- End PosP_properties.

-- #[global]
-- Hint Resolve mult_resp_nonneg.

-- (**
-- ** Properties of one over successor
-- %\begin{convention}% Let [R] be an ordered field.
-- %\end{convention}%
-- *)

-- Definition one_div_succ (R : COrdField) i : R := [1][/] Snring R i[//]nringS_ap_zero _ i.

-- Arguments one_div_succ [R].

-- Section One_div_succ_properties.

-- Variable R : COrdField.

-- Lemma one_div_succ_resp_leEq : forall m n, m <= n -> one_div_succ (R:=R) n [<=] one_div_succ m.
-- Proof.
--  unfold one_div_succ in |- *. unfold Snring in |- *. intros.
--  apply recip_resp_leEq.
--   apply pos_nring_S.
--  apply nring_leEq.
--  auto with arith.
-- Qed.

-- Lemma one_div_succ_pos : forall i, ([0]:R) [<] one_div_succ i.
-- Proof.
--  intro.
--  unfold one_div_succ in |- *.
--  unfold Snring in |- *.
--  apply recip_resp_pos.
--  apply nring_pos.
--  auto with arith.
-- Qed.

-- Lemma one_div_succ_resp_less : forall i j, i < j -> one_div_succ j [<] one_div_succ (R:=R) i.
-- Proof.
--  intros.
--  unfold one_div_succ in |- *. unfold Snring in |- *. intros.
--  apply recip_resp_less.
--   apply pos_nring_S.
--  apply nring_less.
--  auto with arith.
-- Qed.

-- End One_div_succ_properties.

-- (**
-- ** Properties of [Half]
-- *)

-- Definition Half (R : COrdField) := ([1]:R) [/]TwoNZ.

/--
`Half` is defined as `1 / 2` in `R`.
-/
def Half (R : Type*) [Field R] : R := 1 / 2

-- Arguments Half {R}.

-- Section Half_properties.

-- (**
-- %\begin{convention}%
-- Let [R] be an ordered field.
-- %\end{convention}%
-- *)

-- Variable R : COrdField.

-- Lemma half_1 : (Half:R) [*]Two [=] [1].
-- Proof.
--  unfold Half in |- *.
--  apply div_1.
-- Qed.
-- Hint Resolve half_1: algebra.

/--
`Half * 2 = 1` in `R`.
-/
lemma half_1 : (Half R) * 2 = 1 := by
  simp [Half]

-- Lemma pos_half : ([0]:R) [<] Half.
-- Proof.
--  apply mult_cancel_pos_lft with (Two:R).
--   apply (pos_wd R (Half[*]Two) [1]).
--    exact half_1.
--   apply pos_one.
--  apply less_leEq; apply pos_two.
-- Qed.

/--
`0 < Half` in `R`.
-/
lemma pos_half : (0 : R) < Half R :=
  mult_cancel_pos_lft (Half R) 2 (by
    -- 0 < Half * 2
    rw [half_1]
    exact zero_lt_one
  ) (by
    -- 0 ≤ 2
    exact zero_le_two
  )

-- Lemma half_1' : forall x : R, x[*]Half[*]Two [=] x.
-- Proof.
--  intros.
--  unfold Half in |- *.
--  rational.
-- Qed.

/--
For all `x : R`, `x * Half * 2 = x`.
-/
lemma half_1' (x : R) : x * Half R * 2 = x := by
  simp [Half]

-- Lemma half_2 : (Half:R) [+]Half [=] [1].
-- Proof.
--  unfold Half in |- *.
--  rational.
-- Qed.

/--
`Half + Half = 1` in `R`.
-/
lemma half_2 : (Half R) + (Half R) = 1 := by
  simp [Half]
  ring

-- Lemma half_lt1 : (Half:R) [<] [1].
-- Proof.
--  astepr (Half[+] (Half:R)).
--   rstepl ((Half:R) [+][0]).
--   apply plus_resp_less_lft.
--   exact pos_half.
--  exact half_2.
-- Qed.

/--
`Half < 1` in `R`.
-/
lemma half_lt1 : (Half R) < 1 :=
  calc
    Half R = Half R + 0 := by rw [add_zero]
    _ < Half R + Half R := add_lt_add_left pos_half (Half R)
    _ = 1 := half_2

-- Lemma half_3 : forall x : R, [0] [<] x -> Half[*]x [<] x.
-- Proof.
--  intros.
--  astepr ([1][*]x).
--  apply mult_resp_less; auto.
--  exact half_lt1.
-- Qed.

/--
If `0 < x`, then `Half * x < x`.
-/
lemma half_3 (x : R) (hx : 0 < x) : Half R * x < x :=
  calc
    Half R * x < 1 * x := mul_lt_mul_of_pos_right half_lt1 hx
    _ = x := one_mul x

-- End Half_properties.
-- #[global]
-- Hint Resolve half_1 half_1' half_2: algebra.

#min_imports
