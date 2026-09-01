/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Angle ranges for the E2 parametrization

This module derives the linear angle inequalities used by the E2 algebraic argument.
-/

namespace LeanPool.Erdos132WeiE2.Algebra

/-- Linear angle consequences of the frozen E2 algebra interface. -/
lemma angle_ranges (A B C : ℝ)
    (hB : 0 < B) (hBA : B < A) (hAC : A < C) (_hC : C < Real.pi / 3)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    A + B < 2 * Real.pi / 3 ∧
      2 * A + B < Real.pi ∧
      0 < A + 2 * B ∧
      A + 2 * B < 2 * A + B ∧
      3 * A + 2 * B < Real.pi := by
  have hA : 0 < A := lt_trans hB hBA
  have hthree : 3 * A + 2 * B < Real.pi := by linarith
  constructor
  · linarith [Real.pi_pos]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · exact hthree

lemma add_lt_two_pi_div_three (A B C : ℝ)
    (hB : 0 < B) (hBA : B < A) (hAC : A < C) (hC : C < Real.pi / 3)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    A + B < 2 * Real.pi / 3 :=
  (angle_ranges A B C hB hBA hAC hC hsum).1

lemma two_mul_add_lt_pi (A B C : ℝ)
    (hB : 0 < B) (hBA : B < A) (hAC : A < C) (hC : C < Real.pi / 3)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    2 * A + B < Real.pi :=
  (angle_ranges A B C hB hBA hAC hC hsum).2.1

lemma add_two_mul_pos (A B C : ℝ)
    (hB : 0 < B) (hBA : B < A) (hAC : A < C) (hC : C < Real.pi / 3)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    0 < A + 2 * B :=
  (angle_ranges A B C hB hBA hAC hC hsum).2.2.1

lemma add_two_mul_lt_two_mul_add (A B C : ℝ)
    (hB : 0 < B) (hBA : B < A) (hAC : A < C) (hC : C < Real.pi / 3)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    A + 2 * B < 2 * A + B :=
  (angle_ranges A B C hB hBA hAC hC hsum).2.2.2.1

lemma three_mul_add_lt_pi (A B C : ℝ)
    (hB : 0 < B) (hBA : B < A) (hAC : A < C) (hC : C < Real.pi / 3)
    (hsum : 2 * C + 3 * A + 2 * B = Real.pi) :
    3 * A + 2 * B < Real.pi :=
  (angle_ranges A B C hB hBA hAC hC hsum).2.2.2.2

end LeanPool.Erdos132WeiE2.Algebra
