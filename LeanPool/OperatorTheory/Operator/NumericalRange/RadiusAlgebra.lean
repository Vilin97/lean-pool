/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Algebraic estimates for the numerical radius

The numerical radius is not submultiplicative, but its sharp equivalence
with the operator norm gives uniform product estimates.  This file records
those estimates and their immediate commutator and anticommutator
consequences.
-/
import Mathlib.Analysis.Normed.Operator.Mul
import LeanPool.OperatorTheory.Operator.NumericalRange.Radius

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical radius of a product is bounded by the product of the
operator norms. -/
theorem numericalRadius_mul_le_norm_mul_norm
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ ‖A‖ * ‖B‖ :=
  (numericalRadius_le_norm (A * B)).trans (norm_mul_le A B)

/-- A product estimate using numerical radius in the left factor. -/
theorem numericalRadius_mul_le_two_mul_numericalRadius_mul_norm
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ 2 * numericalRadius A * ‖B‖ := by
  exact (numericalRadius_mul_le_norm_mul_norm A B).trans
    (mul_le_mul_of_nonneg_right
      (norm_le_two_mul_numericalRadius A) (norm_nonneg B))

/-- A product estimate using numerical radius in the right factor. -/
theorem numericalRadius_mul_le_two_mul_norm_mul_numericalRadius
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤ 2 * ‖A‖ * numericalRadius B := by
  calc
    numericalRadius (A * B) ≤ ‖A‖ * ‖B‖ :=
      numericalRadius_mul_le_norm_mul_norm A B
    _ ≤ ‖A‖ * (2 * numericalRadius B) :=
      mul_le_mul_of_nonneg_left
        (norm_le_two_mul_numericalRadius B) (norm_nonneg A)
    _ = 2 * ‖A‖ * numericalRadius B := by ring

/-- Uniform quasi-submultiplicativity of numerical radius. -/
theorem numericalRadius_mul_le_four_mul
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B) ≤
      4 * numericalRadius A * numericalRadius B := by
  calc
    numericalRadius (A * B) ≤ 2 * numericalRadius A * ‖B‖ :=
      numericalRadius_mul_le_two_mul_numericalRadius_mul_norm A B
    _ ≤ (2 * numericalRadius A) * (2 * numericalRadius B) :=
      mul_le_mul_of_nonneg_left (norm_le_two_mul_numericalRadius B)
        (mul_nonneg zero_le_two (numericalRadius_nonneg A))
    _ = 4 * numericalRadius A * numericalRadius B := by ring

/-- Powers are controlled by the power of twice the numerical radius. -/
theorem numericalRadius_pow_le_two_mul_pow
    [Nontrivial E] (A : E →L[ℂ] E) (n : ℕ) :
    numericalRadius (A ^ n) ≤ (2 * numericalRadius A) ^ n := by
  calc
    numericalRadius (A ^ n) ≤ ‖A ^ n‖ := numericalRadius_le_norm (A ^ n)
    _ ≤ ‖A‖ ^ n := norm_pow_le A n
    _ ≤ (2 * numericalRadius A) ^ n :=
      pow_le_pow_left₀ (norm_nonneg A)
        (norm_le_two_mul_numericalRadius A) n

/-- The numerical radius of a commutator has the uniform constant-eight
bound coming from quasi-submultiplicativity. -/
theorem numericalRadius_commutator_le_eight_mul
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B - B * A) ≤
      8 * numericalRadius A * numericalRadius B := by
  calc
    numericalRadius (A * B - B * A) ≤
        numericalRadius (A * B) + numericalRadius (B * A) :=
      numericalRadius_sub_le (A * B) (B * A)
    _ ≤ 4 * numericalRadius A * numericalRadius B +
        4 * numericalRadius B * numericalRadius A :=
      add_le_add (numericalRadius_mul_le_four_mul A B)
        (numericalRadius_mul_le_four_mul B A)
    _ = 8 * numericalRadius A * numericalRadius B := by ring

/-- The same uniform constant-eight bound holds for the anticommutator. -/
theorem numericalRadius_anticommutator_le_eight_mul
    (A B : E →L[ℂ] E) :
    numericalRadius (A * B + B * A) ≤
      8 * numericalRadius A * numericalRadius B := by
  calc
    numericalRadius (A * B + B * A) ≤
        numericalRadius (A * B) + numericalRadius (B * A) :=
      numericalRadius_add_le (A * B) (B * A)
    _ ≤ 4 * numericalRadius A * numericalRadius B +
        4 * numericalRadius B * numericalRadius A :=
      add_le_add (numericalRadius_mul_le_four_mul A B)
        (numericalRadius_mul_le_four_mul B A)
    _ = 8 * numericalRadius A * numericalRadius B := by ring

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
