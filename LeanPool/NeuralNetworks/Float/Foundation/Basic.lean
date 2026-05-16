/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

/-!
# Float Foundation: Basic Abstractions

Core type-theoretic foundations for floating-point arithmetic formalization.

## Mathematical Content
- Ordered field abstractions suitable for floating-point arithmetic
- Basic properties of real number operations
- Type class infrastructure for progressive generalization

## Implementation Notes
TODO
-/


/-! ## Core Type Class Hierarchy -/

/-- **Floating-Point Compatible Ordered Field**
An ordered field suitable for floating-point arithmetic formalization.
This extends `LinearOrderedField` with additional structure needed for radix-based arithmetic. -/
class FloatingPointField (α : Type*)
    extends Field α, LinearOrder α, IsStrictOrderedRing α where
  /-- The field supports exact representation of small natural numbers -/
  nat_cast_injective : ∀ n m : ℕ, (n : α) = (m : α) → n = m
  /-- Division by powers of 2 is exact (crucial for binary floating-point) -/
  two_ne_zero : (2 : α) ≠ 0
  /-- Absolute value is multiplicative -/
  abs_mul_eq : ∀ x y : α, |x * y| = |x| * |y|

namespace FloatingPointField

variable {α : Type*} [FloatingPointField α]

/-- **Canonical instance for real numbers** -/
noncomputable instance : FloatingPointField ℝ where
  nat_cast_injective := Nat.cast_injective
  two_ne_zero := by norm_num
  abs_mul_eq := abs_mul

/-- **Non-negativity preservation under subtraction**
for floating-point error analysis. -/
theorem sub_nonneg_of_le {x y : α} (h : x ≤ y) : 0 ≤ y - x := by
  rwa [sub_nonneg]

/-- **Absolute value characterization**
for floating-point rounding analysis. -/
theorem abs_eq_iff_eq_or_eq_neg {x y : α} : |x| = |y| ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    rcases le_total x 0 with hx | hx
    · rcases le_total y 0 with hy | hy
      · rw [abs_of_nonpos hx, abs_of_nonpos hy, neg_inj] at h
        exact Or.inl h
      · rw [abs_of_nonpos hx, abs_of_nonneg hy] at h
        exact Or.inr (neg_eq_iff_eq_neg.mp h)
    · rcases le_total y 0 with hy | hy
      · rw [abs_of_nonneg hx, abs_of_nonpos hy] at h
        exact Or.inr h
      · rw [abs_of_nonneg hx, abs_of_nonneg hy] at h
        exact Or.inl h
  · intro h
    rcases h with h | h <;> simp [h, abs_neg]

end FloatingPointField

/-! ## Multiplicative Structure for Floating-Point Analysis -/

section MultiplicativeProperties

variable {α : Type*} [FloatingPointField α]

/-- **Multiplication preserves order with non-negative factors**
for floating-point arithmetic bounds and error analysis. -/
theorem mul_lt_mul_of_nonneg_left {a b c : α} (hab : a < b) (hc : 0 < c) :
    c * a < c * b := by
  exact mul_lt_mul_of_pos_left hab hc

/-- **Multiplication inequality with four terms**
for floating-point multiplication error bounds. -/
theorem mul_lt_mul_of_nonneg' {a b c d : α} (hab : a < b) (hcd : c < d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) : a * c < b * d := by
  calc a * c ≤ a * d := mul_le_mul_of_nonneg_left (le_of_lt hcd) ha
  _ < b * d := mul_lt_mul_of_pos_right hab (lt_of_le_of_lt hc hcd)

end MultiplicativeProperties

/-! ## Additive Structure and Subtraction Properties -/

section AdditiveProperties

variable {α : Type*} [FloatingPointField α]

/-- **Multiplicative inequality with subtraction**
Fundamental for floating-point error analysis involving differences. -/
theorem abs_sub_le_of_bounds {x y : α} (hy_nonneg : 0 ≤ y) (hy_le_2x : y ≤ 2 * x) :
    |x - y| ≤ x := by
  rw [abs_le]
  constructor <;> linarith

end AdditiveProperties

/-! ## Absolute Value Advanced Properties -/

section AbsoluteValueProperties

variable {α : Type*} [FloatingPointField α]

/-- **Absolute value comparison characterization**
for floating-point rounding mode analysis. -/
theorem abs_le_iff_bounds {x y : α} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y := by
  exact abs_le

theorem abs_lt_iff_bounds {x y : α} : |x| < y ↔ -y < x ∧ x < y := by
  exact abs_lt

/-- **Absolute value reversal under negation**
for floating-point sign handling. -/
theorem abs_ge_iff_ge_or_le_neg {x y : α} : x ≤ |y| ↔ y ≤ -x ∨ x ≤ y := by
  cases le_total 0 y with
  | inl hy =>
    rw [abs_of_nonneg hy]
    constructor
    · intro h
      right
      exact h
    · intro h
      cases h with
      | inl h₁ =>
        have h₂ : x ≤ 0 := by linarith [hy, h₁]
        linarith [h₂, hy]
      | inr h₂ =>
        exact h₂
  | inr hy =>
    rw [abs_of_nonpos hy]
    constructor
    · intro h
      left
      exact le_neg_of_le_neg h
    · intro h
      cases h with
      | inl h₁ =>
        exact le_neg_of_le_neg h₁
      | inr h₂ =>
        linarith [h₂, hy]

end AbsoluteValueProperties
