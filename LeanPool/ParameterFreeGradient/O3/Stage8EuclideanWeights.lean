/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Euclidean

/-!
# Exact Euclidean estimate-sequence weights

This module records the source recurrence
`A₀ = 0`, `aₖ₊₁ = euclideanWeight Aₖ`, and
`Aₖ₊₁ = Aₖ + aₖ₊₁`.  In particular, the quadratic identity defining the
weight gives the exact alternative form `Aₖ₊₁ = aₖ₊₁²`.
-/

@[expose] public section

namespace O3

/-- The cumulative weights in the Euclidean estimate sequence. -/
noncomputable def euclideanA : ℕ → ℝ
  | 0 => 0
  | k + 1 => euclideanA k + euclideanWeight (euclideanA k)

@[simp] theorem euclideanA_zero : euclideanA 0 = 0 := rfl

@[simp] theorem euclideanA_succ (k : ℕ) :
    euclideanA (k + 1) = euclideanA k + euclideanWeight (euclideanA k) := rfl

theorem euclideanA_nonneg : ∀ k : ℕ, 0 ≤ euclideanA k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [euclideanA_succ]
      exact add_nonneg ih (euclideanWeight_pos ih).le

/-- Every recursive increment is strictly positive. -/
theorem euclideanA_increment_pos (k : ℕ) :
    0 < euclideanWeight (euclideanA k) :=
  euclideanWeight_pos (euclideanA_nonneg k)

/-- Exact defining increment of the cumulative weight. -/
theorem euclideanA_increment (k : ℕ) :
    euclideanA (k + 1) - euclideanA k = euclideanWeight (euclideanA k) := by
  rw [euclideanA_succ]
  ring

/-- The source quadratic relation `aₖ₊₁²=Aₖ₊₁`. -/
theorem euclideanWeight_sq_eq_next (k : ℕ) :
    (euclideanWeight (euclideanA k)) ^ 2 = euclideanA (k + 1) := by
  rw [euclideanA_succ]
  exact euclideanWeight_equation (euclideanA_nonneg k)

theorem euclideanA_pos_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    0 < euclideanA k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm 1 j]
  rw [euclideanA_succ]
  exact add_pos_of_nonneg_of_pos (euclideanA_nonneg j) (euclideanA_increment_pos j)

/-- A convenient lower bound on the next weight implied by a quadratic lower
bound on the current cumulative weight. -/
theorem euclideanWeight_ge_half_succ {k : ℕ}
    (hA : ((k : ℝ) + 1) ^ 2 / 4 ≤ euclideanA k) :
    ((k : ℝ) + 2) / 2 ≤ euclideanWeight (euclideanA k) := by
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hrad : 0 ≤ 1 + 4 * euclideanA k := by
    have := euclideanA_nonneg k
    linarith
  have hsqrt_sq := Real.sq_sqrt hrad
  have hsqrt_nonneg := Real.sqrt_nonneg (1 + 4 * euclideanA k)
  have htarget_nonneg : 0 ≤ (k : ℝ) + 1 := by positivity
  have hsqrt_ge : (k : ℝ) + 1 ≤ Real.sqrt (1 + 4 * euclideanA k) := by
    nlinarith
  unfold euclideanWeight
  linarith

/-- Exact source denominator growth: for every nonzero horizon,
`Aₘ ≥ (m+1)²/4`. -/
theorem euclideanA_quadratic_lower {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ 2 / 4 ≤ euclideanA m := by
  induction m, hm using Nat.le_induction with
  | base =>
      norm_num [euclideanA, euclideanWeight]
  | succ k hk ih =>
      rw [euclideanA_succ]
      have ha := euclideanWeight_ge_half_succ ih
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith

end O3
