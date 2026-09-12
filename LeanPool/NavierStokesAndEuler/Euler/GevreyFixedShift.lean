/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Bound

/-!
# Absorbing a fixed factorial shift into a coefficient radius

The factor `(n+1)²` costs only `4^n`. Thus the one-shift estimate for an actual
bounded inverse becomes a shift-zero coefficient estimate at a larger fixed
radius. The enlargement is independent of the derivative order.
-/

@[expose] public section


namespace EulerGevrey

/-- The elementary exponential bound needed for one fixed derivative shift. -/
theorem succ_le_two_pow_real (n : ℕ) : (n : ℝ)+1 ≤ (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith [show (0 : ℝ) ≤ n by positivity]

/-- One fixed factorial shift is a fixed radius enlargement for coefficients. -/
theorem majorant_one_le_radius_four (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 1 n ≤ R*majorant (4*R) 0 n := by
  have hs : ((n : ℝ)+1)^2 ≤ (4 : ℝ)^n := by
    have h := (sq_le_sq₀ (by positivity) (by positivity)).2 (succ_le_two_pow_real n)
    calc
      ((n : ℝ)+1)^2 ≤ ((2 : ℝ)^n)^2 := h
      _ = (4 : ℝ)^n := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  calc
    majorant R 1 n = (R*(R^n*(n.factorial : ℝ)^2))*((n : ℝ)+1)^2 := by
      simp only [majorant, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    _ ≤ (R*(R^n*(n.factorial : ℝ)^2))*(4 : ℝ)^n :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = R*majorant (4*R) 0 n := by
      simp only [majorant, Nat.add_zero, mul_pow]
      ring

end EulerGevrey
