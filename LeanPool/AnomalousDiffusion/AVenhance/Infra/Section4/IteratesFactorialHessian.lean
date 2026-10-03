/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHomogeneousAnalyticMaterial

/-! # Iterates Factorial Hessian

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The material Hessian and its L2 partner cost the same factorial order,
 up to an absolute factor; the cancellation gains no factorial denominator. -/
theorem iterate_hessian_factorial_product_le (n : ℕ) :
    ((n + 1).factorial : ℝ) * ((n + 3).factorial : ℝ) ≤
      2 * ((n + 2).factorial : ℝ) ^ 2 := by
  have h1 : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n + 1).factorial : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  have h2 : ((n + 3).factorial : ℝ) = ((n : ℝ) + 3) * ((n + 2).factorial : ℝ) := by
    rw [show n + 3 = (n + 2) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  calc
    ((n + 1).factorial : ℝ) * ((n + 3).factorial : ℝ) =
        ((n : ℝ) + 3) * (((n + 1).factorial : ℝ) * ((n + 2).factorial : ℝ)) := by rw [h2]; ring
    _ ≤ (2 * ((n : ℝ) + 2)) *
        (((n + 1).factorial : ℝ) * ((n + 2).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
        (by positivity)
    _ = 2 * ((n + 2).factorial : ℝ) ^ 2 := by rw [h1]; ring

end AVenhance.Infra.Section4
