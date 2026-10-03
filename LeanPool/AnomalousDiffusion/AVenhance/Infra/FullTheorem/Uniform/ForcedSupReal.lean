/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Abstract real step for the sup-in-time stream-difference estimate -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.FullTheorem.Uniform

/-- From the energy balance `l + 2κA = -2C`, Cauchy–Schwarz `C² ≤ E A`, and `E ≤ η² B`,
conclude `√l ≤ (η/κ) (√κ √B)`. -/
theorem forced_sup_real {κ η A B C E l : ℝ} (hκ : 0 < κ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hE0 : 0 ≤ E) (hid : l + 2 * κ * A = -2 * C)
    (hCE : C ^ 2 ≤ E * A) (hE : E ≤ η ^ 2 * B) :
    Real.sqrt l ≤ (η / κ) * (Real.sqrt κ * Real.sqrt B) := by
  have hy0 : 0 ≤ κ * A + E / (4 * κ) := by positivity
  have hsq : (κ * A + E / (4 * κ)) ^ 2 = (κ * A - E / (4 * κ)) ^ 2 + E * A := by
    field_simp
    ring
  have hy : (-C) ^ 2 ≤ (κ * A + E / (4 * κ)) ^ 2 := by
    nlinarith [sq_nonneg (κ * A - E / (4 * κ))]
  have hC : -C ≤ κ * A + E / (4 * κ) := (abs_le_of_sq_le_sq' hy hy0).2
  have hl1 : l ≤ E / (2 * κ) := by
    have h2 : E / (2 * κ) = 2 * (E / (4 * κ)) := by field_simp; ring
    rw [h2]
    linarith
  have hl2 : E / (2 * κ) ≤ η ^ 2 * B / κ := by
    rw [div_le_div_iff₀ (by positivity) hκ]
    have : 0 ≤ E * κ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hE hκ.le]
  have hR : 0 ≤ (η / κ) * (Real.sqrt κ * Real.sqrt B) := by positivity
  rw [Real.sqrt_le_iff]
  refine ⟨hR, ?_⟩
  have hsq2 : ((η / κ) * (Real.sqrt κ * Real.sqrt B)) ^ 2 = η ^ 2 * B / κ := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hκ.le, Real.sq_sqrt hB, div_pow]
    field_simp
  rw [hsq2]
  exact hl1.trans hl2

end AVenhance.Infra.FullTheorem.Uniform
