/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CanonicalCorrectionBounds

/-! Abstract real algebra for higher material velocity rates and scale sums. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The velocity scale is a single negative epsilon power at each level. -/
theorem amnr_higher_material_spatial_scale {E β : ℝ} (hE : 0 < E) (k r : ℕ) :
    E ^ (β - 1) * (E ^ (β - 2)) ^ r * E⁻¹ ^ k =
      E ^ (β - 1 + (β - 2) * (r : ℝ) - (k : ℝ)) := by
  rw [← Real.rpow_natCast (E ^ (β - 2)) r, ← Real.rpow_mul hE.le,
    ← Real.rpow_natCast E⁻¹ k, ← Real.rpow_neg_one,
    ← Real.rpow_mul hE.le, ← Real.rpow_add hE, ← Real.rpow_add hE]
  congr 1
  ring

/-- Every nonzero derivative has a negative coarse-to-fine scale exponent. -/
theorem amnr_higher_material_exponent_nonpos {β : ℝ} (hβ : β < 4 / 3)
    (k r : ℕ) (hkr : 1 ≤ k + r) :
    β - 1 + (β - 2) * (r : ℝ) - (k : ℝ) ≤ 0 := by
  have hβ2 : β - 2 ≤ 0 := by linarith
  by_cases hk : 1 ≤ k
  · have hprod := mul_nonpos_of_nonpos_of_nonneg hβ2 (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  · have hr : 1 ≤ r := by omega
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hprod := mul_le_mul_of_nonpos_left hr' hβ2
    have hk0 : k = 0 := by omega
    simp only [hk0, Nat.cast_zero, sub_zero]
    linarith

/-- Positive material levels have the uniform negative exponent needed by
the supergeometric scale summation. -/
theorem amnr_higher_material_exponent_le {β : ℝ} (hβ : β < 4 / 3)
    (k r : ℕ) (hr : 1 ≤ r) :
    β - 1 + (β - 2) * (r : ℝ) - (k : ℝ) ≤ -(1 / 7 : ℝ) := by
  have hβ2 : β - 2 ≤ 0 := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hprod := mul_le_mul_of_nonpos_left hr' hβ2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- Nonempty coarse velocity jets are bounded by the same current-scale
rates. The zero-order drift is deliberately absent from this statement. -/
theorem amnr_higher_velocity_scale_antitone {E F β : ℝ} (hE : 0 < E)
    (hF : 0 < F) (hEF : E ≤ F) (hβ : β < 4 / 3) (k r : ℕ) (hkr : 1 ≤ k + r) :
    F ^ (β - 1) * (F ^ (β - 2)) ^ r * F⁻¹ ^ k ≤
      E ^ (β - 1) * (E ^ (β - 2)) ^ r * E⁻¹ ^ k := by
  rw [amnr_higher_material_spatial_scale hF, amnr_higher_material_spatial_scale hE]
  exact Real.rpow_le_rpow_of_nonpos hE hEF (amnr_higher_material_exponent_nonpos hβ k r hkr)

end AVenhance.Infra.Section4
