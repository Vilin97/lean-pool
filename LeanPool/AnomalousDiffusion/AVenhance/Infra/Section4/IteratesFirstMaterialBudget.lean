/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHigherEnergyBudget

/-! # Iterates First Material Budget

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The exceptional first-increment material coefficient. -/
def iterateFirstMaterialCoefficient (C Ccoef : ℝ) : ℝ :=
  16 * C ^ 2 + 24 * C ^ 2 * (8 + 544 * C ^ 2) +
    (96 * C ^ 2 + (8 + 32 * Real.sqrt (8 + 64 * C ^ 2)) * C ^ 2 +
      1 + 128 * C ^ 2 * Ccoef ^ 2)

/-- Budget combining the three contributions to the first material derivative estimate. -/
def iterateFirstMaterialBudget (C Ccoef ρ q N W Wbase : ℝ) : ℝ :=
  iterateFirstMaterialCoefficient C Ccoef * q ^ 2 * N ^ 2 * W ^ 2 +
    384 * C ^ 2 * ρ ^ 2 * (N ^ 2 * Wbase ^ 2) +
    32 * Ccoef ^ 2 * ρ ^ 2 * N ^ 2 * Wbase ^ 2

/-- The first material budget carries two powers of q. -/
theorem iterate_first_material_budget_majorant {C Ccoef ρ q N W Wbase : ℝ}
    (hρ : 0 ≤ ρ) (hρq : ρ ≤ q) (hW : 0 ≤ Wbase) (hWle : Wbase ≤ W) :
    iterateFirstMaterialBudget C Ccoef ρ q N W Wbase ≤
      (iterateFirstMaterialCoefficient C Ccoef + 384 * C ^ 2 + 32 * Ccoef ^ 2) *
        q ^ 2 * N ^ 2 * W ^ 2 := by
  have hr := (sq_le_sq₀ hρ (hρ.trans hρq)).mpr hρq
  have hw := (sq_le_sq₀ hW (hW.trans hWle)).mpr hWle
  have hm := mul_le_mul hr hw (sq_nonneg _) (sq_nonneg _)
  have hmN := mul_le_mul_of_nonneg_left hm (sq_nonneg N)
  have h1 := mul_le_mul_of_nonneg_left hmN (show 0 ≤ 384 * C ^ 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hmN (show 0 ≤ 32 * Ccoef ^ 2 by positivity)
  unfold iterateFirstMaterialBudget
  nlinarith only [h1, h2]

/-- First-increment normalization avoids division by the initial-data norm. -/
theorem iterate_first_material_budget_normalized {C Ccoef ρ q N W Wbase C₀ : ℝ}
    (hρ : 0 ≤ ρ) (hρq : ρ ≤ q) (hW : 0 ≤ Wbase) (hWle : Wbase ≤ W)
    (hC₀ : C₀ ≠ 0) :
    24 * iterateFirstMaterialBudget C Ccoef ρ q N W Wbase ≤
      (24 * (iterateFirstMaterialCoefficient C Ccoef + 384 * C ^ 2 + 32 * Ccoef ^ 2) /
        C₀ ^ 2) * N ^ 2 * (C₀ * q) ^ 2 * W ^ 2 := by
  have hb := mul_le_mul_of_nonneg_left
    (iterate_first_material_budget_majorant (C := C) (Ccoef := Ccoef) (N := N) hρ hρq hW hWle)
    (show (0 : ℝ) ≤ 24 by norm_num)
  convert hb using 1
  field_simp

end AVenhance.Infra.Section4
