/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialBudgetConstant
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialBudgetAmplitude
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusiveMaterialScale

/-! # Iterates Material Budget Normalized

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The explicit higher material budget closes with the corrected C/C0 term.
Only scalar coefficient scales and amplitudes enter this algebraic lemma. -/
theorem iterate_higher_material_budget_normalized
    {κ Ccoef Cs Cv Cf N ρ q C₀ W Wprev : ℝ} {i : ℕ}
    (hκ : 0 < κ) (hρ : 0 ≤ ρ) (hρq : ρ ≤ q)
    (hC₀ : 0 < C₀) (hq : 0 < q) (hsmall : C₀ * q ≤ 1) (hi : 1 ≤ i)
    (hW : 0 ≤ Wprev) (hWle : Wprev ≤ W) :
    24 * iterateHigherMaterialBudget κ Ccoef Cs Cv Cf
      (N * iterateAmplitude (C₀ * q) i / Real.sqrt κ)
      (N * iterateAmplitude (C₀ * q) (i - 1) / Real.sqrt κ)
      (N * iterateAmplitude (C₀ * q) i) ρ q W Wprev ≤
      ((24 * amnrMaterialMajorantConstant Ccoef Cs Cv Cf) / C₀ +
        2 * (24 * amnrMaterialMajorantConstant Ccoef Cs Cv Cf) / C₀ ^ 2) *
      N ^ 2 * iterateAmplitude (C₀ * q) (i + 1) ^ 2 * W ^ 2 := by
  have hb := iterate_higher_material_budget_one_constant (Ccoef := Ccoef) (Cs := Cs) (Cv := Cv)
      (Cf := Cf) hκ.le hρ hρq hW hWle
    (iterate_diffusive_gradient_normalization (N := N * iterateAmplitude (C₀ * q) i) hκ).le
    (iterate_diffusive_gradient_normalization (N := N * iterateAmplitude (C₀ * q) (i - 1)) hκ).le
  have hC : 0 ≤ 24 * amnrMaterialMajorantConstant Ccoef Cs Cv Cf :=
    mul_nonneg (by norm_num) (iterate_material_majorant_constant_nonneg _ _ _ _)
  have ha := iterate_corrected_material_unnormalized hC hC₀ hq hsmall (by omega : 2 ≤ i + 1)
  have he1 : i + 1 - 1 = i := by omega
  have he2 : i + 1 - 2 = i - 1 := by omega
  rw [he1, he2] at ha
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha (sq_nonneg N)) (sq_nonneg W)
  have hb24 := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 24 by norm_num)
  calc
    _ ≤ 24 * (amnrMaterialMajorantConstant Ccoef Cs Cv Cf *
      (q ^ 2 * (N * iterateAmplitude (C₀ * q) i) ^ 2 +
        q * (N * iterateAmplitude (C₀ * q) i) ^ 2 +
        q ^ 2 * (N * iterateAmplitude (C₀ * q) (i - 1)) ^ 2) * W ^ 2) := hb24
    _ = N ^ 2 * ((24 * amnrMaterialMajorantConstant Ccoef Cs Cv Cf) *
      (q ^ 2 * iterateAmplitude (C₀ * q) i ^ 2 +
        q * iterateAmplitude (C₀ * q) i ^ 2 +
        q ^ 2 * iterateAmplitude (C₀ * q) (i - 1) ^ 2)) * W ^ 2 := by ring
    _ ≤ _ := by
      convert hm using 1
      ring

end AVenhance.Infra.Section4
