/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPhysicalKernelGains
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBudgetConstantChoice

/-! # Iterates Physical Coefficient Bundle

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- Every scalar scale required by the actual induction follows from literal
pointwise diffusivity bounds and the amplitude-times-period estimate. -/
theorem iterate_physical_coefficient_bundle {a e γ κ c Ck τ K H ρ L F Cflow Cmean : ℝ}
    (ha : 0 ≤ a) (he : 0 < e) (hκ : 0 < κ) (hc : 0 < c) (hCk : 0 ≤ Ck)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hH : 0 ≤ H) (hρ : 0 ≤ ρ) (hL : 0 < L)
    (hF1 : 1 ≤ F) (hlower : c * (a * e ^ (2 + γ)) ≤ κ)
    (hupper : κ ≤ Ck * (a * e ^ (2 + γ))) (htime : τ * a ≤ H * ρ)
    (hF : F = e ^ (1 + γ / 2) * L) :
    let Cs := iterateBudgetScaleConstant K Ck c H
    let C := iterateBudgetUniversalConstant K Ck c H Cflow Cmean
    ((2 * τ * K * κ) * L ^ 2 ≤ Cs * (ρ * F ^ 2)) ∧
    ((2 : ℝ) ^ 21 * a ≤ Cs * κ * L ^ 2) ∧
    ((2 * τ * K * κ) * ((2 : ℝ) ^ 21 * a) ≤ Cs * κ * ρ) ∧
    ((24 * (2 * ((2 : ℝ) ^ 19 * a) / L ^ 2)) / κ ≤ C / F ^ 2) ∧
    ((24 * (16 / κ * (32 * a * e ^ 2) ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)) / κ ≤ C / F ^ 4) ∧
    ((24 * (8 * (2 * τ * K * κ) * (8192 * a * e) * (256 * e⁻¹))) / κ ≤ C * ρ) := by
  dsimp only
  have hFp : 0 < F := by linarith only [hF1]
  have hCs := iterate_budget_scale_constant_bounds hK hCk hc hH
  have hC := iterate_budget_universal_constant_bounds (Ck := Ck) (Cflow := Cflow) (Cmean := Cmean)
      hK hc hH
  dsimp only at hC
  have hprim := iterate_primitive_radius_scale he hτ hK hCk hupper htime hF
  have hprim' := hprim.trans (mul_le_mul_of_nonneg_right hCs.2.1
    (mul_nonneg hρ (sq_nonneg F)))
  have hr := iterate_stream_ratio_of_literal_lower he hκ hc hL hFp hlower hF
  have hF2 : 1 ≤ F ^ 2 := by nlinarith only [hF1]
  have hinv : 1 / c / F ^ 2 ≤ 1 / c := by
    apply (div_le_iff₀ (sq_pos_of_pos hFp)).mpr
    have hb := mul_le_mul_of_nonneg_left hF2 (show 0 ≤ (1 : ℝ) / c by positivity)
    simpa only [mul_one] using hb
  have har := (div_le_iff₀ (mul_pos hκ (sq_pos_of_pos hL))).mp (hr.trans hinv)
  have hvel0 := mul_le_mul_of_nonneg_left har (show (0 : ℝ) ≤ 2 ^ 21 by norm_num)
  have hvel1 := mul_le_mul_of_nonneg_right hCs.2.2.2
    (mul_nonneg hκ.le (sq_nonneg L))
  have hvel : (2 : ℝ) ^ 21 * a ≤ iterateBudgetScaleConstant K Ck c H * κ * L ^ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ 21 * (1 / c * (κ * L ^ 2)) := hvel0
      _ = ((2 : ℝ) ^ 21 / c) * (κ * L ^ 2) := by ring
      _ ≤ _ := hvel1
      _ = _ := by ring
  have hflow0 := mul_le_mul_of_nonneg_left htime
    (show 0 ≤ 2 * K * (2 : ℝ) ^ 21 * κ by positivity)
  have hflow1 := mul_le_mul_of_nonneg_right hCs.2.2.1 (mul_nonneg hκ.le hρ)
  have hflow : (2 * τ * K * κ) * ((2 : ℝ) ^ 21 * a) ≤
      iterateBudgetScaleConstant K Ck c H * κ * ρ := by nlinarith only [hflow0, hflow1]
  have hkernels := iterate_physical_stream_kernel_gains ha he hκ hc hL hFp hlower hF
  have hu := hkernels.1.trans (div_le_div_of_nonneg_right hC.2.2.2.1 (sq_nonneg F))
  have hv := hkernels.2.trans (div_le_div_of_nonneg_right hC.2.2.2.2.1 (by positivity : 0 ≤ F ^ 4))
  have hlinear := (iterate_physical_linear_kernel_gain hκ hK he.ne' htime).trans
    (mul_le_mul_of_nonneg_right hC.2.2.2.2.2 hρ)
  exact ⟨hprim', hvel, hflow, hu, hv, hlinear⟩

end AVenhance.Infra.Section4
