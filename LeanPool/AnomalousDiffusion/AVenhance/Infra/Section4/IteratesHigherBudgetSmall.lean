/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergyBudgetSplit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialBudgetNormalized
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamBudgetNormalized
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCorrectedUnnormalizedQuarter
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesAnalyticWeightOrder

/-! # Iterates Higher Budget Small

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The complete explicit higher-increment remainder closes under scalar
coefficient scales. The PDE energy inequality is not an assumption here. -/
theorem iterate_higher_energy_budget_small (n : ℕ) {i : ℕ}
    {κ D a e L Ccoef Cs Cv Cf N ρ F C₀ C : ℝ}
    (hi : 1 ≤ i) (hκ : 0 < κ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (he : 0 ≤ e) (hL : 0 < L) (hρ : 0 < ρ) (hρq : ρ ≤ ρ * F ^ 2)
    (hC : 0 ≤ C) (hC₀ : 1 ≤ C₀) (hF : C₀ ≤ F)
    (hlarge : 32 * C ≤ C₀) (hsmall : C₀ * (ρ * F ^ 2) ≤ 1)
    (hmat : 24 * amnrMaterialMajorantConstant Ccoef Cs Cv Cf ≤ C)
    (hu : (24 * (2 * ((2 : ℝ) ^ 19 * a) / L ^ 2)) / κ ≤ C / F ^ 2)
    (hv : (24 * (16 / κ * (32 * a * e ^ 2) ^ 2 *
      (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)) / κ ≤ C / F ^ 4)
    (hc : (24 * (8 * D * (8192 * a * e) * (256 * e⁻¹))) / κ ≤ C * ρ) :
    24 * iterateHigherEnergyBudget n i κ D a e L Ccoef Cs Cv Cf
      (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1) / Real.sqrt κ)
      (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) i / Real.sqrt κ)
      (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i - 1) / Real.sqrt κ)
      (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) i) ρ (ρ * F ^ 2) (fun _ => 1) ≤
      N ^ 2 * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1) ^ 2 *
        iterateAnalyticWeight n (i + 1) L ^ 2 / 4 := by
  have hp : 0 < C₀ := by linarith only [hC₀]
  have hFp : 0 < F := hp.trans_le hF
  have hq : 0 < ρ * F ^ 2 := mul_pos hρ (sq_pos_of_pos hFp)
  have hη : 0 < C₀ * (ρ * F ^ 2) := mul_pos hp hq
  have hW := iterateAnalyticWeight_nonneg n i hL.le
  have hWle := iterateAnalyticWeight_mono (n := n) hL.le (by omega : i ≤ i + 1)
  have hm := iterate_higher_material_budget_normalized
    (Ccoef := Ccoef) (Cs := Cs) (Cv := Cv) (Cf := Cf) (N := N)
    hκ hρ.le hρq hp hq hsmall hi hW hWle
  have hmc := add_le_add (div_le_div_of_nonneg_right hmat hp.le)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmat (show (0 : ℝ) ≤ 2 by norm_num))
      (sq_nonneg C₀))
  have hmC := hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmc (sq_nonneg N))
      (sq_nonneg (iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1))))
      (sq_nonneg (iterateAnalyticWeight n (i + 1) L)))
  have hs := iterate_stream_budget_normalized n
    (N := N) (Aprev := iterateAmplitude (C₀ * (ρ * F ^ 2)) i)
    (A := iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1))
    (W := iterateAnalyticWeight n (i + 1) L)
    hκ (by positivity) (by positivity) (by positivity)
    (iterateAmplitude_pos hη i).le (iterateAmplitude_pos hη (i + 1)).le hu hv hc
  have hb := iterate_corrected_unnormalized_quarter_budget hC hC₀ hρ hF hlarge hsmall
    (by omega : 1 ≤ i + 1)
  have hbNW := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (sq_nonneg N))
    (sq_nonneg (iterateAnalyticWeight n (i + 1) L))
  rw [show i + 1 - 1 = i by omega] at hbNW
  rw [iterate_higher_energy_budget_split]
  have heq : 24 * iterateStreamEnergyBudget n
      (2 * ((2 : ℝ) ^ 19 * a) *
        (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1) / Real.sqrt κ) ^ 2 / L ^ 2)
      (16 / κ * (32 * a * e ^ 2) ^ 2 *
        (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1) / Real.sqrt κ) ^ 2 *
        (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)
      (8 * D * (8192 * a * e) *
        (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) i / Real.sqrt κ) *
        (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1) / Real.sqrt κ) * (256 * e⁻¹))
      (iterateAnalyticWeight n (i + 1) L) (fun _ => 1) =
      iterateStreamEnergyBudget n
        ((24 * (2 * ((2 : ℝ) ^ 19 * a) / L ^ 2)) *
          (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1) / Real.sqrt κ) ^ 2)
        ((24 * (16 / κ * (32 * a * e ^ 2) ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)) *
          (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1) / Real.sqrt κ) ^ 2)
        ((24 * (8 * D * (8192 * a * e) * (256 * e⁻¹))) *
          (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) i / Real.sqrt κ) *
          (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) (i + 1) / Real.sqrt κ))
      (iterateAnalyticWeight n (i + 1) L) (fun _ => 1) := by
    unfold iterateStreamEnergyBudget
    ring
  rw [← heq] at hs
  have hsum := add_le_add hmC hs
  nlinarith only [hsum, hbNW]

end AVenhance.Infra.Section4
