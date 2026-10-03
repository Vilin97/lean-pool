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

/-! # Iterates First Budget Small

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The complete explicit higher-increment remainder closes under scalar
coefficient scales. The PDE energy inequality is not an assumption here. -/
theorem iterate_first_energy_budget_small (n : ℕ)
    {κ D a e r L Ccoef Cs B N ρ F C₀ C : ℝ}
    (hκ : 0 < κ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (_he : 0 ≤ e) (hB : 0 ≤ B) (hr : 0 ≤ r) (hL : 0 < L) (hρ : 0 < ρ) (hρq : ρ ≤ ρ * F ^ 2)
    (hC : 0 ≤ C) (hC₀ : 1 ≤ C₀) (hF : C₀ ≤ F)
    (hlarge : 32 * C ≤ C₀) (hsmall : C₀ * (ρ * F ^ 2) ≤ 1)
    (hmat : 24 * (iterateFirstMaterialCoefficient Cs Ccoef + 384 * Cs ^ 2 + 32 * Ccoef ^ 2) ≤ C)
    (hu : (24 * (2 * ((2 : ℝ) ^ 19 * a) / L ^ 2)) / κ ≤ C / F ^ 2)
    (hv : (24 * (16 / κ * (32 * a * e ^ 2) ^ 2 *
      (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)) / κ ≤ C / F ^ 4)
    (hc : (24 * (8 * D * B * r)) / κ ≤ C * ρ) :
    24 * iterateFirstEnergyBudget n κ D a e r L Cs Ccoef B
      (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 / Real.sqrt κ)
      N ρ (ρ * F ^ 2) (fun _ => 1) ≤
      N ^ 2 * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 ^ 2 *
        iterateAnalyticWeight n 1 L ^ 2 / 4 := by
  have hp : 0 < C₀ := by linarith only [hC₀]
  have hFp : 0 < F := hp.trans_le hF
  have hq : 0 < ρ * F ^ 2 := mul_pos hρ (sq_pos_of_pos hFp)
  have hη : 0 < C₀ * (ρ * F ^ 2) := mul_pos hp hq
  have hW := iterateAnalyticWeight_nonneg n 0 hL.le
  have hWle := iterateAnalyticWeight_mono (n := n) hL.le (show 0 ≤ 1 by omega)
  have hm := iterate_first_material_budget_normalized (C := Cs) (Ccoef := Ccoef)
    (N := N) hρ.le hρq hW hWle hp.ne'
  have hmc0 := div_le_div_of_nonneg_right hmat (sq_nonneg C₀)
  have hmc : (24 * (iterateFirstMaterialCoefficient Cs Ccoef +
      384 * Cs ^ 2 + 32 * Ccoef ^ 2)) / C₀ ^ 2 ≤ C / C₀ + 2 * C / C₀ ^ 2 := by
    have h0 : 0 ≤ C / C₀ := by positivity
    have h1 : 0 ≤ C / C₀ ^ 2 := by positivity
    rw [show 2 * C / C₀ ^ 2 = 2 * (C / C₀ ^ 2) by ring]
    linarith only [hmc0, h0, h1]
  have hmC := hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmc (sq_nonneg N))
      (sq_nonneg (C₀ * (ρ * F ^ 2)))) (sq_nonneg (iterateAnalyticWeight n 1 L)))
  have hA1 : iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 = C₀ * (ρ * F ^ 2) := by
    simp only [iterateAmplitude]; norm_num
  rw [← hA1] at hmC
  have hs := iterate_stream_budget_normalized n
    (N := N) (Aprev := iterateAmplitude (C₀ * (ρ * F ^ 2)) 0)
    (A := iterateAmplitude (C₀ * (ρ * F ^ 2)) 1)
    (W := iterateAnalyticWeight n 1 L)
    hκ (by positivity) (by positivity) (by positivity)
    (iterateAmplitude_pos hη 0).le (iterateAmplitude_pos hη 1).le hu hv hc
  have hb := iterate_corrected_unnormalized_quarter_budget hC hC₀ hρ hF hlarge hsmall
    (show 1 ≤ 1 by omega)
  have hbNW := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (sq_nonneg N))
    (sq_nonneg (iterateAnalyticWeight n 1 L))
  have hA0 : iterateAmplitude (C₀ * (ρ * F ^ 2)) 0 = 1 := by
    simp [iterateAmplitude]
  rw [Nat.sub_self, hA0] at hbNW
  rw [iterate_first_energy_budget_split]
  have heq : 24 * iterateStreamEnergyBudget n
      (2 * ((2 : ℝ) ^ 19 * a) *
        (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 / Real.sqrt κ) ^ 2 / L ^ 2)
      (16 / κ * (32 * a * e ^ 2) ^ 2 *
        (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 / Real.sqrt κ) ^ 2 *
        (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)
      (8 * D * B *
        (N / Real.sqrt κ) *
        (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 / Real.sqrt κ) * r)
      (iterateAnalyticWeight n 1 L) (fun _ => 1) =
      iterateStreamEnergyBudget n
        ((24 * (2 * ((2 : ℝ) ^ 19 * a) / L ^ 2)) *
          (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 / Real.sqrt κ) ^ 2)
        ((24 * (16 / κ * (32 * a * e ^ 2) ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)) *
          (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 / Real.sqrt κ) ^ 2)
        ((24 * (8 * D * B * r)) *
          (N / Real.sqrt κ) *
          (N * iterateAmplitude (C₀ * (ρ * F ^ 2)) 1 / Real.sqrt κ))
      (iterateAnalyticWeight n 1 L) (fun _ => 1) := by
    unfold iterateStreamEnergyBudget
    ring
  rw [hA0, mul_one] at hs
  rw [← heq] at hs
  have hsum := add_le_add hmC hs
  nlinarith only [hsum, hbNW]

end AVenhance.Infra.Section4
