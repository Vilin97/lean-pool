/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFirstMaterialBudget
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialBudgetMajorant
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamBudgetKernel

/-! # Iterates Energy Budget Split

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The explicit higher remainder separates into its material contribution
and the three exact current-order kernels. -/
theorem iterate_higher_energy_budget_split (n i : ℕ)
    (κ D a e L Ccoef Cs Cv Cf Gcur Gprev Gprevprev Nprev ρ q : ℝ) (d : ℕ → ℝ) :
    iterateHigherEnergyBudget n i κ D a e L Ccoef Cs Cv Cf Gcur Gprev Gprevprev Nprev ρ q d =
      iterateHigherMaterialBudget κ Ccoef Cs Cv Cf Gprev Gprevprev Nprev ρ q
        (iterateAnalyticWeight n (i + 1) L) (iterateAnalyticWeight n i L) +
      iterateStreamEnergyBudget n
        (2 * ((2 : ℝ) ^ 19 * a) * Gcur ^ 2 / L ^ 2)
        (16 / κ * (32 * a * e ^ 2) ^ 2 * Gcur ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)
        (8 * D * (8192 * a * e) * Gprev * Gcur * (256 * e⁻¹))
        (iterateAnalyticWeight n (i + 1) L) d := by
  unfold iterateHigherEnergyBudget iterateHigherMaterialBudget iterateStreamEnergyBudget
  ring

/-- The exceptional first remainder has the same current-order kernels. -/
theorem iterate_first_energy_budget_split (n : ℕ)
    (κ D a e r L C Ccoef B Gcur N ρ q : ℝ) (d : ℕ → ℝ) :
    iterateFirstEnergyBudget n κ D a e r L C Ccoef B Gcur N ρ q d =
      iterateFirstMaterialBudget C Ccoef ρ q N
        (iterateAnalyticWeight n 1 L) (iterateAnalyticWeight n 0 L) +
      iterateStreamEnergyBudget n
        (2 * ((2 : ℝ) ^ 19 * a) * Gcur ^ 2 / L ^ 2)
        (16 / κ * (32 * a * e ^ 2) ^ 2 * Gcur ^ 2 * (2 * ((256 * e⁻¹) / L) ^ 2) ^ 2)
        (8 * D * B * (N / Real.sqrt κ) * Gcur * r)
        (iterateAnalyticWeight n 1 L) d := by
  unfold iterateFirstEnergyBudget iterateFirstMaterialBudget iterateFirstMaterialCoefficient
    iterateStreamEnergyBudget
  ring

end AVenhance.Infra.Section4
