/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesHigherEnergyBudget

/-! # Iterates Material Budget Majorant

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The five material contributions in the explicit higher-increment budget. -/
def iterateHigherMaterialBudget (κ Ccoef Cs Cv Cf Gprev Gprevprev Nprev ρ q W Wprev : ℝ) : ℝ :=
  16 * Cs ^ 2 * q ^ 2 * Nprev ^ 2 * W ^ 2 +
  Cs ^ 2 * q ^ 2 * κ * ((192 + 13056 * Cv ^ 2) * Gprev ^ 2 * W ^ 2 +
    12288 * Ccoef ^ 2 * Gprevprev ^ 2 * Wprev ^ 2) +
  (24 * Cs ^ 2 * q ^ 2 + (1 + Cs ^ 2 * (32 * Ccoef ^ 2)) * q) *
    (4 * κ * Gprev ^ 2 * W ^ 2) +
  384 * Cf ^ 2 * ρ ^ 2 * (κ * Gprev ^ 2 * Wprev ^ 2) +
  32 * κ * Ccoef ^ 2 * ρ ^ 2 * Gprev ^ 2 * Wprev ^ 2

/-- The material budget has exactly the three corrected amplitude terms.
The middle term is linear in q and remains in the induction. -/
theorem iterate_higher_material_budget_majorant
    {κ Ccoef Cs Cv Cf Gprev Gprevprev Nprev Nprevprev ρ q W Wprev : ℝ}
    (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ) (hρq : ρ ≤ q)
    (hW : 0 ≤ Wprev) (hWle : Wprev ≤ W)
    (hprev : κ * Gprev ^ 2 ≤ Nprev ^ 2)
    (hprevprev : κ * Gprevprev ^ 2 ≤ Nprevprev ^ 2) :
    iterateHigherMaterialBudget κ Ccoef Cs Cv Cf Gprev Gprevprev Nprev ρ q W Wprev ≤
      ((16 * Cs ^ 2 + Cs ^ 2 * (192 + 13056 * Cv ^ 2) + 96 * Cs ^ 2 +
        384 * Cf ^ 2 + 32 * Ccoef ^ 2) * q ^ 2 * Nprev ^ 2 +
       (4 * (1 + 32 * Cs ^ 2 * Ccoef ^ 2)) * q * Nprev ^ 2 +
       (12288 * Cs ^ 2 * Ccoef ^ 2) * q ^ 2 * Nprevprev ^ 2) * W ^ 2 := by
  have hq : 0 ≤ q := hρ.trans hρq
  have hr : ρ ^ 2 ≤ q ^ 2 := (sq_le_sq₀ hρ hq).mpr hρq
  have hw : Wprev ^ 2 ≤ W ^ 2 := (sq_le_sq₀ hW (hW.trans hWle)).mpr hWle
  have hpW := mul_le_mul hprev hw (sq_nonneg _) (sq_nonneg _)
  have hppW := mul_le_mul hprevprev hw (sq_nonneg _) (sq_nonneg _)
  have hpW0 := mul_le_mul_of_nonneg_right hprev (sq_nonneg W)
  have h1 := mul_le_mul_of_nonneg_left hpW0
    (show 0 ≤ Cs ^ 2 * q ^ 2 * (192 + 13056 * Cv ^ 2) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hppW
    (show 0 ≤ 12288 * Cs ^ 2 * Ccoef ^ 2 * q ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hpW0
    (show 0 ≤ 4 * (24 * Cs ^ 2 * q ^ 2 + (1 + Cs ^ 2 * (32 * Ccoef ^ 2)) * q) by positivity)
  have h4 := mul_le_mul hr hpW (by positivity) (sq_nonneg _)
  have h4' := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 384 * Cf ^ 2 by positivity)
  have h5 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 32 * Ccoef ^ 2 by positivity)
  unfold iterateHigherMaterialBudget
  nlinarith only [h1, h2, h3, h4', h5]

end AVenhance.Infra.Section4
