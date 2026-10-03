/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialBudgetMajorant

/-! # Iterates Material Budget Constant

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- One universal constant dominates the three material coefficients.
It depends only on the coefficient constants, not on any iteration index. -/
def amnrMaterialMajorantConstant (Ccoef Cs Cv Cf : ℝ) : ℝ :=
  (16 * Cs ^ 2 + Cs ^ 2 * (192 + 13056 * Cv ^ 2) + 96 * Cs ^ 2 +
    384 * Cf ^ 2 + 32 * Ccoef ^ 2) +
  4 * (1 + 32 * Cs ^ 2 * Ccoef ^ 2) + 12288 * Cs ^ 2 * Ccoef ^ 2

theorem iterate_material_majorant_constant_nonneg (Ccoef Cs Cv Cf : ℝ) :
    0 ≤ amnrMaterialMajorantConstant Ccoef Cs Cv Cf := by
  unfold amnrMaterialMajorantConstant
  positivity

/-- A single constant bounds the three distinct material remainders.
The q term is retained separately from the two q-squared terms. -/
theorem iterate_higher_material_budget_one_constant
    {κ Ccoef Cs Cv Cf Gprev Gprevprev Nprev Nprevprev ρ q W Wprev : ℝ}
    (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ) (hρq : ρ ≤ q)
    (hW : 0 ≤ Wprev) (hWle : Wprev ≤ W)
    (hprev : κ * Gprev ^ 2 ≤ Nprev ^ 2)
    (hprevprev : κ * Gprevprev ^ 2 ≤ Nprevprev ^ 2) :
    iterateHigherMaterialBudget κ Ccoef Cs Cv Cf Gprev Gprevprev Nprev ρ q W Wprev ≤
      amnrMaterialMajorantConstant Ccoef Cs Cv Cf *
        (q ^ 2 * Nprev ^ 2 + q * Nprev ^ 2 + q ^ 2 * Nprevprev ^ 2) * W ^ 2 := by
  have hq : 0 ≤ q := hρ.trans hρq
  have hb := iterate_higher_material_budget_majorant (Ccoef := Ccoef) (Cs := Cs) (Cv := Cv) (Cf :=
      Cf) hκ hρ hρq hW hWle hprev hprevprev
  have h0 : 0 ≤ 16 * Cs ^ 2 + Cs ^ 2 * (192 + 13056 * Cv ^ 2) + 96 * Cs ^ 2 +
      384 * Cf ^ 2 + 32 * Ccoef ^ 2 := by positivity
  have h1 : 0 ≤ 4 * (1 + 32 * Cs ^ 2 * Ccoef ^ 2) := by positivity
  have h2 : 0 ≤ 12288 * Cs ^ 2 * Ccoef ^ 2 := by positivity
  have ht0 := mul_nonneg (add_nonneg h1 h2) (sq_nonneg q)
  have ht1 := mul_nonneg (add_nonneg h0 h2) hq
  have ht2 := mul_nonneg (add_nonneg h0 h1) (sq_nonneg q)
  have ht0' := mul_nonneg ht0 (sq_nonneg Nprev)
  have ht1' := mul_nonneg ht1 (sq_nonneg Nprev)
  have ht2' := mul_nonneg ht2 (sq_nonneg Nprevprev)
  apply hb.trans
  unfold amnrMaterialMajorantConstant
  have hsum := mul_nonneg (add_nonneg (add_nonneg ht0' ht1') ht2') (sq_nonneg W)
  nlinarith only [hsum]

end AVenhance.Infra.Section4
