/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMaterialBudgetConstant
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFirstMaterialBudget

/-! # Iterates Budget Constant Choice

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- A universal coefficient constant for the three primitive/material scales. -/
def iterateBudgetScaleConstant (K Ck c H : ℝ) : ℝ :=
  2 * K * Ck * H + 2 * K * (2 : ℝ) ^ 21 * H + (2 : ℝ) ^ 21 / c

/-- The actual coefficient profile constant from cutoff averaging. -/
def iterateBudgetCoefficientConstant (K Cflow Cmean : ℝ) : ℝ :=
  K + 1 + Cmean + (2 * K * Cflow + 4 * (K + 1) * Cflow * (Cflow + 1))

/-- One constant dominates every loss in the complete energy budgets. -/
def iterateBudgetUniversalConstant (K Ck c H Cflow Cmean : ℝ) : ℝ :=
  let Cs := iterateBudgetScaleConstant K Ck c H
  let Ccoef := iterateBudgetCoefficientConstant K Cflow Cmean
  24 * amnrMaterialMajorantConstant Ccoef Cs Cs Cs +
    24 * (iterateFirstMaterialCoefficient Cs Ccoef + 384 * Cs ^ 2 + 32 * Ccoef ^ 2) +
    48 * (2 : ℝ) ^ 19 / c + (24 * (16 * 32 ^ 2 * 4 * 256 ^ 4)) / c ^ 2 +
    24 * 8 * 2 * K * (2 : ℝ) ^ 21 * H

/-- A concrete source constant closes the corrected budget and both
analytic-frequency conditions, and absorbs the theta frequency. -/
def iterateSourceConstant (C Rflow Cθ : ℝ) : ℝ :=
  max 4 (max (32 * C) (max (8 * |Rflow|) (2 * Cθ)))

theorem iterate_budget_scale_constant_bounds {K Ck c H : ℝ}
    (hK : 0 ≤ K) (hCk : 0 ≤ Ck) (hc : 0 < c) (hH : 0 ≤ H) :
    0 ≤ iterateBudgetScaleConstant K Ck c H ∧
    2 * K * Ck * H ≤ iterateBudgetScaleConstant K Ck c H ∧
    2 * K * (2 : ℝ) ^ 21 * H ≤ iterateBudgetScaleConstant K Ck c H ∧
    (2 : ℝ) ^ 21 / c ≤ iterateBudgetScaleConstant K Ck c H := by
  have h0 : 0 ≤ 2 * K * Ck * H := by positivity
  have h1 : 0 ≤ 2 * K * (2 : ℝ) ^ 21 * H := by positivity
  have h2 : 0 ≤ (2 : ℝ) ^ 21 / c := by positivity
  unfold iterateBudgetScaleConstant
  constructor
  · positivity
  constructor
  · linarith only [h1, h2]
  constructor
  · linarith only [h0, h2]
  · linarith only [h0, h1]

theorem iterate_budget_universal_constant_bounds {K Ck c H Cflow Cmean : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hH : 0 ≤ H) :
    let Cs := iterateBudgetScaleConstant K Ck c H
    let Ccoef := iterateBudgetCoefficientConstant K Cflow Cmean
    let C := iterateBudgetUniversalConstant K Ck c H Cflow Cmean
    0 ≤ C ∧ 24 * amnrMaterialMajorantConstant Ccoef Cs Cs Cs ≤ C ∧
    24 * (iterateFirstMaterialCoefficient Cs Ccoef + 384 * Cs ^ 2 + 32 * Ccoef ^ 2) ≤ C ∧
    48 * (2 : ℝ) ^ 19 / c ≤ C ∧ (24 * (16 * 32 ^ 2 * 4 * 256 ^ 4)) / c ^ 2 ≤ C ∧
    24 * 8 * 2 * K * (2 : ℝ) ^ 21 * H ≤ C := by
  dsimp only
  have h0 : 0 ≤ 24 * amnrMaterialMajorantConstant
      (iterateBudgetCoefficientConstant K Cflow Cmean)
      (iterateBudgetScaleConstant K Ck c H) (iterateBudgetScaleConstant K Ck c H)
      (iterateBudgetScaleConstant K Ck c H) :=
    mul_nonneg (by norm_num) (iterate_material_majorant_constant_nonneg _ _ _ _)
  have h1 : 0 ≤ 24 * (iterateFirstMaterialCoefficient
      (iterateBudgetScaleConstant K Ck c H) (iterateBudgetCoefficientConstant K Cflow Cmean) +
      384 * iterateBudgetScaleConstant K Ck c H ^ 2 +
      32 * iterateBudgetCoefficientConstant K Cflow Cmean ^ 2) := by
    unfold iterateFirstMaterialCoefficient
    positivity
  have h2 : 0 ≤ 48 * (2 : ℝ) ^ 19 / c := by positivity
  have h3 : 0 ≤ (24 * (16 * (32 : ℝ) ^ 2 * 4 * 256 ^ 4)) / c ^ 2 := by positivity
  have h4 : 0 ≤ 24 * 8 * 2 * K * (2 : ℝ) ^ 21 * H := by positivity
  unfold iterateBudgetUniversalConstant
  dsimp only
  constructor
  · linarith only [h0, h1, h2, h3, h4]
  constructor
  · linarith only [h1, h2, h3, h4]
  constructor
  · linarith only [h0, h2, h3, h4]
  constructor
  · linarith only [h0, h1, h3, h4]
  constructor
  · linarith only [h0, h1, h2, h4]
  · linarith only [h0, h1, h2, h3]

theorem iterate_source_constant_bounds (C Rflow Cθ : ℝ) :
    1 ≤ iterateSourceConstant C Rflow Cθ ∧
    32 * C ≤ iterateSourceConstant C Rflow Cθ ∧
    4 * Rflow ≤ iterateSourceConstant C Rflow Cθ ∧
    2 * Cθ ≤ iterateSourceConstant C Rflow Cθ ∧
    4 ≤ iterateSourceConstant C Rflow Cθ := by
  unfold iterateSourceConstant
  have h4 := le_max_left (4 : ℝ) (max (32 * C) (max (8 * |Rflow|) (2 * Cθ)))
  have hC := (le_max_left (32 * C) (max (8 * |Rflow|) (2 * Cθ))).trans (le_max_right (4 : ℝ) _)
  have hR8 := (le_max_left (8 * |Rflow|) (2 * Cθ)).trans
    ((le_max_right (32 * C) _).trans (le_max_right (4 : ℝ) _))
  have hθ := (le_max_right (8 * |Rflow|) (2 * Cθ)).trans
    ((le_max_right (32 * C) _).trans (le_max_right (4 : ℝ) _))
  have hR : 4 * Rflow ≤ iterateSourceConstant C Rflow Cθ := by
    unfold iterateSourceConstant
    linarith only [hR8, le_abs_self Rflow, abs_nonneg Rflow]
  exact ⟨(by linarith only [h4]), hC, hR, hθ, h4⟩

/-- LeftJacobian's doubled flow radius is absorbed by the same chosen source constant. -/
theorem iterate_source_constant_doubled_radius (C Rflow Cθ : ℝ) :
    4 * (2 * Rflow) ≤ iterateSourceConstant C Rflow Cθ := by
  unfold iterateSourceConstant
  have hR := (le_max_left (8 * |Rflow|) (2 * Cθ)).trans
    ((le_max_right (32 * C) _).trans (le_max_right (4 : ℝ) _))
  linarith only [hR, le_abs_self Rflow]

end AVenhance.Infra.Section4
