/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

open MeasureTheory Set

namespace NumberField.Odlyzko

theorem support_tartarWeight_subset :
    Function.support Tartar.weight ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  rw [Function.mem_support] at hx
  simp only [mem_Icc, neg_le]
  constructor <;> by_contra h
  · exact hx (tartarWeight_eq_zero_of_one_le_abs (by
      grind))
  · exact hx (tartarWeight_eq_zero_of_one_le_abs (by
      grind))

theorem tartarWeight_hasCompactSupport : HasCompactSupport Tartar.weight :=
  IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    (closure_minimal support_tartarWeight_subset isClosed_Icc)

theorem tartarWeight_integrable : Integrable Tartar.weight :=
  tartarWeight_continuous.integrable_of_hasCompactSupport tartarWeight_hasCompactSupport

theorem tartarWeight_eq_indicator :
    Tartar.weight = (Set.Icc (-1 : ℝ) 1).indicator (fun x ↦ 1 - x ^ 2) := by
  funext x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hx]
    exact tartarWeight_eq_one_sub_sq_of_abs_le_one (by grind)
  · rw [Set.indicator_of_notMem hx]
    apply tartarWeight_eq_zero_of_one_le_abs
    grind

theorem integral_tartarWeight :
    ∫ x : ℝ, Tartar.weight x = 4 / 3 := by
  rw [tartarWeight_eq_indicator, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have h1 : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ ↦ x ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const, integral_pow]
  norm_num

end NumberField.Odlyzko
