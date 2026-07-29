/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Numerics.Integral
public import LeanPool.Odlyzko.TestFunction.Quadratic

/-! TODO: Add doc-string. -/

@[expose] public section

open MeasureTheory Set

namespace NumberField.Odlyzko

theorem archimedeanIntegrand_nonneg {y x : ℝ} (hx : 0 < x) :
    0 ≤ archimedeanIntegrand y x := by
  rw [archimedeanIntegrand]
  exact div_nonneg (sub_nonneg.mpr (tartarTestFunction_le_one _))
    (Real.sinh_nonneg_iff.mpr hx.le)

theorem archimedeanIntegrand_le_linear {y x : ℝ} (hx : 0 < x) :
    archimedeanIntegrand y x ≤ y ^ 2 / 5 * x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hxs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  have hquad := one_sub_tartarTestFunction_le_sq_div_five (y * x)
  rw [archimedeanIntegrand, div_le_iff₀ hs]
  calc
    1 - Tartar.testFunction (y * x) ≤ (y * x) ^ 2 / 5 := hquad
    _ = (y ^ 2 / 5 * x) * x := by ring
    _ ≤ (y ^ 2 / 5 * x) * Real.sinh x := by
      gcongr

theorem integrableOn_archimedeanIntegrand_Ioc_zero_one (y : ℝ) :
    IntegrableOn (archimedeanIntegrand y) (Set.Ioc 0 1) := by
  have hmajor : IntegrableOn (fun x : ℝ ↦ y ^ 2 / 5 * x) (Set.Ioc 0 1) :=
    (by fun_prop : Continuous (fun x : ℝ ↦ y ^ 2 / 5 * x)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  apply Integrable.mono' hmajor
  · exact (((measurable_const.sub
      (tartarTestFunction_measurable.comp (measurable_const.mul measurable_id))).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (archimedeanIntegrand_nonneg hx.1)]
    exact archimedeanIntegrand_le_linear hx.1

theorem integrableOn_archimedeanIntegrand_Ioi_one (y : ℝ) :
    IntegrableOn (archimedeanIntegrand y) (Set.Ioi 1) := by
  have hmajor :
      IntegrableOn (fun x : ℝ ↦ (8 / 3 : ℝ) * Real.exp (-x)) (Set.Ioi 1) :=
    (integrableOn_exp_neg_Ioi 1).const_mul _
  apply Integrable.mono' hmajor
  · exact (((measurable_const.sub
      (tartarTestFunction_measurable.comp (measurable_const.mul measurable_id))).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (archimedeanIntegrand_nonneg (zero_lt_one.trans hx))]
    exact archimedeanIntegrand_le_exp_tail hx.le

theorem integrableOn_archimedeanIntegrand_Ioi (y : ℝ) :
    IntegrableOn (archimedeanIntegrand y) (Set.Ioi 0) := by
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by simp
  rw [← hunion]
  exact (integrableOn_archimedeanIntegrand_Ioc_zero_one y).union
    (integrableOn_archimedeanIntegrand_Ioi_one y)

end NumberField.Odlyzko
