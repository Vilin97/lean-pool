/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Numerics.Tail
public import LeanPool.Odlyzko.TestFunction.Amplitude
public import LeanPool.Odlyzko.TestFunction.Quadratic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

/-- An archimedean integrand used in the Odlyzko-bound argument. -/
noncomputable def archimedeanIntegrand (y x : ℝ) : ℝ :=
  (1 - Tartar.testFunction (y * x)) / Real.sinh x

/-- An archimedean integral used in the Odlyzko-bound argument. -/
noncomputable def archimedeanIntegral (y : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), archimedeanIntegrand y x

theorem archimedeanIntegrand_le_one_div_sinh {y x : ℝ} (hx : 0 < x) :
    archimedeanIntegrand y x ≤ 1 / Real.sinh x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  rw [archimedeanIntegrand, div_le_div_iff_of_pos_right hs]
  linarith [tartarTestFunction_nonneg (y * x)]

theorem archimedeanIntegrand_le_exp_tail {y x : ℝ} (hx : 1 ≤ x) :
    archimedeanIntegrand y x ≤ (8 / 3 : ℝ) * Real.exp (-x) := by
  exact (archimedeanIntegrand_le_one_div_sinh (lt_of_lt_of_le zero_lt_one hx)).trans
    (one_div_sinh_le_exp_tail hx)

theorem NumericalCertificate.exp_tail_at_four_lt :
    (512 / 255 : ℝ) * Real.exp (-4) < 1 / 25 := by
  have he : Real.exp (-1) < 0.3678794412 := Real.exp_neg_one_lt_d9
  have hexp : Real.exp (-4) = Real.exp (-1) ^ 4 := by
    calc
      Real.exp (-4) = Real.exp ((4 : ℕ) * (-1 : ℝ)) := by norm_num
      _ = Real.exp (-1) ^ 4 := Real.exp_nat_mul (-1) 4
  rw [hexp]
  calc
    (512 / 255 : ℝ) * Real.exp (-1) ^ 4
        < (512 / 255 : ℝ) * (0.3678794412 : ℝ) ^ 4 := by gcongr
    _ < 1 / 25 := by norm_num

theorem NumericalCertificate.integral_archimedeanIntegrand_Ioi_four_lt {y : ℝ}
    (hint : MeasureTheory.IntegrableOn (archimedeanIntegrand y) (Set.Ioi 4)) :
    (∫ x in Set.Ioi (4 : ℝ), archimedeanIntegrand y x) < 1 / 25 := by
  have hmajor :
      MeasureTheory.IntegrableOn (fun x : ℝ ↦ (512 / 255 : ℝ) * Real.exp (-x)) (Set.Ioi 4) :=
    (integrableOn_exp_neg_Ioi 4).const_mul _
  have hi :
      (∫ x in Set.Ioi (4 : ℝ), archimedeanIntegrand y x) ≤
        (512 / 255 : ℝ) * Real.exp (-4) := by
    calc
      (∫ x in Set.Ioi (4 : ℝ), archimedeanIntegrand y x)
          ≤ ∫ x in Set.Ioi (4 : ℝ), (512 / 255 : ℝ) * Real.exp (-x) := by
            apply MeasureTheory.integral_mono_ae hint hmajor
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
            exact (archimedeanIntegrand_le_one_div_sinh (by
              grind)).trans
              (one_div_sinh_le_exp_tail_four hx.le)
      _ = (512 / 255 : ℝ) * Real.exp (-4) := by
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
  exact hi.trans_lt NumericalCertificate.exp_tail_at_four_lt

end NumberField.Odlyzko

section

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

end
