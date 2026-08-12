/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.TestFunction.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Bounds

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

namespace NumberField.Odlyzko

theorem abs_tartarAmplitude_le_six {x : ℝ} (hx : 1 ≤ |x|) :
    |Tartar.amplitude x| ≤ 6 := by
  have hx0 : x ≠ 0 := by grind
  rw [tartarAmplitude_eq_of_ne hx0, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_pow]
  have hnum : |Real.sin x - x * Real.cos x| ≤ 1 + |x| := by
    calc
      |Real.sin x - x * Real.cos x|
          ≤ |Real.sin x| + |x * Real.cos x| := abs_sub _ _
      _ ≤ 1 + |x| := by
        rw [abs_mul]
        nlinarith [Real.abs_sin_le_one x, Real.abs_cos_le_one x, abs_nonneg x]
  have hxp : 0 < |x| ^ 3 := pow_pos (lt_of_lt_of_le zero_lt_one hx) _
  rw [div_le_iff₀ hxp]
  calc
    3 * |Real.sin x - x * Real.cos x| ≤ 3 * (1 + |x|) := by simp_all
    _ ≤ 6 * |x| ^ 3 := by
      have ha := abs_nonneg x
      have ha_sq : |x| ≤ |x| ^ 2 := by
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hx)]
      nlinarith

theorem tartarTestFunction_le_thirty_six {x : ℝ} (hx : 1 ≤ |x|) :
    Tartar.testFunction x ≤ 36 := by
  rw [Tartar.testFunction]
  have ha := abs_tartarAmplitude_le_six hx
  have ha0 := abs_nonneg (Tartar.amplitude x)
  rw [← sq_abs]
  nlinarith

theorem abs_tartarAmplitude_le_six_div_sq {x : ℝ} (hx : 1 ≤ |x|) :
    |Tartar.amplitude x| ≤ 6 / |x| ^ 2 := by
  have hx0 : x ≠ 0 := by grind
  rw [tartarAmplitude_eq_of_ne hx0, abs_div, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow]
  have hnum : |Real.sin x - x * Real.cos x| ≤ 2 * |x| := by
    calc
      |Real.sin x - x * Real.cos x|
          ≤ |Real.sin x| + |x * Real.cos x| := abs_sub _ _
      _ ≤ 1 + |x| := by
        rw [abs_mul]
        nlinarith [Real.abs_sin_le_one x, Real.abs_cos_le_one x, abs_nonneg x]
      _ ≤ 2 * |x| := by linarith
  have hxp : 0 < |x| ^ 3 := pow_pos (zero_lt_one.trans_le hx) _
  calc
    3 * |Real.sin x - x * Real.cos x| / |x| ^ 3
        ≤ (6 * |x|) / |x| ^ 3 := by
          apply div_le_div_of_nonneg_right _ hxp.le
          grind
    _ = 6 / |x| ^ 2 := by grind

theorem tartarTestFunction_le_thirty_six_div_fourth {x : ℝ} (hx : 1 ≤ |x|) :
    Tartar.testFunction x ≤ 36 / |x| ^ 4 := by
  rw [Tartar.testFunction, ← sq_abs]
  have h := abs_tartarAmplitude_le_six_div_sq hx
  have h0 := abs_nonneg (Tartar.amplitude x)
  calc
    |Tartar.amplitude x| ^ 2 ≤ (6 / |x| ^ 2) ^ 2 := by nlinarith
    _ = 36 / |x| ^ 4 := by grind

theorem integrableOn_thirty_six_div_abs_fourth_Ioi :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ 36 / |x| ^ 4) (Set.Ioi 1) := by
  have h := (integrableOn_Ioi_rpow_of_lt (a := (-4 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 1)).const_mul 36
  refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro x hx
  have hxpos : 0 < x := zero_lt_one.trans hx
  change 36 * x ^ (-4 : ℝ) = 36 / |x| ^ 4
  rw [abs_of_pos hxpos, Real.rpow_neg hxpos.le]
  rw [div_eq_mul_inv]
  simp

theorem integrableOn_thirty_six_div_abs_fourth_tails :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ 36 / |x| ^ 4)
      (Set.Iio (-1) ∪ Set.Ioi 1) := by
  have hn : MeasureTheory.IntegrableOn (fun x : ℝ ↦ 36 / |x| ^ 4) (Set.Iio (-1)) := by
    have hp : MeasureTheory.IntegrableOn (fun x : ℝ ↦ 36 / |x| ^ 4)
        (Set.Ioi (-(-1 : ℝ))) := by
      simpa only [neg_neg] using integrableOn_thirty_six_div_abs_fourth_Ioi
    apply MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.IntegrableOn.comp_neg_Iio (c := (-1 : ℝ))
        hp)
    · intro x hx
      simp
    · simp
  exact hn.union integrableOn_thirty_six_div_abs_fourth_Ioi

theorem tartarTestFunction_integrable :
    MeasureTheory.Integrable Tartar.testFunction := by
  have hmajor : MeasureTheory.Integrable
      (fun x : ℝ ↦ (Set.Icc (-1 : ℝ) 1).indicator (fun _ ↦ 1) x +
        (Set.Iio (-1 : ℝ) ∪ Set.Ioi 1).indicator (fun x ↦ 36 / |x| ^ 4) x) := by
    apply MeasureTheory.Integrable.add
    · exact (by fun_prop : Continuous (fun _ : ℝ ↦ (1 : ℝ))).continuousOn.integrableOn_Icc
        |>.integrable_indicator measurableSet_Icc
    · exact integrableOn_thirty_six_div_abs_fourth_tails.integrable_indicator
        (measurableSet_Iio.union measurableSet_Ioi)
  apply MeasureTheory.Integrable.mono' hmajor tartarTestFunction_measurable.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (tartarTestFunction_nonneg x)]
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · simp only [Set.indicator, hx, ite_eq_left]
    have hnot : x ∉ Set.Iio (-1 : ℝ) ∪ Set.Ioi 1 := by simp_all
    simp only [hnot, ite_false, add_zero]
    exact tartarTestFunction_le_one x
  · have htailmem : x ∈ Set.Iio (-1 : ℝ) ∪ Set.Ioi 1 := by
      grind
    simp only [Set.indicator, hx, htailmem, ite_false, ite_true, zero_add]
    have habs : 1 ≤ |x| := by grind
    exact tartarTestFunction_le_thirty_six_div_fourth habs

end NumberField.Odlyzko
