/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Numerics.Tail
public import LeanPool.Odlyzko.TestFunction.Amplitude
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

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
