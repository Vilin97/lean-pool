/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

theorem numericalCertificate_of_integral_le {J : ℝ} (hJ : J ≤ 2 / 5) :
    Real.log (33 / 4) ≤
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) - J - 20 * Real.pi / 123 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hx : 0 ≤ (16 * Real.pi / 33 - 1) := by
    nlinarith
  have hlog :
      2 * (16 * Real.pi / 33 - 1) / ((16 * Real.pi / 33 - 1) + 2) ≤
        Real.log (16 * Real.pi / 33) := by
    simpa only [add_sub_cancel] using Real.le_log_one_add_of_nonneg hx
  have hrat :
      (862 : ℝ) / 2081 <
        2 * (16 * Real.pi / 33 - 1) / ((16 * Real.pi / 33 - 1) + 2) := by
    have hden' : 0 < (16 * Real.pi / 33 - 1) + 2 := by positivity
    rw [lt_div_iff₀ hden']
    norm_num [div_eq_mul_inv] at *
    nlinarith
  have hlogTarget :
      (862 : ℝ) / 2081 < Real.log (4 * Real.pi) - Real.log (33 / 4) := by
    rw [← Real.log_div (by positivity) (by norm_num), show
      (4 * Real.pi) / (33 / 4) = 16 * Real.pi / 33 by ring]
    grind
  have hγ : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hbudget :
      (2 / 5 : ℝ) < 1 / 2 + 862 / 2081 - 21 / 41 := by
    norm_num
  nlinarith [Real.pi_lt_d2]

end NumberField.Odlyzko
