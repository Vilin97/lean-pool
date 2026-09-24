/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Pressure Gradient Origin BSlot Energy Holder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CKN.Core.Step4

/-- The subadditivity of the power `6/5` for three terms, with the explicit constant `4`: the
`6/5`-th power of `a + b + c` is bounded by four times the sum of the `6/5`-th powers. It is
obtained from `(x + y) ^ p ≤ 2 ^ (p - 1) * (x ^ p + y ^ p)` applied twice, together with the
numerical bound `2 ^ (6/5 - 1) ≤ 2`. -/
theorem three_add_rpow_six_fifths_le (a b c : ℝ≥0∞) :
    (a + b + c) ^ (6 / 5 : ℝ) ≤ 4 * (a ^ (6 / 5 : ℝ) + b ^ (6 / 5 : ℝ) + c ^ (6 / 5 : ℝ)) := by
  have htwo : (2 : ℝ≥0∞) ^ (6 / 5 - 1 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  have h (x y : ℝ≥0∞) : (x + y) ^ (6 / 5 : ℝ) ≤
      2 * (x ^ (6 / 5 : ℝ) + y ^ (6 / 5 : ℝ)) :=
    (ENNReal.rpow_add_le_mul_rpow_add_rpow x y (by norm_num)).trans
      (mul_le_mul' htwo le_rfl)
  calc
    _ ≤ 2 * ((a + b) ^ (6 / 5 : ℝ) + c ^ (6 / 5 : ℝ)) := h _ _
    _ ≤ 2 * (2 * (a ^ (6 / 5 : ℝ) + b ^ (6 / 5 : ℝ)) + 2 * c ^ (6 / 5 : ℝ)) :=
      mul_le_mul' le_rfl
        (add_le_add (h _ _) (le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 2)))
    _ = _ := by ring

end CKN.Core.Step4
