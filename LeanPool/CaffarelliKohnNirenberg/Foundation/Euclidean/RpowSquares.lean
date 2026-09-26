/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Rpow Squares

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

noncomputable section

namespace CKN.Foundation.Euclidean

/-- `(κ^{1/2})² = κ` for `κ > 0`. -/
theorem rpow_half_sq {κ : ℝ} (hκ : 0 < κ) : (κ ^ (1 / 2 : ℝ)) ^ 2 = κ := by
  rw [pow_two, ← Real.rpow_add hκ]
  norm_num

/-- `(κ^{-1/2})² = κ⁻¹` for `κ > 0`. -/
theorem rpow_neg_half_sq {κ : ℝ} (hκ : 0 < κ) :
    (κ ^ (-1 / 2 : ℝ)) ^ 2 = κ ^ (-1 : ℝ) := by
  rw [pow_two, ← Real.rpow_add hκ]
  norm_num

/-- `(κ^{1/3})² = κ^{2/3}` for `κ > 0`. -/
theorem rpow_third_sq {κ : ℝ} (hκ : 0 < κ) :
    (κ ^ (1 / 3 : ℝ)) ^ 2 = κ ^ (2 / 3 : ℝ) := by
  rw [pow_two, ← Real.rpow_add hκ]
  norm_num

/-- `(x^{1/2})² = x` for `x ≥ 0`. -/
theorem rpow_half_sq_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

end CKN.Foundation.Euclidean
