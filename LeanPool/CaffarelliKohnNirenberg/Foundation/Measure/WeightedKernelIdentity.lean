/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Weighted Kernel Identity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped ENNReal

namespace CKN.Foundation.Measure

/-- An algebraic identity in extended reals used in the strong-type maximal estimates:
rewriting `C / (t/2) * A * t^(p-1)` as `2*C * (t^(p-2) * A)`. -/
theorem div_ofReal_half_mul_ofReal_rpow_sub_one {C A : ℝ≥0∞} {t p : ℝ} (ht : 0 < t) :
    (C / ENNReal.ofReal (t / 2) * A) * ENNReal.ofReal (t ^ (p - 1)) =
      (2 * C) * (ENNReal.ofReal (t ^ (p - 2)) * A) := by
  have hpow : t ^ (p - 2) * t = t ^ (p - 1) := by
    calc
      t ^ (p - 2) * t = t ^ (p - 2) * t ^ 1 := by rw [Real.rpow_one]
      _ = t ^ ((p - 2) + 1) := (Real.rpow_add ht (p - 2) 1).symm
      _ = t ^ (p - 1) := by
        congr 1
        ring
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  have httop : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
  rw [← hpow, ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inr httop) (Or.inl (by simp))]
  simp only [inv_inv]
  calc
    _ = 2 * C * A * ENNReal.ofReal (t ^ (p - 2)) *
        ((ENNReal.ofReal t)⁻¹ * ENNReal.ofReal t) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel ht0 httop]; ring

end CKN.Foundation.Measure
