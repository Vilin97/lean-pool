/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveDyadicKernel

/-!
# Normalized radii for the paper's finite dyadic blocks

The scale index places the normalized spatial scale in `[1, 2)`. Consequently
each endpoint of the finite block is within a factor of two of the desired
fixed normalized radius. The integer exponents below retain the paper's
exact indexing.
-/

namespace QuadraticCarleson
namespace KrauseLaceyNormalizedBlockRadii


/-- A single positive dilation controls every shifted dyadic radius. -/
theorem normalizedRadius_bracket (a : ℝ) (ha : 0 < a) (j k : ℤ)
    (hlow : 1 ≤ a * (2 : ℝ) ^ j) (hhigh : a * (2 : ℝ) ^ j ≤ 2) :
    (2 : ℝ) ^ (j + k) ≤ (2 : ℝ) ^ (k + 1) / a ∧
      (2 : ℝ) ^ (k + 1) / a ≤ 2 * (2 : ℝ) ^ (j + k) := by
  have hk : 0 ≤ (2 : ℝ) ^ k := (zpow_pos (by norm_num : (0 : ℝ) < 2) k).le
  constructor
  · apply (le_div_iff₀ ha).2
    simp only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    nlinarith [mul_le_mul_of_nonneg_right hhigh hk]
  · apply (div_le_iff₀ ha).2
    simp only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    nlinarith [mul_le_mul_of_nonneg_right hlow hk]

/-- The starting radius corresponds to the fixed normalized radius `1/4`. -/
theorem lowerRadius_bracket (a : ℝ) (ha : 0 < a) (j : ℤ)
    (hlow : 1 ≤ a * (2 : ℝ) ^ j) (hhigh : a * (2 : ℝ) ^ j ≤ 2) :
    (2 : ℝ) ^ (j - 3) ≤ (1 / 4 : ℝ) / a ∧
      (1 / 4 : ℝ) / a ≤ 2 * (2 : ℝ) ^ (j - 3) := by
  have h := normalizedRadius_bracket a ha j (-3) hlow hhigh
  norm_num [← sub_eq_add_neg] at h ⊢
  exact h

/-- The ending radius retains the exact integer index `B - 1` after scaling. -/
theorem upperRadius_bracket (a : ℝ) (ha : 0 < a) (j : ℤ) (B : ℕ)
    (hlow : 1 ≤ a * (2 : ℝ) ^ j) (hhigh : a * (2 : ℝ) ^ j ≤ 2) :
    (2 : ℝ) ^ (j + (B : ℤ) - 2) ≤ (2 : ℝ) ^ ((B : ℤ) - 1) / a ∧
      (2 : ℝ) ^ ((B : ℤ) - 1) / a ≤
        2 * (2 : ℝ) ^ (j + (B : ℤ) - 2) := by
  have h := normalizedRadius_bracket a ha j ((B : ℤ) - 2) hlow hhigh
  simpa only [show j + ((B : ℤ) - 2) = j + (B : ℤ) - 2 by omega,
    show (B : ℤ) - 2 + 1 = (B : ℤ) - 1 by omega] using h

/-- Positive modulation turns the selected scale specification into the
normalization inequality required by the radius comparisons. -/
theorem positiveModulation_scale_bracket (lam : ℝ) (hlam : 0 < lam) :
    1 ≤ Real.sqrt lam * (2 : ℝ) ^ oscillatoryScaleIndex lam 0 hlam.ne' ∧
      Real.sqrt lam * (2 : ℝ) ^ oscillatoryScaleIndex lam 0 hlam.ne' < 2 := by
  simpa only [OscillatoryScaleSpec, abs_of_pos hlam, pow_zero, zero_add,
    pow_one, mul_comm] using oscillatoryScaleIndex_spec lam 0 hlam.ne'

theorem paperBlockLowerRadius_bracket (lam : ℝ) (hlam : 0 < lam) :
    (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam.ne' - 3) ≤
      (1 / 4 : ℝ) / Real.sqrt lam ∧
    (1 / 4 : ℝ) / Real.sqrt lam ≤
      2 * (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam.ne' - 3) := by
  have h := positiveModulation_scale_bracket lam hlam
  exact lowerRadius_bracket (Real.sqrt lam) (Real.sqrt_pos.mpr hlam)
    (oscillatoryScaleIndex lam 0 hlam.ne') h.1 h.2.le

theorem paperBlockUpperRadius_bracket (lam : ℝ) (hlam : 0 < lam) (B : ℕ) :
    (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam.ne' + (B : ℤ) - 2) ≤
      (2 : ℝ) ^ ((B : ℤ) - 1) / Real.sqrt lam ∧
    (2 : ℝ) ^ ((B : ℤ) - 1) / Real.sqrt lam ≤
      2 * (2 : ℝ) ^ (oscillatoryScaleIndex lam 0 hlam.ne' + (B : ℤ) - 2) := by
  have h := positiveModulation_scale_bracket lam hlam
  exact upperRadius_bracket (Real.sqrt lam) (Real.sqrt_pos.mpr hlam)
    (oscillatoryScaleIndex lam 0 hlam.ne') B h.1 h.2.le


end KrauseLaceyNormalizedBlockRadii
end QuadraticCarleson
