/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadEventSummability

/-! # Deterministic Thresholds -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Deterministic threshold algebra for bad scales

This file records the real-variable estimates used when choosing the
intermediate scale `ℓ` in the proof of Theorem `t.homogenization.quenched`.
-/

noncomputable section

/-- A logarithmic gap for `ℓ` makes the deterministic centered contribution
fit into half of the bad-event threshold.

The intended substitution is
`x = α (m - N) - t (m - n)`, so that the right side is one half of the
post-discount threshold. -/
theorem prefactor_rpow_three_neg_le_half_rpow_of_log_gap
    {K a x : ℝ} {ℓ : ℕ}
    (ha : 0 < a)
    (hgap :
      (a * Real.log 3)⁻¹ *
          (Real.log (max (2 * K) 1) + x * Real.log 3) ≤ (ℓ : ℝ)) :
    K * Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)) ≤
      (1 / 2 : ℝ) * Real.rpow (3 : ℝ) (-x) := by
  let A : ℝ := max (2 * K) 1
  have hlog3_pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hden_pos : 0 < a * Real.log 3 := mul_pos ha hlog3_pos
  have hA_ge_twoK : 2 * K ≤ A := by
    dsimp [A]
    exact le_max_left _ _
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    exact le_max_right _ _
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge_one
  have hlog_main :
      Real.log A + x * Real.log 3 ≤ a * Real.log 3 * (ℓ : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hgap hden_pos.le
    have hcancel :
        a * Real.log 3 *
            ((a * Real.log 3)⁻¹ *
              (Real.log A + x * Real.log 3)) =
          Real.log A + x * Real.log 3 := by
      field_simp [hden_pos.ne']
    nlinarith
  have hlog_le :
      Real.log A ≤ (a * (ℓ : ℝ) - x) * Real.log 3 := by
    nlinarith
  have hA_le :
      A ≤ Real.rpow (3 : ℝ) (a * (ℓ : ℝ) - x) := by
    have hexp : A ≤ Real.exp ((a * (ℓ : ℝ) - x) * Real.log 3) :=
      (Real.log_le_iff_le_exp hA_pos).mp hlog_le
    have hrpow :
        Real.rpow (3 : ℝ) (a * (ℓ : ℝ) - x) =
          Real.exp ((a * (ℓ : ℝ) - x) * Real.log 3) := by
      calc
        Real.rpow (3 : ℝ) (a * (ℓ : ℝ) - x)
            = Real.exp (Real.log (3 : ℝ) * (a * (ℓ : ℝ) - x)) := by
                simpa using
                  (Real.rpow_def_of_pos (x := (3 : ℝ))
                    (y := a * (ℓ : ℝ) - x) (by norm_num : 0 < (3 : ℝ)))
        _ = Real.exp ((a * (ℓ : ℝ) - x) * Real.log 3) := by
                congr 1
                ring
    rw [hrpow]
    exact hexp
  have htwoK_le :
      2 * K ≤ Real.rpow (3 : ℝ) (a * (ℓ : ℝ) - x) :=
    hA_ge_twoK.trans hA_le
  have hdecay_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hmul :
      (2 * K) * Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)) ≤
        Real.rpow (3 : ℝ) (a * (ℓ : ℝ) - x) *
          Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)) :=
    mul_le_mul_of_nonneg_right htwoK_le hdecay_nonneg
  calc
    K * Real.rpow (3 : ℝ) (-a * (ℓ : ℝ))
        = (1 / 2 : ℝ) *
            ((2 * K) * Real.rpow (3 : ℝ) (-a * (ℓ : ℝ))) := by
            ring
    _ ≤ (1 / 2 : ℝ) *
          (Real.rpow (3 : ℝ) (a * (ℓ : ℝ) - x) *
            Real.rpow (3 : ℝ) (-a * (ℓ : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = (1 / 2 : ℝ) * Real.rpow (3 : ℝ) (-x) := by
            have hprod :
                Real.rpow (3 : ℝ) (a * (ℓ : ℝ) - x) *
                    Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)) =
                  Real.rpow (3 : ℝ) (-x) := by
              calc
                Real.rpow (3 : ℝ) (a * (ℓ : ℝ) - x) *
                    Real.rpow (3 : ℝ) (-a * (ℓ : ℝ))
                    =
                  Real.rpow (3 : ℝ)
                    ((a * (ℓ : ℝ) - x) + (-a * (ℓ : ℝ))) := by
                    exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
                      (a * (ℓ : ℝ) - x) (-a * (ℓ : ℝ))).symm
                _ = Real.rpow (3 : ℝ) (-x) := by
                    congr 1
                    ring
            rw [hprod]

/-- Ceiling form of `prefactor_rpow_three_neg_le_half_rpow_of_log_gap`. -/
theorem prefactor_rpow_three_neg_le_half_rpow_of_natCeil_log_gap
    {K a x : ℝ} (ha : 0 < a) :
    let ℓ : ℕ :=
      Nat.ceil
        ((a * Real.log 3)⁻¹ *
          (Real.log (max (2 * K) 1) + x * Real.log 3))
    K * Real.rpow (3 : ℝ) (-a * (ℓ : ℝ)) ≤
      (1 / 2 : ℝ) * Real.rpow (3 : ℝ) (-x) := by
  intro ℓ
  exact
    prefactor_rpow_three_neg_le_half_rpow_of_log_gap
      (K := K) (a := a) (x := x) (ℓ := ℓ) ha
      (by
        dsimp [ℓ]
        exact Nat.le_ceil _)

/-- The post-discount threshold identity used in the fixed-pair bad-event
estimate. -/
theorem rpow_three_discount_mul_postThreshold
    {t α : ℝ} {m n N : ℕ} :
    Real.rpow (3 : ℝ) (-t * ((m - n : ℕ) : ℝ)) *
        Real.rpow (3 : ℝ)
          (-(α * ((m - N : ℕ) : ℝ) -
            t * ((m - n : ℕ) : ℝ))) =
      Real.rpow (3 : ℝ) (-α * ((m - N : ℕ) : ℝ)) := by
  calc
    Real.rpow (3 : ℝ) (-t * ((m - n : ℕ) : ℝ)) *
        Real.rpow (3 : ℝ)
          (-(α * ((m - N : ℕ) : ℝ) -
            t * ((m - n : ℕ) : ℝ))) =
      Real.rpow (3 : ℝ)
        (-t * ((m - n : ℕ) : ℝ) +
          (-(α * ((m - N : ℕ) : ℝ) -
            t * ((m - n : ℕ) : ℝ)))) := by
        exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
          (-t * ((m - n : ℕ) : ℝ))
          (-(α * ((m - N : ℕ) : ℝ) -
            t * ((m - n : ℕ) : ℝ)))).symm
    _ = Real.rpow (3 : ℝ) (-α * ((m - N : ℕ) : ℝ)) := by
        congr 1
        ring

end

end Section57
end Ch05
end Book
end Homogenization
