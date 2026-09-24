/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsM4

/-! # Finiteness of the explicit Adams constants

The geometric series and maximal-function constants are finite under the
same strict exponent conditions as the potential estimate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Endgame

private theorem dyadic_series_lt_top {a : ℝ} (ha : a < 0) (b : ℝ) :
    (∑' n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) * a + b)) < ∞ := by
  have heq : ∀ n : ℕ, (2 : ℝ≥0∞) ^ ((n : ℝ) * a + b) =
      ((2 : ℝ≥0∞) ^ a) ^ n * (2 : ℝ≥0∞) ^ b := by
    intro n
    rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num), mul_comm (n : ℝ) a,
      ENNReal.rpow_mul, ENNReal.rpow_natCast]
  simp_rw [heq]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_lt_top
    (tsum_geometric_lt_top.mpr (ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) ha))
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)))

/-- The near-field geometric constant is finite at every positive order. -/
theorem hedberg_near_constant_lt_top {β : ℝ} (hβ : 0 < β) :
    parabolicHedbergNearConstant β < ∞ := by
  have hseries : (∑' n : ℕ, ENNReal.ofReal
      (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β)) < ∞ := by
    have heq : ∀ n : ℕ, ENNReal.ofReal
        (((2 : ℝ) ^ (Int.negSucc n : ℝ)) ^ β) =
          (2 : ℝ≥0∞) ^ ((n : ℝ) * (-β) + (-β)) := by
      intro n
      rw [← Real.rpow_mul (by norm_num), ← ENNReal.ofReal_rpow_of_pos (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat, Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    simp_rw [heq]
    exact dyadic_series_lt_top (neg_neg_of_pos hβ) (-β)
  unfold parabolicHedbergNearConstant
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        Integration.volume_parabolicCylinder_lt_top)) hseries

/-- The far-field geometric constant is finite in the subcritical range. -/
theorem tail_kernel_constant_lt_top {β τ : ℝ} (hτ : 0 < τ) (hβτ : β * τ < 5) :
    parabolicTailKernelConstant β τ < ∞ := by
  have ha : β - 5 / τ < 0 := by
    have hdiv := (lt_div_iff₀ hτ).mpr hβτ
    linarith only [hdiv]
  simpa only [parabolicTailKernelConstant, ENNReal.ofReal_ofNat] using
    dyadic_series_lt_top ha (2 * (5 * (1 - 1 / τ)))

/-- The explicit maximal-function constant is finite for `P > 1`. -/
theorem maximal_strong_constant_lt_top {P : ℝ} (hP : 1 < P) :
    parabolicMaximalStrongConstant P < ∞ := by
  unfold parabolicMaximalStrongConstant
  have hden : ENNReal.ofReal (P - 1) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr hP)).ne'
  have htwo : (2 : ℝ≥0∞) ^ P < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (by linarith only [hP]) (by norm_num)
  apply ENNReal.div_lt_top
  · exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      htwo
      ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top).ne
  · exact hden

/-- The localized maximal constant is finite throughout the Adams range. -/
theorem adams_maximal_constant_lt_top {P τ : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) :
    parabolicAdamsMaximalConstant P τ < ∞ := by
  have hP0 : 0 < P := by linarith only [hP]
  have hτ0 : 0 < τ := hP0.trans_le hPτ
  have hV : volume (parabolicCylinder 0 0 1) < ∞ :=
    Integration.volume_parabolicCylinder_lt_top
  have hV0 : volume (parabolicCylinder 0 0 1) ≠ 0 :=
    (Integration.volume_parabolicCylinder_pos (by norm_num)).ne'
  have ha : 0 ≤ 1 - 1 / P := by
    have h := (div_le_one hP0).mpr hP.le
    linarith only [h]
  have hb : 0 ≤ 5 * (1 - P / τ) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr ((div_le_one hτ0).mpr hPτ))
  have hpow : volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg ha hV.ne
  have hratio : ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
      volume (parabolicCylinder 0 0 1)) < ∞ := by
    apply ENNReal.div_lt_top _ hV0
    exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.ofReal_ne_top
  unfold parabolicAdamsMaximalConstant
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hP.le) (by norm_num)
  · apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.mul_lt_top (maximal_strong_constant_lt_top hP)
        (ENNReal.rpow_lt_top_of_nonneg hb ENNReal.ofReal_ne_top)
    · exact ENNReal.mul_lt_top hV (ENNReal.rpow_lt_top_of_nonneg hP0.le
        (ENNReal.mul_ne_top hratio.ne hpow.ne))

/-- No finiteness assumption on the explicit Adams coefficient is needed
in the strict subcritical exponent range. -/
theorem adams_potential_constant_lt_top {β P τ : ℝ}
    (hβ : 0 < β) (hP : 1 < P) (hPτ : P ≤ τ) (hβτ : β * τ < 5) :
    parabolicAdamsPotentialConstant β P τ < ∞ := by
  have hP0 : 0 < P := by linarith only [hP]
  have hτ0 : 0 < τ := hP0.trans_le hPτ
  have hlam : 0 < 1 - β * τ / 5 := by linarith only [hβτ]
  have hs : 0 < P / (1 - β * τ / 5) := div_pos hP0 hlam
  have hθ : 0 ≤ β * τ / 5 := by positivity
  have ha : 0 ≤ 1 - 1 / P := by
    have h := (div_le_one hP0).mpr hP.le
    linarith only [h]
  have hD : volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg ha Integration.volume_parabolicCylinder_lt_top.ne
  have hsum : parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ < ∞ :=
    ENNReal.add_lt_top.mpr
      ⟨hedberg_near_constant_lt_top hβ, tail_kernel_constant_lt_top hτ0 hβτ⟩
  unfold parabolicAdamsPotentialConstant
  apply ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hs.le)
  apply ENNReal.mul_ne_top
  · exact (ENNReal.rpow_lt_top_of_nonneg hs.le
      (ENNReal.mul_ne_top hsum.ne
        (ENNReal.rpow_ne_top_of_nonneg hθ hD.ne))).ne
  · exact (adams_maximal_constant_lt_top hP hPτ).ne

end CKN.Core.Endgame
