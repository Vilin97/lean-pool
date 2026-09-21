/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectRootLocalization

/-!
# Homogeneity for the direct quadratic one-node normalization

The direct estimate is proved after normalizing the two root averages.  This
file isolates the exact operator identity needed to restore the original
scales.  No stopping-time argument is used here.
-/

open MeasureTheory
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectNormalization

open KrauseLaceyStoppingRecursion


noncomputable section

/-- Exact scaling of a local real `p`-mass by a nonnegative real scalar. -/
theorem integral_norm_rpow_smul
    (c : ℝ) (hc : 0 ≤ c) (f : L0Infinity) (I : RealInterval) (p : ℝ) :
    (∫ x in I.carrier, ‖L0Infinity.smul (c : ℂ) f x‖ ^ p) =
      c ^ p * ∫ x in I.carrier, ‖f x‖ ^ p := by
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [L0Infinity.smul_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc]
  rw [Real.mul_rpow hc (norm_nonneg (f x))]

/-- Normalized local averages are exactly homogeneous under multiplication
by a positive real scalar. -/
theorem localAverage_smul
    (c : ℝ) (hc : 0 < c) (f : L0Infinity) (I : RealInterval)
    (p : ℝ) (hp : 0 < p) :
    localAverage p (L0Infinity.smul (c : ℂ) f) I =
      c * localAverage p f I := by
  unfold localAverage
  rw [integral_norm_rpow_smul c hc.le f I p]
  have hmass : 0 ≤ I.length⁻¹ * ∫ x in I.carrier, ‖f x‖ ^ p :=
    mul_nonneg (inv_nonneg.mpr I.length_pos.le)
      (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (f x)) p)
  rw [show I.length⁻¹ *
      (c ^ p * ∫ x in I.carrier, ‖f x‖ ^ p) =
        c ^ p * (I.length⁻¹ * ∫ x in I.carrier, ‖f x‖ ^ p) by ring]
  rw [Real.mul_rpow (Real.rpow_nonneg hc.le p) hmass]
  rw [← Real.rpow_mul hc.le]
  have hcancel : p * (1 / p) = 1 := by field_simp [hp.ne']
  rw [hcancel, Real.rpow_one]

private theorem localizedTailAction_smul
    (c : ℂ) (ell₀ : ℤ) (scale : RealInterval → ℤ)
    (S : Finset RealInterval) (f : L0Infinity) (ell : ℤ) (x : ℝ) :
    localizedTailAction scale S (L0Infinity.smul c f) ell x =
      c * localizedTailAction scale S f ell x := by
  classical
  have hpiece (I : RealInterval) :
      krauseLaceyLocalizedPiece 1 (scale I) I (L0Infinity.smul c f) x =
        c * krauseLaceyLocalizedPiece 1 (scale I) I f x := by
    unfold krauseLaceyLocalizedPiece
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : x - y ∈ I.centralThird
    · simp only [Set.indicator_of_mem hy, L0Infinity.smul_apply]
      ring
    · simp only [Set.indicator_of_notMem hy, mul_zero]
  unfold localizedTailAction
  calc
    (∑ I ∈ S, if (2 : ℝ) ^ ell ≤ I.length then
        krauseLaceyLocalizedPiece 1 (scale I) I (L0Infinity.smul c f) x else 0) =
        ∑ I ∈ S, c * (if (2 : ℝ) ^ ell ≤ I.length then
          krauseLaceyLocalizedPiece 1 (scale I) I f x else 0) := by
      apply Finset.sum_congr rfl
      intro I hI
      by_cases hlen : (2 : ℝ) ^ ell ≤ I.length
      · simp only [if_pos hlen, hpiece]
      · simp only [if_neg hlen, mul_zero]
    _ = c * ∑ I ∈ S, if (2 : ℝ) ^ ell ≤ I.length then
          krauseLaceyLocalizedPiece 1 (scale I) I f x else 0 := by
      rw [Finset.mul_sum]

/-- The localized maximal tail is exactly homogeneous under complex scalar
multiplication of its input. -/
theorem localizedTailMaximal_smul
    (c : ℂ) (ell₀ : ℤ) (scale : RealInterval → ℤ)
    (S : Finset RealInterval) (f : L0Infinity) (x : ℝ) :
    localizedTailMaximal ell₀ scale S (L0Infinity.smul c f) x =
      ‖c‖ₑ * localizedTailMaximal ell₀ scale S f x := by
  unfold localizedTailMaximal
  calc
    (⨆ ell : {ell : ℤ // ell₀ ≤ ell},
        ‖localizedTailAction scale S (L0Infinity.smul c f) ell.1 x‖ₑ) =
        ⨆ ell : {ell : ℤ // ell₀ ≤ ell},
          ‖c‖ₑ * ‖localizedTailAction scale S f ell.1 x‖ₑ := by
      apply iSup_congr
      intro ell
      rw [localizedTailAction_smul c ell₀ scale S f ell.1 x, enorm_mul]
    _ = ‖c‖ₑ * ⨆ ell : {ell : ℤ // ell₀ ≤ ell},
          ‖localizedTailAction scale S f ell.1 x‖ₑ :=
      (ENNReal.mul_iSup _ _).symm


end
end KrauseLaceyQuadraticDirectNormalization
end QuadraticCarleson
