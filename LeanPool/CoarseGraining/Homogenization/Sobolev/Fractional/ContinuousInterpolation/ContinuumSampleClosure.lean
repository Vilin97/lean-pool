/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.RootScaleControl

/-!
# Closure of the continuum and sampled continuous K energies

This module reinserts the root triadic sample into the lower continuum-series
comparison, without applying any real-valued totalization to the energies.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The lower triadic-series factor is strictly positive. -/
theorem triadicContinuousKLowerSeriesConstant_pos (s : FractionalOrder) :
    0 < triadicContinuousKLowerSeriesConstant s := by
  unfold triadicContinuousKLowerSeriesConstant
  rw [ENNReal.mul_pos_iff]
  exact ⟨ENNReal.ofReal_pos.2 (by norm_num),
    ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (by norm_num) _)⟩

/-- The lower triadic-series factor is nonzero. -/
theorem triadicContinuousKLowerSeriesConstant_ne_zero (s : FractionalOrder) :
    triadicContinuousKLowerSeriesConstant s ≠ 0 :=
  ne_of_gt (triadicContinuousKLowerSeriesConstant_pos s)

/-- The lower triadic-series factor is finite. -/
theorem triadicContinuousKLowerSeriesConstant_ne_top (s : FractionalOrder) :
    triadicContinuousKLowerSeriesConstant s ≠ ∞ := by
  unfold triadicContinuousKLowerSeriesConstant
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The inverse lower triadic-series factor is finite. -/
theorem triadicContinuousKLowerSeriesConstant_inv_ne_top (s : FractionalOrder) :
    (triadicContinuousKLowerSeriesConstant s)⁻¹ ≠ ∞ :=
  ENNReal.inv_ne_top.2 (triadicContinuousKLowerSeriesConstant_ne_zero s)

/-- The shifted sampled energy is controlled by the continuum K energy after
dividing through by the strictly positive finite lower series factor. -/
theorem triadicContinuousKShiftedSampleEnergy_le_lowerSeriesConstant_inv_mul_continuumEnergy
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKShiftedSampleEnergy s F ≤
      (triadicContinuousKLowerSeriesConstant s)⁻¹ *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t := by
  let C : ℝ≥0∞ := triadicContinuousKLowerSeriesConstant s
  let S : ℝ≥0∞ := triadicContinuousKShiftedSampleEnergy s F
  let I : ℝ≥0∞ := ∫⁻ t in Set.Ioo (0 : ℝ) 1,
    continuousKSeminormIntegrand s.1 F t
  have hC0 : C ≠ 0 := triadicContinuousKLowerSeriesConstant_ne_zero s
  have hCtop : C ≠ ∞ := triadicContinuousKLowerSeriesConstant_ne_top s
  have hcomparison : C * S ≤ I := by
    simpa only [C, S, I] using triadicContinuousKLowerSeriesComparison s F
  calc
    S = C⁻¹ * (C * S) := by
      rw [ENNReal.inv_mul_cancel_left hC0 hCtop]
    _ ≤ C⁻¹ * I := mul_le_mul_right hcomparison _

/-- The full sampled continuous K energy is controlled by the normalized
Euclidean `L²` energy and the continuum K energy. -/
theorem triadicContinuousKSampleEnergy_le_sq_normalizedEuclideanLpENorm_add_lowerSeriesConstant_inv_mul_continuumEnergy
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKSampleEnergy s F ≤
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) ^ 2 +
        (triadicContinuousKLowerSeriesConstant s)⁻¹ *
          ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t := by
  calc
    triadicContinuousKSampleEnergy s F ≤
        ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) ^ 2 +
          triadicContinuousKShiftedSampleEnergy s F :=
      triadicContinuousKSampleEnergy_le_sq_normalizedEuclideanLpENorm_add_shifted s F
    _ ≤ ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) ^ 2 +
        (triadicContinuousKLowerSeriesConstant s)⁻¹ *
          ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t :=
      add_le_add_right
        (triadicContinuousKShiftedSampleEnergy_le_lowerSeriesConstant_inv_mul_continuumEnergy
          s F) _

end

end Homogenization
