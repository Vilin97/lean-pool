/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.MeanInequalitiesPow
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.AllDimensionalComposition
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuumSampleClosure
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.EuclideanHsMeasurability

/-!
# Convention-neutral comparison of continuous interpolation seminorms

This module takes half-powers of the all-dimensional energy comparisons. It keeps the
directional seminorm bounds separate for use by the approved source-facing full norm.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

private theorem rpow_half_mul_sq_add_mul_le (A B C D : ℝ≥0∞) :
    (A * (B ^ 2 + C * D)) ^ (1 / 2 : ℝ) ≤
      (A ^ (1 / 2 : ℝ) * max 1 (C ^ (1 / 2 : ℝ))) *
        (B + D ^ (1 / 2 : ℝ)) := by
  have hB : (B ^ 2) ^ (1 / 2 : ℝ) = B := by
    simpa only [one_div] using!
      ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) B
  have hCD :
      (C * D) ^ (1 / 2 : ℝ) = C ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  calc
    (A * (B ^ 2 + C * D)) ^ (1 / 2 : ℝ) =
        A ^ (1 / 2 : ℝ) * (B ^ 2 + C * D) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg]
      norm_num
    _ ≤ A ^ (1 / 2 : ℝ) *
        ((B ^ 2) ^ (1 / 2 : ℝ) + (C * D) ^ (1 / 2 : ℝ)) := by
      exact mul_le_mul_right
        (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)) _
    _ = A ^ (1 / 2 : ℝ) *
        (B + C ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ)) := by
      rw [hB, hCD]
    _ ≤ A ^ (1 / 2 : ℝ) *
        (max 1 (C ^ (1 / 2 : ℝ)) * B +
          max 1 (C ^ (1 / 2 : ℝ)) * D ^ (1 / 2 : ℝ)) := by
      apply mul_le_mul_right
      exact add_le_add
        (by simpa only [one_mul] using
          mul_le_mul_left (le_max_left 1 (C ^ (1 / 2 : ℝ))) B)
        (mul_le_mul_left (le_max_right 1 (C ^ (1 / 2 : ℝ)))
          (D ^ (1 / 2 : ℝ)))
    _ = (A ^ (1 / 2 : ℝ) * max 1 (C ^ (1 / 2 : ℝ))) *
        (B + D ^ (1 / 2 : ℝ)) := by
      ring

private theorem triadicContinuousKUpperSeriesConstant_lt_top (s : FractionalOrder) :
    triadicContinuousKUpperSeriesConstant s < ∞ := by
  unfold triadicContinuousKUpperSeriesConstant
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

private theorem normalizedEuclideanLpENorm_lt_top {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F < ∞ := by
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm] using
    F.euclideanMagnitudeMemL2.eLpNorm_lt_top

/-- The finite constant in the continuous `K`-seminorm to Euclidean `H^s`-seminorm
direction. -/
noncomputable def continuousKToEuclideanHsSeminormConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  (triadicContinuousKUpperSeriesConstant s *
    allDimensionalSampleToHsConstant s d) ^ (1 / 2 : ℝ)

/-- The continuous `K`-to-Euclidean-`H^s` seminorm constant is finite. -/
theorem continuousKToEuclideanHsSeminormConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    continuousKToEuclideanHsSeminormConstant s d < ∞ := by
  unfold continuousKToEuclideanHsSeminormConstant
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.mul_lt_top
      (triadicContinuousKUpperSeriesConstant_lt_top s)
      (allDimensionalSampleToHsConstant_lt_top s d)).ne

/-- The finite constant in the Euclidean `H^s`-seminorm to continuous `K`-seminorm
direction, including the normalized `L²` root-scale term. -/
noncomputable def euclideanHsToContinuousKSeminormConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  (allDimensionalHsToSampleConstant d) ^ (1 / 2 : ℝ) *
    max 1 ((triadicContinuousKLowerSeriesConstant s)⁻¹ ^ (1 / 2 : ℝ))

/-- The Euclidean-`H^s`-to-continuous-`K` seminorm constant is finite. -/
theorem euclideanHsToContinuousKSeminormConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    euclideanHsToContinuousKSeminormConstant s d < ∞ := by
  unfold euclideanHsToContinuousKSeminormConstant
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (allDimensionalHsToSampleConstant_lt_top d).ne
  · rw [max_lt_iff]
    exact ⟨ENNReal.one_lt_top,
      ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (triadicContinuousKLowerSeriesConstant_inv_ne_top s)⟩

/-- In every dimension, the exact Euclidean fractional seminorm controls the continuous
`K`-seminorm through an explicit finite constant. -/
theorem continuousKSeminorm_le_mul_euclideanHsESeminorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    continuousKSeminorm s F ≤
      continuousKToEuclideanHsSeminormConstant s d * euclideanHsESeminorm s F := by
  calc
    continuousKSeminorm s F ≤
        (triadicContinuousKUpperSeriesConstant s *
          triadicContinuousKSampleEnergy s F) ^ (1 / 2 : ℝ) :=
      triadicContinuousKUpperSeriesComparison_rpow s F
    _ ≤ (triadicContinuousKUpperSeriesConstant s *
        (allDimensionalSampleToHsConstant s d * euclideanHsEnergy s F)) ^
          (1 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact mul_le_mul_right
        (triadicContinuousKSampleEnergy_le_mul_euclideanHsEnergy_all_dim s F) _
    _ = continuousKToEuclideanHsSeminormConstant s d *
        euclideanHsESeminorm s F := by
      unfold continuousKToEuclideanHsSeminormConstant euclideanHsESeminorm
      rw [← mul_assoc,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      norm_num

/-- In every dimension, the continuous `K`-seminorm and normalized Euclidean `L²` norm
control the exact Euclidean fractional seminorm through an explicit finite constant. -/
theorem euclideanHsESeminorm_le_mul_normalizedEuclideanLpENorm_add_continuousKSeminorm
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsESeminorm s F ≤
      euclideanHsToContinuousKSeminormConstant s d *
        ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
          continuousKSeminorm s F) := by
  let L : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F
  let I : ℝ≥0∞ := ∫⁻ t in Set.Ioo (0 : ℝ) 1,
    continuousKSeminormIntegrand s.1 F t
  let A : ℝ≥0∞ := allDimensionalHsToSampleConstant d
  let C : ℝ≥0∞ := (triadicContinuousKLowerSeriesConstant s)⁻¹
  calc
    euclideanHsESeminorm s F = euclideanHsEnergy s F ^ (1 / 2 : ℝ) := by
      unfold euclideanHsESeminorm
      norm_num
    _ ≤ (A * triadicContinuousKSampleEnergy s F) ^ (1 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      simpa only [A] using
        euclideanHsEnergy_le_mul_triadicContinuousKSampleEnergy_all_dim s F
    _ ≤ (A * (L ^ 2 + C * I)) ^ (1 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply mul_le_mul_right
      calc
        triadicContinuousKSampleEnergy s F ≤ L ^ 2 +
            triadicContinuousKShiftedSampleEnergy s F := by
          simpa only [L] using
            triadicContinuousKSampleEnergy_le_sq_normalizedEuclideanLpENorm_add_shifted
              s F
        _ ≤ L ^ 2 + C * I := by
          apply add_le_add_right
          simpa only [C, I] using
            triadicContinuousKShiftedSampleEnergy_le_lowerSeriesConstant_inv_mul_continuumEnergy
              s F
    _ ≤ (A ^ (1 / 2 : ℝ) * max 1 (C ^ (1 / 2 : ℝ))) *
        (L + I ^ (1 / 2 : ℝ)) :=
      rpow_half_mul_sq_add_mul_le A L C I
    _ = euclideanHsToContinuousKSeminormConstant s d *
        ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
          continuousKSeminorm s F) := by
      rfl

/-- The exact Euclidean fractional seminorm is finite exactly when the continuous
`K`-seminorm is finite. -/
theorem continuousKSeminorm_lt_top_iff_euclideanHsESeminorm_lt_top {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    continuousKSeminorm s F < ∞ ↔ euclideanHsESeminorm s F < ∞ := by
  constructor
  · intro hK
    exact lt_of_le_of_lt
      (euclideanHsESeminorm_le_mul_normalizedEuclideanLpENorm_add_continuousKSeminorm
        s F)
      (ENNReal.mul_lt_top
        (euclideanHsToContinuousKSeminormConstant_lt_top s d)
        (ENNReal.add_lt_top.2 ⟨normalizedEuclideanLpENorm_lt_top F, hK⟩))
  · intro hHs
    exact lt_of_le_of_lt
      (continuousKSeminorm_le_mul_euclideanHsESeminorm s F)
      (ENNReal.mul_lt_top
        (continuousKToEuclideanHsSeminormConstant_lt_top s d) hHs)

/-- Exact Euclidean fractional membership is equivalent to finiteness of the
continuous `K`-seminorm, with no measurable-representative or dimension hypothesis. -/
theorem memEuclideanHs_iff_continuousKSeminorm_lt_top {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    MemEuclideanHs s F ↔ continuousKSeminorm s F < ∞ := by
  rw [memEuclideanHs_iff_euclideanHsESeminorm_lt_top]
  exact (continuousKSeminorm_lt_top_iff_euclideanHsESeminorm_lt_top s F).symm

end

end Homogenization
