/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.RootScaleControl
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.EuclideanGagliardoCoordinateBridge

/-!
# Zero-dimensional closure of the continuous interpolation quantities

All vector fields and gradient matrices in dimension zero are forced to vanish. This module
records the resulting exact zero identities for the normalized `L²`, continuous `K`, sampled
series, and Euclidean fractional quantities.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The normalized Euclidean extended `L²` norm vanishes in dimension zero. -/
theorem normalizedEuclideanLpENorm_zero_dim (F : UnitCubeEuclideanL2Field 0) :
    (unitCenteredCubeDomain 0).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F = 0 := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  have hzero : (fun x => euclideanNorm (F x)) = fun _ => (0 : ℝ) := by
    funext x
    rw [show F x = 0 by exact Subsingleton.elim _ _]
    exact euclideanNorm_zero
  rw [hzero, MeasureTheory.eLpNorm_zero']

private theorem continuousKResidualNorm_default_zero_dim
    (F : UnitCubeEuclideanL2Field 0) :
    continuousKResidualNorm F (default : ContinuousKCompetitor 0) = 0 := by
  unfold continuousKResidualNorm BoundedMeasurableDomain.normalizedEuclideanLpNorm
    BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
    BoundedMeasurableDomain.normalizedLpENorm
  change (MeasureTheory.eLpNorm
    (fun x => euclideanNorm (F x - (default : ContinuousKCompetitor 0).toField x))
    (2 : ℝ≥0∞) (unitCenteredCubeDomain 0).normalizedVolume).toReal = 0
  have hzero :
      (fun x => euclideanNorm (F x - (default : ContinuousKCompetitor 0).toField x)) =
        fun _ => (0 : ℝ) := by
    funext x
    rw [show F x - (default : ContinuousKCompetitor 0).toField x = 0 by
      exact Subsingleton.elim _ _]
    exact euclideanNorm_zero
  rw [hzero, MeasureTheory.eLpNorm_zero']
  rfl

private theorem continuousKGradientNorm_default_zero_dim :
    continuousKGradientNorm (default : ContinuousKCompetitor 0) = 0 := by
  unfold continuousKGradientNorm BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
    BoundedMeasurableDomain.normalizedLpENorm
  change (MeasureTheory.eLpNorm
    (fun x => matrixFrobeniusMagnitude ((default : ContinuousKCompetitor 0).gradient x))
    (2 : ℝ≥0∞) (unitCenteredCubeDomain 0).normalizedVolume).toReal = 0
  have hzero :
      (fun x => matrixFrobeniusMagnitude
        ((default : ContinuousKCompetitor 0).gradient x)) = fun _ => (0 : ℝ) := by
    funext x
    rw [show (default : ContinuousKCompetitor 0).gradient x = 0 by
      exact Subsingleton.elim _ _]
    exact matrixFrobeniusMagnitude_zero
  rw [hzero, MeasureTheory.eLpNorm_zero']
  rfl

private theorem continuousKFunctionalCompetitorValue_default_zero_dim
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field 0) :
    continuousKFunctionalCompetitorValue t F default = 0 := by
  unfold continuousKFunctionalCompetitorValue
  rw [continuousKResidualNorm_default_zero_dim,
    continuousKGradientNorm_default_zero_dim]
  norm_num

/-- The continuous `K`-functional vanishes at every scale in dimension zero. -/
theorem continuousKFunctional_zero_dim (t : ContinuousKScale)
    (F : UnitCubeEuclideanL2Field 0) : continuousKFunctional t F = 0 := by
  apply le_antisymm
  · exact (continuousKFunctional_le_competitor t F default).trans_eq
      (continuousKFunctionalCompetitorValue_default_zero_dim t F)
  · exact continuousKFunctional_nonneg t F

/-- Every weighted triadic `K` sample vanishes in dimension zero. -/
theorem triadicContinuousKSampleTerm_zero_dim (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field 0) (j : ℕ) :
    triadicContinuousKSampleTerm s F j = 0 := by
  unfold triadicContinuousKSampleTerm
  rw [continuousKFunctional_zero_dim]
  norm_num

/-- The full triadic sampled `K` energy vanishes in dimension zero. -/
theorem triadicContinuousKSampleEnergy_zero_dim (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field 0) :
    triadicContinuousKSampleEnergy s F = 0 := by
  unfold triadicContinuousKSampleEnergy
  simp only [triadicContinuousKSampleTerm_zero_dim, tsum_zero]

/-- The shifted triadic sampled `K` energy vanishes in dimension zero. -/
theorem triadicContinuousKShiftedSampleEnergy_zero_dim (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field 0) :
    triadicContinuousKShiftedSampleEnergy s F = 0 := by
  unfold triadicContinuousKShiftedSampleEnergy
  simp only [triadicContinuousKSampleTerm_zero_dim, tsum_zero]

/-- The continuum interpolation seminorm vanishes in dimension zero. -/
theorem continuousKSeminorm_zero_dim (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field 0) : continuousKSeminorm s F = 0 := by
  apply le_antisymm
  · calc
      continuousKSeminorm s F ≤
          (triadicContinuousKUpperSeriesConstant s *
            triadicContinuousKSampleEnergy s F) ^ (1 / 2 : ℝ) :=
        triadicContinuousKUpperSeriesComparison_rpow s F
      _ = 0 := by rw [triadicContinuousKSampleEnergy_zero_dim]; norm_num
  · exact bot_le

/-- The exact Euclidean fractional seminorm vanishes in dimension zero. -/
theorem euclideanHsESeminorm_zero_dim (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field 0) : euclideanHsESeminorm s F = 0 := by
  unfold euclideanHsESeminorm
  rw [euclideanHsEnergy_zero_dim]
  norm_num

end

end Homogenization
