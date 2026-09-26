/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.TriadicSeries

/-!
# Root-scale control for the sampled continuous K energy

The continuum scale integral omits the endpoint `t = 1`. This module controls that missing
triadic sample directly with the zero `H¹` competitor and separates it exactly from the shifted
sampled energy.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

private theorem continuousKGradientNorm_default_eq_zero {d : ℕ} :
    continuousKGradientNorm (default : ContinuousKCompetitor d) = 0 := by
  unfold continuousKGradientNorm
  calc
    (unitCenteredCubeDomain d).normalizedLpNorm (2 : ℝ≥0∞)
        (fun x => matrixFrobeniusMagnitude
          ((default : ContinuousKCompetitor d).gradient x))
        (default : ContinuousKCompetitor d).gradientFrobeniusMemL2 =
      (unitCenteredCubeDomain d).normalizedLpNorm (2 : ℝ≥0∞)
        (fun _ => (0 : ℝ)) MeasureTheory.MemLp.zero' := by
          apply BoundedMeasurableDomain.normalizedLpNorm_congr_ae
          filter_upwards [] with x
          rw [show (default : ContinuousKCompetitor d).gradient x = 0 by
            ext i j
            rfl]
          exact matrixFrobeniusMagnitude_zero
    _ = 0 := by
      unfold BoundedMeasurableDomain.normalizedLpNorm
        BoundedMeasurableDomain.normalizedLpFiniteENorm
        BoundedMeasurableDomain.normalizedLpENorm
      simp [MeasureTheory.eLpNorm'_eq_lintegral_enorm]

private theorem ofReal_continuousKResidualNorm_default_eq_normalizedEuclideanLpENorm
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    ENNReal.ofReal
        (continuousKResidualNorm F (default : ContinuousKCompetitor d)) =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
  have hresidual :
      (fun x => euclideanNorm (F x - (default : ContinuousKCompetitor d).toField x)) =
        fun x => euclideanNorm (F x) := by
    funext x
    rw [show (default : ContinuousKCompetitor d).toField x = 0 by
      ext i
      rfl]
    exact congrArg euclideanNorm (sub_zero (F x))
  unfold continuousKResidualNorm BoundedMeasurableDomain.normalizedEuclideanLpNorm
    BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
    BoundedMeasurableDomain.normalizedLpENorm
  simp only [show (2 : ℝ≥0∞) ≠ 0 by norm_num,
    show (2 : ℝ≥0∞) ≠ ∞ by norm_num, if_false, ENNReal.toReal_ofNat]
  change ENNReal.ofReal
      (MeasureTheory.eLpNorm'
        (fun x => euclideanNorm (F x - (default : ContinuousKCompetitor d).toField x))
        2 (unitCenteredCubeDomain d).normalizedVolume).toReal = _
  rw [hresidual]
  have hfinite : MeasureTheory.eLpNorm' (fun x => euclideanNorm (F x))
      2 (unitCenteredCubeDomain d).normalizedVolume ≠ ∞ := by
    have h := F.euclideanMagnitudeMemL2.eLpNorm_ne_top
    rw [MeasureTheory.eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)
      F.euclideanMagnitudeMemL2.aestronglyMeasurable] at h
    exact h
  exact ENNReal.ofReal_toReal hfinite

private theorem continuousKFunctional_le_residualNorm_default {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t F ≤
      continuousKResidualNorm F (default : ContinuousKCompetitor d) := by
  calc
    continuousKFunctional t F ≤
        continuousKFunctionalCompetitorValue t F default :=
      continuousKFunctional_le_competitor t F default
    _ = continuousKResidualNorm F default := by
      unfold continuousKFunctionalCompetitorValue
      rw [continuousKGradientNorm_default_eq_zero]
      simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero,
        Real.sqrt_sq_eq_abs,
        abs_of_nonneg (continuousKResidualNorm_nonneg F default)]

/-- The endpoint sample at `t = 1` is controlled by the square of the exact normalized
Euclidean extended `L²` norm. This is valid in every dimension without extra assumptions. -/
theorem triadicContinuousKSampleTerm_zero_le_sq_normalizedEuclideanLpENorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKSampleTerm s F 0 ≤
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) ^ 2 := by
  have hK :
      continuousKFunctional (triadicContinuousKScale 0) F ≤
        continuousKResidualNorm F (default : ContinuousKCompetitor d) :=
    continuousKFunctional_le_residualNorm_default (triadicContinuousKScale 0) F
  have hsq :
      continuousKFunctional (triadicContinuousKScale 0) F ^ 2 ≤
        continuousKResidualNorm F (default : ContinuousKCompetitor d) ^ 2 :=
    (sq_le_sq₀
      (continuousKFunctional_nonneg (triadicContinuousKScale 0) F)
      (continuousKResidualNorm_nonneg F default)).2 hK
  calc
    triadicContinuousKSampleTerm s F 0 =
        ENNReal.ofReal (continuousKFunctional (triadicContinuousKScale 0) F ^ 2) := by
      simp [triadicContinuousKSampleTerm, triadicContinuousKScale]
    _ ≤ ENNReal.ofReal
        (continuousKResidualNorm F (default : ContinuousKCompetitor d) ^ 2) :=
      ENNReal.ofReal_le_ofReal hsq
    _ = ENNReal.ofReal
          (continuousKResidualNorm F (default : ContinuousKCompetitor d)) ^ 2 := by
      rw [ENNReal.ofReal_pow (continuousKResidualNorm_nonneg F default)]
    _ = ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) F) ^ 2 := by
      rw [ofReal_continuousKResidualNorm_default_eq_normalizedEuclideanLpENorm]

/-- The sampled energy is exactly its root sample plus the shifted sampled energy. -/
theorem triadicContinuousKSampleEnergy_eq_root_add_shifted {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKSampleEnergy s F =
      triadicContinuousKSampleTerm s F 0 +
        triadicContinuousKShiftedSampleEnergy s F := by
  unfold triadicContinuousKSampleEnergy triadicContinuousKShiftedSampleEnergy
  exact tsum_eq_zero_add' ENNReal.summable

/-- The full sampled energy is bounded by the normalized Euclidean `L²` square plus the shifted
sampled energy. -/
theorem triadicContinuousKSampleEnergy_le_sq_normalizedEuclideanLpENorm_add_shifted {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    triadicContinuousKSampleEnergy s F ≤
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) ^ 2 +
        triadicContinuousKShiftedSampleEnergy s F := by
  rw [triadicContinuousKSampleEnergy_eq_root_add_shifted]
  exact add_le_add
    (triadicContinuousKSampleTerm_zero_le_sq_normalizedEuclideanLpENorm s F) le_rfl

end

end Homogenization
