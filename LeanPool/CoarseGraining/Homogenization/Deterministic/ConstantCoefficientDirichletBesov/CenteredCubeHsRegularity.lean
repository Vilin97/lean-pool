/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlap
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeScaleTransport
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.ContinuousKFullRegularity

/-!
# Exact centered-cube Euclidean `H^s` Dirichlet regularity

This module first converts the unit-cube continuous interpolation estimate to
the exact Euclidean fractional full norm.  It then transports that estimate to
every centered triadic cube.  The physical full norm carries the essential
root factor `3^(-m s)` in front of its normalized `L²` term, making both terms
scale by the same factor.

## Main definitions

- `centeredCubeEuclideanHsFullENorm`: the homogeneous physical fractional
  full norm.

## Main results

- `exactOverlapRootWeight_originCube_eq_scale_rpow`: the exact root-factor
  formula.
- `centeredCubeEuclideanHsFullENorm_eq_scale_mul_pullbackToUnit`: exact full
  norm scaling.
- `exists_centeredCubeDirichletEuclideanHsFullENormRegularity`: the all-scale
  exact Euclidean `H^s` Dirichlet estimate.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The homogeneous exact Euclidean fractional full norm on a centered cube.
The normalized `L²` term carries the same root-scale weight as the fractional
seminorm. -/
noncomputable def centeredCubeEuclideanHsFullENorm {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : ℝ≥0∞ :=
  exactOverlapRootWeight (originCube d m) s.1 *
      (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
    centeredCubeEuclideanHsESeminorm s F

/-- Evaluation formula for the homogeneous physical fractional full norm. -/
theorem centeredCubeEuclideanHsFullENorm_eq {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsFullENorm s F =
      exactOverlapRootWeight (originCube d m) s.1 *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
        centeredCubeEuclideanHsESeminorm s F :=
  rfl

/-- On `originCube d m`, the overlap root factor is exactly the fractional
dilation factor `(3 ^ m)^(-s)`. -/
theorem exactOverlapRootWeight_originCube_eq_scale_rpow {d : ℕ}
    (m : ℤ) (s : ℝ) :
    exactOverlapRootWeight (originCube d m) s =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s) := by
  unfold exactOverlapRootWeight
  have hscale : ENNReal.ofReal (centeredCubeScale m) =
      (3 : ℝ≥0∞) ^ (m : ℝ) := by
    unfold centeredCubeScale
    rw [← Real.rpow_intCast]
    rw [← ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < 3 by norm_num)]
    norm_num
  rw [hscale, ← ENNReal.rpow_mul]
  congr 1
  simp only [originCube]
  ring

/-- The physical full norm scales homogeneously by `(3 ^ m)^(-s)` under
pullback to the centered unit cube. -/
theorem centeredCubeEuclideanHsFullENorm_eq_scale_mul_pullbackToUnit {d : ℕ}
    {m : ℤ} (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsFullENorm s F =
      (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
        euclideanHsFullENorm s F.pullbackToUnit := by
  rw [centeredCubeEuclideanHsFullENorm_eq,
    exactOverlapRootWeight_originCube_eq_scale_rpow,
    ← CenteredCubeEuclideanL2Field.normalizedEuclideanLpENorm_pullbackToUnit,
    centeredCubeEuclideanHsESeminorm_eq_scale_mul_pullbackToUnit,
    euclideanHsFullENorm_eq]
  rw [mul_add]

private theorem euclideanHsFullENorm_congr_ae {d : ℕ} {s : FractionalOrder}
    {F G : UnitCubeEuclideanL2Field d}
    (hFG : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] G) :
    euclideanHsFullENorm s F = euclideanHsFullENorm s G := by
  unfold euclideanHsFullENorm
  rw [(unitCenteredCubeDomain d).normalizedEuclideanLpENorm_congr_ae
    (2 : ℝ≥0∞) hFG, euclideanHsESeminorm_congr_ae hFG]

/-- The unit-cube weak Dirichlet problem controls the exact Euclidean
fractional full norm.  Both directions of the approved full-norm comparison
are used internally. -/
theorem exists_unitCubeDirichletEuclideanHsFullENormRegularity
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (h : UnitCubeEuclideanL2Field d)
        (w : H10Function (openCubeSet (originCube d 0))),
        CubeDirichletDivergenceProblem (originCube d 0) w h →
          euclideanHsFullENorm s (unitCubeGradientEuclideanL2Field w) ≤
            C * euclideanHsFullENorm s h := by
  rcases exists_unitCubeDirichletContinuousKFullENormRegularity d with
    ⟨CK, hCK, hK⟩
  let A : ℝ≥0∞ := continuousKEuclideanHsFullENormConstant s d
  let C : ℝ≥0∞ := A * CK * A
  refine ⟨C, ?_, ?_⟩
  · exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (continuousKEuclideanHsFullENormConstant_lt_top s d) hCK)
      (continuousKEuclideanHsFullENormConstant_lt_top s d)
  · intro h w hproblem
    calc
      euclideanHsFullENorm s (unitCubeGradientEuclideanL2Field w) ≤
          A * continuousKFullENorm s (unitCubeGradientEuclideanL2Field w) := by
        simpa only [A] using
          euclideanHsFullENorm_le_mul_continuousKFullENorm s
            (unitCubeGradientEuclideanL2Field w)
      _ ≤ A * (CK * continuousKFullENorm s h) := by
        exact mul_le_mul_right (hK s h w hproblem) A
      _ ≤ A * (CK * (A * euclideanHsFullENorm s h)) := by
        exact mul_le_mul_right (mul_le_mul_right
          (continuousKFullENorm_le_mul_euclideanHsFullENorm s h) CK) A
      _ = C * euclideanHsFullENorm s h := by
        simp only [C]
        ring

private theorem centeredCubeHsScaleFactor_pos (m : ℤ) (s : FractionalOrder) :
    0 < (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) :=
  ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (centeredCubeScale_pos m))
    ENNReal.ofReal_ne_top

private theorem centeredCubeHsScaleFactor_ne_top (m : ℤ) (s : FractionalOrder) :
    (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) ≠ ∞ := by
  intro htop
  rcases ENNReal.rpow_eq_top_iff.mp htop with hzero | htop'
  · exact (ENNReal.ofReal_ne_zero_iff.mpr (centeredCubeScale_pos m)) hzero.1
  · exact ENNReal.ofReal_ne_top htop'.1

/-- One finite constant, fixed before the cube scale, datum, and solution,
controls the homogeneous exact Euclidean fractional full norm on every
centered triadic cube. -/
theorem exists_centeredCubeDirichletEuclideanHsFullENormRegularity
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (h : CenteredCubeEuclideanL2Field d m)
        (w : H10Function (openCubeSet (originCube d m))),
        CubeDirichletDivergenceProblem (originCube d m) w h →
          centeredCubeEuclideanHsFullENorm s
              (centeredCubeGradientEuclideanL2Field w) ≤
            C * centeredCubeEuclideanHsFullENorm s h := by
  rcases exists_unitCubeDirichletEuclideanHsFullENormRegularity d s with
    ⟨C, hC, hunit⟩
  refine ⟨C, hC, ?_⟩
  intro m h w hproblem
  let a : ℝ≥0∞ := (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1)
  have ha_zero : a ≠ 0 := (centeredCubeHsScaleFactor_pos m s).ne'
  have ha_top : a ≠ ∞ := centeredCubeHsScaleFactor_ne_top m s
  have hunitProblem : CubeDirichletDivergenceProblem (originCube d 0)
      (centeredCubeNormalizedPullback w) h.pullbackToUnit :=
    cubeDirichletDivergenceProblem_normalizedPullback h w hproblem
  have hunitEstimate := hunit h.pullbackToUnit
    (centeredCubeNormalizedPullback w) hunitProblem
  have hgradient :
      euclideanHsFullENorm s
          (centeredCubeGradientEuclideanL2Field w).pullbackToUnit =
        euclideanHsFullENorm s
          (unitCubeGradientEuclideanL2Field (centeredCubeNormalizedPullback w)) :=
    euclideanHsFullENorm_congr_ae
      (unitCubeGradientEuclideanL2Field_normalizedPullback_ae_eq w).symm
  have hunitEstimate' :
      euclideanHsFullENorm s
          (centeredCubeGradientEuclideanL2Field w).pullbackToUnit ≤
        C * euclideanHsFullENorm s h.pullbackToUnit := by
    rw [hgradient]
    exact hunitEstimate
  rw [centeredCubeEuclideanHsFullENorm_eq_scale_mul_pullbackToUnit,
    centeredCubeEuclideanHsFullENorm_eq_scale_mul_pullbackToUnit]
  change a * euclideanHsFullENorm s
      (centeredCubeGradientEuclideanL2Field w).pullbackToUnit ≤
    C * (a * euclideanHsFullENorm s h.pullbackToUnit)
  rw [show C * (a * euclideanHsFullENorm s h.pullbackToUnit) =
      a * (C * euclideanHsFullENorm s h.pullbackToUnit) by ac_rfl]
  exact (ENNReal.mul_le_mul_iff_right ha_zero ha_top).2 hunitEstimate'

end

end Homogenization
