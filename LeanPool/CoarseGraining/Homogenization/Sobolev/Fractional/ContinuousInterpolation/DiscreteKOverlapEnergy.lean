/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.ConcreteAveraging
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapPoincare
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKBridge
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.OverlapGagliardoBridge

/-!
# Extended discrete K-functional energy and concrete overlap comparison

The discrete K-functional energy is the `ℝ≥0∞` supremum of its finite squared
partial seminorms.  Both comparison directions below are lifted directly from
proved finite-depth averaging and overlap-Poincare estimates.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The extended internal discrete K-functional energy on the centered unit
cube, defined only through finite partial sums. -/
noncomputable def extendedDiscreteKFunctionalEnergy {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal
    ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2)

/-- Every finite squared discrete K-functional partial seminorm is bounded by
the extended discrete energy. -/
theorem ofReal_sq_cubeKPartialSeminorm_le_extendedDiscreteKFunctionalEnergy
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (N : ℕ) :
    ENNReal.ofReal
        ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2) ≤
      extendedDiscreteKFunctionalEnergy s F :=
  le_iSup (fun M : ℕ => ENNReal.ofReal
    ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 M F) ^ 2)) N

private theorem UnitCubeEuclideanL2Field.memLp_originCube_normalizedCubeMeasure
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) := by
  rw [normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  apply MemLp.of_eval
  intro i
  have hF := F.euclideanMemL2
  rw [memLp_piLp_iff] at hF
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF i

/-- The concrete overlap-averaging constant after combining residual and
gradient contributions. -/
noncomputable def discreteKOverlapAveragingConstant (d : ℕ) : ℝ :=
  2 * concreteOverlapAveragingCompetitorConstant d

theorem discreteKOverlapAveragingConstant_nonneg (d : ℕ) :
    0 ≤ discreteKOverlapAveragingConstant d := by
  unfold discreteKOverlapAveragingConstant
  exact mul_nonneg (by norm_num) (concreteOverlapAveragingCompetitorConstant_nonneg d)

/-- The squared concrete averaging factor remains finite after promotion to
extended nonnegative values. -/
theorem discreteKOverlapAveragingConstant_sq_lt_top (d : ℕ) :
    ENNReal.ofReal (discreteKOverlapAveragingConstant d ^ 2) < ∞ :=
  ENNReal.ofReal_lt_top

/-- The concrete overlap-Poincare constant after assembling one K-functional
competitor value. -/
noncomputable def overlapDiscreteKConstant (d : ℕ) : ℝ :=
  8 * (3 ^ d : ℝ) + 2 * (cubeVectorH1OverlapPoincareConstant d) ^ 2 + 1

theorem overlapDiscreteKConstant_nonneg (d : ℕ) :
    0 ≤ overlapDiscreteKConstant d := by
  unfold overlapDiscreteKConstant
  positivity

/-- The squared concrete overlap-Poincare factor remains finite after
promotion to extended nonnegative values. -/
theorem overlapDiscreteKConstant_sq_lt_top (d : ℕ) :
    ENNReal.ofReal (overlapDiscreteKConstant d ^ 2) < ∞ :=
  ENNReal.ofReal_lt_top

private theorem cubeKPartialSeminorm_le_mul_overlapPartialSeminorm
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (N : ℕ) :
    cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F ≤
      discreteKOverlapAveragingConstant d *
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo (originCube d 0) s.1 N F := by
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) :=
    F.memLp_originCube_normalizedCubeMeasure
  apply
    cubeKBesovVectorPartialSeminormTwo_le_mul_cubeBesovOverlappingPositiveVectorPartialSeminormTwo_of_forall_depthSeminorm_le
  · exact discreteKOverlapAveragingConstant_nonneg d
  · intro j _
    exact
      (cubeKBesovDepthBoundByOverlappingPositiveUniform_of_overlapAveragingCompetitorEstimate
        (concreteOverlapAveragingCompetitorConstant_nonneg d)
        (cubeKBesovOverlapAveragingCompetitorEstimate_concrete d)).2
        s.2.1 s.2.2 (originCube d 0) F j hF

private theorem overlapPartialSeminorm_le_mul_cubeKPartialSeminorm
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (N : ℕ) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo (originCube d 0) s.1 N F ≤
      overlapDiscreteKConstant d *
        cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F := by
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) :=
    F.memLp_originCube_normalizedCubeMeasure
  simpa only [overlapDiscreteKConstant] using
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_mul_cubeKBesovVectorPartialSeminormTwo_of_overlapPoincare
      (cubeVectorH1OverlapPoincareConstant_nonneg d)
      (cubeVectorH1OverlapPoincareEstimate d)
      (originCube d 0) s.1 N F hF

private theorem ofReal_sq_le_mul_of_nonneg_mul
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : A ≤ C * B) :
    ENNReal.ofReal (A ^ 2) ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (B ^ 2) := by
  have hCB : 0 ≤ C * B := mul_nonneg hC hB
  have hsq : A ^ 2 ≤ C ^ 2 * B ^ 2 := by
    calc
      A ^ 2 ≤ (C * B) ^ 2 := (sq_le_sq₀ hA hCB).mpr h
      _ = C ^ 2 * B ^ 2 := by ring
  calc
    ENNReal.ofReal (A ^ 2) ≤ ENNReal.ofReal (C ^ 2 * B ^ 2) :=
      ENNReal.ofReal_le_ofReal hsq
    _ = ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (B ^ 2) := by
      rw [ENNReal.ofReal_mul (sq_nonneg C)]

/-- The extended discrete K-functional energy is controlled by the extended
overlap energy using only the concrete overlap-averaging producer. -/
theorem extendedDiscreteKFunctionalEnergy_le_mul_extendedVectorOverlapBesovEnergy
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    extendedDiscreteKFunctionalEnergy s F ≤
      ENNReal.ofReal (discreteKOverlapAveragingConstant d ^ 2) *
        extendedVectorOverlapBesovEnergy s F := by
  refine iSup_le fun N => ?_
  have hfinite := cubeKPartialSeminorm_le_mul_overlapPartialSeminorm s F N
  calc
    ENNReal.ofReal
        ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2)
        ≤ ENNReal.ofReal (discreteKOverlapAveragingConstant d ^ 2) *
            ENNReal.ofReal
              ((cubeBesovOverlappingPositiveVectorPartialSeminormTwo
                (originCube d 0) s.1 N F) ^ 2) :=
          ofReal_sq_le_mul_of_nonneg_mul
            (cubeKBesovVectorPartialSeminormTwo_nonneg (originCube d 0) s.1 N F)
            (cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg
              (originCube d 0) s.1 N F)
            (discreteKOverlapAveragingConstant_nonneg d) hfinite
    _ ≤ ENNReal.ofReal (discreteKOverlapAveragingConstant d ^ 2) *
          extendedVectorOverlapBesovEnergy s F :=
        mul_le_mul_right
          (ofReal_sq_vectorPartialSeminorm_le_extendedVectorOverlapBesovEnergy s F N) _

/-- The extended overlap energy is controlled by the extended discrete
K-functional energy using only the proved overlap-Poincare producer. -/
theorem extendedVectorOverlapBesovEnergy_le_mul_extendedDiscreteKFunctionalEnergy
    {d : ℕ} (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    extendedVectorOverlapBesovEnergy s F ≤
      ENNReal.ofReal (overlapDiscreteKConstant d ^ 2) *
        extendedDiscreteKFunctionalEnergy s F := by
  refine iSup_le fun N => ?_
  have hfinite := overlapPartialSeminorm_le_mul_cubeKPartialSeminorm s F N
  calc
    ENNReal.ofReal
        ((cubeBesovOverlappingPositiveVectorPartialSeminormTwo
          (originCube d 0) s.1 N F) ^ 2)
        ≤ ENNReal.ofReal (overlapDiscreteKConstant d ^ 2) *
            ENNReal.ofReal
              ((cubeKBesovVectorPartialSeminormTwo (originCube d 0) s.1 N F) ^ 2) :=
          ofReal_sq_le_mul_of_nonneg_mul
            (cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg
              (originCube d 0) s.1 N F)
            (cubeKBesovVectorPartialSeminormTwo_nonneg (originCube d 0) s.1 N F)
            (overlapDiscreteKConstant_nonneg d) hfinite
    _ ≤ ENNReal.ofReal (overlapDiscreteKConstant d ^ 2) *
          extendedDiscreteKFunctionalEnergy s F :=
        mul_le_mul_right
          (ofReal_sq_cubeKPartialSeminorm_le_extendedDiscreteKFunctionalEnergy s F N) _

end

end Homogenization
