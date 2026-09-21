/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKSeriesBridge

/-!
# Positive-dimensional composition of exact finite-energy bridges

This module composes the finite-energy arrows in the positive-dimensional,
measurable-representative lane.  It does not introduce a source-facing full
norm comparison.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem UnitCubeEuclideanL2Field.memLp_originCube_normalizedCubeMeasure
    {d : ℕ} (F : UnitCubeEuclideanL2Field d) :
    MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) := by
  rw [normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  apply MemLp.of_eval
  intro i
  have hF := F.euclideanMemL2
  rw [memLp_piLp_iff] at hF
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF i

/-- The finite constant for the sample-energy to Euclidean-energy direction,
apart from the continuous/discrete series bridge factor. -/
noncomputable def positiveDimensionalDiscreteToHsTailConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (discreteKOverlapAveragingConstant d ^ 2) *
    ((d : ℝ≥0∞) * (2 * 3 ^ d)) *
      ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))

/-- The finite constant for the Euclidean-energy to discrete-energy direction,
apart from the continuous/discrete series bridge factor. -/
noncomputable def positiveDimensionalHsToDiscreteTailConstant
    (d : ℕ) : ℝ≥0∞ :=
  ((d : ℝ≥0∞) * (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ)) *
    ENNReal.ofReal (overlapDiscreteKConstant d ^ 2)

theorem positiveDimensionalDiscreteToHsTailConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    positiveDimensionalDiscreteToHsTailConstant s d < ∞ := by
  unfold positiveDimensionalDiscreteToHsTailConstant
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · exact overlapBesovEnergy_gagliardoConstant_lt_top d
  · exact coordinateGagliardoEnergy_euclideanHsConstant_lt_top d s

theorem positiveDimensionalHsToDiscreteTailConstant_lt_top (d : ℕ) :
    positiveDimensionalHsToDiscreteTailConstant d < ∞ := by
  unfold positiveDimensionalHsToDiscreteTailConstant
  exact ENNReal.mul_lt_top
    (coordinateGagliardoEnergy_overlapBesovConstant_lt_top d)
    ENNReal.ofReal_lt_top

/-- The full finite sample-energy to Euclidean-energy composition constant. -/
noncomputable def positiveDimensionalSampleToHsConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2) *
    positiveDimensionalDiscreteToHsTailConstant s d

/-- The full finite Euclidean-energy to sample-energy composition constant. -/
noncomputable def positiveDimensionalHsToSampleConstant
    (d : ℕ) : ℝ≥0∞ :=
  positiveDimensionalHsToDiscreteTailConstant d *
    ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2)

theorem positiveDimensionalSampleToHsConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    positiveDimensionalSampleToHsConstant s d < ∞ := by
  unfold positiveDimensionalSampleToHsConstant
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (positiveDimensionalDiscreteToHsTailConstant_lt_top s d)

theorem positiveDimensionalHsToSampleConstant_lt_top (d : ℕ) :
    positiveDimensionalHsToSampleConstant d < ∞ := by
  unfold positiveDimensionalHsToSampleConstant
  exact ENNReal.mul_lt_top (positiveDimensionalHsToDiscreteTailConstant_lt_top d)
    ENNReal.ofReal_lt_top

/-- In positive dimension, the exact sampled continuous K-energy controls the
exact Euclidean `H^s` energy through the four finite bridge layers. -/
theorem euclideanHsEnergy_le_mul_triadicContinuousKSampleEnergy
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) (hFmeas : Measurable F) :
    euclideanHsEnergy s F ≤
      positiveDimensionalHsToSampleConstant d *
        triadicContinuousKSampleEnergy s F := by
  let CK : ℝ≥0∞ := ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2)
  let COG : ℝ≥0∞ :=
    (d : ℝ≥0∞) * (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ)
  let COD : ℝ≥0∞ := ENNReal.ofReal (overlapDiscreteKConstant d ^ 2)
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) :=
    F.memLp_originCube_normalizedCubeMeasure
  calc
    euclideanHsEnergy s F ≤ coordinateGagliardoEnergy s F :=
      euclideanHsEnergy_le_coordinateGagliardoEnergy s F hFmeas
    _ ≤ COG * extendedVectorOverlapBesovEnergy s F := by
      simpa only [COG] using
        coordinateGagliardoEnergy_le_mul_extendedVectorOverlapBesovEnergy s F hFmeas hF
    _ ≤ COG * (COD * extendedDiscreteKFunctionalEnergy s F) :=
      mul_le_mul_right
        (extendedVectorOverlapBesovEnergy_le_mul_extendedDiscreteKFunctionalEnergy s F) COG
    _ ≤ COG * (COD * (CK * triadicContinuousKSampleEnergy s F)) :=
      mul_le_mul_right
        (mul_le_mul_right
          (extendedDiscreteKFunctionalEnergy_le_mul_triadicContinuousKSampleEnergy s F) COD) COG
    _ = positiveDimensionalHsToSampleConstant d *
          triadicContinuousKSampleEnergy s F := by
      dsimp [positiveDimensionalHsToSampleConstant,
        positiveDimensionalHsToDiscreteTailConstant, CK, COG, COD]
      ring

/-- In positive dimension, the exact Euclidean `H^s` energy controls the
exact sampled continuous K-energy through the same finite bridge layers. -/
theorem triadicContinuousKSampleEnergy_le_mul_euclideanHsEnergy
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) (hFmeas : Measurable F) :
    triadicContinuousKSampleEnergy s F ≤
      positiveDimensionalSampleToHsConstant s d * euclideanHsEnergy s F := by
  let CK : ℝ≥0∞ := ENNReal.ofReal (continuousDiscreteKBridgeConstant d ^ 2)
  let CD : ℝ≥0∞ := ENNReal.ofReal (discreteKOverlapAveragingConstant d ^ 2)
  let CO : ℝ≥0∞ := (d : ℝ≥0∞) * (2 * 3 ^ d)
  let CG : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d 0)) :=
    F.memLp_originCube_normalizedCubeMeasure
  calc
    triadicContinuousKSampleEnergy s F ≤ CK * extendedDiscreteKFunctionalEnergy s F := by
      simpa only [CK] using
        triadicContinuousKSampleEnergy_le_mul_extendedDiscreteKFunctionalEnergy s F
    _ ≤ CK * (CD * extendedVectorOverlapBesovEnergy s F) :=
      mul_le_mul_right
        (extendedDiscreteKFunctionalEnergy_le_mul_extendedVectorOverlapBesovEnergy s F) CK
    _ ≤ CK * (CD * (CO * coordinateGagliardoEnergy s F)) :=
      mul_le_mul_right
        (mul_le_mul_right
          (extendedVectorOverlapBesovEnergy_le_mul_coordinateGagliardoEnergy s F hFmeas hF) CD) CK
    _ ≤ CK * (CD * (CO * (CG * euclideanHsEnergy s F))) := by
      exact mul_le_mul_right
        (mul_le_mul_right
          (mul_le_mul_right
            (coordinateGagliardoEnergy_le_mul_euclideanHsEnergy s F hFmeas) CO) CD) CK
    _ = positiveDimensionalSampleToHsConstant s d * euclideanHsEnergy s F := by
      dsimp [positiveDimensionalSampleToHsConstant,
        positiveDimensionalDiscreteToHsTailConstant, CK, CD, CO, CG]
      ring

end

end Homogenization
