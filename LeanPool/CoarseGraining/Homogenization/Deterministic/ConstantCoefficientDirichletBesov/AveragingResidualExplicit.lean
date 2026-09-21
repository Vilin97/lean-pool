/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.AveragingResidual

/-! # Averaging Residual Explicit -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

namespace SmoothOverlapPartition

/-- The explicit residual constant carried by a smooth overlap partition. -/
noncomputable def residualConstant {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) : ℝ :=
  Real.sqrt
    ((P.activeCardBound : ℝ) * (3 ^ d : ℝ) *
      (Fintype.card (Fin d) : ℝ))

theorem residualConstant_nonneg {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) :
    0 ≤ P.residualConstant :=
  Real.sqrt_nonneg _

/-- Pointwise residual estimate with the explicit active-cardinality field of
the partition. -/
theorem vecNormSq_sub_averagingField_le_activeBound_mul_sum_openOverlap_indicator
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    vecNormSq (h x - P.averagingField h x) ≤
      (P.activeCardBound : ℝ) *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (openOverlapCubeSet S).indicator
              (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x) := by
  classical
  let A : Finset (TriadicCube d) :=
    (overlapCentersAtDepth Q j).filter (fun S => P.weight S x ≠ 0)
  let localEnergy : ℝ :=
    A.sum (fun S => vecNormSq (h x - overlapCubeAverageVec S h))
  let indicators : ℝ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (openOverlapCubeSet S).indicator
          (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x)
  have hres :
      vecNormSq (h x - P.averagingField h x) ≤
        (A.card : ℝ) * localEnergy := by
    simpa [A, localEnergy] using
      P.vecNormSq_sub_averagingField_le_activeCard_mul_activeSum_vecNormSq h hx
  have hcard : (A.card : ℝ) ≤ (P.activeCardBound : ℝ) := by
    exact_mod_cast P.active_card_bound hx
  have hlocal_nonneg : 0 ≤ localEnergy := by
    dsimp [localEnergy]
    exact Finset.sum_nonneg fun S _hS => vecNormSq_nonneg _
  have hlocal_le_indicators : localEnergy ≤ indicators := by
    simpa [A, localEnergy, indicators] using
      P.activeSum_vecNormSq_le_sum_openOverlap_indicator h hx
  calc
    vecNormSq (h x - P.averagingField h x)
        ≤ (A.card : ℝ) * localEnergy := hres
    _ ≤ (P.activeCardBound : ℝ) * localEnergy :=
          mul_le_mul_of_nonneg_right hcard hlocal_nonneg
    _ ≤ (P.activeCardBound : ℝ) * indicators := by
          exact mul_le_mul_of_nonneg_left hlocal_le_indicators (by positivity)
    _ =
        (P.activeCardBound : ℝ) *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              (openOverlapCubeSet S).indicator
                (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x) := by
          rfl

/-- `ENNReal` pointwise residual estimate with the explicit active-cardinality
field. -/
theorem ofReal_vecNormSq_sub_averagingField_le_activeBound_mul_sum_overlap_indicator
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    ENNReal.ofReal (vecNormSq (h x - P.averagingField h x)) ≤
      (P.activeCardBound : ℝ≥0∞) *
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (overlapCubeSet S).indicator
              (fun y : Vec d =>
                ENNReal.ofReal
                  (vecNormSq (h y - overlapCubeAverageVec S h))) x) := by
  classical
  let openRealSum : ℝ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (openOverlapCubeSet S).indicator
          (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x)
  let overlapRealSum : ℝ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (overlapCubeSet S).indicator
          (fun y : Vec d => vecNormSq (h y - overlapCubeAverageVec S h)) x)
  let overlapEnnSum : ℝ≥0∞ :=
    (overlapCentersAtDepth Q j).sum
      (fun S =>
        (overlapCubeSet S).indicator
          (fun y : Vec d =>
            ENNReal.ofReal
              (vecNormSq (h y - overlapCubeAverageVec S h))) x)
  have hopen_le_overlap : openRealSum ≤ overlapRealSum := by
    dsimp [openRealSum, overlapRealSum]
    refine Finset.sum_le_sum ?_
    intro S _hS
    by_cases hxOpen : x ∈ openOverlapCubeSet S
    · have hxClosed : x ∈ overlapCubeSet S :=
        openOverlapCubeSet_subset_overlapCubeSet S hxOpen
      simp [Set.indicator, hxOpen, hxClosed]
    · by_cases hxClosed : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxOpen, hxClosed, vecNormSq_nonneg]
      · simp [Set.indicator, hxOpen, hxClosed]
  have hoverlap_nonneg : 0 ≤ overlapRealSum := by
    dsimp [overlapRealSum]
    refine Finset.sum_nonneg ?_
    intro S _hS
    by_cases hxS : x ∈ overlapCubeSet S
    · simp [Set.indicator, hxS, vecNormSq_nonneg]
    · simp [Set.indicator, hxS]
  have hreal :
      vecNormSq (h x - P.averagingField h x) ≤
        (P.activeCardBound : ℝ) * overlapRealSum := by
    calc
      vecNormSq (h x - P.averagingField h x)
          ≤ (P.activeCardBound : ℝ) * openRealSum := by
            simpa [openRealSum] using
              P.vecNormSq_sub_averagingField_le_activeBound_mul_sum_openOverlap_indicator h hx
      _ ≤ (P.activeCardBound : ℝ) * overlapRealSum := by
            exact mul_le_mul_of_nonneg_left hopen_le_overlap
              (Nat.cast_nonneg P.activeCardBound)
  have hsum_ofReal : ENNReal.ofReal overlapRealSum = overlapEnnSum := by
    dsimp [overlapRealSum, overlapEnnSum]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl ?_
      intro S _hS
      by_cases hxS : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxS]
      · simp [Set.indicator, hxS]
    · intro S _hS
      by_cases hxS : x ∈ overlapCubeSet S
      · simp [Set.indicator, hxS, vecNormSq_nonneg]
      · simp [Set.indicator, hxS]
  calc
    ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))
        ≤ ENNReal.ofReal ((P.activeCardBound : ℝ) * overlapRealSum) :=
          ENNReal.ofReal_le_ofReal hreal
    _ = (P.activeCardBound : ℝ≥0∞) * overlapEnnSum := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg P.activeCardBound)]
          rw [ENNReal.ofReal_natCast, hsum_ofReal]

/-- Integrated residual-energy estimate with the explicit active-cardinality
field. -/
theorem lintegral_ofReal_vecNormSq_sub_averagingField_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hfQ :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable
          ((overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))))
          (MeasureTheory.volume.restrict (cubeSet Q))) :
    ∫⁻ x,
        ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))
        ∂ normalizedCubeMeasure Q
      ≤
        (P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                ∫⁻ x,
                  ENNReal.ofReal
                    (vecNormSq (h x - overlapCubeAverageVec S h))
                  ∂ normalizedOverlapCubeMeasure S)) := by
  classical
  let Fsum : Vec d → ℝ≥0∞ :=
    fun x =>
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          (overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))) x)
  have hpoint :
      (fun x =>
          ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))) ≤ᵐ[
        normalizedCubeMeasure Q] fun x => (P.activeCardBound : ℝ≥0∞) * Fsum x := by
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q] with x hx
    simpa [Fsum] using
      P.ofReal_vecNormSq_sub_averagingField_le_activeBound_mul_sum_overlap_indicator h hx
  have hlin :
      ∫⁻ x,
          ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))
          ∂ normalizedCubeMeasure Q
        ≤
          ∫⁻ x, (P.activeCardBound : ℝ≥0∞) * Fsum x
            ∂ normalizedCubeMeasure Q :=
    MeasureTheory.lintegral_mono_ae hpoint
  have hconst :
      ∫⁻ x, (P.activeCardBound : ℝ≥0∞) * Fsum x ∂ normalizedCubeMeasure Q =
        (P.activeCardBound : ℝ≥0∞) *
          ∫⁻ x, Fsum x ∂ normalizedCubeMeasure Q := by
    rw [MeasureTheory.lintegral_const_mul'
      (r := (P.activeCardBound : ℝ≥0∞)) (f := Fsum)]
    norm_num
  have hoverlap :
      ∫⁻ x, Fsum x ∂ normalizedCubeMeasure Q
        ≤
          (3 ^ d : ℝ≥0∞) *
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S)) := by
    simpa [Fsum] using
      overlapCentersAtDepth_lintegral_sum_indicator_normalizedCubeMeasure_le
        (Q := Q) (j := j)
        (f := fun S x =>
          ENNReal.ofReal (vecNormSq (h x - overlapCubeAverageVec S h)))
        hfQ
  calc
    ∫⁻ x,
        ENNReal.ofReal (vecNormSq (h x - P.averagingField h x))
        ∂ normalizedCubeMeasure Q
        ≤
          ∫⁻ x, (P.activeCardBound : ℝ≥0∞) * Fsum x
            ∂ normalizedCubeMeasure Q := hlin
    _ =
          (P.activeCardBound : ℝ≥0∞) *
            ∫⁻ x, Fsum x ∂ normalizedCubeMeasure Q := hconst
    _ ≤
          (P.activeCardBound : ℝ≥0∞) *
            ((3 ^ d : ℝ≥0∞) *
              (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
                (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S))) := by
          exact mul_le_mul_of_nonneg_left hoverlap
            (zero_le : (0 : ℝ≥0∞) ≤ (P.activeCardBound : ℝ≥0∞))
    _ =
          (P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
            (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
              (overlapCentersAtDepth Q j).sum
                (fun S =>
                  ∫⁻ x,
                    ENNReal.ofReal
                      (vecNormSq (h x - overlapCubeAverageVec S h))
                    ∂ normalizedOverlapCubeMeasure S)) := by
          rw [mul_assoc]

/-- Real squared `L²` residual estimate with the explicit active-cardinality
field. -/
theorem cubeLpNorm_sq_sub_averagingField_le
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hfQ :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable
          ((overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))))
          (MeasureTheory.volume.restrict (cubeSet Q)))
    (hfinite :
      ((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
        (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              ∫⁻ x,
                ENNReal.ofReal
                  (vecNormSq (h x - overlapCubeAverageVec S h))
                ∂ normalizedOverlapCubeMeasure S))) ≠ ∞) :
    (cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x => h x - P.averagingField h x)) ^ 2 ≤
      (((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
        (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (overlapCentersAtDepth Q j).sum
            (fun S =>
              ∫⁻ x,
                ENNReal.ofReal
                  (vecNormSq (h x - overlapCubeAverageVec S h))
                ∂ normalizedOverlapCubeMeasure S)))).toReal := by
  exact
    cubeLpNorm_two_sq_le_lintegral_ofReal_vecNormSq_toReal_of_le
      (Q := Q)
      (F := fun x => h x - P.averagingField h x)
      hfinite
      (P.lintegral_ofReal_vecNormSq_sub_averagingField_le h hfQ)

/-- Squared residual estimate against the overlapping positive depth average,
with the explicit active-cardinality field. -/
theorem cubeLpNorm_sq_sub_averagingField_le_mul_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hfQ :
      ∀ S ∈ overlapCentersAtDepth Q j,
        AEMeasurable
          ((overlapCubeSet S).indicator
            (fun y : Vec d =>
              ENNReal.ofReal
                (vecNormSq (h y - overlapCubeAverageVec S h))))
          (MeasureTheory.volume.restrict (cubeSet Q)))
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    (cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x => h x - P.averagingField h x)) ^ 2 ≤
      ((P.activeCardBound : ℝ) * (3 ^ d : ℝ) *
        (Fintype.card (Fin d) : ℝ)) *
          cubeBesovOverlappingPositiveVectorDepthAverage Q h j := by
  classical
  let A : ℝ≥0∞ :=
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          ∫⁻ x,
            ENNReal.ofReal
              (vecNormSq (h x - overlapCubeAverageVec S h))
            ∂ normalizedOverlapCubeMeasure S))
  let B : ℝ≥0∞ :=
    (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
      (overlapCentersAtDepth Q j).sum
        (fun S =>
          ∫⁻ x,
            ‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ)
            ∂ normalizedOverlapCubeMeasure S))
  let C : ℝ :=
    (P.activeCardBound : ℝ) * (3 ^ d : ℝ) *
      (Fintype.card (Fin d) : ℝ)
  have hres_sq :
      (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => h x - P.averagingField h x)) ^ 2 ≤
        (((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * A).toReal) := by
    have hfinite :
        ((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * A) ≠ ∞ := by
      simpa [A] using
        residualEuclideanOverlapBound_ne_top_of_memLp_overlap
          Q h j P.activeCardBound hloc
    simpa [A] using P.cubeLpNorm_sq_sub_averagingField_le h hfQ hfinite
  have hA_le : A ≤ (Fintype.card (Fin d) : ℝ≥0∞) * B := by
    simpa [A, B] using
      overlapCentersAtDepth_average_lintegral_ofReal_vecNormSq_fluctuation_le
        Q j h
  have hB_ne : B ≠ ∞ := by
    simpa [B] using
      overlapCentersAtDepth_average_lintegral_fluctuation_ne_top Q h j hloc
  have hright_ne :
      (P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          ((Fintype.card (Fin d) : ℝ≥0∞) * B) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp : (P.activeCardBound : ℝ≥0∞) ≠ ∞)
        (by simp : (3 ^ d : ℝ≥0∞) ≠ ∞))
      (ENNReal.mul_ne_top
        (by simp : (Fintype.card (Fin d) : ℝ≥0∞) ≠ ∞) hB_ne)
  have hA_toReal :
      (((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * A).toReal) ≤
        (((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          ((Fintype.card (Fin d) : ℝ≥0∞) * B)).toReal) := by
    refine ENNReal.toReal_mono hright_ne ?_
    exact mul_le_mul_of_nonneg_left hA_le (zero_le)
  have hB_toReal :
      B.toReal = cubeBesovOverlappingPositiveVectorDepthAverage Q h j := by
    have hfin :
        ∀ S ∈ overlapCentersAtDepth Q j,
          (∫⁻ x,
            ‖overlapCubeFluctuationVec S h x‖ₑ ^ (2 : ℝ)
            ∂ normalizedOverlapCubeMeasure S) ≠ ∞ := by
      intro S hS
      exact lintegral_overlapCubeFluctuationVec_rpow_enorm_two_ne_top S h
        (hloc S hS)
    simpa [B] using
      toReal_overlapCentersAtDepth_average_lintegral_fluctuation_eq_depthAverage
        Q h j hfin
  have hconst_toReal :
      (((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          ((Fintype.card (Fin d) : ℝ≥0∞) * B)).toReal) =
        C * cubeBesovOverlappingPositiveVectorDepthAverage Q h j := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp [C, hB_toReal]
    ring
  calc
    (cubeLpNorm Q (2 : ℝ≥0∞)
        (fun x => h x - P.averagingField h x)) ^ 2
        ≤ (((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) * A).toReal) := hres_sq
    _ ≤
        (((P.activeCardBound : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) *
          ((Fintype.card (Fin d) : ℝ≥0∞) * B)).toReal) := hA_toReal
    _ = C * cubeBesovOverlappingPositiveVectorDepthAverage Q h j := hconst_toReal
    _ =
      ((P.activeCardBound : ℝ) * (3 ^ d : ℝ) *
        (Fintype.card (Fin d) : ℝ)) *
          cubeBesovOverlappingPositiveVectorDepthAverage Q h j := by
        rfl

theorem cubeLpNorm_sub_averagingField_le_residualConstant_mul_sqrt_depthAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    (P : SmoothOverlapPartition Q j) (h : Vec d → Vec d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x => h x - P.averagingField h x) ≤
      P.residualConstant *
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q h j) := by
  have hsq :=
    P.cubeLpNorm_sq_sub_averagingField_le_mul_depthAverage h
      (fun S hS => aemeasurable_overlapCubeResidualIndicator_of_memLp hS (hloc S hS))
      hloc
  let A : ℝ :=
    cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x => h x - P.averagingField h x)
  let D : ℝ := cubeBesovOverlappingPositiveVectorDepthAverage Q h j
  let C2 : ℝ :=
    (P.activeCardBound : ℝ) * (3 ^ d : ℝ) *
      (Fintype.card (Fin d) : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact cubeLpNorm_nonneg Q (2 : ℝ≥0∞)
      (fun x => h x - P.averagingField h x)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact cubeBesovOverlappingPositiveVectorDepthAverage_nonneg Q h j
  have hC2_nonneg : 0 ≤ C2 := by
    dsimp [C2]
    positivity
  have hright_nonneg : 0 ≤ P.residualConstant * Real.sqrt D :=
    mul_nonneg P.residualConstant_nonneg (Real.sqrt_nonneg _)
  have hresidual_sq : P.residualConstant ^ 2 = C2 := by
    dsimp [residualConstant, C2]
    rw [Real.sq_sqrt]
    positivity
  have hsq' : A ^ 2 ≤ (P.residualConstant * Real.sqrt D) ^ 2 := by
    calc
      A ^ 2 ≤ C2 * D := by
        simpa [A, D, C2] using hsq
      _ = (P.residualConstant * Real.sqrt D) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hD_nonneg]
        rw [hresidual_sq]
  exact (sq_le_sq₀ hA_nonneg hright_nonneg).mp hsq'

end SmoothOverlapPartition

end

end Homogenization
