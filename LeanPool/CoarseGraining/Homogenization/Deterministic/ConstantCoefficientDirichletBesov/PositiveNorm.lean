/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PartitionWeights

/-! # Positive Norm -/

@[expose] public section

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

theorem aemeasurable_overlapCubeResidualIndicator_of_memLp
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ} {h : Vec d → Vec d}
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hh : MeasureTheory.MemLp h (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S)) :
    AEMeasurable
      ((overlapCubeSet S).indicator
        (fun y : Vec d =>
          ENNReal.ofReal
            (vecNormSq (h y - overlapCubeAverageVec S h))))
      (MeasureTheory.volume.restrict (cubeSet Q)) := by
  let μS : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (overlapCubeSet S)
  have hcoeff :
      ENNReal.ofReal ((overlapCubeVolume S)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (overlapCubeVolume_pos S))
  have hh_vol : AEMeasurable h μS := by
    have hh_norm : AEMeasurable h (normalizedOverlapCubeMeasure S) :=
      hh.1.aemeasurable
    simpa [μS, normalizedOverlapCubeMeasure, overlapCubeMeasure] using
      (aemeasurable_smul_measure_iff
        (μ := MeasureTheory.volume.restrict (overlapCubeSet S))
        (f := h) hcoeff).1 hh_norm
  have hmap :
      Measurable (fun v : Vec d =>
        vecNormSq (v - overlapCubeAverageVec S h)) := by
    unfold vecNormSq vecDot
    fun_prop
  have hbase : AEMeasurable
      (fun y : Vec d =>
        ENNReal.ofReal
          (vecNormSq (h y - overlapCubeAverageVec S h))) μS := by
    exact (hmap.comp_aemeasurable hh_vol).ennreal_ofReal
  have hsubset : overlapCubeSet S ⊆ cubeSet Q :=
    overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hS
  refine (aemeasurable_indicator_iff (measurableSet_overlapCubeSet S)).2 ?_
  rwa [MeasureTheory.Measure.restrict_restrict_of_subset hsubset]

/-- Coordinate version of the closed-overlap fluctuation indicator
measurability lemma. -/
theorem aemeasurable_overlapCubeCoordResidualIndicator_of_memLp
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ} {h : Vec d → Vec d}
    (i : Fin d)
    (hS : S ∈ overlapCentersAtDepth Q j)
    (hh : MeasureTheory.MemLp h (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S)) :
    AEMeasurable
      ((overlapCubeSet S).indicator
        (fun y : Vec d =>
          ENNReal.ofReal
            ((h y i - overlapCubeAverageVec S h i) ^ 2)))
      (MeasureTheory.volume.restrict (cubeSet Q)) := by
  let μS : MeasureTheory.Measure (Vec d) :=
    MeasureTheory.volume.restrict (overlapCubeSet S)
  have hcoeff :
      ENNReal.ofReal ((overlapCubeVolume S)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (overlapCubeVolume_pos S))
  have hh_vol : AEMeasurable h μS := by
    have hh_norm : AEMeasurable h (normalizedOverlapCubeMeasure S) :=
      hh.1.aemeasurable
    simpa [μS, normalizedOverlapCubeMeasure, overlapCubeMeasure] using
      (aemeasurable_smul_measure_iff
        (μ := MeasureTheory.volume.restrict (overlapCubeSet S))
        (f := h) hcoeff).1 hh_norm
  have hmap :
      Measurable (fun v : Vec d =>
        (v i - overlapCubeAverageVec S h i) ^ 2) := by
    fun_prop
  have hbase : AEMeasurable
      (fun y : Vec d =>
        ENNReal.ofReal
          ((h y i - overlapCubeAverageVec S h i) ^ 2)) μS := by
    exact (hmap.comp_aemeasurable hh_vol).ennreal_ofReal
  have hsubset : overlapCubeSet S ⊆ cubeSet Q :=
    overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hS
  refine (aemeasurable_indicator_iff (measurableSet_overlapCubeSet S)).2 ?_
  rwa [MeasureTheory.Measure.restrict_restrict_of_subset hsubset]

/-- Integrated coordinate fluctuation indicators are controlled by the
vector-valued overlap fluctuation average. -/
theorem lintegral_sum_coord_fluctuation_indicator_le_vector_average
    {d : ℕ} (Q : TriadicCube d) (h : Vec d → Vec d) (j : ℕ)
    (i : Fin d)
    (hloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp h (2 : ℝ≥0∞)
          (normalizedOverlapCubeMeasure S)) :
    ∫⁻ x,
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (overlapCubeSet S).indicator
              (fun y : Vec d =>
                ENNReal.ofReal
                  ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
        ∂ normalizedCubeMeasure Q
      ≤
        (3 ^ d : ℝ≥0∞) *
          (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                ∫⁻ x,
                  ENNReal.ofReal
                    (vecNormSq (h x - overlapCubeAverageVec S h))
                  ∂ normalizedOverlapCubeMeasure S)) := by
  classical
  let D : Finset (TriadicCube d) := overlapCentersAtDepth Q j
  let scalar : TriadicCube d → Vec d → ℝ≥0∞ :=
    fun S y => ENNReal.ofReal
      ((h y i - overlapCubeAverageVec S h i) ^ 2)
  let vector : TriadicCube d → Vec d → ℝ≥0∞ :=
    fun S y => ENNReal.ofReal
      (vecNormSq (h y - overlapCubeAverageVec S h))
  have hfinite :
      ∫⁻ x,
          D.sum (fun S => (overlapCubeSet S).indicator (scalar S) x)
          ∂ normalizedCubeMeasure Q
        ≤
          (3 ^ d : ℝ≥0∞) *
            (((D.card : ℝ≥0∞)⁻¹) *
              D.sum
                (fun S =>
                  ∫⁻ x, scalar S x ∂ normalizedOverlapCubeMeasure S)) := by
    simpa [D, scalar] using
      overlapCentersAtDepth_lintegral_sum_indicator_normalizedCubeMeasure_le
        Q j
        (f := scalar)
        (fun S hS =>
          aemeasurable_overlapCubeCoordResidualIndicator_of_memLp
            (Q := Q) (j := j) (h := h) i hS (hloc S hS))
  have hscalar_le_vector :
      (((D.card : ℝ≥0∞)⁻¹) *
        D.sum
          (fun S =>
            ∫⁻ x, scalar S x ∂ normalizedOverlapCubeMeasure S))
        ≤
      (((D.card : ℝ≥0∞)⁻¹) *
        D.sum
          (fun S =>
            ∫⁻ x, vector S x ∂ normalizedOverlapCubeMeasure S)) := by
    refine mul_le_mul_right ?_ _
    refine Finset.sum_le_sum ?_
    intro S _hS
    exact MeasureTheory.lintegral_mono fun x => by
      have hcoord :
          (h x i - overlapCubeAverageVec S h i) ^ 2 ≤
            vecNormSq (h x - overlapCubeAverageVec S h) := by
        simpa using
          sq_apply_le_vecNormSq (h x - overlapCubeAverageVec S h) i
      exact ENNReal.ofReal_le_ofReal hcoord
  calc
    ∫⁻ x,
        (overlapCentersAtDepth Q j).sum
          (fun S =>
            (overlapCubeSet S).indicator
              (fun y : Vec d =>
                ENNReal.ofReal
                  ((h y i - overlapCubeAverageVec S h i) ^ 2)) x)
        ∂ normalizedCubeMeasure Q
        ≤
          (3 ^ d : ℝ≥0∞) *
            (((D.card : ℝ≥0∞)⁻¹) *
              D.sum
                (fun S =>
                  ∫⁻ x, scalar S x ∂ normalizedOverlapCubeMeasure S)) := by
          simpa [D, scalar] using hfinite
    _ ≤
        (3 ^ d : ℝ≥0∞) *
          (((D.card : ℝ≥0∞)⁻¹) *
            D.sum
              (fun S =>
                ∫⁻ x, vector S x ∂ normalizedOverlapCubeMeasure S)) := by
          exact mul_le_mul_right hscalar_le_vector _
    _ =
        (3 ^ d : ℝ≥0∞) *
          (((overlapCentersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (overlapCentersAtDepth Q j).sum
              (fun S =>
                ∫⁻ x,
                  ENNReal.ofReal
                    (vecNormSq (h x - overlapCubeAverageVec S h))
                  ∂ normalizedOverlapCubeMeasure S)) := by
          rfl

theorem cubeBesovOverlappingPositiveVectorDepthAverage_add_le {d : ℕ}
    (Q : TriadicCube d) (u v : Vec d → Vec d) (j : ℕ)
    (hu :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hv :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q (fun x => u x + v x) j ≤
      2 * cubeBesovOverlappingPositiveVectorDepthAverage Q u j +
        2 * cubeBesovOverlappingPositiveVectorDepthAverage Q v j := by
  unfold cubeBesovOverlappingPositiveVectorDepthAverage
  calc
    overlapCentersAverage Q j
        (fun S => (overlapCubeLpNorm S (2 : ℝ≥0∞)
          (overlapCubeFluctuationVec S (fun x => u x + v x))) ^ 2)
        ≤
          overlapCentersAverage Q j
            (fun S =>
              2 * (overlapCubeLpNorm S (2 : ℝ≥0∞)
                (overlapCubeFluctuationVec S u)) ^ 2 +
              2 * (overlapCubeLpNorm S (2 : ℝ≥0∞)
                (overlapCubeFluctuationVec S v)) ^ 2) := by
          refine overlapCentersAverage_le_overlapCentersAverage Q j ?_
          intro S hS
          let n : ℝ := overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S (fun x => u x + v x))
          let a : ℝ := overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S u)
          let b : ℝ := overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S v)
          have hfluct :
              overlapCubeFluctuationVec S (fun x => u x + v x) =
                fun x => overlapCubeFluctuationVec S u x +
                  overlapCubeFluctuationVec S v x :=
            overlapCubeFluctuationVec_add_of_memLp_two S (hu S hS) (hv S hS)
          have hfu :
              MeasureTheory.MemLp (overlapCubeFluctuationVec S u)
                (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
            memLp_overlapCubeFluctuationVec S u (hu S hS)
          have hfv :
              MeasureTheory.MemLp (overlapCubeFluctuationVec S v)
                (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
            memLp_overlapCubeFluctuationVec S v (hv S hS)
          have hnorm : n ≤ a + b := by
            dsimp [n, a, b]
            rw [hfluct]
            exact overlapCubeLpNorm_add_le S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S u)
              (overlapCubeFluctuationVec S v) hfu hfv (by norm_num)
          have hn_nonneg : 0 ≤ n := by
            dsimp [n]
            exact overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S (fun x => u x + v x))
          have ha_nonneg : 0 ≤ a := by
            dsimp [a]
            exact overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S u)
          have hb_nonneg : 0 ≤ b := by
            dsimp [b]
            exact overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S v)
          have hsq : n ^ 2 ≤ (a + b) ^ 2 :=
            (sq_le_sq₀ hn_nonneg (add_nonneg ha_nonneg hb_nonneg)).mpr hnorm
          have hquad : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
            nlinarith [sq_nonneg (a - b)]
          simpa [n, a, b] using le_trans hsq hquad
    _ =
          overlapCentersAverage Q j
            (fun S =>
              2 * (overlapCubeLpNorm S (2 : ℝ≥0∞)
                (overlapCubeFluctuationVec S u)) ^ 2) +
          overlapCentersAverage Q j
            (fun S =>
              2 * (overlapCubeLpNorm S (2 : ℝ≥0∞)
                (overlapCubeFluctuationVec S v)) ^ 2) := by
          rw [overlapCentersAverage_add]
    _ =
          2 * overlapCentersAverage Q j
            (fun S => (overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S u)) ^ 2) +
          2 * overlapCentersAverage Q j
            (fun S => (overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S v)) ^ 2) := by
          rw [overlapCentersAverage_mul_left, overlapCentersAverage_mul_left]

theorem cubeBesovOverlappingPositiveVectorDepthAverage_residual_le {d : ℕ}
    (Q : TriadicCube d) (R : Vec d → Vec d) (j : ℕ)
    (hR : MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hRloc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp R (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q R j ≤
      4 * (3 ^ d : ℝ) * (cubeLpNorm Q (2 : ℝ≥0∞) R) ^ 2 := by
  have havg_lintegral :=
    overlapCentersAverage_lintegral_rpow_enorm_two_le Q j R hR hRloc
  unfold cubeBesovOverlappingPositiveVectorDepthAverage
  calc
    overlapCentersAverage Q j
        (fun S => (overlapCubeLpNorm S (2 : ℝ≥0∞)
          (overlapCubeFluctuationVec S R)) ^ 2)
        ≤
          overlapCentersAverage Q j
            (fun S => (2 * overlapCubeLpNorm S (2 : ℝ≥0∞) R) ^ 2) := by
          refine overlapCentersAverage_le_overlapCentersAverage Q j ?_
          intro S hS
          have hfluct :
              overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S R) ≤
                2 * overlapCubeLpNorm S (2 : ℝ≥0∞) R :=
            overlapCubeLpNorm_two_overlapCubeFluctuationVec_le_two_mul_overlapCubeLpNorm_two
              S R (hRloc S hS)
          exact (sq_le_sq₀
            (overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S R))
            (mul_nonneg (by norm_num) (overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) R))).mpr
            hfluct
    _ =
          overlapCentersAverage Q j
            (fun S => 4 * (overlapCubeLpNorm S (2 : ℝ≥0∞) R) ^ 2) := by
          congr 1
          funext S
          ring
    _ =
          4 * overlapCentersAverage Q j
            (fun S => (overlapCubeLpNorm S (2 : ℝ≥0∞) R) ^ 2) := by
          rw [overlapCentersAverage_mul_left]
    _ =
          4 * overlapCentersAverage Q j
            (fun S =>
              (∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ) ∂ normalizedOverlapCubeMeasure S).toReal) := by
          classical
          congr 1
          let D := overlapCentersAtDepth Q j
          unfold overlapCentersAverage
          change
            ((D.card : ℝ)⁻¹) *
                D.sum (fun S => (overlapCubeLpNorm S (2 : ℝ≥0∞) R) ^ 2) =
              ((D.card : ℝ)⁻¹) *
                D.sum (fun S =>
                  (∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ)
                    ∂ normalizedOverlapCubeMeasure S).toReal)
          congr 1
          refine Finset.sum_congr rfl ?_
          intro S _hS
          exact overlapCubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal S R
    _ ≤
          4 * ((3 ^ d : ℝ) *
            (∫⁻ x, ‖R x‖ₑ ^ (2 : ℝ) ∂ normalizedCubeMeasure Q).toReal) := by
          exact mul_le_mul_of_nonneg_left havg_lintegral (by norm_num)
    _ =
          4 * ((3 ^ d : ℝ) * (cubeLpNorm Q (2 : ℝ≥0∞) R) ^ 2) := by
          rw [cubeLpNorm_two_sq_eq_lintegral_rpow_enorm_toReal]
    _ =
          4 * (3 ^ d : ℝ) * (cubeLpNorm Q (2 : ℝ≥0∞) R) ^ 2 := by
          ring

/-- Depth-`j` overlapping positive `q = 2` seminorm. -/
noncomputable def cubeBesovOverlappingPositiveVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (s * (j : ℝ)) *
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q u j)

theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j := by
  unfold cubeBesovOverlappingPositiveVectorDepthSeminorm
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (Real.sqrt_nonneg _)

theorem sq_cubeBesovOverlappingPositiveVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2 =
      (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
        cubeBesovOverlappingPositiveVectorDepthAverage Q u j := by
  have hA : 0 ≤ cubeBesovOverlappingPositiveVectorDepthAverage Q u j :=
    cubeBesovOverlappingPositiveVectorDepthAverage_nonneg Q u j
  calc
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q u j)) ^ 2 := by
              rfl
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          (Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q u j)) ^ 2 := by
            ring
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          cubeBesovOverlappingPositiveVectorDepthAverage Q u j := by
            rw [Real.sq_sqrt hA]

/-- Finite-depth overlapping positive `q = 2` seminorm. -/
noncomputable def cubeBesovOverlappingPositiveVectorPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) : ℝ :=
  Real.sqrt <|
    Finset.sum (Finset.range (N + 1)) fun j =>
      (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    0 ≤ cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u :=
  Real.sqrt_nonneg _

theorem sq_cubeBesovOverlappingPositiveVectorPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u) ^ 2 =
      Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
  unfold cubeBesovOverlappingPositiveVectorPartialSeminormTwo
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun j _ =>
    sq_nonneg (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j)

/-- Full overlapping positive `q = 2` seminorm. -/
noncomputable def cubeBesovOverlappingPositiveVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) : ℝ :=
  sSup (Set.range fun N : ℕ =>
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u)

theorem cubeBesovOverlappingPositiveVectorSeminormTwo_le_of_partialBound {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) {B : ℝ}
    (hB :
      ∀ N : ℕ, cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u ≤ B) :
    cubeBesovOverlappingPositiveVectorSeminormTwo Q s u ≤ B := by
  unfold cubeBesovOverlappingPositiveVectorSeminormTwo
  refine csSup_le ?_ ?_
  · exact ⟨cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s 0 u, ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hB N

theorem cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_seminorm_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u))
    (N : ℕ) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u ≤
      cubeBesovOverlappingPositiveVectorSeminormTwo Q s u := by
  unfold cubeBesovOverlappingPositiveVectorSeminormTwo
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovOverlappingPositiveVectorSeminormTwo_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N u)) :
    0 ≤ cubeBesovOverlappingPositiveVectorSeminormTwo Q s u := by
  have h0_le :
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s 0 u ≤
        cubeBesovOverlappingPositiveVectorSeminormTwo Q s u :=
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_seminorm_of_bddAbove
      Q s u hBdd 0
  exact
    (cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg Q s 0 u).trans
      h0_le

/-- Corrected full positive `q = 2` Besov norm for vector fields, using
overlapping cubes at each depth. -/
noncomputable def cubeBesovOverlappingPositiveVectorNormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt (vecNormSq (cubeAverageVec Q F)) +
    cubeBesovOverlappingPositiveVectorSeminormTwo Q s F

theorem cubeBesovOverlappingPositiveVectorNormTwo_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F)) :
    0 ≤ cubeBesovOverlappingPositiveVectorNormTwo Q s F := by
  unfold cubeBesovOverlappingPositiveVectorNormTwo
  exact add_nonneg (Real.sqrt_nonneg _)
    (cubeBesovOverlappingPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s F hBdd)

/-- Corrected `H^s` regularity package for the overlapping positive norm. -/
structure CubeVectorOverlappingBesovHRegularity {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (g : Vec d → Vec d) : Prop where
  memLp : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q)
  partialSeminorms_bddAbove :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N g)

theorem CubeVectorOverlappingBesovHRegularity.partialSeminorm_le_seminorm
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : CubeVectorOverlappingBesovHRegularity Q s g) (N : ℕ) :
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N g ≤
      cubeBesovOverlappingPositiveVectorSeminormTwo Q s g :=
  cubeBesovOverlappingPositiveVectorPartialSeminormTwo_le_seminorm_of_bddAbove
    Q s g hg.partialSeminorms_bddAbove N

theorem CubeVectorOverlappingBesovHRegularity.seminorm_nonneg
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : CubeVectorOverlappingBesovHRegularity Q s g) :
    0 ≤ cubeBesovOverlappingPositiveVectorSeminormTwo Q s g :=
  cubeBesovOverlappingPositiveVectorSeminormTwo_nonneg_of_bddAbove
    Q s g hg.partialSeminorms_bddAbove

theorem CubeVectorOverlappingBesovHRegularity.norm_nonneg
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {g : Vec d → Vec d}
    (hg : CubeVectorOverlappingBesovHRegularity Q s g) :
    0 ≤ cubeBesovOverlappingPositiveVectorNormTwo Q s g :=
  cubeBesovOverlappingPositiveVectorNormTwo_nonneg_of_bddAbove
    Q s g hg.partialSeminorms_bddAbove


end

end Homogenization
