/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Positive.Overlap
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PositiveNorm

/-!
# Coordinate bridges for the overlapping positive Besov seminorm

The scalar fractional-Sobolev comparison and the vector discrete `K`-functional use two
historically duplicated presentations of the same overlap geometry. This file identifies those
presentations and compares their finite `p = q = 2` truncations. No full real-valued `sSup`
seminorm occurs here.
-/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

namespace ScalarOverlap

/-- The duplicated overlap side-length definitions agree. -/
theorem scaleFactor_eq_overlapCubeScaleFactor {d : ℕ} (S : TriadicCube d) :
    scaleFactor S = Homogenization.overlapCubeScaleFactor S := by
  rfl

/-- The duplicated half-open overlap cubes agree. -/
theorem cubeSet_eq_overlapCubeSet {d : ℕ} (S : TriadicCube d) :
    cubeSet S = Homogenization.overlapCubeSet S := by
  rfl

/-- The duplicated open overlap cubes agree. -/
theorem openCubeSet_eq_openOverlapCubeSet {d : ℕ} (S : TriadicCube d) :
    openCubeSet S = Homogenization.openOverlapCubeSet S := by
  rfl

/-- The duplicated overlap-volume definitions agree. -/
theorem cubeVolume_eq_overlapCubeVolume {d : ℕ} (S : TriadicCube d) :
    cubeVolume S = Homogenization.overlapCubeVolume S := by
  rfl

/-- The duplicated unnormalized overlap measures agree. -/
theorem cubeMeasure_eq_overlapCubeMeasure {d : ℕ} (S : TriadicCube d) :
    cubeMeasure S = Homogenization.overlapCubeMeasure S := by
  rfl

/-- The duplicated normalized overlap measures agree. -/
theorem normalizedCubeMeasure_eq_normalizedOverlapCubeMeasure {d : ℕ}
    (S : TriadicCube d) :
    normalizedCubeMeasure S = Homogenization.normalizedOverlapCubeMeasure S := by
  rfl

/-- The duplicated finite sets of overlap centers agree at every depth. -/
theorem centersAtDepth_eq_overlapCentersAtDepth {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    centersAtDepth Q j = Homogenization.overlapCentersAtDepth Q j := by
  rfl

/-- The duplicated finite-center averages agree. -/
theorem centersAverage_eq_overlapCentersAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (f : TriadicCube d → ℝ) :
    centersAverage Q j f = Homogenization.overlapCentersAverage Q j f := by
  rfl

/-- The duplicated scalar overlap averages agree. -/
theorem cubeAverage_eq_overlapCubeAverage {d : ℕ}
    (S : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage S f = Homogenization.overlapCubeAverage S f := by
  rfl

/-- The duplicated vector overlap averages agree. -/
theorem cubeAverageVec_eq_overlapCubeAverageVec {d : ℕ}
    (S : TriadicCube d) (F : Vec d → Vec d) :
    cubeAverageVec S F = Homogenization.overlapCubeAverageVec S F := by
  rfl

/-- The duplicated normalized overlap `L^p` norms agree. -/
theorem cubeLpNorm_eq_overlapCubeLpNorm {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (S : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → E) :
    cubeLpNorm S p f = Homogenization.overlapCubeLpNorm S p f := by
  rfl

end ScalarOverlap

/-- A coordinate of the vector overlap fluctuation is the scalar overlap fluctuation used by
`cubeBesovOverlapOscillation`. -/
theorem cubeBesovOverlapOscillation_two_coordinate_eq_overlapCubeLpNorm {d : ℕ}
    (S : TriadicCube d) (F : Vec d → Vec d) (i : Fin d) :
    cubeBesovOverlapOscillation S (2 : ℝ≥0∞) (fun x => F x i) =
      overlapCubeLpNorm S (2 : ℝ≥0∞) (fun x => overlapCubeFluctuationVec S F x i) := by
  unfold cubeBesovOverlapOscillation overlapCubeFluctuationVec
  rw [ScalarOverlap.cubeLpNorm_eq_overlapCubeLpNorm,
    ScalarOverlap.cubeAverage_eq_overlapCubeAverage]
  rfl

/-- Each scalar coordinate oscillation is bounded by the corrected vector oscillation on the
same overlap cube. -/
theorem cubeBesovOverlapOscillation_two_coordinate_le_vector {d : ℕ}
    (S : TriadicCube d) (F : Vec d → Vec d) (i : Fin d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlapOscillation S (2 : ℝ≥0∞) (fun x => F x i) ≤
      overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S F) := by
  rw [cubeBesovOverlapOscillation_two_coordinate_eq_overlapCubeLpNorm]
  exact overlapCubeLpNorm_component_le_overlapCubeLpNorm S (2 : ℝ≥0∞)
    (overlapCubeFluctuationVec S F) i (memLp_overlapCubeFluctuationVec S F hF)

/-- The corrected vector oscillation is bounded by the sum of its scalar coordinate
oscillations on the same overlap cube. -/
theorem overlapCubeLpNorm_fluctuationVec_le_sum_cubeBesovOverlapOscillation_two {d : ℕ}
    (S : TriadicCube d) (F : Vec d → Vec d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S F) ≤
      ∑ i : Fin d, cubeBesovOverlapOscillation S (2 : ℝ≥0∞) (fun x => F x i) := by
  calc
    overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S F)
        ≤ ∑ i : Fin d,
            overlapCubeLpNorm S (2 : ℝ≥0∞)
              (fun x => overlapCubeFluctuationVec S F x i) :=
      overlapCubeLpNorm_two_vec_le_sum_components S (overlapCubeFluctuationVec S F)
        (memLp_overlapCubeFluctuationVec S F hF)
    _ = ∑ i : Fin d,
          cubeBesovOverlapOscillation S (2 : ℝ≥0∞) (fun x => F x i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact (cubeBesovOverlapOscillation_two_coordinate_eq_overlapCubeLpNorm S F i).symm

/-- The legacy overlap depth weight is the root-scale factor times the corrected vector depth
weight. -/
theorem cubeBesovOverlapDepthWeight_eq_scaleWeight_mul_rpow {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    cubeBesovOverlapDepthWeight Q s j =
      cubeBesovScaleWeight s Q * Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
  have hQ_nonneg : 0 ≤ cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (le_of_lt (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
  calc
    cubeBesovOverlapDepthWeight Q s j =
        (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-s) := by
      rfl
    _ = (cubeScaleFactor Q) ^ (-s) / ((3 : ℝ) ^ j) ^ (-s) := by
      exact Real.div_rpow hQ_nonneg (by positivity) (-s)
    _ = (cubeScaleFactor Q ^ s)⁻¹ / (((3 : ℝ) ^ j) ^ s)⁻¹ := by
      rw [Real.rpow_neg hQ_nonneg,
        Real.rpow_neg (show 0 ≤ ((3 : ℝ) ^ j) by positivity)]
    _ = (cubeScaleFactor Q ^ s)⁻¹ * ((3 : ℝ) ^ j) ^ s := by
      rw [div_eq_mul_inv, inv_inv]
    _ = (cubeScaleFactor Q) ^ (-s) * ((3 : ℝ) ^ j) ^ s := by
      rw [← Real.rpow_neg hQ_nonneg]
    _ = (cubeScaleFactor Q) ^ (-s) * Real.rpow (3 : ℝ) ((j : ℝ) * s) := by
      congr 1
      symm
      simpa [mul_comm] using Real.rpow_natCast_mul (by positivity : 0 ≤ (3 : ℝ)) j s
    _ = (cubeScaleFactor Q) ^ (-s) * Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
      congr 1
      rw [mul_comm]
    _ = cubeBesovScaleWeight s Q * Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
      rfl

/-- A scalar coordinate depth average is bounded by the corrected vector depth average. -/
theorem cubeBesovOverlapDepthAverage_two_coordinate_le_vector {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d) (i : Fin d) (j : ℕ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j ≤
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j := by
  rw [cubeBesovOverlapDepthAverage, cubeBesovOverlappingPositiveVectorDepthAverage,
    ScalarOverlap.centersAverage_eq_overlapCentersAverage]
  refine overlapCentersAverage_le_overlapCentersAverage Q j ?_
  intro S hS
  have hFS : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (normalizedOverlapCubeMeasure S) :=
    memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS hF
  have hlocal := cubeBesovOverlapOscillation_two_coordinate_le_vector S F i hFS
  have hleft_nonneg :
      0 ≤ cubeBesovOverlapOscillation S (2 : ℝ≥0∞) (fun x => F x i) :=
    cubeBesovOverlapOscillation_nonneg S (2 : ℝ≥0∞) (fun x => F x i)
  have hright_nonneg :
      0 ≤ overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S F) :=
    overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S F)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (sq_le_sq₀ hleft_nonneg hright_nonneg).2 hlocal

/-- The square root of the corrected vector depth average is bounded by the sum of the square
roots of the scalar coordinate depth averages. -/
theorem sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_sum_coordinates {d : ℕ}
    (Q : TriadicCube d) (F : Vec d → Vec d) (j : ℕ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) ≤
      ∑ i : Fin d,
        Real.sqrt (cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j) := by
  let A : TriadicCube d → Fin d → ℝ := fun S i =>
    cubeBesovOverlapOscillation S (2 : ℝ≥0∞) (fun x => F x i)
  have hA_nonneg :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ i ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ A S i := by
    intro S _hS i _hi
    exact cubeBesovOverlapOscillation_nonneg S (2 : ℝ≥0∞) (fun x => F x i)
  have havg :
      cubeBesovOverlappingPositiveVectorDepthAverage Q F j ≤
        overlapCentersAverage Q j (fun S => (∑ i : Fin d, A S i) ^ 2) := by
    rw [cubeBesovOverlappingPositiveVectorDepthAverage]
    refine overlapCentersAverage_le_overlapCentersAverage Q j ?_
    intro S hS
    have hFS : MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedOverlapCubeMeasure S) :=
      memLp_normalizedOverlapCubeMeasure_of_memLp_normalizedCubeMeasure hS hF
    have hlocal :=
      overlapCubeLpNorm_fluctuationVec_le_sum_cubeBesovOverlapOscillation_two S F hFS
    have hleft_nonneg :
        0 ≤ overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S F) :=
      overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S F)
    have hright_nonneg : 0 ≤ ∑ i : Fin d, A S i :=
      Finset.sum_nonneg fun i hi => hA_nonneg S hS i hi
    exact (sq_le_sq₀ hleft_nonneg hright_nonneg).2 hlocal
  calc
    Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j)
        ≤ Real.sqrt (overlapCentersAverage Q j (fun S => (∑ i : Fin d, A S i) ^ 2)) :=
      Real.sqrt_le_sqrt havg
    _ ≤ ∑ i : Fin d,
          Real.sqrt (overlapCentersAverage Q j (fun S => (A S i) ^ 2)) :=
      by
        simpa [Real.sqrt_eq_rpow] using
          overlapCentersAverage_L2_sum_le_sum_overlapCentersAverage_L2
            Q j Finset.univ A hA_nonneg
    _ = ∑ i : Fin d,
          Real.sqrt
            (cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      congr 1
      rw [cubeBesovOverlapDepthAverage,
        ScalarOverlap.centersAverage_eq_overlapCentersAverage]
      norm_num [A, Real.rpow_two]

/-- A scalar coordinate depth seminorm is bounded by the root-scale factor times the corrected
vector depth seminorm. -/
theorem cubeBesovOverlapDepthSeminorm_two_coordinate_le_vector {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (i : Fin d) (j : ℕ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j ≤
      cubeBesovScaleWeight s Q *
        cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j := by
  have havg := cubeBesovOverlapDepthAverage_two_coordinate_le_vector Q F i j hF
  have hsqrt :
      Real.sqrt (cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j) ≤
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) :=
    Real.sqrt_le_sqrt havg
  have hweight_nonneg : 0 ≤ cubeBesovOverlapDepthWeight Q s j :=
    cubeBesovOverlapDepthWeight_nonneg Q s j
  calc
    cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j =
        cubeBesovOverlapDepthWeight Q s j *
          Real.sqrt
            (cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j) := by
      simp [cubeBesovOverlapDepthSeminorm, Real.sqrt_eq_rpow]
    _ ≤ cubeBesovOverlapDepthWeight Q s j *
          Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j) :=
      mul_le_mul_of_nonneg_left hsqrt hweight_nonneg
    _ = cubeBesovScaleWeight s Q *
          cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j := by
      rw [cubeBesovOverlapDepthWeight_eq_scaleWeight_mul_rpow]
      simp [cubeBesovOverlappingPositiveVectorDepthSeminorm, mul_assoc]

/-- After inserting the root-scale factor, the corrected vector depth seminorm is bounded by
the sum of the scalar coordinate depth seminorms. -/
theorem scaleWeight_mul_vectorDepthSeminorm_le_sum_coordinates {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (j : ℕ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovScaleWeight s Q *
        cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j ≤
      ∑ i : Fin d,
        cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j := by
  have hroot :=
    sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_le_sum_coordinates Q F j hF
  have hscale_nonneg : 0 ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hweight_nonneg : 0 ≤ cubeBesovScaleWeight s Q :=
    cubeBesovScaleWeight_nonneg s Q
  calc
    cubeBesovScaleWeight s Q *
        cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j =
      cubeBesovScaleWeight s Q *
        (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q F j)) := by
      rfl
    _ ≤ cubeBesovScaleWeight s Q *
        (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          ∑ i : Fin d,
            Real.sqrt
              (cubeBesovOverlapDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hroot hscale_nonneg) hweight_nonneg
    _ = ∑ i : Fin d,
          cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [cubeBesovOverlapDepthSeminorm,
        cubeBesovOverlapDepthWeight_eq_scaleWeight_mul_rpow]
      simp [Real.sqrt_eq_rpow, mul_assoc]

/-- The scalar finite `p = q = 2` overlap seminorm is the square root of the sum of its squared
depth terms. -/
theorem cubeBesovOverlapPartialSeminorm_two_two_eq_sqrt_sum_sq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (f : Vec d → ℝ) :
    cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N f =
      Real.sqrt
        (∑ j ∈ Finset.range (N + 1),
          (cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) f j) ^ 2) := by
  unfold cubeBesovOverlapPartialSeminorm
  rw [Real.sqrt_eq_rpow]
  norm_num

private theorem sqrt_sum_sq_const_mul_eq {ι : Type*}
    (I : Finset ι) (c : ℝ) (f : ι → ℝ) (hc : 0 ≤ c) :
    Real.sqrt (∑ i ∈ I, (c * f i) ^ 2) =
      c * Real.sqrt (∑ i ∈ I, (f i) ^ 2) := by
  have hsum_nonneg : 0 ≤ ∑ i ∈ I, (f i) ^ 2 :=
    Finset.sum_nonneg fun i _hi => sq_nonneg (f i)
  calc
    Real.sqrt (∑ i ∈ I, (c * f i) ^ 2) =
        Real.sqrt (c ^ 2 * ∑ i ∈ I, (f i) ^ 2) := by
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      ring
    _ = Real.sqrt (c ^ 2) * Real.sqrt (∑ i ∈ I, (f i) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg c)]
    _ = c * Real.sqrt (∑ i ∈ I, (f i) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

private theorem sqrt_sum_sq_add_le {ι : Type*}
    (I : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) (hg : ∀ i ∈ I, 0 ≤ g i) :
    Real.sqrt (∑ i ∈ I, (f i + g i) ^ 2) ≤
      Real.sqrt (∑ i ∈ I, (f i) ^ 2) + Real.sqrt (∑ i ∈ I, (g i) ^ 2) := by
  simpa [Real.sqrt_eq_rpow] using
    (Real.Lp_add_le_of_nonneg
      (s := I) (f := f) (g := g) (p := (2 : ℝ)) (by norm_num) hf hg)

private theorem sqrt_sum_sq_sum_le_sum_sqrt_sum_sq
    {ι κ : Type*} [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (A : ι → κ → ℝ)
    (hA : ∀ i ∈ I, ∀ k ∈ J, 0 ≤ A i k) :
    Real.sqrt (∑ i ∈ I, (∑ k ∈ J, A i k) ^ 2) ≤
      ∑ k ∈ J, Real.sqrt (∑ i ∈ I, (A i k) ^ 2) := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
      have hsum_nonneg : ∀ i ∈ I, 0 ≤ ∑ k ∈ J, A i k := by
        intro i hi
        exact Finset.sum_nonneg fun k hk => hA i hi k (Finset.mem_insert_of_mem hk)
      calc
        Real.sqrt (∑ i ∈ I, (∑ k ∈ insert a J, A i k) ^ 2) =
            Real.sqrt (∑ i ∈ I, (A i a + ∑ k ∈ J, A i k) ^ 2) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.sum_insert ha]
        _ ≤ Real.sqrt (∑ i ∈ I, (A i a) ^ 2) +
              Real.sqrt (∑ i ∈ I, (∑ k ∈ J, A i k) ^ 2) :=
          sqrt_sum_sq_add_le I (fun i => A i a) (fun i => ∑ k ∈ J, A i k)
            (fun i hi => hA i hi a (by simp [ha])) hsum_nonneg
        _ ≤ Real.sqrt (∑ i ∈ I, (A i a) ^ 2) +
              ∑ k ∈ J, Real.sqrt (∑ i ∈ I, (A i k) ^ 2) := by
          exact add_le_add le_rfl <|
            ih (fun i hi k hk => hA i hi k (Finset.mem_insert_of_mem hk))
        _ = ∑ k ∈ insert a J, Real.sqrt (∑ i ∈ I, (A i k) ^ 2) := by
          simp [ha]

/-- A scalar coordinate finite truncation is bounded by the root-scale factor times the
corrected vector finite truncation. -/
theorem cubeBesovOverlapPartialSeminorm_two_coordinate_le_vector {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (i : Fin d) (N : ℕ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
        (fun x => F x i) ≤
      cubeBesovScaleWeight s Q *
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F := by
  have hsum_le :
      (∑ j ∈ Finset.range (N + 1),
          (cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j) ^ 2) ≤
        ∑ j ∈ Finset.range (N + 1),
          (cubeBesovScaleWeight s Q *
            cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    have hdepth := cubeBesovOverlapDepthSeminorm_two_coordinate_le_vector
      Q s F i j hF
    exact (sq_le_sq₀
      (cubeBesovOverlapDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) (fun x => F x i) j)
      (mul_nonneg (cubeBesovScaleWeight_nonneg s Q)
        (cubeBesovOverlappingPositiveVectorDepthSeminorm_nonneg Q s F j))).2 hdepth
  calc
    cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
        (fun x => F x i) =
      Real.sqrt
        (∑ j ∈ Finset.range (N + 1),
          (cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j) ^ 2) :=
      cubeBesovOverlapPartialSeminorm_two_two_eq_sqrt_sum_sq Q s N (fun x => F x i)
    _ ≤ Real.sqrt
        (∑ j ∈ Finset.range (N + 1),
          (cubeBesovScaleWeight s Q *
            cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2) :=
      Real.sqrt_le_sqrt hsum_le
    _ = cubeBesovScaleWeight s Q *
        Real.sqrt
          (∑ j ∈ Finset.range (N + 1),
            (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2) :=
      sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) (cubeBesovScaleWeight s Q)
        (fun j => cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j)
        (cubeBesovScaleWeight_nonneg s Q)
    _ = cubeBesovScaleWeight s Q *
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F := by
      rfl

/-- After inserting the root-scale factor, the corrected vector finite truncation is bounded by
the sum of the scalar coordinate finite truncations. This is uniform in the truncation depth. -/
theorem scaleWeight_mul_vectorPartialSeminorm_le_sum_coordinates {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (N : ℕ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovScaleWeight s Q *
        cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F ≤
      ∑ i : Fin d,
        cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => F x i) := by
  let A : ℕ → Fin d → ℝ := fun j i =>
    cubeBesovOverlapDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j
  let W : ℝ := cubeBesovScaleWeight s Q
  have hA_nonneg :
      ∀ j ∈ Finset.range (N + 1), ∀ i ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ A j i := by
    intro j _hj i _hi
    exact cubeBesovOverlapDepthSeminorm_nonneg Q s (2 : ℝ≥0∞) (fun x => F x i) j
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        W * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j ≤
          ∑ i : Fin d, A j i := by
    intro j _hj
    exact scaleWeight_mul_vectorDepthSeminorm_le_sum_coordinates Q s F j hF
  have hsum_le :
      ∑ j ∈ Finset.range (N + 1),
          (W * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2 ≤
        ∑ j ∈ Finset.range (N + 1), (∑ i : Fin d, A j i) ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact (sq_le_sq₀
      (mul_nonneg (cubeBesovScaleWeight_nonneg s Q)
        (cubeBesovOverlappingPositiveVectorDepthSeminorm_nonneg Q s F j))
      (Finset.sum_nonneg fun i hi => hA_nonneg j hj i hi)).2 (hdepth j hj)
  calc
    W * cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F =
        Real.sqrt
          (∑ j ∈ Finset.range (N + 1),
            (W * cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j) ^ 2) := by
      rw [sqrt_sum_sq_const_mul_eq (Finset.range (N + 1)) W
        (fun j => cubeBesovOverlappingPositiveVectorDepthSeminorm Q s F j)]
      · rfl
      · exact cubeBesovScaleWeight_nonneg s Q
    _ ≤ Real.sqrt
          (∑ j ∈ Finset.range (N + 1), (∑ i : Fin d, A j i) ^ 2) :=
      Real.sqrt_le_sqrt hsum_le
    _ ≤ ∑ i : Fin d,
          Real.sqrt (∑ j ∈ Finset.range (N + 1), (A j i) ^ 2) :=
      sqrt_sum_sq_sum_le_sum_sqrt_sum_sq
        (Finset.range (N + 1)) Finset.univ A hA_nonneg
    _ = ∑ i : Fin d,
          cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => F x i) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact (cubeBesovOverlapPartialSeminorm_two_two_eq_sqrt_sum_sq
        Q s N (fun x => F x i)).symm

/-- The Euclidean aggregate of the scalar coordinate finite truncations is controlled by the
corrected vector truncation with the explicit factor `sqrt d`. -/
theorem sqrt_sum_sq_coordinatePartialSeminorm_le_sqrt_dim_mul_vector {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (N : ℕ)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Real.sqrt
        (∑ i : Fin d,
          (cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => F x i)) ^ 2) ≤
      Real.sqrt (d : ℝ) *
        (cubeBesovScaleWeight s Q *
          cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F) := by
  let B : ℝ := cubeBesovScaleWeight s Q *
    cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg (cubeBesovScaleWeight_nonneg s Q)
      (cubeBesovOverlappingPositiveVectorPartialSeminormTwo_nonneg Q s N F)
  have hsum_le :
      (∑ i : Fin d,
          (cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => F x i)) ^ 2) ≤
        (d : ℝ) * B ^ 2 := by
    calc
      (∑ i : Fin d,
          (cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => F x i)) ^ 2) ≤
          ∑ _i : Fin d, B ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        exact (sq_le_sq₀
          (cubeBesovOverlapPartialSeminorm_nonneg Q s (2 : ℝ≥0∞)
            (2 : ℝ≥0∞) N (fun x => F x i)) hB_nonneg).2
          (cubeBesovOverlapPartialSeminorm_two_coordinate_le_vector Q s F i N hF)
      _ = (d : ℝ) * B ^ 2 := by
        simp
  calc
    Real.sqrt
        (∑ i : Fin d,
          (cubeBesovOverlapPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => F x i)) ^ 2) ≤
        Real.sqrt ((d : ℝ) * B ^ 2) :=
      Real.sqrt_le_sqrt hsum_le
    _ = Real.sqrt (d : ℝ) * Real.sqrt (B ^ 2) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d)]
    _ = Real.sqrt (d : ℝ) * B := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB_nonneg]
    _ = Real.sqrt (d : ℝ) *
        (cubeBesovScaleWeight s Q *
          cubeBesovOverlappingPositiveVectorPartialSeminormTwo Q s N F) := by
      rfl

end

end Homogenization
