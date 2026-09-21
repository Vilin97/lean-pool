/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.QTwo
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoliLocalGradientBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Correctors
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesQTwo

/-! # Seminorm Recurrence -/

namespace Homogenization

noncomputable section


theorem cubeAverageVec_sub
    {d : ℕ} (Q : TriadicCube d) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) :
    cubeAverageVec Q (fun x => u x - v x) = cubeAverageVec Q u - cubeAverageVec Q v := by
  funext i
  have hui :
      MeasureTheory.MemLp (fun x => u x i) (2 : ENNReal)
        (volumeMeasureOn (cubeSet Q)) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hvi :
      MeasureTheory.MemLp (fun x => v x i) (2 : ENNReal)
        (volumeMeasureOn (cubeSet Q)) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hv
  have hui_int :
      MeasureTheory.Integrable (fun x => u x i) (volumeMeasureOn (cubeSet Q)) :=
    hui.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  have hvi_int :
      MeasureTheory.Integrable (fun x => v x i) (volumeMeasureOn (cubeSet Q)) :=
    hvi.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  show cubeAverage Q (fun x => (u x - v x) i) =
    cubeAverage Q (fun x => u x i) - cubeAverage Q (fun x => v x i)
  have hfun : (fun x => (u x - v x) i) = fun x => u x i - v x i := by
    funext x
    simp
  unfold cubeAverage
  rw [hfun]
  rw [MeasureTheory.integral_sub hui_int hvi_int]
  ring

theorem cubeAverageVec_add
    {d : ℕ} (Q : TriadicCube d) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) :
    cubeAverageVec Q (fun x => u x + v x) = cubeAverageVec Q u + cubeAverageVec Q v := by
  funext i
  have hui :
      MeasureTheory.MemLp (fun x => u x i) (2 : ENNReal)
        (volumeMeasureOn (cubeSet Q)) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hvi :
      MeasureTheory.MemLp (fun x => v x i) (2 : ENNReal)
        (volumeMeasureOn (cubeSet Q)) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hv
  have hui_int :
      MeasureTheory.Integrable (fun x => u x i) (volumeMeasureOn (cubeSet Q)) :=
    hui.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  have hvi_int :
      MeasureTheory.Integrable (fun x => v x i) (volumeMeasureOn (cubeSet Q)) :=
    hvi.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  show cubeAverage Q (fun x => (u x + v x) i) =
    cubeAverage Q (fun x => u x i) + cubeAverage Q (fun x => v x i)
  have hfun : (fun x => (u x + v x) i) = fun x => u x i + v x i := by
    funext x
    simp
  unfold cubeAverage
  rw [hfun]
  rw [MeasureTheory.integral_add hui_int hvi_int]
  ring

theorem cubeBesovNegativeVectorDepthAverage_eq_of_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (huv : ∀ x ∈ cubeSet Q, u x = v x) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q u j =
      cubeBesovNegativeVectorDepthAverage Q v j := by
  unfold cubeBesovNegativeVectorDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  exact congrArg vecNormSq <|
    cubeAverageVec_eq_of_eq_on_cubeSet fun x hx =>
      huv x (cubeSet_subset_of_mem_descendantsAtDepth hR hx)

theorem cubeBesovNegativeVectorDepthSeminorm_eq_of_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (s : ℝ) (huv : ∀ x ∈ cubeSet Q, u x = v x) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s u j =
      cubeBesovNegativeVectorDepthSeminorm Q s v j := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  rw [cubeBesovNegativeVectorDepthAverage_eq_of_eq_on_cubeSet huv]

theorem cubeBesovNegativeVectorPartialSeminormTwo_eq_of_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (s : ℝ) (N : ℕ) (huv : ∀ x ∈ cubeSet Q, u x = v x) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N u =
      cubeBesovNegativeVectorPartialSeminormTwo Q s N v := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [cubeBesovNegativeVectorDepthSeminorm_eq_of_eq_on_cubeSet s huv j]

theorem cubeBesovNegativeVectorSeminormTwo_eq_of_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {u v : Vec d → Vec d}
    (s : ℝ) (huv : ∀ x ∈ cubeSet Q, u x = v x) :
    cubeBesovNegativeVectorSeminormTwo Q s u =
      cubeBesovNegativeVectorSeminormTwo Q s v := by
  unfold cubeBesovNegativeVectorSeminormTwo
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨N, (cubeBesovNegativeVectorPartialSeminormTwo_eq_of_eq_on_cubeSet
      (Q := Q) (u := u) (v := v) s N huv).symm⟩
  · rintro ⟨N, rfl⟩
    exact ⟨N, cubeBesovNegativeVectorPartialSeminormTwo_eq_of_eq_on_cubeSet
      (Q := Q) (u := u) (v := v) s N huv⟩

theorem cubeBesovNegativeVectorDepthAverage_sub_le_two_mul_add
    {d : ℕ} (Q : TriadicCube d) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q (fun x => u x - v x) j ≤
      2 * cubeBesovNegativeVectorDepthAverage Q u j +
        2 * cubeBesovNegativeVectorDepthAverage Q v j := by
  unfold cubeBesovNegativeVectorDepthAverage
  calc
    descendantsAverage Q j (fun R => vecNormSq (cubeAverageVec R (fun x => u x - v x)))
        ≤
          descendantsAverage Q j
            (fun R => 2 * (vecNormSq (cubeAverageVec R u) + vecNormSq (cubeAverageVec R v))) := by
              refine descendantsAverage_le_descendantsAverage Q j ?_
              intro R hR
              have huR : MemVectorL2 (cubeSet R) u := by
                simpa [MemVectorL2, volumeMeasureOn] using
                  hu.mono_measure
                    (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
                      (cubeSet_subset_of_mem_descendantsAtDepth hR))
              have hvR : MemVectorL2 (cubeSet R) v := by
                simpa [MemVectorL2, volumeMeasureOn] using
                  hv.mono_measure
                    (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
                      (cubeSet_subset_of_mem_descendantsAtDepth hR))
              calc
                vecNormSq (cubeAverageVec R (fun x => u x - v x))
                    = vecNormSq (cubeAverageVec R u - cubeAverageVec R v) := by
                        rw [cubeAverageVec_sub R u v huR hvR]
                _ ≤ 2 * (vecNormSq (cubeAverageVec R u) + vecNormSq (cubeAverageVec R v)) := by
                      exact vecNormSq_sub_le (cubeAverageVec R u) (cubeAverageVec R v)
    _ =
        2 * descendantsAverage Q j (fun R => vecNormSq (cubeAverageVec R u) + vecNormSq (cubeAverageVec R v)) := by
          rw [descendantsAverage_smul Q j (2 : ℝ)
            (fun R => vecNormSq (cubeAverageVec R u) + vecNormSq (cubeAverageVec R v))]
    _ =
        2 * (cubeBesovNegativeVectorDepthAverage Q u j +
          cubeBesovNegativeVectorDepthAverage Q v j) := by
            rw [descendantsAverage_add Q j
              (fun R => vecNormSq (cubeAverageVec R u))
              (fun R => vecNormSq (cubeAverageVec R v))]
            simp [cubeBesovNegativeVectorDepthAverage]
    _ = 2 * cubeBesovNegativeVectorDepthAverage Q u j +
          2 * cubeBesovNegativeVectorDepthAverage Q v j := by
            ring

theorem sq_cubeBesovNegativeVectorDepthSeminorm_sub_le_two_mul_add
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) (j : ℕ) :
    (cubeBesovNegativeVectorDepthSeminorm Q s (fun x => u x - v x) j) ^ 2 ≤
      2 * (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 +
        2 * (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2 := by
  have havg :=
    cubeBesovNegativeVectorDepthAverage_sub_le_two_mul_add Q u v hu hv j
  calc
    (cubeBesovNegativeVectorDepthSeminorm Q s (fun x => u x - v x) j) ^ 2
        =
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            cubeBesovNegativeVectorDepthAverage Q (fun x => u x - v x) j := by
              rw [sq_cubeBesovNegativeVectorDepthSeminorm]
    _ ≤
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            (2 * cubeBesovNegativeVectorDepthAverage Q u j +
              2 * cubeBesovNegativeVectorDepthAverage Q v j) := by
                exact mul_le_mul_of_nonneg_left havg (sq_nonneg _)
    _ =
          2 * ((Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              cubeBesovNegativeVectorDepthAverage Q u j) +
            2 * ((Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              cubeBesovNegativeVectorDepthAverage Q v j) := by
                ring
    _ =
          2 * (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 +
            2 * (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2 := by
              rw [← sq_cubeBesovNegativeVectorDepthSeminorm,
                ← sq_cubeBesovNegativeVectorDepthSeminorm]

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_sub_le_two_mul_add
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) (N : ℕ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x - v x)) ^ 2 ≤
      2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
        2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := by
  rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
  calc
    Finset.sum (Finset.range (N + 1))
        (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s (fun x => u x - v x) j) ^ 2)
        ≤
          Finset.sum (Finset.range (N + 1))
            (fun j =>
              2 * (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 +
                2 * (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2) := by
                  refine Finset.sum_le_sum ?_
                  intro j hj
                  exact
                    sq_cubeBesovNegativeVectorDepthSeminorm_sub_le_two_mul_add
                      Q s u v hu hv j
    _ =
          Finset.sum (Finset.range (N + 1))
            (fun j => 2 * (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) +
          Finset.sum (Finset.range (N + 1))
            (fun j => 2 * (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2) := by
              rw [Finset.sum_add_distrib]
    _ =
          2 * Finset.sum (Finset.range (N + 1))
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) +
          2 * Finset.sum (Finset.range (N + 1))
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ =
          2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
            2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := by
      rw [← sq_cubeBesovNegativeVectorPartialSeminormTwo,
        ← sq_cubeBesovNegativeVectorPartialSeminormTwo]

theorem cubeBesovNegativeVectorDepthAverage_add_le_two_mul_add
    {d : ℕ} (Q : TriadicCube d) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q (fun x => u x + v x) j ≤
      2 * cubeBesovNegativeVectorDepthAverage Q u j +
        2 * cubeBesovNegativeVectorDepthAverage Q v j := by
  unfold cubeBesovNegativeVectorDepthAverage
  calc
    descendantsAverage Q j (fun R => vecNormSq (cubeAverageVec R (fun x => u x + v x)))
        ≤
          descendantsAverage Q j
            (fun R => 2 * (vecNormSq (cubeAverageVec R u) + vecNormSq (cubeAverageVec R v))) := by
              refine descendantsAverage_le_descendantsAverage Q j ?_
              intro R hR
              have huR : MemVectorL2 (cubeSet R) u := by
                simpa [MemVectorL2, volumeMeasureOn] using
                  hu.mono_measure
                    (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
                      (cubeSet_subset_of_mem_descendantsAtDepth hR))
              have hvR : MemVectorL2 (cubeSet R) v := by
                simpa [MemVectorL2, volumeMeasureOn] using
                  hv.mono_measure
                    (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
                      (cubeSet_subset_of_mem_descendantsAtDepth hR))
              calc
                vecNormSq (cubeAverageVec R (fun x => u x + v x))
                    = vecNormSq (cubeAverageVec R u + cubeAverageVec R v) := by
                        rw [cubeAverageVec_add R u v huR hvR]
                _ ≤ 2 * (vecNormSq (cubeAverageVec R u) + vecNormSq (cubeAverageVec R v)) := by
                      exact vecNormSq_add_le (cubeAverageVec R u) (cubeAverageVec R v)
    _ =
        2 * descendantsAverage Q j (fun R => vecNormSq (cubeAverageVec R u) + vecNormSq (cubeAverageVec R v)) := by
          rw [descendantsAverage_smul Q j (2 : ℝ)
            (fun R => vecNormSq (cubeAverageVec R u) + vecNormSq (cubeAverageVec R v))]
    _ =
        2 * (cubeBesovNegativeVectorDepthAverage Q u j +
          cubeBesovNegativeVectorDepthAverage Q v j) := by
            rw [descendantsAverage_add Q j
              (fun R => vecNormSq (cubeAverageVec R u))
              (fun R => vecNormSq (cubeAverageVec R v))]
            simp [cubeBesovNegativeVectorDepthAverage]
    _ = 2 * cubeBesovNegativeVectorDepthAverage Q u j +
          2 * cubeBesovNegativeVectorDepthAverage Q v j := by
            ring

theorem sq_cubeBesovNegativeVectorDepthSeminorm_add_le_two_mul_add
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) (j : ℕ) :
    (cubeBesovNegativeVectorDepthSeminorm Q s (fun x => u x + v x) j) ^ 2 ≤
      2 * (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 +
        2 * (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2 := by
  have havg :=
    cubeBesovNegativeVectorDepthAverage_add_le_two_mul_add Q u v hu hv j
  calc
    (cubeBesovNegativeVectorDepthSeminorm Q s (fun x => u x + v x) j) ^ 2
        =
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            cubeBesovNegativeVectorDepthAverage Q (fun x => u x + v x) j := by
              rw [sq_cubeBesovNegativeVectorDepthSeminorm]
    _ ≤
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            (2 * cubeBesovNegativeVectorDepthAverage Q u j +
              2 * cubeBesovNegativeVectorDepthAverage Q v j) := by
                exact mul_le_mul_of_nonneg_left havg (sq_nonneg _)
    _ =
          2 * ((Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              cubeBesovNegativeVectorDepthAverage Q u j) +
            2 * ((Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              cubeBesovNegativeVectorDepthAverage Q v j) := by
                ring
    _ =
          2 * (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 +
            2 * (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2 := by
              rw [← sq_cubeBesovNegativeVectorDepthSeminorm,
                ← sq_cubeBesovNegativeVectorDepthSeminorm]

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_add_le_two_mul_add
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) (N : ℕ) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x + v x)) ^ 2 ≤
      2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
        2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := by
  rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
  calc
    Finset.sum (Finset.range (N + 1))
        (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s (fun x => u x + v x) j) ^ 2)
        ≤
          Finset.sum (Finset.range (N + 1))
            (fun j =>
              2 * (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 +
                2 * (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2) := by
                  refine Finset.sum_le_sum ?_
                  intro j hj
                  exact
                    sq_cubeBesovNegativeVectorDepthSeminorm_add_le_two_mul_add
                      Q s u v hu hv j
    _ =
          Finset.sum (Finset.range (N + 1))
            (fun j => 2 * (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) +
          Finset.sum (Finset.range (N + 1))
            (fun j => 2 * (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2) := by
              rw [Finset.sum_add_distrib]
    _ =
          2 * Finset.sum (Finset.range (N + 1))
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) +
          2 * Finset.sum (Finset.range (N + 1))
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s v j) ^ 2) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ =
          2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
            2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := by
              rw [← sq_cubeBesovNegativeVectorPartialSeminormTwo,
                ← sq_cubeBesovNegativeVectorPartialSeminormTwo]

theorem cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x + v x) ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N v) := by
  have hsq :=
    sq_cubeBesovNegativeVectorPartialSeminormTwo_add_le_two_mul_add Q s u v hu hv N
  have hadd_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x + v x) :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N (fun x => u x + v x)
  have hu_nonneg : 0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N u
  have hv_nonneg : 0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N v :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N v
  have hsum_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v :=
    add_nonneg hu_nonneg hv_nonneg
  have hsq_bound :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x + v x)) ^ 2 ≤
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
            cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) ^ 2 := by
    calc
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x + v x)) ^ 2
          ≤
        2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
          2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := hsq
      _ ≤ 2 *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
            cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := by
            nlinarith
      _ = (Real.sqrt 2 *
            (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
              cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) ^ 2 := by
            have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
              nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
            calc
              2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2
                  =
                (Real.sqrt 2) ^ 2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := by
                        rw [hsqrt2]
              _ =
                (Real.sqrt 2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) ^ 2 := by
                        ring
  have hright_nonneg :
      0 ≤ Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N v) := by
    exact mul_nonneg (Real.sqrt_nonneg _) hsum_nonneg
  nlinarith

theorem cubeBesovNegativeVectorSeminormTwo_add_le_sqrtTwo_mul_add_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v)
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hvBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => u x + v x) ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorSeminormTwo Q s u +
          cubeBesovNegativeVectorSeminormTwo Q s v) := by
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s
    (fun x => u x + v x) ?_
  intro N
  calc
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x + v x)
        ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N v) := by
            exact cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add
              Q s u v hu hv N
    _ ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorSeminormTwo Q s u +
          cubeBesovNegativeVectorSeminormTwo Q s v) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add
                (by
                  unfold cubeBesovNegativeVectorSeminormTwo
                  exact le_csSup huBdd ⟨N, rfl⟩)
                (by
                  unfold cubeBesovNegativeVectorSeminormTwo
                  exact le_csSup hvBdd ⟨N, rfl⟩))
              (Real.sqrt_nonneg _)

theorem cubeBesovNegativeVectorPartialSeminormTwo_sub_le_sqrtTwo_mul_add
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x - v x) ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N v) := by
  have hsq :=
    sq_cubeBesovNegativeVectorPartialSeminormTwo_sub_le_two_mul_add Q s u v hu hv N
  have hsub_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x - v x) :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N (fun x => u x - v x)
  have hu_nonneg : 0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N u
  have hv_nonneg : 0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N v :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N v
  have hsum_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v :=
    add_nonneg hu_nonneg hv_nonneg
  have hsq_bound :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x - v x)) ^ 2 ≤
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
            cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) ^ 2 := by
    calc
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x - v x)) ^ 2
          ≤
        2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 +
          2 * (cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := hsq
      _ ≤ 2 *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
            cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := by
            nlinarith
      _ = (Real.sqrt 2 *
            (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
              cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) ^ 2 := by
            have hsqrt2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
              nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
            calc
              2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2
                  =
                (Real.sqrt 2) ^ 2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N v) ^ 2 := by
                        rw [hsqrt2]
              _ =
                (Real.sqrt 2 *
                  (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
                    cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) ^ 2 := by
                        ring
  have hright_nonneg :
      0 ≤ Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N v) := by
    exact mul_nonneg (Real.sqrt_nonneg _) hsum_nonneg
  nlinarith

theorem cubeBesovNegativeVectorSeminormTwo_sub_le_sqrtTwo_mul_add_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v)
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hvBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => u x - v x) ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorSeminormTwo Q s u +
          cubeBesovNegativeVectorSeminormTwo Q s v) := by
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s
    (fun x => u x - v x) ?_
  intro N
  calc
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x - v x)
        ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N v) := by
            exact cubeBesovNegativeVectorPartialSeminormTwo_sub_le_sqrtTwo_mul_add
              Q s u v hu hv N
    _ ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorSeminormTwo Q s u +
          cubeBesovNegativeVectorSeminormTwo Q s v) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add
                (by
                  unfold cubeBesovNegativeVectorSeminormTwo
                  exact le_csSup huBdd ⟨N, rfl⟩)
                (by
                  unfold cubeBesovNegativeVectorSeminormTwo
                  exact le_csSup hvBdd ⟨N, rfl⟩))
              (Real.sqrt_nonneg _)

theorem cubeBesovNegativeVectorSeminormTwo_add_sub_le_sqrtTwo_mul_add_sqrtTwo_mul_add_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u v w : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v)
    (hw : MemVectorL2 (cubeSet Q) w)
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hvBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v))
    (hwBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N w)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => u x + v x - w x) ≤
      Real.sqrt 2 *
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorSeminormTwo Q s u +
            cubeBesovNegativeVectorSeminormTwo Q s v) +
          cubeBesovNegativeVectorSeminormTwo Q s w) := by
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s
    (fun x => u x + v x - w x) ?_
  intro N
  have huv : MemVectorL2 (cubeSet Q) (fun x => u x + v x) := hu.add hv
  calc
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x + v x - w x)
        ≤
      Real.sqrt 2 *
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => u x + v x) +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N w) := by
            exact cubeBesovNegativeVectorPartialSeminormTwo_sub_le_sqrtTwo_mul_add
              Q s (fun x => u x + v x) w huv hw N
    _ ≤
      Real.sqrt 2 *
        (Real.sqrt 2 *
            (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
              cubeBesovNegativeVectorPartialSeminormTwo Q s N v) +
          cubeBesovNegativeVectorPartialSeminormTwo Q s N w) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add
                (cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add
                  Q s u v hu hv N)
                le_rfl)
              (Real.sqrt_nonneg _)
    _ ≤
      Real.sqrt 2 *
        (Real.sqrt 2 *
          (cubeBesovNegativeVectorSeminormTwo Q s u +
            cubeBesovNegativeVectorSeminormTwo Q s v) +
          cubeBesovNegativeVectorSeminormTwo Q s w) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (add_le_add
                  (by
                    unfold cubeBesovNegativeVectorSeminormTwo
                    exact le_csSup huBdd ⟨N, rfl⟩)
                  (by
                    unfold cubeBesovNegativeVectorSeminormTwo
                    exact le_csSup hvBdd ⟨N, rfl⟩))
                (Real.sqrt_nonneg _))
              (by
                unfold cubeBesovNegativeVectorSeminormTwo
                exact le_csSup hwBdd ⟨N, rfl⟩)

theorem cubeBesovNegativeVectorPartialSeminormTwo_le_succ
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤
      cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u := by
  have hsq :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤
        (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 := by
    rw [sq_cubeBesovNegativeVectorPartialSeminormTwo,
      sq_cubeBesovNegativeVectorPartialSeminormTwo]
    have hsplit :
        Finset.sum (Finset.range (N + 2))
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) =
          Finset.sum (Finset.range (N + 1))
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) +
            (cubeBesovNegativeVectorDepthSeminorm Q s u (N + 1)) ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_range_succ
          (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) (N + 1))
    calc
      Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2)
          ≤
        Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) +
            (cubeBesovNegativeVectorDepthSeminorm Q s u (N + 1)) ^ 2 := by
              exact le_add_of_nonneg_right (sq_nonneg _)
      _ =
        Finset.sum (Finset.range (N + 2))
          (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) := by
            rw [hsplit]
  have hN_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N u
  have hSucc_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s (N + 1) u
  have habs :
      |cubeBesovNegativeVectorPartialSeminormTwo Q s N u| ≤
        |cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u| :=
    sq_le_sq.mp hsq
  simpa [abs_of_nonneg hN_nonneg, abs_of_nonneg hSucc_nonneg] using habs

theorem cubeBesovPositiveVectorPartialSeminormTwo_le_succ
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N u ≤
      cubeBesovPositiveVectorPartialSeminormTwo Q s (N + 1) u := by
  have hsq :
      (cubeBesovPositiveVectorPartialSeminormTwo Q s N u) ^ 2 ≤
        (cubeBesovPositiveVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 := by
    rw [sq_cubeBesovPositiveVectorPartialSeminormTwo,
      sq_cubeBesovPositiveVectorPartialSeminormTwo]
    have hsplit :
        Finset.sum (Finset.range (N + 2))
            (fun j => (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2) =
          Finset.sum (Finset.range (N + 1))
            (fun j => (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2) +
            (cubeBesovPositiveVectorDepthSeminorm Q s u (N + 1)) ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Finset.sum_range_succ
          (fun j => (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2) (N + 1))
    calc
      Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2)
          ≤
        Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2) +
            (cubeBesovPositiveVectorDepthSeminorm Q s u (N + 1)) ^ 2 := by
              exact le_add_of_nonneg_right (sq_nonneg _)
      _ =
        Finset.sum (Finset.range (N + 2))
          (fun j => (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2) := by
            rw [hsplit]
  have hN_nonneg :
      0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s N u :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s N u
  have hSucc_nonneg :
      0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s (N + 1) u :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s (N + 1) u
  have habs :
      |cubeBesovPositiveVectorPartialSeminormTwo Q s N u| ≤
        |cubeBesovPositiveVectorPartialSeminormTwo Q s (N + 1) u| :=
    sq_le_sq.mp hsq
  simpa [abs_of_nonneg hN_nonneg, abs_of_nonneg hSucc_nonneg] using habs

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_of_partialSqBound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) {B : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hpartial :
      ∀ N : ℕ,
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤ B) :
    (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤ B := by
  let C : ℝ := Real.sqrt B
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Real.sqrt_nonneg _
  have hpartial_le :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ C := by
    intro N
    have hpartial_nonneg :
        0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u :=
      cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N u
    have hsq :
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤ C ^ 2 := by
      simpa [C, Real.sq_sqrt hB_nonneg] using hpartial N
    have habs :
        |cubeBesovNegativeVectorPartialSeminormTwo Q s N u| ≤ |C| :=
      sq_le_sq.mp hsq
    simpa [abs_of_nonneg hpartial_nonneg, abs_of_nonneg hC_nonneg] using habs
  have hfull_le :
      cubeBesovNegativeVectorSeminormTwo Q s u ≤ C :=
    cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s u hpartial_le
  have hbdd :
      BddAbove
        (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q s N u) := by
    refine ⟨C, ?_⟩
    rintro x ⟨N, rfl⟩
    exact hpartial_le N
  have hfull_nonneg : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s u := by
    have hpartial0_le :
        cubeBesovNegativeVectorPartialSeminormTwo Q s 0 u ≤
          cubeBesovNegativeVectorSeminormTwo Q s u := by
      unfold cubeBesovNegativeVectorSeminormTwo
      exact le_csSup hbdd ⟨0, rfl⟩
    exact
      (cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s 0 u).trans hpartial0_le
  have habs :
      |cubeBesovNegativeVectorSeminormTwo Q s u| ≤ |C| := by
    simpa [abs_of_nonneg hfull_nonneg, abs_of_nonneg hC_nonneg] using hfull_le
  have hsq :
      (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤ C ^ 2 :=
    sq_le_sq.mpr habs
  simpa [C, Real.sq_sqrt hB_nonneg] using hsq


theorem cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤
      cubeBesovNegativeVectorSeminormTwo Q s u := by
  unfold cubeBesovNegativeVectorSeminormTwo
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N u))
    (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N u ≤
      cubeBesovPositiveVectorSeminormTwo Q s u := by
  unfold cubeBesovPositiveVectorSeminormTwo
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u)) :
    0 ≤ cubeBesovNegativeVectorSeminormTwo Q s u := by
  have h0_le :
      cubeBesovNegativeVectorPartialSeminormTwo Q s 0 u ≤
        cubeBesovNegativeVectorSeminormTwo Q s u :=
    cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove Q s u hBdd 0
  exact (cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s 0 u).trans h0_le

theorem cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N u)) :
    0 ≤ cubeBesovPositiveVectorSeminormTwo Q s u := by
  have h0_le :
      cubeBesovPositiveVectorPartialSeminormTwo Q s 0 u ≤
      cubeBesovPositiveVectorSeminormTwo Q s u :=
    cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove Q s u hBdd 0
  exact (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s 0 u).trans h0_le

theorem sq_le_inv_one_sub_mul_add_of_sq_le_add_bilinear_term
    {A D U W G η : ℝ}
    (hη : 0 < η) (hη_lt : η < 1)
    (h : W ^ 2 ≤ A + D * (U + W) * G) :
    W ^ 2 ≤ (1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * (((D / 2) * G) ^ 2)) := by
  have hU :
      D * U * G ≤ η * U ^ 2 + η⁻¹ * (((D / 2) * G) ^ 2) := by
    convert (two_mul_le_add_mul_sq (a := U) (b := (D / 2) * G) (ε := η) hη) using 1
    all_goals (first | rfl | ring)
  have hW :
      D * W * G ≤ η * W ^ 2 + η⁻¹ * (((D / 2) * G) ^ 2) := by
    convert (two_mul_le_add_mul_sq (a := W) (b := (D / 2) * G) (ε := η) hη) using 1
    all_goals (first | rfl | ring)
  have hstep :
      (1 - η) * W ^ 2 ≤ A + η * U ^ 2 + 2 * η⁻¹ * (((D / 2) * G) ^ 2) := by
    linarith
  have hone_sub : 0 < 1 - η := by linarith
  calc
    W ^ 2 = (1 - η)⁻¹ * ((1 - η) * W ^ 2) := by
      field_simp [hone_sub.ne']
    _ ≤ (1 - η)⁻¹ * (A + η * U ^ 2 + 2 * η⁻¹ * (((D / 2) * G) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hone_sub.le)

theorem add_bilinear_term_le_add_eta_sq_add_invEta_sq
    {D U W G η : ℝ} (hη : 0 < η) :
    D * (U + W) * G ≤
      η * U ^ 2 + η * W ^ 2 + 2 * η⁻¹ * (((D / 2) * G) ^ 2) := by
  have hU :
      D * U * G ≤ η * U ^ 2 + η⁻¹ * (((D / 2) * G) ^ 2) := by
    convert (two_mul_le_add_mul_sq (a := U) (b := (D / 2) * G) (ε := η) hη) using 1
    all_goals (first | rfl | ring)
  have hW :
      D * W * G ≤ η * W ^ 2 + η⁻¹ * (((D / 2) * G) ^ 2) := by
    convert (two_mul_le_add_mul_sq (a := W) (b := (D / 2) * G) (ε := η) hη) using 1
    all_goals (first | rfl | ring)
  have hsplit : D * (U + W) * G = D * U * G + D * W * G := by
    ring
  rw [hsplit]
  linarith

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_descendantsAverage_add_of_succ_partialBound
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (Bchild : TriadicCube d → ℝ) {F : ℝ}
    (hB_nonneg :
      0 ≤
        Real.rpow (3 : ℝ) (-2 * s) *
          descendantsAverage Q 1 (fun R => (Bchild R) ^ 2) + F)
    (hlocal :
      ∀ N : ℕ,
        (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage Q 1
              (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
          F)
    (hchild :
      ∀ R ∈ descendantsAtDepth Q 1, ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo R s N u ≤ Bchild R) :
    (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s) *
        descendantsAverage Q 1 (fun R => (Bchild R) ^ 2) + F := by
  let Echild : ℝ :=
    Real.rpow (3 : ℝ) (-2 * s) *
      descendantsAverage Q 1 (fun R => (Bchild R) ^ 2)
  have hscale_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-2 * s) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hchildSq :
      ∀ N : ℕ,
        descendantsAverage Q 1
          (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) ≤
          descendantsAverage Q 1 (fun R => (Bchild R) ^ 2) := by
    intro N
    refine descendantsAverage_le_descendantsAverage Q 1 ?_
    intro R hR
    have hchildR := hchild R hR N
    have hpartialR_nonneg :
        0 ≤ cubeBesovNegativeVectorPartialSeminormTwo R s N u :=
      cubeBesovNegativeVectorPartialSeminormTwo_nonneg R s N u
    have hBR_nonneg : 0 ≤ Bchild R := by
      have hchildR0 := hchild R hR 0
      have hpartialR0_nonneg :
          0 ≤ cubeBesovNegativeVectorPartialSeminormTwo R s 0 u :=
        cubeBesovNegativeVectorPartialSeminormTwo_nonneg R s 0 u
      linarith
    have habs :
        |cubeBesovNegativeVectorPartialSeminormTwo R s N u| ≤ |Bchild R| := by
      simpa [abs_of_nonneg hpartialR_nonneg, abs_of_nonneg hBR_nonneg] using hchildR
    exact sq_le_sq.mpr habs
  have hpartial :
      ∀ N : ℕ,
        (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤ Echild + F := by
    intro N
    cases N with
    | zero =>
        have hmono :
            cubeBesovNegativeVectorPartialSeminormTwo Q s 0 u ≤
              cubeBesovNegativeVectorPartialSeminormTwo Q s 1 u :=
          cubeBesovNegativeVectorPartialSeminormTwo_le_succ Q s u 0
        have hmono_sq :
            (cubeBesovNegativeVectorPartialSeminormTwo Q s 0 u) ^ 2 ≤
              (cubeBesovNegativeVectorPartialSeminormTwo Q s 1 u) ^ 2 := by
          have h0_nonneg :
              0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s 0 u :=
            cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s 0 u
          have h1_nonneg :
              0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s 1 u :=
            cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s 1 u
          nlinarith
        have hscaled0 :
            Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage Q 1
                  (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s 0 u) ^ 2) ≤
              Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage Q 1 (fun R => (Bchild R) ^ 2) :=
          mul_le_mul_of_nonneg_left (hchildSq 0) hscale_nonneg
        have hsucc := hlocal 0
        have hsucc' :
            (cubeBesovNegativeVectorPartialSeminormTwo Q s 1 u) ^ 2 ≤ Echild + F := by
          calc
            (cubeBesovNegativeVectorPartialSeminormTwo Q s 1 u) ^ 2
                ≤
              Real.rpow (3 : ℝ) (-2 * s) *
                  descendantsAverage Q 1
                    (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s 0 u) ^ 2) +
                F := by
                  simpa using hsucc
            _ ≤
              Real.rpow (3 : ℝ) (-2 * s) *
                  descendantsAverage Q 1 (fun R => (Bchild R) ^ 2) +
                F := by
                  exact add_le_add hscaled0 le_rfl
            _ = Echild + F := by
                  rfl
        exact hmono_sq.trans hsucc'
    | succ N =>
        have hscaledN :
            Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage Q 1
                  (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) ≤
              Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage Q 1 (fun R => (Bchild R) ^ 2) :=
          mul_le_mul_of_nonneg_left (hchildSq N) hscale_nonneg
        have hsucc := hlocal N
        calc
          (cubeBesovNegativeVectorPartialSeminormTwo Q s (N + 1) u) ^ 2
              ≤
            Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage Q 1
                  (fun R => (cubeBesovNegativeVectorPartialSeminormTwo R s N u) ^ 2) +
              F := hsucc
          _ ≤
            Real.rpow (3 : ℝ) (-2 * s) *
                descendantsAverage Q 1 (fun R => (Bchild R) ^ 2) +
              F := by
                exact add_le_add hscaledN le_rfl
          _ = Echild + F := by
                rfl
  simpa [Echild] using
    sq_cubeBesovNegativeVectorSeminormTwo_le_of_partialSqBound
      (Q := Q) (s := s) (u := u) hB_nonneg hpartial

theorem real_forward_recurrence_iterate_le
    (R E : ℕ → ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hstep : ∀ m : ℕ, R m ≤ γ * R (m + 1) + E m)
    (m N : ℕ) :
    R m ≤ γ ^ N * R (m + N) +
      (∑ k ∈ Finset.range N, γ ^ k * E (m + k)) := by
  induction N generalizing m with
  | zero =>
      simp
  | succ N ih =>
      have htail := ih (m + 1)
      have hmul :
          γ * R (m + 1) ≤
            γ *
              (γ ^ N * R ((m + 1) + N) +
                ∑ k ∈ Finset.range N, γ ^ k * E ((m + 1) + k)) := by
        exact mul_le_mul_of_nonneg_left htail hγ
      have hsum_shift :
          γ * (∑ k ∈ Finset.range N, γ ^ k * E ((m + 1) + k)) =
            ∑ k ∈ Finset.range N, γ ^ (k + 1) * E (m + (k + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        ring_nf
      calc
        R m ≤ γ * R (m + 1) + E m := hstep m
        _ ≤
            γ *
                (γ ^ N * R ((m + 1) + N) +
                  ∑ k ∈ Finset.range N, γ ^ k * E ((m + 1) + k)) +
              E m := by
                exact add_le_add hmul le_rfl
        _ =
            γ ^ (N + 1) * R (m + (N + 1)) +
              ∑ k ∈ Finset.range (N + 1), γ ^ k * E (m + k) := by
                rw [mul_add, hsum_shift, Finset.sum_range_succ']
                simp [pow_succ, Nat.add_assoc]
                ring_nf

end

end Homogenization
