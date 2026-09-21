/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PositiveNorm
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionVector

/-! # Standard Projection Residual -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Overlap bounds for standard projection residuals

This file isolates the residual half of the hard comparison from the corrected
overlapping positive norm back to the ordinary triadic positive norm.  After
subtracting the depth-`j` standard projection, the existing finite-overlap
residual estimate controls the overlapping depth-`j` oscillation by the
ordinary depth-`j` positive average.
-/

/-- The overlapping depth average of the depth-`j` standard projection residual
is controlled by the ordinary positive depth average at the same scale. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_sub_cubeProjectionVec_le
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hres :
      MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hresLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (fun x => u x - cubeProjectionVec Q j u x) j ≤
      4 * (3 ^ d : ℝ) * cubeBesovPositiveVectorDepthAverage Q u j := by
  have hbase :=
    cubeBesovOverlappingPositiveVectorDepthAverage_residual_le
      Q (fun x => u x - cubeProjectionVec Q j u x) j hres hresLoc
  calc
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (fun x => u x - cubeProjectionVec Q j u x) j
        ≤
          4 * (3 ^ d : ℝ) *
            (cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x => u x - cubeProjectionVec Q j u x)) ^ 2 := hbase
    _ = 4 * (3 ^ d : ℝ) * cubeBesovPositiveVectorDepthAverage Q u j := by
          rw [cubeLpNorm_sub_cubeProjectionVec_sq_eq_cubeBesovPositiveVectorDepthAverage
            Q u j hres]

/-- The depth-zero standard projection is constant on every admissible overlap
cube, so its overlap average is the parent average. -/
theorem overlapCubeAverageVec_cubeProjectionVec_zero_of_mem_overlapCentersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ} (u : Vec d → Vec d)
    (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeAverageVec S (cubeProjectionVec Q 0 u) = cubeAverageVec Q u := by
  calc
    overlapCubeAverageVec S (cubeProjectionVec Q 0 u)
        = overlapCubeAverageVec S (fun _ : Vec d => cubeAverageVec Q u) := by
          exact overlapCubeAverageVec_congr_on_overlapCubeSet
            (S := S)
            (u := cubeProjectionVec Q 0 u)
            (v := fun _ : Vec d => cubeAverageVec Q u)
            (fun x hx =>
              cubeProjectionVec_zero_eq_cubeAverageVec_of_mem_cubeSet
                Q u (overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hS hx))
    _ = cubeAverageVec Q u := by
          simp

/-- The depth-zero standard projection has zero overlap fluctuation on every
admissible overlap cube. -/
theorem overlapCubeLpNorm_overlapCubeFluctuationVec_cubeProjectionVec_zero_eq_zero
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ} (u : Vec d → Vec d)
    (hS : S ∈ overlapCentersAtDepth Q j) :
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S (cubeProjectionVec Q 0 u)) = 0 := by
  have havg :
      overlapCubeAverageVec S (cubeProjectionVec Q 0 u) = cubeAverageVec Q u :=
    overlapCubeAverageVec_cubeProjectionVec_zero_of_mem_overlapCentersAtDepth
      (Q := Q) (S := S) (j := j) u hS
  calc
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S (cubeProjectionVec Q 0 u))
        = overlapCubeLpNorm S (2 : ℝ≥0∞) (0 : Vec d → Vec d) := by
          exact overlapCubeLpNorm_congr_on_overlapCubeSet_generic S (2 : ℝ≥0∞)
            (fun x hx => by
              have hpoint :
                  cubeProjectionVec Q 0 u x = cubeAverageVec Q u :=
                cubeProjectionVec_zero_eq_cubeAverageVec_of_mem_cubeSet
                  Q u (overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hS hx)
              simp [overlapCubeFluctuationVec, havg, hpoint])
    _ = 0 := by
          simpa using!
            (overlapCubeLpNorm_const (S := S) (p := (2 : ℝ≥0∞))
              (c := (0 : Vec d)) (by norm_num))

/-- The depth-zero standard projection contributes no corrected overlapping
positive depth average. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeProjectionVec_zero_eq_zero
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q (cubeProjectionVec Q 0 u) j = 0 := by
  unfold cubeBesovOverlappingPositiveVectorDepthAverage overlapCentersAverage
  let D := overlapCentersAtDepth Q j
  have hsum :
      D.sum
          (fun S =>
            (overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S (cubeProjectionVec Q 0 u))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro S hS
    have hzero :=
      overlapCubeLpNorm_overlapCubeFluctuationVec_cubeProjectionVec_zero_eq_zero
        (Q := Q) (S := S) (j := j) u (by simpa [D] using hS)
    simp [hzero]
  simp [D, hsum]

/-- Seminorm form of
`cubeBesovOverlappingPositiveVectorDepthAverage_cubeProjectionVec_zero_eq_zero`. -/
theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_cubeProjectionVec_zero_eq_zero
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s (cubeProjectionVec Q 0 u) j = 0 := by
  unfold cubeBesovOverlappingPositiveVectorDepthSeminorm
  rw [cubeBesovOverlappingPositiveVectorDepthAverage_cubeProjectionVec_zero_eq_zero]
  simp

/-- If an overlap cube is contained in one standard descendant at the scale of
a martingale increment, then that increment has zero overlap fluctuation on
the overlap cube. -/
theorem overlapCubeLpNorm_overlapCubeFluctuationVec_cubeIncrementVec_eq_zero_of_subset_descendant
    {d : ℕ} {Q S R : TriadicCube d} {m : ℕ} (u : Vec d → Vec d)
    (hR : R ∈ descendantsAtDepth Q (m + 1))
    (hsub : overlapCubeSet S ⊆ cubeSet R) :
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u)) = 0 := by
  rcases exists_const_cubeIncrementVec_on_mem_descendantsAtDepth_succ
    (Q := Q) (R := R) (m := m) u hR with ⟨c, hc⟩
  have havg :
      overlapCubeAverageVec S (cubeIncrementVec Q (m + 1) u) = c := by
    calc
      overlapCubeAverageVec S (cubeIncrementVec Q (m + 1) u)
          = overlapCubeAverageVec S (fun _ : Vec d => c) := by
            exact overlapCubeAverageVec_congr_on_overlapCubeSet
              (S := S)
              (u := cubeIncrementVec Q (m + 1) u)
              (v := fun _ : Vec d => c)
              (fun x hx => hc x (hsub hx))
      _ = c := by
            simp
  calc
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))
        = overlapCubeLpNorm S (2 : ℝ≥0∞) (0 : Vec d → Vec d) := by
          exact overlapCubeLpNorm_congr_on_overlapCubeSet_generic S (2 : ℝ≥0∞)
            (fun x hx => by
              have hpoint : cubeIncrementVec Q (m + 1) u x = c :=
                hc x (hsub hx)
              simp [overlapCubeFluctuationVec, havg, hpoint])
    _ = 0 := by
          simpa using!
            (overlapCubeLpNorm_const (S := S) (p := (2 : ℝ≥0∞))
              (c := (0 : Vec d)) (by norm_num))

/-- Corrected overlapping depth averages only depend on the tested function on
the overlap cubes used at that depth. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_congr_on_overlapCenters
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) {u v : Vec d → Vec d}
    (h :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ x ∈ overlapCubeSet S, u x = v x) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q u j =
      cubeBesovOverlappingPositiveVectorDepthAverage Q v j := by
  unfold cubeBesovOverlappingPositiveVectorDepthAverage overlapCentersAverage
  refine congrArg (fun t : ℝ => ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro S hS
  have havg :
      overlapCubeAverageVec S u = overlapCubeAverageVec S v :=
    overlapCubeAverageVec_congr_on_overlapCubeSet
      (S := S) (u := u) (v := v) (h S hS)
  congr 1
  exact overlapCubeLpNorm_congr_on_overlapCubeSet_generic S (2 : ℝ≥0∞)
    (fun x hx => by
      rw [overlapCubeFluctuationVec, overlapCubeFluctuationVec, h S hS x hx, havg])

/-- Triangle inequality for the overlap fluctuation of a finite sum. -/
theorem overlapCubeLpNorm_overlapCubeFluctuationVec_finset_sum_le
    {d : ℕ} {ι : Type*} (S : TriadicCube d) (I : Finset ι)
    (u : ι → Vec d → Vec d)
    (hu :
      ∀ i ∈ I,
        MeasureTheory.MemLp (u i) (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x)) ≤
      ∑ i ∈ I,
        overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S (u i)) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      have hzero :
          overlapCubeLpNorm S (2 : ℝ≥0∞) (0 : Vec d → Vec d) = 0 := by
        simpa using!
          (overlapCubeLpNorm_const (S := S) (p := (2 : ℝ≥0∞))
            (c := (0 : Vec d)) (by norm_num))
      have hfun :
          (fun x => ∑ i ∈ (∅ : Finset ι), u i x) = (0 : Vec d → Vec d) := by
        funext x
        simp
      rw [hfun, overlapCubeFluctuationVec_zero]
      exact le_of_eq hzero
  | @insert a I ha ih =>
      have hua :
          MeasureTheory.MemLp (u a) (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
        hu a (by simp [ha])
      have huI :
          ∀ i ∈ I,
            MeasureTheory.MemLp (u i) (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) := by
        intro i hi
        exact hu i (Finset.mem_insert_of_mem hi)
      have hsum :
          MeasureTheory.MemLp (fun x => ∑ i ∈ I, u i x)
            (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) := by
        exact MeasureTheory.memLp_finsetSum
          (μ := normalizedOverlapCubeMeasure S) (p := (2 : ℝ≥0∞))
          (s := I) (f := fun i => u i) huI
      have hfluct :
          overlapCubeFluctuationVec S
              (fun x => ∑ i ∈ insert a I, u i x) =
            fun x =>
              overlapCubeFluctuationVec S (u a) x +
                overlapCubeFluctuationVec S (fun y => ∑ i ∈ I, u i y) x := by
        have hsum_fun :
            (fun x => ∑ i ∈ insert a I, u i x) =
              fun x => u a x + (∑ i ∈ I, u i x) := by
          funext x
          simp [Finset.sum_insert, ha]
        rw [hsum_fun]
        exact overlapCubeFluctuationVec_add_of_memLp_two S hua hsum
      have hfa :
          MeasureTheory.MemLp (overlapCubeFluctuationVec S (u a))
            (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
        memLp_overlapCubeFluctuationVec S (u a) hua
      have hfI :
          MeasureTheory.MemLp
            (overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x))
            (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S) :=
        memLp_overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x) hsum
      have htri :
          overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S
                (fun x => ∑ i ∈ insert a I, u i x)) ≤
            overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S (u a)) +
              overlapCubeLpNorm S (2 : ℝ≥0∞)
                (overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x)) := by
        rw [hfluct]
        exact overlapCubeLpNorm_add_le S (2 : ℝ≥0∞)
          (overlapCubeFluctuationVec S (u a))
          (overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x))
          hfa hfI (by norm_num)
      calc
        overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S (fun x => ∑ i ∈ insert a I, u i x))
            ≤
              overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S (u a)) +
                overlapCubeLpNorm S (2 : ℝ≥0∞)
                  (overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x)) := htri
        _ ≤
              overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S (u a)) +
                ∑ i ∈ I,
                  overlapCubeLpNorm S (2 : ℝ≥0∞)
                    (overlapCubeFluctuationVec S (u i)) := by
              exact add_le_add_right (ih huI) _
        _ =
              ∑ i ∈ insert a I,
                overlapCubeLpNorm S (2 : ℝ≥0∞)
                  (overlapCubeFluctuationVec S (u i)) := by
              simp [Finset.sum_insert, ha]

/-- Minkowski inequality for corrected overlapping depth averages of finite
sums, in square-root form. -/
theorem sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_finset_sum_le
    {d : ℕ} {ι : Type*} (Q : TriadicCube d) (j : ℕ) (I : Finset ι)
    (u : ι → Vec d → Vec d)
    (hu :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ i ∈ I,
        MeasureTheory.MemLp (u i) (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    Real.sqrt
        (cubeBesovOverlappingPositiveVectorDepthAverage Q
          (fun x => ∑ i ∈ I, u i x) j) ≤
      ∑ i ∈ I,
        Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q (u i) j) := by
  classical
  let A : TriadicCube d → ι → ℝ :=
    fun S i =>
      overlapCubeLpNorm S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S (u i))
  have hA_nonneg :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ i ∈ I, 0 ≤ A S i := by
    intro S hS i hi
    exact overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞) (overlapCubeFluctuationVec S (u i))
  have hpoint :
      ∀ S ∈ overlapCentersAtDepth Q j,
        (overlapCubeLpNorm S (2 : ℝ≥0∞)
          (overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x))) ^ 2 ≤
          (∑ i ∈ I, A S i) ^ 2 := by
    intro S hS
    have hnorm :=
      overlapCubeLpNorm_overlapCubeFluctuationVec_finset_sum_le
        S I u (hu S hS)
    have hleft_nonneg :
        0 ≤ overlapCubeLpNorm S (2 : ℝ≥0∞)
          (overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x)) :=
      overlapCubeLpNorm_nonneg S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S (fun x => ∑ i ∈ I, u i x))
    have hright_nonneg : 0 ≤ ∑ i ∈ I, A S i :=
      Finset.sum_nonneg fun i hi => hA_nonneg S hS i hi
    exact (sq_le_sq₀ hleft_nonneg hright_nonneg).mpr hnorm
  have havg_le :
      cubeBesovOverlappingPositiveVectorDepthAverage Q
          (fun x => ∑ i ∈ I, u i x) j ≤
        overlapCentersAverage Q j (fun S => (∑ i ∈ I, A S i) ^ 2) := by
    unfold cubeBesovOverlappingPositiveVectorDepthAverage
    exact overlapCentersAverage_le_overlapCentersAverage Q j hpoint
  have hroot_le :
      (cubeBesovOverlappingPositiveVectorDepthAverage Q
          (fun x => ∑ i ∈ I, u i x) j) ^ (1 / 2 : ℝ) ≤
        (overlapCentersAverage Q j (fun S => (∑ i ∈ I, A S i) ^ 2)) ^
          (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow
      (cubeBesovOverlappingPositiveVectorDepthAverage_nonneg Q
        (fun x => ∑ i ∈ I, u i x) j)
      havg_le (by norm_num)
  have hL2 :=
    overlapCentersAverage_L2_sum_le_sum_overlapCentersAverage_L2
      Q j I A hA_nonneg
  calc
    Real.sqrt
        (cubeBesovOverlappingPositiveVectorDepthAverage Q
          (fun x => ∑ i ∈ I, u i x) j)
        =
          (cubeBesovOverlappingPositiveVectorDepthAverage Q
            (fun x => ∑ i ∈ I, u i x) j) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
    _ ≤
          (overlapCentersAverage Q j (fun S => (∑ i ∈ I, A S i) ^ 2)) ^
            (1 / 2 : ℝ) := hroot_le
    _ ≤
          ∑ i ∈ I,
            (overlapCentersAverage Q j (fun S => (A S i) ^ 2)) ^ (1 / 2 : ℝ) := hL2
    _ =
          ∑ i ∈ I,
            Real.sqrt (cubeBesovOverlappingPositiveVectorDepthAverage Q (u i) j) := by
          simp [cubeBesovOverlappingPositiveVectorDepthAverage, A, Real.sqrt_eq_rpow]

/-- The projection part of the hard comparison reduces to the projection gap
from depth zero.  This is the algebraic split before estimating the gap by
ordinary standard positive terms. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeProjectionVec_le_gap_zero
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hzeroLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hgapLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q (cubeProjectionVec Q j u) j ≤
      2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeProjectionGapVec Q 0 j u) j := by
  have hcongr :
      cubeBesovOverlappingPositiveVectorDepthAverage Q (cubeProjectionVec Q j u) j =
        cubeBesovOverlappingPositiveVectorDepthAverage Q
          (fun x => cubeProjectionVec Q 0 u x + cubeProjectionGapVec Q 0 j u x) j := by
    exact cubeBesovOverlappingPositiveVectorDepthAverage_congr_on_overlapCenters
      Q j
      (fun S _hS x _hx => by
        simpa using congrFun
          (cubeProjectionVec_eq_projection_zero_add_gap_zero Q j u) x)
  rw [hcongr]
  have hadd :=
    cubeBesovOverlappingPositiveVectorDepthAverage_add_le
      Q (cubeProjectionVec Q 0 u) (cubeProjectionGapVec Q 0 j u) j hzeroLoc hgapLoc
  calc
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (fun x => cubeProjectionVec Q 0 u x + cubeProjectionGapVec Q 0 j u x) j
        ≤
          2 * cubeBesovOverlappingPositiveVectorDepthAverage Q (cubeProjectionVec Q 0 u) j +
            2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
              (cubeProjectionGapVec Q 0 j u) j := hadd
    _ =
          2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
            (cubeProjectionGapVec Q 0 j u) j := by
          rw [cubeBesovOverlappingPositiveVectorDepthAverage_cubeProjectionVec_zero_eq_zero]
          ring

/-- Split a field into its depth-`j` standard projection residual plus its
depth-`j` standard projection, at the corrected overlapping depth average. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_le_residual_add_projection
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hresLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hprojLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q u j ≤
      2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
          (fun x => u x - cubeProjectionVec Q j u x) j +
        2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
          (cubeProjectionVec Q j u) j := by
  have hcongr :
      cubeBesovOverlappingPositiveVectorDepthAverage Q u j =
        cubeBesovOverlappingPositiveVectorDepthAverage Q
          (fun x => (u x - cubeProjectionVec Q j u x) +
            cubeProjectionVec Q j u x) j := by
    exact cubeBesovOverlappingPositiveVectorDepthAverage_congr_on_overlapCenters
      Q j (fun _S _hS x _hx => by
        simp)
  rw [hcongr]
  exact cubeBesovOverlappingPositiveVectorDepthAverage_add_le
    Q (fun x => u x - cubeProjectionVec Q j u x) (cubeProjectionVec Q j u) j
    hresLoc hprojLoc

/-- Seminorm-squared form of
`cubeBesovOverlappingPositiveVectorDepthAverage_cubeProjectionVec_le_gap_zero`. -/
theorem sq_cubeBesovOverlappingPositiveVectorDepthSeminorm_cubeProjectionVec_le_gap_zero
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (hzeroLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hgapLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s (cubeProjectionVec Q j u) j) ^ 2 ≤
      2 * (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (cubeProjectionGapVec Q 0 j u) j) ^ 2 := by
  have havg :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeProjectionVec_le_gap_zero
      Q u j hzeroLoc hgapLoc
  have hweight_nonneg :
      0 ≤ (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 := sq_nonneg _
  calc
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s (cubeProjectionVec Q j u) j) ^ 2
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            cubeBesovOverlappingPositiveVectorDepthAverage Q (cubeProjectionVec Q j u) j := by
          exact sq_cubeBesovOverlappingPositiveVectorDepthSeminorm
            Q s (cubeProjectionVec Q j u) j
    _ ≤
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            (2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
              (cubeProjectionGapVec Q 0 j u) j) := by
          exact mul_le_mul_of_nonneg_left havg hweight_nonneg
    _ =
          2 * ((Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            cubeBesovOverlappingPositiveVectorDepthAverage Q
              (cubeProjectionGapVec Q 0 j u) j) := by
          ring
    _ =
          2 * (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
            (cubeProjectionGapVec Q 0 j u) j) ^ 2 := by
          rw [sq_cubeBesovOverlappingPositiveVectorDepthSeminorm]

/-- The depth-`j` projection gap from depth zero is the finite sum of vector
martingale increments, at the level of corrected overlapping depth averages. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_gap_zero_eq_sum_incrementVec
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q (cubeProjectionGapVec Q 0 j u) j =
      cubeBesovOverlappingPositiveVectorDepthAverage Q
        (fun x =>
          Finset.sum (Finset.range j)
            (fun m => cubeIncrementVec Q (m + 1) u x)) j := by
  symm
  exact cubeBesovOverlappingPositiveVectorDepthAverage_congr_on_overlapCenters
    Q j
    (fun S _hS x _hx => by
      simpa using congrFun
        (sum_cubeIncrementVec_eq_cubeProjectionGapVec
          (Q := Q) (u := u) (j := 0) (n := j)) x)

/-- Seminorm form of
`cubeBesovOverlappingPositiveVectorDepthAverage_gap_zero_eq_sum_incrementVec`. -/
theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_eq_sum_incrementVec
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s (cubeProjectionGapVec Q 0 j u) j =
      cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (fun x =>
          Finset.sum (Finset.range j)
            (fun m => cubeIncrementVec Q (m + 1) u x)) j := by
  unfold cubeBesovOverlappingPositiveVectorDepthSeminorm
  rw [cubeBesovOverlappingPositiveVectorDepthAverage_gap_zero_eq_sum_incrementVec]

/-- The projection gap is controlled, in corrected overlapping square-root
depth average, by the sum of its martingale increments. -/
theorem sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_gap_zero_le_sum_incrementVec
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ m ∈ Finset.range j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    Real.sqrt
        (cubeBesovOverlappingPositiveVectorDepthAverage Q (cubeProjectionGapVec Q 0 j u) j) ≤
      ∑ m ∈ Finset.range j,
        Real.sqrt
          (cubeBesovOverlappingPositiveVectorDepthAverage Q
            (cubeIncrementVec Q (m + 1) u) j) := by
  rw [cubeBesovOverlappingPositiveVectorDepthAverage_gap_zero_eq_sum_incrementVec]
  exact sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_finset_sum_le
    Q j (Finset.range j) (fun m => cubeIncrementVec Q (m + 1) u) hincLoc

/-- Seminorm form of
`sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_gap_zero_le_sum_incrementVec`. -/
theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_incrementVec
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ m ∈ Finset.range j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s (cubeProjectionGapVec Q 0 j u) j ≤
      ∑ m ∈ Finset.range j,
        cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
          (cubeIncrementVec Q (m + 1) u) j := by
  have hroot :=
    sqrt_cubeBesovOverlappingPositiveVectorDepthAverage_gap_zero_le_sum_incrementVec
      Q u j hincLoc
  have hweight_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  unfold cubeBesovOverlappingPositiveVectorDepthSeminorm
  calc
    Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.sqrt
          (cubeBesovOverlappingPositiveVectorDepthAverage Q (cubeProjectionGapVec Q 0 j u) j)
        ≤
          Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            (∑ m ∈ Finset.range j,
              Real.sqrt
                (cubeBesovOverlappingPositiveVectorDepthAverage Q
                  (cubeIncrementVec Q (m + 1) u) j)) := by
          exact mul_le_mul_of_nonneg_left hroot hweight_nonneg
    _ =
          ∑ m ∈ Finset.range j,
            Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              Real.sqrt
                (cubeBesovOverlappingPositiveVectorDepthAverage Q
                  (cubeIncrementVec Q (m + 1) u) j) := by
          rw [Finset.mul_sum]

/-- Seminorm-squared form of
`cubeBesovOverlappingPositiveVectorDepthAverage_sub_cubeProjectionVec_le`. -/
theorem sq_cubeBesovOverlappingPositiveVectorDepthSeminorm_sub_cubeProjectionVec_le
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (hres :
      MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hresLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (fun x => u x - cubeProjectionVec Q j u x) j) ^ 2 ≤
      4 * (3 ^ d : ℝ) * (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
  have havg :=
    cubeBesovOverlappingPositiveVectorDepthAverage_sub_cubeProjectionVec_le
      Q u j hres hresLoc
  have hweight_nonneg :
      0 ≤ (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 := sq_nonneg _
  calc
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (fun x => u x - cubeProjectionVec Q j u x) j) ^ 2
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            cubeBesovOverlappingPositiveVectorDepthAverage Q
              (fun x => u x - cubeProjectionVec Q j u x) j := by
          exact sq_cubeBesovOverlappingPositiveVectorDepthSeminorm
            Q s (fun x => u x - cubeProjectionVec Q j u x) j
    _ ≤
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            (4 * (3 ^ d : ℝ) * cubeBesovPositiveVectorDepthAverage Q u j) := by
          exact mul_le_mul_of_nonneg_left havg hweight_nonneg
    _ =
          4 * (3 ^ d : ℝ) *
            ((Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
              cubeBesovPositiveVectorDepthAverage Q u j) := by
          ring
    _ =
          4 * (3 ^ d : ℝ) *
            (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
          rw [sq_cubeBesovPositiveVectorDepthSeminorm]

/-- Combined depth split for the hard comparison.  The residual branch is paid
by the ordinary same-depth positive term, while the projection branch is paid
by the depth-zero projection gap. -/
theorem sq_cubeBesovOverlappingPositiveVectorDepthSeminorm_le_standard_add_gap_zero
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (hres :
      MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hresLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hprojLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hzeroLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionVec Q 0 u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hgapLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeProjectionGapVec Q 0 j u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S)) :
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2 ≤
      8 * (3 ^ d : ℝ) * (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 +
        4 * (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
          (cubeProjectionGapVec Q 0 j u) j) ^ 2 := by
  have hsplit :=
    cubeBesovOverlappingPositiveVectorDepthAverage_le_residual_add_projection
      Q u j hresLoc hprojLoc
  have hresAvg :=
    cubeBesovOverlappingPositiveVectorDepthAverage_sub_cubeProjectionVec_le
      Q u j hres hresLoc
  have hprojAvg :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeProjectionVec_le_gap_zero
      Q u j hzeroLoc hgapLoc
  have havg :
      cubeBesovOverlappingPositiveVectorDepthAverage Q u j ≤
        8 * (3 ^ d : ℝ) * cubeBesovPositiveVectorDepthAverage Q u j +
          4 * cubeBesovOverlappingPositiveVectorDepthAverage Q
            (cubeProjectionGapVec Q 0 j u) j := by
    calc
      cubeBesovOverlappingPositiveVectorDepthAverage Q u j
          ≤
            2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
                (fun x => u x - cubeProjectionVec Q j u x) j +
              2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
                (cubeProjectionVec Q j u) j := hsplit
      _ ≤
            2 * (4 * (3 ^ d : ℝ) * cubeBesovPositiveVectorDepthAverage Q u j) +
              2 * (2 * cubeBesovOverlappingPositiveVectorDepthAverage Q
                (cubeProjectionGapVec Q 0 j u) j) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hresAvg (by norm_num))
              (mul_le_mul_of_nonneg_left hprojAvg (by norm_num))
      _ =
            8 * (3 ^ d : ℝ) * cubeBesovPositiveVectorDepthAverage Q u j +
              4 * cubeBesovOverlappingPositiveVectorDepthAverage Q
                (cubeProjectionGapVec Q 0 j u) j := by
            ring
  have hweight_nonneg :
      0 ≤ (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 := sq_nonneg _
  calc
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            cubeBesovOverlappingPositiveVectorDepthAverage Q u j := by
          exact sq_cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j
    _ ≤
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            (8 * (3 ^ d : ℝ) * cubeBesovPositiveVectorDepthAverage Q u j +
              4 * cubeBesovOverlappingPositiveVectorDepthAverage Q
                (cubeProjectionGapVec Q 0 j u) j) := by
          exact mul_le_mul_of_nonneg_left havg hweight_nonneg
    _ =
          8 * (3 ^ d : ℝ) *
              ((Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
                cubeBesovPositiveVectorDepthAverage Q u j) +
            4 * ((Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
              cubeBesovOverlappingPositiveVectorDepthAverage Q
                (cubeProjectionGapVec Q 0 j u) j) := by
          ring
    _ =
          8 * (3 ^ d : ℝ) * (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 +
            4 * (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
              (cubeProjectionGapVec Q 0 j u) j) ^ 2 := by
          rw [sq_cubeBesovPositiveVectorDepthSeminorm,
            sq_cubeBesovOverlappingPositiveVectorDepthSeminorm]

end

end Homogenization
