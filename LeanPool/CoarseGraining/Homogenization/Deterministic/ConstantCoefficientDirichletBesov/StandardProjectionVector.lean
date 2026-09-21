/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.ProjectionCharacterization
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise

/-! # Standard Projection Vector -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Vector projection API for standard positive Besov depths

This file packages the coordinatewise version of the scalar triadic projection
and records that, on each depth-`j` descendant, the projection residual is
exactly the ordinary cube fluctuation used in the standard positive vector norm.
-/

/-- Coordinatewise triadic projection of a vector field. -/
noncomputable def cubeProjectionVec {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (u : Vec d → Vec d) : Vec d → Vec d :=
  fun x i => cubeProjection Q j (fun y => u y i) x

/-- Coordinatewise triadic martingale increment of a vector field. -/
noncomputable def cubeIncrementVec {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (u : Vec d → Vec d) : Vec d → Vec d :=
  fun x i => cubeIncrement Q j (fun y => u y i) x

/-- Coordinatewise projection gap `P_{j+n} u - P_j u`. -/
noncomputable def cubeProjectionGapVec {d : ℕ} (Q : TriadicCube d) (j n : ℕ)
    (u : Vec d → Vec d) : Vec d → Vec d :=
  fun x i => cubeProjectionGap Q j n (fun y => u y i) x

@[simp] theorem cubeProjectionVec_apply {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (u : Vec d → Vec d) (x : Vec d) (i : Fin d) :
    cubeProjectionVec Q j u x i = cubeProjection Q j (fun y => u y i) x :=
  rfl

@[simp] theorem cubeIncrementVec_apply {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (u : Vec d → Vec d) (x : Vec d) (i : Fin d) :
    cubeIncrementVec Q j u x i = cubeIncrement Q j (fun y => u y i) x :=
  rfl

@[simp] theorem cubeProjectionGapVec_apply {d : ℕ} (Q : TriadicCube d) (j n : ℕ)
    (u : Vec d → Vec d) (x : Vec d) (i : Fin d) :
    cubeProjectionGapVec Q j n u x i =
      cubeProjectionGap Q j n (fun y => u y i) x :=
  rfl

/-- On a descendant cube, the vector projection is the descendant average. -/
theorem cubeProjectionVec_eq_cubeAverageVec_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (u : Vec d → Vec d) {x : Vec d}
    (hR : R ∈ descendantsAtDepth Q j) (hxR : x ∈ cubeSet R) :
    cubeProjectionVec Q j u x = cubeAverageVec R u := by
  ext i
  exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (fun y => u y i) hR hxR

/-- Depth-zero vector projections are the parent average on the parent cube. -/
theorem cubeProjectionVec_zero_eq_cubeAverageVec_of_mem_cubeSet {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) {x : Vec d}
    (hxQ : x ∈ cubeSet Q) :
    cubeProjectionVec Q 0 u x = cubeAverageVec Q u := by
  exact cubeProjectionVec_eq_cubeAverageVec_of_mem_descendantsAtDepth
    (Q := Q) (R := Q) (j := 0) u (by simp) hxQ

/-- Vector projection gaps are pointwise projection differences. -/
theorem cubeProjectionGapVec_eq_sub_cubeProjectionVec {d : ℕ}
    (Q : TriadicCube d) (j n : ℕ) (u : Vec d → Vec d) :
    cubeProjectionGapVec Q j n u =
      fun x => cubeProjectionVec Q (j + n) u x - cubeProjectionVec Q j u x := by
  funext x
  ext i
  rfl

/-- Projection as depth-zero projection plus the gap from depth zero. -/
theorem cubeProjectionVec_eq_projection_zero_add_gap_zero {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (u : Vec d → Vec d) :
    cubeProjectionVec Q j u =
      fun x => cubeProjectionVec Q 0 u x + cubeProjectionGapVec Q 0 j u x := by
  funext x
  ext i
  simp [cubeProjectionGapVec, cubeProjectionGap]

/-- Vector projections telescope as a finite sum of coordinatewise increments. -/
theorem sum_cubeIncrementVec_eq_cubeProjectionGapVec {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j n : ℕ) :
    (fun x =>
        Finset.sum (Finset.range n)
          (fun m => cubeIncrementVec Q (j + m + 1) u x)) =
      cubeProjectionGapVec Q j n u := by
  funext x
  ext i
  simpa [cubeIncrementVec, cubeProjectionGapVec] using
    congrFun (sum_cubeIncrement_eq_cubeProjectionGap
      (Q := Q) (u := fun y => u y i) (j := j) (n := n)) x

@[simp] theorem cubeProjectionGapVec_zero {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (u : Vec d → Vec d) :
    cubeProjectionGapVec Q j 0 u = 0 := by
  funext x
  ext i
  simp [cubeProjectionGapVec, cubeProjectionGap]

/-- The depth-`j` vector projection is the parent average plus the gap from
depth zero to depth `j`, on the parent cube. -/
theorem cubeProjectionVec_eq_average_add_gap_zero_of_mem_cubeSet {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (u : Vec d → Vec d) {x : Vec d}
    (hxQ : x ∈ cubeSet Q) :
    cubeProjectionVec Q j u x =
      cubeAverageVec Q u + cubeProjectionGapVec Q 0 j u x := by
  ext i
  have hzero :
      cubeProjectionVec Q 0 u x i = cubeAverageVec Q u i := by
    rw [cubeProjectionVec_zero_eq_cubeAverageVec_of_mem_cubeSet Q u hxQ]
  calc
    cubeProjectionVec Q j u x i
        =
          cubeAverageVec Q u i +
            (cubeProjectionVec Q j u x i - cubeProjectionVec Q 0 u x i) := by
          rw [hzero]
          ring
    _ =
          (cubeAverageVec Q u + cubeProjectionGapVec Q 0 j u x) i := by
          simp [cubeProjectionGapVec, cubeProjectionGap]

/-- On a child of a depth-`m` descendant, the vector martingale increment is
the child average minus the parent average. -/
theorem cubeIncrementVec_eq_sub_cubeAverageVec_of_mem_childCubes
    {d : ℕ} {Q T R : TriadicCube d} {m : ℕ} (u : Vec d → Vec d)
    (hT : T ∈ descendantsAtDepth Q m) (hRT : R ∈ childCubes T) {x : Vec d}
    (hxR : x ∈ cubeSet R) :
    cubeIncrementVec Q (m + 1) u x = cubeAverageVec R u - cubeAverageVec T u := by
  have hR : R ∈ descendantsAtDepth Q (m + 1) := by
    rw [descendantsAtDepth_succ]
    exact Finset.mem_biUnion.mpr ⟨T, hT, hRT⟩
  have hxT : x ∈ cubeSet T := cubeSet_subset_of_mem_childCubes hRT hxR
  ext i
  have hnext :
      cubeProjection Q (m + 1) (fun y => u y i) x =
        cubeAverage R (fun y => u y i) :=
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := m + 1) (fun y => u y i) hR hxR
  have hprev :
      cubeProjection Q m (fun y => u y i) x =
        cubeAverage T (fun y => u y i) :=
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := T) (j := m) (fun y => u y i) hT hxT
  simp [cubeIncrementVec, cubeIncrement, hnext, hprev, cubeAverageVec]

/-- A vector martingale increment is constant on every standard descendant at
its own scale. -/
theorem exists_const_cubeIncrementVec_on_mem_descendantsAtDepth_succ {d : ℕ}
    {Q R : TriadicCube d} {m : ℕ} (u : Vec d → Vec d)
    (hR : R ∈ descendantsAtDepth Q (m + 1)) :
    ∃ c : Vec d, ∀ x ∈ cubeSet R, cubeIncrementVec Q (m + 1) u x = c := by
  rcases mem_descendantsAtDepth_succ_iff.mp hR with ⟨T, hT, hRT⟩
  refine ⟨cubeAverageVec R u - cubeAverageVec T u, ?_⟩
  intro x hxR
  have hxT : x ∈ cubeSet T := cubeSet_subset_of_mem_childCubes hRT hxR
  ext i
  have hnext :
      cubeProjection Q (m + 1) (fun y => u y i) x =
        cubeAverage R (fun y => u y i) :=
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := m + 1) (fun y => u y i) hR hxR
  have hprev :
      cubeProjection Q m (fun y => u y i) x =
        cubeAverage T (fun y => u y i) :=
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := T) (j := m) (fun y => u y i) hT hxT
  simp [cubeIncrementVec, cubeIncrement, hnext, hprev, cubeAverageVec]

/-- On a descendant cube, the vector projection residual is the ordinary
fluctuation on that cube. -/
theorem sub_cubeProjectionVec_eq_cubeFluctuationVec_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (u : Vec d → Vec d) {x : Vec d}
    (hR : R ∈ descendantsAtDepth Q j) (hxR : x ∈ cubeSet R) :
    u x - cubeProjectionVec Q j u x = cubeFluctuationVec R u x := by
  rw [cubeProjectionVec_eq_cubeAverageVec_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) u hR hxR]
  rfl

/-- The `L²` norm of the projection residual on a descendant is the ordinary
positive fluctuation norm on that descendant. -/
theorem cubeLpNorm_sub_cubeProjectionVec_eq_cubeLpNorm_cubeFluctuationVec_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (u : Vec d → Vec d)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeLpNorm R (2 : ℝ≥0∞) (fun x => u x - cubeProjectionVec Q j u x) =
      cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u) := by
  apply cubeLpNorm_congr_on_cubeSet_generic R (2 : ℝ≥0∞)
  intro x hx
  exact sub_cubeProjectionVec_eq_cubeFluctuationVec_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) u hR hx

/-- Ordinary positive vector depth averages can be read as projection-residual
averages at the same depth. -/
theorem cubeBesovPositiveVectorDepthAverage_eq_projectionVec_residual {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovPositiveVectorDepthAverage Q u j =
      descendantsAverage Q j
        (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => u x - cubeProjectionVec Q j u x)) ^ 2) := by
  unfold cubeBesovPositiveVectorDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  rw [cubeLpNorm_sub_cubeProjectionVec_eq_cubeLpNorm_cubeFluctuationVec_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) u hR]

/-- Depth seminorm form of `cubeBesovPositiveVectorDepthAverage_eq_projectionVec_residual`. -/
theorem cubeBesovPositiveVectorDepthSeminorm_eq_projectionVec_residual {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovPositiveVectorDepthSeminorm Q s u j =
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.sqrt
          (descendantsAverage Q j
            (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => u x - cubeProjectionVec Q j u x)) ^ 2)) := by
  unfold cubeBesovPositiveVectorDepthSeminorm
  rw [cubeBesovPositiveVectorDepthAverage_eq_projectionVec_residual]

/-- The descendant average of squared vector `L²` norms is the parent squared
`L²` norm. -/
theorem descendantsAverage_cubeLpNorm_two_sq_eq_cubeLpNorm_two_sq {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → Vec d) (j : ℕ)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun R => (cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2) =
      (cubeLpNorm Q (2 : ℝ≥0∞) v) ^ 2 := by
  have hnorm_int :
      MeasureTheory.IntegrableOn (fun x => ‖v x‖ ^ (2 : ℝ))
        (cubeSet Q) MeasureTheory.volume := by
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q)
      (hv.integrable_norm_rpow (by norm_num) (by norm_num))
  calc
    descendantsAverage Q j (fun R => (cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2)
        = descendantsAverage Q j (fun R => cubeAverage R (fun x => ‖v x‖ ^ (2 : ℝ))) := by
            unfold descendantsAverage
            refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            simpa using
              (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := R) (p := (2 : ℝ≥0∞))
                (f := v) (by norm_num) (by norm_num)
                (memLp_on_descendant_of_memLp_generic (Q := Q) (R := R) (j := j)
                  hR hv))
    _ = cubeAverage Q (fun x => ‖v x‖ ^ (2 : ℝ)) := by
          rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
            (Q := Q) (j := j) (f := fun x => ‖v x‖ ^ (2 : ℝ)) hnorm_int]
    _ = (cubeLpNorm Q (2 : ℝ≥0∞) v) ^ 2 := by
          simpa using
            (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := Q) (p := (2 : ℝ≥0∞))
              (f := v) (by norm_num) (by norm_num) hv).symm

/-- The parent `L²` norm of the depth-`j` projection residual is exactly the
ordinary positive depth average. -/
theorem cubeLpNorm_sub_cubeProjectionVec_sq_eq_cubeBesovPositiveVectorDepthAverage
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hres :
      MeasureTheory.MemLp (fun x => u x - cubeProjectionVec Q j u x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeProjectionVec Q j u x)) ^ 2 =
      cubeBesovPositiveVectorDepthAverage Q u j := by
  calc
    (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeProjectionVec Q j u x)) ^ 2
        =
          descendantsAverage Q j
            (fun R => (cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => u x - cubeProjectionVec Q j u x)) ^ 2) := by
          exact (descendantsAverage_cubeLpNorm_two_sq_eq_cubeLpNorm_two_sq
            Q (fun x => u x - cubeProjectionVec Q j u x) j hres).symm
    _ = cubeBesovPositiveVectorDepthAverage Q u j := by
          exact (cubeBesovPositiveVectorDepthAverage_eq_projectionVec_residual
            Q u j).symm

end

end Homogenization
