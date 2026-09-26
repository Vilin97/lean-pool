/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionBoundary

/-! # Standard Projection Boundary Gap -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Projection gaps from boundary-budgeted increments

This file sits downstream of `StandardProjectionBoundary`: the boundary file
controls one martingale increment by an abstract ancestor budget.  Here we
insert that one-increment estimate into the already-proved telescoping estimate
for the projection gap `P_j u - P_0 u`.
-/

/-- Seminorm form of the one-increment boundary-budget estimate. -/
theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_cubeIncrementVec_le_sqrt_boundaryBudget
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) (B : TriadicCube d → ℝ)
    (hB : ∀ R ∈ descendantsAtDepth Q (m + 1), 0 ≤ B R)
    (hbound :
      ∀ R ∈ descendantsAtDepth Q (m + 1),
        ∀ S ∈ descendantBoundaryLayerAtDepth R (j - m),
          (overlapCubeLpNorm S (2 : ℝ≥0∞)
            (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2 ≤ B R) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (cubeIncrementVec Q (m + 1) u) j ≤
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.sqrt
          ((((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
            ((2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
              ∑ R ∈ descendantsAtDepth Q (m + 1), B R)) := by
  have havg :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_pow_inv_const_mul_ancestor_sum
      (Q := Q) (u := u) (j := j) (m := m) hmj B hB hbound
  have hweight_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  unfold cubeBesovOverlappingPositiveVectorDepthSeminorm
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt havg) hweight_nonneg

/-- The projection gap is controlled by the sum of square-root boundary budgets
for its martingale increments. -/
theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_sqrt_boundaryBudget
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (B : ℕ → TriadicCube d → ℝ)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ m ∈ Finset.range j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hB :
      ∀ m ∈ Finset.range j,
        ∀ R ∈ descendantsAtDepth Q (m + 1), 0 ≤ B m R)
    (hbound :
      ∀ m ∈ Finset.range j,
        ∀ R ∈ descendantsAtDepth Q (m + 1),
          ∀ S ∈ descendantBoundaryLayerAtDepth R (j - m),
            (overlapCubeLpNorm S (2 : ℝ≥0∞)
              (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2 ≤
                B m R) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (cubeProjectionGapVec Q 0 j u) j ≤
      ∑ m ∈ Finset.range j,
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt
            ((((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
              ((2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
                ∑ R ∈ descendantsAtDepth Q (m + 1), B m R)) := by
  have hgap :=
    cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_incrementVec
      Q s u j hincLoc
  calc
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (cubeProjectionGapVec Q 0 j u) j
        ≤
          ∑ m ∈ Finset.range j,
            cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
              (cubeIncrementVec Q (m + 1) u) j := hgap
    _ ≤
          ∑ m ∈ Finset.range j,
            Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              Real.sqrt
                ((((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
                  ((2 * d * (3 ^ (d - 1)) ^ (j - m) : ℝ) *
                    ∑ R ∈ descendantsAtDepth Q (m + 1), B m R)) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          exact
            cubeBesovOverlappingPositiveVectorDepthSeminorm_cubeIncrementVec_le_sqrt_boundaryBudget
              (Q := Q) (s := s) (u := u) (j := j) (m := m)
              (Nat.le_of_lt (Finset.mem_range.mp hm))
              (B m) (hB m hm) (hbound m hm)

end

end Homogenization
