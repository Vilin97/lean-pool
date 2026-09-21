/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionBoundary
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionIncrementEnergy

/-! # Standard Projection Boundary Neighbor -/

namespace Homogenization

noncomputable section

open scoped ENNReal BigOperators

/-!
# Boundary sums with local neighbor-energy budgets

This file refines the boundary-crossing reduction so that the enlarged
boundary-layer sum is gated back to admissible overlap centers.  That lets us
insert the local-neighbor increment-energy estimate, whose hypotheses require
`overlapCubeSet S ⊆ cubeSet Q`.
-/

/-- Child-energy budget of the depth-`m` parents whose cubes meet the overlap
cube centered at `S`. -/
noncomputable def overlapIntersectingParentEnergy {d : ℕ}
    (Q S : TriadicCube d) (m : ℕ) (u : Vec d → Vec d) : ℝ :=
  ∑ T ∈ overlapIntersectingParentsAtDepth Q S m,
    ∑ R ∈ childCubes T,
      ∑ i : Fin d,
        cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2)

theorem overlapIntersectingParentEnergy_nonneg {d : ℕ}
    (Q S : TriadicCube d) (m : ℕ) (u : Vec d → Vec d) :
    0 ≤ overlapIntersectingParentEnergy Q S m u := by
  unfold overlapIntersectingParentEnergy
  exact Finset.sum_nonneg fun T _hT => parentChildEnergy_sum_nonneg T u

/-- Boundary-layer reduction with a gate back to admissible overlap centers.
The gate is important because the raw ancestor boundary layer also contains
fine descendants whose overlap cube may leave `Q`; crossing centers never do. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_admissible_boundaryLayer_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j ≤
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (incrementBoundaryLayerCentersAtDepth Q j m).sum
          (fun S =>
            if S ∈ overlapCentersAtDepth Q j then
              (overlapCubeLpNorm S (2 : ℝ≥0∞)
                (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2
            else
              0) := by
  classical
  let F : TriadicCube d → ℝ := fun S =>
    (overlapCubeLpNorm S (2 : ℝ≥0∞)
      (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2
  let G : TriadicCube d → ℝ := fun S =>
    if S ∈ overlapCentersAtDepth Q j then F S else 0
  have hcross_eq :
      (overlapCrossingCentersAtDepth Q j m).sum F =
        (overlapCrossingCentersAtDepth Q j m).sum G := by
    refine Finset.sum_congr rfl ?_
    intro S hS
    have hcenter : S ∈ overlapCentersAtDepth Q j :=
      mem_overlapCentersAtDepth_of_mem_overlapCrossingCentersAtDepth hS
    simp [G, hcenter]
  have hsum :
      (overlapCrossingCentersAtDepth Q j m).sum G ≤
        (incrementBoundaryLayerCentersAtDepth Q j m).sum G := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (overlapCrossingCentersAtDepth_subset_incrementBoundaryLayerCentersAtDepth
        Q hmj) ?_
    intro S _hS _hSnot
    by_cases hcenter : S ∈ overlapCentersAtDepth Q j
    · simp [hcenter, F, sq_nonneg]
    · simp [hcenter]
  rw [cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_eq_crossing_sum]
  calc
    ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (overlapCrossingCentersAtDepth Q j m).sum F
        =
          ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
            (overlapCrossingCentersAtDepth Q j m).sum G := by
          rw [hcross_eq]
    _ ≤
          ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
            (incrementBoundaryLayerCentersAtDepth Q j m).sum G := by
          exact mul_le_mul_of_nonneg_left hsum
            (inv_nonneg.mpr
              (by positivity : 0 ≤ ((overlapCentersAtDepth Q j).card : ℝ)))
    _ =
          ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
            (incrementBoundaryLayerCentersAtDepth Q j m).sum
              (fun S =>
                if S ∈ overlapCentersAtDepth Q j then
                  (overlapCubeLpNorm S (2 : ℝ≥0∞)
                    (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2
                else
                  0) := rfl

/-- Insert the local-neighbor increment-energy estimate into the admissible
boundary-layer reduction.  The remaining task after this theorem is purely
geometric summation: control the admissible boundary-layer neighbor-energy
sum by the ordinary standard positive depth budgets. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_boundary_neighborEnergy_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huChild :
      ∀ T ∈ descendantsAtDepth Q m, ∀ R ∈ childCubes T,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j ≤
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (incrementBoundaryLayerCentersAtDepth Q j m).sum
          (fun S =>
            if S ∈ overlapCentersAtDepth Q j then
              4 * overlapIntersectingParentEnergy Q S m u
            else
              0) := by
  classical
  have hbase :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_admissible_boundaryLayer_sum
      (Q := Q) (u := u) hmj
  let F : TriadicCube d → ℝ := fun S =>
    if S ∈ overlapCentersAtDepth Q j then
      (overlapCubeLpNorm S (2 : ℝ≥0∞)
        (overlapCubeFluctuationVec S (cubeIncrementVec Q (m + 1) u))) ^ 2
    else
      0
  let G : TriadicCube d → ℝ := fun S =>
    if S ∈ overlapCentersAtDepth Q j then
      4 * overlapIntersectingParentEnergy Q S m u
    else
      0
  have hsum :
      (incrementBoundaryLayerCentersAtDepth Q j m).sum F ≤
        (incrementBoundaryLayerCentersAtDepth Q j m).sum G := by
    refine Finset.sum_le_sum ?_
    intro S hS
    by_cases hcenter : S ∈ overlapCentersAtDepth Q j
    · have hlocal :=
        sq_overlapCubeLpNorm_overlapCubeFluctuationVec_cubeIncrementVec_le_four_mul_overlapIntersectingParentEnergy_sum
          (Q := Q) (S := S) (m := m) u
          (overlapCubeSet_subset_cubeSet_of_mem_overlapCentersAtDepth hcenter)
          (hincLoc S hcenter) huChild
      simpa [F, G, hcenter, overlapIntersectingParentEnergy] using hlocal
    · simp [hcenter]
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr
        (by positivity : 0 ≤ ((overlapCentersAtDepth Q j).card : ℝ))))

/-- Admissible boundary-neighbor centers which charge a fixed depth-`m`
parent. -/
noncomputable def boundaryNeighborCentersForParent {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    Finset (TriadicCube d) := by
  classical
  exact (incrementBoundaryLayerCentersAtDepth Q j m).filter fun S =>
    S ∈ overlapCentersAtDepth Q j ∧
      T ∈ overlapIntersectingParentsAtDepth Q S m

theorem mem_boundaryNeighborCentersForParent_iff {d : ℕ}
    {Q S T : TriadicCube d} {j m : ℕ} :
    S ∈ boundaryNeighborCentersForParent Q j m T ↔
      S ∈ incrementBoundaryLayerCentersAtDepth Q j m ∧
        S ∈ overlapCentersAtDepth Q j ∧
          T ∈ overlapIntersectingParentsAtDepth Q S m := by
  classical
  simp [boundaryNeighborCentersForParent]

theorem boundaryNeighborCentersForParent_subset_incrementBoundaryLayerCentersAtDepth
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    boundaryNeighborCentersForParent Q j m T ⊆
      incrementBoundaryLayerCentersAtDepth Q j m := by
  intro S hS
  exact (mem_boundaryNeighborCentersForParent_iff.mp hS).1

/-- Safe global fallback for the parent-hit count.  This is not the sharp
surface-count estimate needed at the end, but it proves that every parent-hit
family is a subfamily of the global increment boundary layer. -/
theorem boundaryNeighborCentersForParent_card_le_globalBoundaryLayer_card
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    (boundaryNeighborCentersForParent Q j m T).card ≤
      (incrementBoundaryLayerCentersAtDepth Q j m).card :=
  Finset.card_le_card
    (boundaryNeighborCentersForParent_subset_incrementBoundaryLayerCentersAtDepth
      Q j m T)

theorem boundaryNeighborCentersForParent_card_le_globalBoundaryLayer_pow
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    (boundaryNeighborCentersForParent Q j m T).card ≤
      (3 ^ d) ^ (m + 1) *
        (2 * d * (3 ^ (d - 1)) ^ (j - m)) := by
  exact (boundaryNeighborCentersForParent_card_le_globalBoundaryLayer_card Q j m T).trans
    (incrementBoundaryLayerCentersAtDepth_card_le_pow Q j m)

theorem boundaryNeighborCentersForParent_card_cast_le_globalBoundaryLayer_pow
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    ((boundaryNeighborCentersForParent Q j m T).card : ℝ) ≤
      ((3 ^ d) ^ (m + 1) *
        (2 * d * (3 ^ (d - 1)) ^ (j - m)) : ℕ) := by
  exact_mod_cast boundaryNeighborCentersForParent_card_le_globalBoundaryLayer_pow
    Q j m T

/-- Boundary-layer centers generated by the children of one depth-`m` parent.
This is the scale-sharp part of the hit count; the separate remaining geometry
is to control centers generated by neighboring depth-`m` parents. -/
noncomputable def childBoundaryLayerCentersAtDepth {d : ℕ}
    (T : TriadicCube d) (n : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (childCubes T).biUnion fun R => descendantBoundaryLayerAtDepth R n

theorem childBoundaryLayerCentersAtDepth_card_le {d : ℕ}
    (T : TriadicCube d) (n : ℕ) :
    (childBoundaryLayerCentersAtDepth T n).card ≤
      (3 ^ d) * (2 * d * (3 ^ (d - 1)) ^ n) := by
  classical
  calc
    (childBoundaryLayerCentersAtDepth T n).card
        ≤ ∑ R ∈ childCubes T, (descendantBoundaryLayerAtDepth R n).card := by
          dsimp [childBoundaryLayerCentersAtDepth]
          exact Finset.card_biUnion_le
    _ ≤ ∑ _R ∈ childCubes T, 2 * d * (3 ^ (d - 1)) ^ n := by
          refine Finset.sum_le_sum ?_
          intro R _hR
          exact descendantBoundaryLayerAtDepth_card_le R n
    _ = (3 ^ d) * (2 * d * (3 ^ (d - 1)) ^ n) := by
          simp [childCubes_card]

theorem childBoundaryLayerCentersAtDepth_card_cast_le {d : ℕ}
    (T : TriadicCube d) (n : ℕ) :
    ((childBoundaryLayerCentersAtDepth T n).card : ℝ) ≤
      (3 ^ d : ℝ) * (2 * d * (3 ^ (d - 1)) ^ n : ℕ) := by
  exact_mod_cast childBoundaryLayerCentersAtDepth_card_le T n

/-- The own-child part of the parent hit family. -/
noncomputable def ownChildBoundaryNeighborCentersForParent {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    Finset (TriadicCube d) := by
  classical
  exact (boundaryNeighborCentersForParent Q j m T).filter fun S =>
    S ∈ childBoundaryLayerCentersAtDepth T (j - m)

theorem ownChildBoundaryNeighborCentersForParent_subset_childBoundaryLayerCentersAtDepth
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    ownChildBoundaryNeighborCentersForParent Q j m T ⊆
      childBoundaryLayerCentersAtDepth T (j - m) := by
  intro S hS
  exact (Finset.mem_filter.mp hS).2

theorem ownChildBoundaryNeighborCentersForParent_card_le {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    (ownChildBoundaryNeighborCentersForParent Q j m T).card ≤
      (3 ^ d) * (2 * d * (3 ^ (d - 1)) ^ (j - m)) :=
  (Finset.card_le_card
    (ownChildBoundaryNeighborCentersForParent_subset_childBoundaryLayerCentersAtDepth
      Q j m T)).trans
    (childBoundaryLayerCentersAtDepth_card_le T (j - m))

/-- Depth-`m` parents whose children generate at least one admissible
boundary-neighbor center for the fixed charged parent `T`. -/
noncomputable def boundaryGeneratingParentsForParent {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth Q m).filter fun P =>
    ∃ S ∈ boundaryNeighborCentersForParent Q j m T,
      S ∈ childBoundaryLayerCentersAtDepth P (j - m)

theorem mem_boundaryGeneratingParentsForParent_iff {d : ℕ}
    {Q P T : TriadicCube d} {j m : ℕ} :
    P ∈ boundaryGeneratingParentsForParent Q j m T ↔
      P ∈ descendantsAtDepth Q m ∧
        ∃ S ∈ boundaryNeighborCentersForParent Q j m T,
          S ∈ childBoundaryLayerCentersAtDepth P (j - m) := by
  classical
  simp [boundaryGeneratingParentsForParent]

theorem boundaryNeighborCentersForParent_subset_generatingParents_childBoundary
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    boundaryNeighborCentersForParent Q j m T ⊆
      (boundaryGeneratingParentsForParent Q j m T).biUnion
        (fun P => childBoundaryLayerCentersAtDepth P (j - m)) := by
  intro S hS
  have hboundary : S ∈ incrementBoundaryLayerCentersAtDepth Q j m :=
    (mem_boundaryNeighborCentersForParent_iff.mp hS).1
  dsimp [incrementBoundaryLayerCentersAtDepth] at hboundary
  rcases Finset.mem_biUnion.mp hboundary with ⟨R, hR, hSR⟩
  rcases mem_descendantsAtDepth_succ_iff.mp hR with ⟨P, hP, hRP⟩
  have hSchild : S ∈ childBoundaryLayerCentersAtDepth P (j - m) := by
    dsimp [childBoundaryLayerCentersAtDepth]
    exact Finset.mem_biUnion.mpr ⟨R, hRP, hSR⟩
  have hPgen : P ∈ boundaryGeneratingParentsForParent Q j m T :=
    mem_boundaryGeneratingParentsForParent_iff.2
      ⟨hP, ⟨S, hS, hSchild⟩⟩
  exact Finset.mem_biUnion.mpr ⟨P, hPgen, hSchild⟩

theorem boundaryNeighborCentersForParent_card_le_generatingParents_mul_surface
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    (boundaryNeighborCentersForParent Q j m T).card ≤
      (boundaryGeneratingParentsForParent Q j m T).card *
        (3 ^ d * (2 * d * (3 ^ (d - 1)) ^ (j - m))) := by
  classical
  calc
    (boundaryNeighborCentersForParent Q j m T).card
        ≤
          ((boundaryGeneratingParentsForParent Q j m T).biUnion
            (fun P => childBoundaryLayerCentersAtDepth P (j - m))).card :=
          Finset.card_le_card
            (boundaryNeighborCentersForParent_subset_generatingParents_childBoundary
              Q j m T)
    _ ≤
          ∑ P ∈ boundaryGeneratingParentsForParent Q j m T,
            (childBoundaryLayerCentersAtDepth P (j - m)).card := by
          exact Finset.card_biUnion_le
    _ ≤
          ∑ _P ∈ boundaryGeneratingParentsForParent Q j m T,
            3 ^ d * (2 * d * (3 ^ (d - 1)) ^ (j - m)) := by
          refine Finset.sum_le_sum ?_
          intro P _hP
          exact childBoundaryLayerCentersAtDepth_card_le P (j - m)
    _ =
          (boundaryGeneratingParentsForParent Q j m T).card *
            (3 ^ d * (2 * d * (3 ^ (d - 1)) ^ (j - m))) := by
          simp

theorem boundaryNeighborCentersForParent_card_le_of_generatingParents_card_le
    {d : ℕ} (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) {K : ℕ}
    (hK : (boundaryGeneratingParentsForParent Q j m T).card ≤ K) :
    (boundaryNeighborCentersForParent Q j m T).card ≤
      K * (3 ^ d * (2 * d * (3 ^ (d - 1)) ^ (j - m))) := by
  exact (boundaryNeighborCentersForParent_card_le_generatingParents_mul_surface
    Q j m T).trans
    (Nat.mul_le_mul_right _ hK)

/-- Pure finite-sum bookkeeping for the remaining geometry.  If every
depth-`m` parent is charged by at most `M` admissible boundary-neighbor centers,
then the full boundary-neighbor energy sum is controlled by `M` times the
ordinary depth-`m` parent child-energy sum. -/
theorem admissible_boundary_neighborEnergy_sum_le_count_mul_parentEnergy_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (j m : ℕ)
    {M : ℝ}
    (hM :
      ∀ T ∈ descendantsAtDepth Q m,
        ((boundaryNeighborCentersForParent Q j m T).card : ℝ) ≤ M) :
    (incrementBoundaryLayerCentersAtDepth Q j m).sum
        (fun S =>
          if S ∈ overlapCentersAtDepth Q j then
            overlapIntersectingParentEnergy Q S m u
          else
            0)
      ≤
        M *
          ∑ T ∈ descendantsAtDepth Q m,
            ∑ R ∈ childCubes T,
              ∑ i : Fin d,
                cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := by
  classical
  let D : Finset (TriadicCube d) := incrementBoundaryLayerCentersAtDepth Q j m
  let P : Finset (TriadicCube d) := descendantsAtDepth Q m
  let E : TriadicCube d → ℝ := fun T =>
    ∑ R ∈ childCubes T,
      ∑ i : Fin d,
        cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2)
  have hE_nonneg : ∀ T ∈ P, 0 ≤ E T := by
    intro T _hT
    exact parentChildEnergy_sum_nonneg T u
  have hpoint :
      ∀ S ∈ D,
        (if S ∈ overlapCentersAtDepth Q j then
            overlapIntersectingParentEnergy Q S m u
          else
            0) ≤
          ∑ T ∈ P,
            if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0 := by
    intro S hS
    by_cases hcenter : S ∈ overlapCentersAtDepth Q j
    · have hsubset :
          overlapIntersectingParentsAtDepth Q S m ⊆
            P.filter (fun T => S ∈ boundaryNeighborCentersForParent Q j m T) := by
        intro T hT
        rw [Finset.mem_filter]
        have hTdesc : T ∈ descendantsAtDepth Q m :=
          (mem_overlapIntersectingParentsAtDepth_iff.mp hT).1
        exact ⟨by simpa [P] using hTdesc,
          mem_boundaryNeighborCentersForParent_iff.2
            ⟨by simpa [D] using hS, hcenter, hT⟩⟩
      have hsum_le :
          (overlapIntersectingParentsAtDepth Q S m).sum E ≤
            (P.filter (fun T => S ∈ boundaryNeighborCentersForParent Q j m T)).sum E :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun T hT _hnot => by
            exact hE_nonneg T (Finset.mem_filter.mp hT).1)
      calc
        (if S ∈ overlapCentersAtDepth Q j then
            overlapIntersectingParentEnergy Q S m u
          else
            0)
            = (overlapIntersectingParentsAtDepth Q S m).sum E := by
              simp [hcenter, overlapIntersectingParentEnergy, E]
        _ ≤ (P.filter
              (fun T => S ∈ boundaryNeighborCentersForParent Q j m T)).sum E :=
              hsum_le
        _ =
            ∑ T ∈ P,
              if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0 := by
              rw [Finset.sum_filter]
    · simp [hcenter]
      exact Finset.sum_nonneg fun T hT => by
        by_cases hmem : S ∈ boundaryNeighborCentersForParent Q j m T
        · simp [hmem, hE_nonneg T hT]
        · simp [hmem]
  have hsum₁ :
      D.sum
          (fun S =>
            if S ∈ overlapCentersAtDepth Q j then
              overlapIntersectingParentEnergy Q S m u
            else
              0)
        ≤
          ∑ S ∈ D, ∑ T ∈ P,
            if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0 :=
    Finset.sum_le_sum hpoint
  have hswap :
      (∑ S ∈ D, ∑ T ∈ P,
          if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0)
        =
          ∑ T ∈ P, ∑ S ∈ D,
            if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0 := by
    exact Finset.sum_comm
  have hinner :
      ∀ T ∈ P,
        (∑ S ∈ D,
            if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0)
          ≤ M * E T := by
    intro T hT
    have hfilter :
        D.filter (fun S => S ∈ boundaryNeighborCentersForParent Q j m T) =
          boundaryNeighborCentersForParent Q j m T := by
      ext S
      constructor
      · intro hS
        exact (Finset.mem_filter.mp hS).2
      · intro hS
        rw [Finset.mem_filter]
        exact ⟨(mem_boundaryNeighborCentersForParent_iff.mp hS).1, hS⟩
    calc
      (∑ S ∈ D,
          if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0)
          =
            ∑ S ∈ D.filter
              (fun S => S ∈ boundaryNeighborCentersForParent Q j m T), E T := by
            rw [Finset.sum_filter]
      _ = ∑ S ∈ boundaryNeighborCentersForParent Q j m T, E T := by
            rw [hfilter]
      _ = ((boundaryNeighborCentersForParent Q j m T).card : ℝ) * E T := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * E T := by
            exact mul_le_mul_of_nonneg_right (hM T (by simpa [P] using hT))
              (hE_nonneg T hT)
  calc
    (incrementBoundaryLayerCentersAtDepth Q j m).sum
        (fun S =>
          if S ∈ overlapCentersAtDepth Q j then
            overlapIntersectingParentEnergy Q S m u
          else
            0)
        = D.sum
            (fun S =>
              if S ∈ overlapCentersAtDepth Q j then
                overlapIntersectingParentEnergy Q S m u
              else
                0) := rfl
    _ ≤
          ∑ S ∈ D, ∑ T ∈ P,
            if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0 :=
          hsum₁
    _ =
          ∑ T ∈ P, ∑ S ∈ D,
            if S ∈ boundaryNeighborCentersForParent Q j m T then E T else 0 :=
          hswap
    _ ≤ ∑ T ∈ P, M * E T := by
          exact Finset.sum_le_sum hinner
    _ = M * ∑ T ∈ P, E T := by
          rw [Finset.mul_sum]
    _ =
        M *
          ∑ T ∈ descendantsAtDepth Q m,
            ∑ R ∈ childCubes T,
              ∑ i : Fin d,
                cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2) := rfl

/-- One-increment boundary estimate after the local-neighbor budget and a
supplied parent-hit counting bound.  The remaining geometric theorem should
provide the count `M ≃ (3^(d-1))^(j-m)`. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_neighbor_count_parentEnergy_sum
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) {M : ℝ}
    (hM :
      ∀ T ∈ descendantsAtDepth Q m,
        ((boundaryNeighborCentersForParent Q j m T).card : ℝ) ≤ M)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huChild :
      ∀ T ∈ descendantsAtDepth Q m, ∀ R ∈ childCubes T,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j ≤
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (4 *
          (M *
            ∑ T ∈ descendantsAtDepth Q m,
              ∑ R ∈ childCubes T,
                ∑ i : Fin d,
                  cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2))) := by
  classical
  let H : TriadicCube d → ℝ := fun S =>
    if S ∈ overlapCentersAtDepth Q j then
      overlapIntersectingParentEnergy Q S m u
    else
      0
  let H4 : TriadicCube d → ℝ := fun S =>
    if S ∈ overlapCentersAtDepth Q j then
      4 * overlapIntersectingParentEnergy Q S m u
    else
      0
  have hboundary :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_boundary_neighborEnergy_sum
      (Q := Q) (u := u) hmj hincLoc huChild
  have hbook :=
    admissible_boundary_neighborEnergy_sum_le_count_mul_parentEnergy_sum
      (Q := Q) (u := u) j m hM
  have hsum4 :
      (incrementBoundaryLayerCentersAtDepth Q j m).sum H4 =
        4 * (incrementBoundaryLayerCentersAtDepth Q j m).sum H := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro S _hS
    by_cases hcenter : S ∈ overlapCentersAtDepth Q j
    · simp [H4, hcenter]
    · simp [H4, hcenter]
  have hsum :
      (incrementBoundaryLayerCentersAtDepth Q j m).sum H4 ≤
        4 *
          (M *
            ∑ T ∈ descendantsAtDepth Q m,
              ∑ R ∈ childCubes T,
                ∑ i : Fin d,
                  cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2)) := by
    rw [hsum4]
    exact mul_le_mul_of_nonneg_left hbook (by norm_num)
  exact hboundary.trans
    (mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr
        (by positivity : 0 ≤ ((overlapCentersAtDepth Q j).card : ℝ))))

/-- One-increment boundary estimate after the parent-hit count, expressed in
terms of the ordinary standard positive depth-`m` average. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_neighbor_count_depthAverage
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) {M : ℝ}
    (hM :
      ∀ T ∈ descendantsAtDepth Q m,
        ((boundaryNeighborCentersForParent Q j m T).card : ℝ) ≤ M)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ T ∈ descendantsAtDepth Q m,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j ≤
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ *
        (4 *
          (M *
            ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
              ((descendantsAtDepth Q m).card : ℝ) *
                cubeBesovPositiveVectorDepthAverage Q u m))) := by
  have hM_nonneg : 0 ≤ M := by
    rcases descendantsAtDepth_nonempty Q m with ⟨T, hT⟩
    exact le_trans (by positivity : 0 ≤ ((boundaryNeighborCentersForParent Q j m T).card : ℝ))
      (hM T hT)
  have huChild :
      ∀ T ∈ descendantsAtDepth Q m, ∀ R ∈ childCubes T,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro T hT R hR
    have hRdesc : R ∈ descendantsAtDepth T 1 := by
      simpa [descendantsAtDepth_one] using hR
    exact memLp_on_descendant_of_memLp_generic hRdesc (huParent T hT)
  have hparent :=
    parentChildEnergy_sum_descendants_le_const_mul_depthAverage
      Q u m huParent
  have hbase :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_neighbor_count_parentEnergy_sum
      (Q := Q) (u := u) hmj hM hincLoc huChild
  have hbudget :
      4 *
          (M *
            ∑ T ∈ descendantsAtDepth Q m,
              ∑ R ∈ childCubes T,
                ∑ i : Fin d,
                  cubeAverage R (fun y => (u y i - cubeAverageVec T u i) ^ 2))
        ≤
      4 *
        (M *
          ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
            ((descendantsAtDepth Q m).card : ℝ) *
              cubeBesovPositiveVectorDepthAverage Q u m)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hparent hM_nonneg) (by norm_num)
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hbudget
      (inv_nonneg.mpr
        (by positivity : 0 ≤ ((overlapCentersAtDepth Q j).card : ℝ))))

/-- Scale-separated normalization form of
`cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_neighbor_count_depthAverage`. -/
theorem cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_pow_inv_neighbor_count_depthAverage
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) {j m : ℕ}
    (hmj : m ≤ j) {M : ℝ}
    (hM :
      ∀ T ∈ descendantsAtDepth Q m,
        ((boundaryNeighborCentersForParent Q j m T).card : ℝ) ≤ M)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ T ∈ descendantsAtDepth Q m,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    cubeBesovOverlappingPositiveVectorDepthAverage Q
        (cubeIncrementVec Q (m + 1) u) j ≤
      (((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
        (4 *
          (M *
            ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
              ((descendantsAtDepth Q m).card : ℝ) *
                cubeBesovPositiveVectorDepthAverage Q u m))) := by
  have hbase :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_neighbor_count_depthAverage
      (Q := Q) (u := u) hmj hM hincLoc huParent
  have hM_nonneg : 0 ≤ M := by
    rcases descendantsAtDepth_nonempty Q m with ⟨T, hT⟩
    exact le_trans (by positivity : 0 ≤ ((boundaryNeighborCentersForParent Q j m T).card : ℝ))
      (hM T hT)
  have hbudget_nonneg :
      0 ≤
        4 *
          (M *
            ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
              ((descendantsAtDepth Q m).card : ℝ) *
                cubeBesovPositiveVectorDepthAverage Q u m)) := by
    have havg_nonneg : 0 ≤ cubeBesovPositiveVectorDepthAverage Q u m :=
      cubeBesovPositiveVectorDepthAverage_nonneg Q u m
    positivity
  have hcardLower :
      (((3 ^ d) ^ j : ℕ) : ℝ) ≤ ((overlapCentersAtDepth Q j).card : ℝ) := by
    exact_mod_cast pow_le_overlapCentersAtDepth_card Q j
  have hcard_pos : 0 < ((overlapCentersAtDepth Q j).card : ℝ) := by
    exact_mod_cast overlapCentersAtDepth_card_pos Q j
  have hpow_pos : 0 < (((3 ^ d) ^ j : ℕ) : ℝ) := by
    positivity
  have hinv :
      ((overlapCentersAtDepth Q j).card : ℝ)⁻¹ ≤
        (((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ :=
    (inv_le_inv₀ hcard_pos hpow_pos).2 hcardLower
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hinv hbudget_nonneg)

/-- Projection-gap seminorm estimate assembled from the one-increment
neighbor-count estimates.  This is the downstream form of the remaining
geometry: supply the hit count for every increment scale, and the projection
jump is controlled by the corresponding weighted standard positive depths. -/
theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_sqrt_neighbor_count_depthAverage
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (M : ℕ → ℝ)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ m ∈ Finset.range j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hM :
      ∀ m ∈ Finset.range j, ∀ T ∈ descendantsAtDepth Q m,
        ((boundaryNeighborCentersForParent Q j m T).card : ℝ) ≤ M m)
    (huParent :
      ∀ m ∈ Finset.range j, ∀ T ∈ descendantsAtDepth Q m,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (cubeProjectionGapVec Q 0 j u) j ≤
      ∑ m ∈ Finset.range j,
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt
            ((((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
              (4 *
                (M m *
                  ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
                    ((descendantsAtDepth Q m).card : ℝ) *
                      cubeBesovPositiveVectorDepthAverage Q u m)))) := by
  have hgap :=
    cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_incrementVec
      Q s u j hincLoc
  refine hgap.trans ?_
  refine Finset.sum_le_sum ?_
  intro m hm
  have hmj : m ≤ j := Nat.le_of_lt (Finset.mem_range.mp hm)
  have havg :=
    cubeBesovOverlappingPositiveVectorDepthAverage_cubeIncrementVec_le_pow_inv_neighbor_count_depthAverage
      (Q := Q) (u := u) (j := j) (m := m) hmj
      (hM m hm) (fun S hS => hincLoc S hS m hm) (huParent m hm)
  have hweight_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  unfold cubeBesovOverlappingPositiveVectorDepthSeminorm
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt havg) hweight_nonneg

/-- Baseline projection-gap estimate using the global boundary-layer count.
This is scale-incorrect for the final theorem, but it is a fully proved
fallback showing that the hit-count interface composes without any remaining
analytic hypotheses. -/
theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_sqrt_globalBoundaryLayer_depthAverage
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ)
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ m ∈ Finset.range j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ m ∈ Finset.range j, ∀ T ∈ descendantsAtDepth Q m,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
        (cubeProjectionGapVec Q 0 j u) j ≤
      ∑ m ∈ Finset.range j,
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt
            ((((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
              (4 *
                ((((3 ^ d) ^ (m + 1) *
                    (2 * d * (3 ^ (d - 1)) ^ (j - m)) : ℕ) : ℝ) *
                  ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
                    ((descendantsAtDepth Q m).card : ℝ) *
                      cubeBesovPositiveVectorDepthAverage Q u m)))) := by
  exact
    cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_sqrt_neighbor_count_depthAverage
      (Q := Q) (s := s) (u := u) (j := j)
      (M := fun m =>
        (((3 ^ d) ^ (m + 1) *
          (2 * d * (3 ^ (d - 1)) ^ (j - m)) : ℕ) : ℝ))
      hincLoc
      (fun m _hm T _hT =>
        boundaryNeighborCentersForParent_card_cast_le_globalBoundaryLayer_pow
          Q j m T)
      huParent

end

end Homogenization
