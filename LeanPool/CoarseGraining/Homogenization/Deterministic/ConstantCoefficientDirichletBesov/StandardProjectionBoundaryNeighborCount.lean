/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.StandardProjectionBoundaryNeighbor

/-! # Standard Projection Boundary Neighbor Count -/

namespace Homogenization

noncomputable section

open scoped ENNReal BigOperators

/-!
# Sharp boundary-neighbor hit counts

This file closes the geometric counting interface left by
`StandardProjectionBoundaryNeighbor`.  For a fixed depth-`m` parent `T`, any
depth-`m` parent whose boundary children can charge `T` must lie in the
one-step lattice neighborhood of `T`.  That neighborhood has dimension-only
cardinality, by triadic color injectivity.
-/

noncomputable def oneStepNeighborParentsAtDepth {d : ℕ}
    (Q : TriadicCube d) (m : ℕ) (T : TriadicCube d) :
    Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth Q m).filter fun P =>
    ∀ i : Fin d, T.index i - 1 ≤ P.index i ∧ P.index i ≤ T.index i + 1

theorem mem_oneStepNeighborParentsAtDepth_iff {d : ℕ}
    {Q P T : TriadicCube d} {m : ℕ} :
    P ∈ oneStepNeighborParentsAtDepth Q m T ↔
      P ∈ descendantsAtDepth Q m ∧
        ∀ i : Fin d, T.index i - 1 ≤ P.index i ∧
          P.index i ≤ T.index i + 1 := by
  classical
  simp [oneStepNeighborParentsAtDepth]

theorem cubeColor_injOn_oneStepNeighborParentsAtDepth {d : ℕ}
    (Q : TriadicCube d) (m : ℕ) (T : TriadicCube d) :
    Set.InjOn cubeColor (oneStepNeighborParentsAtDepth Q m T : Set (TriadicCube d)) := by
  intro P hP R hR hcolor
  rcases mem_oneStepNeighborParentsAtDepth_iff.mp hP with ⟨hPdesc, hPnear⟩
  rcases mem_oneStepNeighborParentsAtDepth_iff.mp hR with ⟨hRdesc, hRnear⟩
  have hscale : P.scale = R.scale := by
    calc
      P.scale = Q.scale - m := scale_eq_sub_of_mem_descendantsAtDepth hPdesc
      _ = R.scale := by
        symm
        exact scale_eq_sub_of_mem_descendantsAtDepth hRdesc
  have hindex : P.index = R.index := by
    funext i
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgap : P.index i + 3 ≤ R.index i :=
        cubeColor_index_add_three_le_of_lt hcolor hlt
      have hPlo := (hPnear i).1
      have hRhi := (hRnear i).2
      omega
    · have hgap : R.index i + 3 ≤ P.index i :=
        cubeColor_index_add_three_le_of_lt hcolor.symm hgt
      have hRlo := (hRnear i).1
      have hPhi := (hPnear i).2
      omega
  cases P with
  | mk Pscale Pindex =>
  cases R with
  | mk Rscale Rindex =>
    simp at hscale hindex ⊢
    exact ⟨hscale, hindex⟩

theorem oneStepNeighborParentsAtDepth_card_le_pow {d : ℕ}
    (Q : TriadicCube d) (m : ℕ) (T : TriadicCube d) :
    (oneStepNeighborParentsAtDepth Q m T).card ≤ 3 ^ d := by
  classical
  have hcard_univ :
      (oneStepNeighborParentsAtDepth Q m T).card ≤
        (Finset.univ : Finset (CubeColor d)).card := by
    refine Finset.card_le_card_of_injOn cubeColor ?_ ?_
    · intro P _hP
      simp
    · exact cubeColor_injOn_oneStepNeighborParentsAtDepth Q m T
  simpa [card_cubeColor] using hcard_univ

theorem cubeScaleFactor_le_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {n : ℕ}
    (hR : R ∈ descendantsAtDepth Q n) :
    cubeScaleFactor R ≤ cubeScaleFactor Q := by
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
  exact div_le_self (le_of_lt (cubeScaleFactor_pos' Q))
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))

theorem cubeIndex_oneStep_of_overlap_inter_cube_of_descendant
    {d : ℕ} {P S T : TriadicCube d} {n : ℕ}
    (hSP : S ∈ descendantsAtDepth P n)
    (hscale : T.scale = P.scale)
    (hinter : (overlapCubeSet S ∩ cubeSet T).Nonempty) :
    ∀ i : Fin d, T.index i - 1 ≤ P.index i ∧
      P.index i ≤ T.index i + 1 := by
  rcases hinter with ⟨x, hxS, hxT⟩
  have hSscale_le : cubeScaleFactor S ≤ cubeScaleFactor P :=
    cubeScaleFactor_le_of_mem_descendantsAtDepth hSP
  have hfactor_eq : cubeScaleFactor T = cubeScaleFactor P := by
    simp [cubeScaleFactor, hscale]
  intro i
  constructor
  · by_contra hnot
    have hindex : P.index i + 2 ≤ T.index i := by omega
    have hgap :
        cubeCoordUpper P i + cubeScaleFactor P ≤ cubeCoordLower T i := by
      rw [cubeCoordUpper, cubeCoordLower, hfactor_eq]
      have hindex_real : (P.index i : ℝ) + 2 ≤ (T.index i : ℝ) := by
        exact_mod_cast hindex
      have hcoeff :
          (P.index i : ℝ) + (3 / 2 : ℝ) ≤
            (T.index i : ℝ) - (1 / 2 : ℝ) := by
        linarith
      have hscale_nonneg : 0 ≤ cubeScaleFactor P :=
        le_of_lt (cubeScaleFactor_pos' P)
      nlinarith [mul_le_mul_of_nonneg_right hcoeff hscale_nonneg]
    have hSupperP : cubeCoordUpper S i ≤ cubeCoordUpper P i :=
      cubeCoordUpper_le_of_mem_descendantsAtDepth hSP i
    have hover_le : overlapCoordUpper S i ≤ cubeCoordLower T i := by
      rw [overlapCoordUpper_eq_cubeCoordUpper_add_cubeScaleFactor]
      linarith
    have hxTlo := (mem_cubeSet_iff_coord_bounds.mp hxT i).1
    have hxSupper := (mem_overlapCubeSet_iff_coord_bounds.mp hxS i).2
    exact not_lt_of_ge hxTlo (lt_of_lt_of_le hxSupper hover_le)
  · by_contra hnot
    have hindex : T.index i + 2 ≤ P.index i := by omega
    have hgap :
        cubeCoordUpper T i + cubeScaleFactor P ≤ cubeCoordLower P i := by
      rw [cubeCoordUpper, cubeCoordLower, hfactor_eq]
      have hindex_real : (T.index i : ℝ) + 2 ≤ (P.index i : ℝ) := by
        exact_mod_cast hindex
      have hcoeff :
          (T.index i : ℝ) + (3 / 2 : ℝ) ≤
            (P.index i : ℝ) - (1 / 2 : ℝ) := by
        linarith
      have hscale_nonneg : 0 ≤ cubeScaleFactor P :=
        le_of_lt (cubeScaleFactor_pos' P)
      nlinarith [mul_le_mul_of_nonneg_right hcoeff hscale_nonneg]
    have hPlowerS : cubeCoordLower P i ≤ cubeCoordLower S i :=
      cubeCoordLower_le_of_mem_descendantsAtDepth hSP i
    have hupper_le : cubeCoordUpper T i ≤ overlapCoordLower S i := by
      rw [overlapCoordLower_eq_cubeCoordLower_sub_cubeScaleFactor]
      linarith
    have hxTupper := (mem_cubeSet_iff_coord_bounds.mp hxT i).2
    have hxSlower := (mem_overlapCubeSet_iff_coord_bounds.mp hxS i).1
    exact not_lt_of_ge (le_trans hupper_le hxSlower) hxTupper

theorem mem_descendantsAtDepth_succ_of_mem_childBoundaryLayerCentersAtDepth
    {d : ℕ} {P S : TriadicCube d} {n : ℕ}
    (hS : S ∈ childBoundaryLayerCentersAtDepth P n) :
    S ∈ descendantsAtDepth P (1 + n) := by
  classical
  dsimp [childBoundaryLayerCentersAtDepth] at hS
  rcases Finset.mem_biUnion.mp hS with ⟨R, hRchild, hSboundary⟩
  have hSdesc : S ∈ descendantsAtDepth R n :=
    (mem_descendantBoundaryLayerAtDepth_iff.mp hSboundary).1
  have hRdesc : R ∈ descendantsAtDepth P 1 := by
    simpa [descendantsAtDepth_one] using hRchild
  exact mem_descendantsAtDepth_add hRdesc hSdesc

theorem boundaryGeneratingParentsForParent_subset_oneStepNeighborParentsAtDepth
    {d : ℕ} (Q : TriadicCube d) {j m : ℕ} (T : TriadicCube d) :
    boundaryGeneratingParentsForParent Q j m T ⊆
      oneStepNeighborParentsAtDepth Q m T := by
  intro P hP
  rcases mem_boundaryGeneratingParentsForParent_iff.mp hP with
    ⟨hPdesc, S, hSneighbor, hSchild⟩
  rcases mem_boundaryNeighborCentersForParent_iff.mp hSneighbor with
    ⟨_hSboundary, _hScenter, hTintersect⟩
  rcases mem_overlapIntersectingParentsAtDepth_iff.mp hTintersect with
    ⟨hTdesc, hinter⟩
  have hscale : T.scale = P.scale := by
    calc
      T.scale = Q.scale - m := scale_eq_sub_of_mem_descendantsAtDepth hTdesc
      _ = P.scale := by
        symm
        exact scale_eq_sub_of_mem_descendantsAtDepth hPdesc
  have hSPdesc : S ∈ descendantsAtDepth P (1 + (j - m)) :=
    mem_descendantsAtDepth_succ_of_mem_childBoundaryLayerCentersAtDepth hSchild
  exact mem_oneStepNeighborParentsAtDepth_iff.2
    ⟨hPdesc,
      cubeIndex_oneStep_of_overlap_inter_cube_of_descendant hSPdesc hscale hinter⟩

theorem boundaryGeneratingParentsForParent_card_le_pow {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    (boundaryGeneratingParentsForParent Q j m T).card ≤ 3 ^ d :=
  (Finset.card_le_card
    (boundaryGeneratingParentsForParent_subset_oneStepNeighborParentsAtDepth
      Q T)).trans
    (oneStepNeighborParentsAtDepth_card_le_pow Q m T)

theorem boundaryNeighborCentersForParent_card_le_sharp {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    (boundaryNeighborCentersForParent Q j m T).card ≤
      3 ^ d * (3 ^ d * (2 * d * (3 ^ (d - 1)) ^ (j - m))) := by
  exact boundaryNeighborCentersForParent_card_le_of_generatingParents_card_le
    Q j m T (boundaryGeneratingParentsForParent_card_le_pow Q j m T)

theorem boundaryNeighborCentersForParent_card_cast_le_sharp {d : ℕ}
    (Q : TriadicCube d) (j m : ℕ) (T : TriadicCube d) :
    ((boundaryNeighborCentersForParent Q j m T).card : ℝ) ≤
      ((3 ^ d * (3 ^ d * (2 * d * (3 ^ (d - 1)) ^ (j - m))) : ℕ) : ℝ) := by
  exact_mod_cast boundaryNeighborCentersForParent_card_le_sharp Q j m T

/-- Projection-gap estimate with the sharp per-parent boundary-neighbor count.
This is the closed geometric version of the hit-count interface from
`StandardProjectionBoundaryNeighbor`: the only remaining inputs are the local
`L²` hypotheses needed to form the overlap norms and the ordinary standard
parent `L²` hypotheses. -/
theorem cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_sqrt_sharpBoundary_depthAverage
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
                (((3 ^ d * (3 ^ d *
                    (2 * d * (3 ^ (d - 1)) ^ (j - m))) : ℕ) : ℝ) *
                  ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
                    ((descendantsAtDepth Q m).card : ℝ) *
                      cubeBesovPositiveVectorDepthAverage Q u m)))) := by
  exact
    cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_sqrt_neighbor_count_depthAverage
      (Q := Q) (s := s) (u := u) (j := j)
      (M := fun m =>
        ((3 ^ d * (3 ^ d *
          (2 * d * (3 ^ (d - 1)) ^ (j - m))) : ℕ) : ℝ))
      hincLoc
      (fun m _hm T _hT =>
        boundaryNeighborCentersForParent_card_cast_le_sharp Q j m T)
      huParent

/-- One-depth hard comparison with the sharp projection-gap branch inserted.
The residual half is paid by the same-depth ordinary standard positive term;
the projection half is paid by the sharp boundary-neighbor sum over coarser
ordinary positive depths. -/
theorem sq_cubeBesovOverlappingPositiveVectorDepthSeminorm_le_standard_add_sharpBoundary_sum
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
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (hincLoc :
      ∀ S ∈ overlapCentersAtDepth Q j, ∀ m ∈ Finset.range j,
        MeasureTheory.MemLp (cubeIncrementVec Q (m + 1) u)
          (2 : ℝ≥0∞) (normalizedOverlapCubeMeasure S))
    (huParent :
      ∀ m ∈ Finset.range j, ∀ T ∈ descendantsAtDepth Q m,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure T)) :
    let G : ℝ :=
      ∑ m ∈ Finset.range j,
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          Real.sqrt
            ((((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
              (4 *
                (((3 ^ d * (3 ^ d *
                    (2 * d * (3 ^ (d - 1)) ^ (j - m))) : ℕ) : ℝ) *
                  ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
                    ((descendantsAtDepth Q m).card : ℝ) *
                      cubeBesovPositiveVectorDepthAverage Q u m))))
    (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s u j) ^ 2 ≤
      8 * (3 ^ d : ℝ) * (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 +
        4 * G ^ 2 := by
  dsimp only
  let G : ℝ :=
    ∑ m ∈ Finset.range j,
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        Real.sqrt
          ((((3 ^ d) ^ j : ℕ) : ℝ)⁻¹ *
            (4 *
              (((3 ^ d * (3 ^ d *
                  (2 * d * (3 ^ (d - 1)) ^ (j - m))) : ℕ) : ℝ) *
                ((3 ^ d : ℝ) * (Fintype.card (Fin d) : ℝ) *
                  ((descendantsAtDepth Q m).card : ℝ) *
                    cubeBesovPositiveVectorDepthAverage Q u m))))
  have hsplit :=
    sq_cubeBesovOverlappingPositiveVectorDepthSeminorm_le_standard_add_gap_zero
      Q s u j hres hresLoc hprojLoc hzeroLoc hgapLoc
  have hgap :
      cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
          (cubeProjectionGapVec Q 0 j u) j ≤ G := by
    dsimp [G]
    exact
      cubeBesovOverlappingPositiveVectorDepthSeminorm_gap_zero_le_sum_sqrt_sharpBoundary_depthAverage
        Q s u j hincLoc huParent
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    refine Finset.sum_nonneg ?_
    intro m _hm
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (Real.sqrt_nonneg _)
  have hgap_sq :
      (cubeBesovOverlappingPositiveVectorDepthSeminorm Q s
          (cubeProjectionGapVec Q 0 j u) j) ^ 2 ≤ G ^ 2 :=
    (sq_le_sq₀
      (cubeBesovOverlappingPositiveVectorDepthSeminorm_nonneg Q s
        (cubeProjectionGapVec Q 0 j u) j)
      hG_nonneg).mpr hgap
  exact hsplit.trans
    (add_le_add_right
      (mul_le_mul_of_nonneg_left hgap_sq (by norm_num : 0 ≤ (4 : ℝ)))
      (8 * (3 ^ d : ℝ) * (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2))

end

end Homogenization
