/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaJacobianPresentation
import LeanPool.BrillNoetherGraphs.Bananas.Jacobian.BananaTorsionSlopes
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossStrandSupport

/-!
# The diagonal relation in the banana Jacobian presentation

The image of `(1, ..., 1)` under the coordinate-divisor map is the principal
divisor obtained by firing the common left endpoint once.  The proof uses
normalized strand slopes, so it treats arbitrary storage orientations and
length-one strands uniformly.
-/

namespace Bananas

open Utilities
open scoped BigOperators
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

private theorem leftChip_initialSlope {g : ℕ} (B : Banana g)
    (alpha : Fin (g + 1)) :
    bananaStepSlope B (oneChip (leftEndpoint B)) alpha 0 = -1 := by
  rw [bananaStepSlope_eq B _ alpha 0 (B.length_pos alpha)]
  let one : B.PathPosition alpha :=
    ⟨1, by have := B.length_pos alpha; omega⟩
  have hOne : strandVertex B alpha one ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B alpha one (by simp [one])
  rw [strandVertex_zero]
  simp only [oneChip]
  rw [if_neg hOne]
  simp

private theorem leftChip_slope_eq_zero_of_pos {g : ℕ} (B : Banana g)
    (alpha : Fin (g + 1)) (r : ℕ) (hrPos : 0 < r)
    (hrLt : r < B.length alpha) :
    bananaStepSlope B (oneChip (leftEndpoint B)) alpha r = 0 := by
  rw [bananaStepSlope_eq B _ alpha r hrLt]
  let current : B.PathPosition alpha := ⟨r, Nat.lt_succ_of_lt hrLt⟩
  let next : B.PathPosition alpha := ⟨r + 1, by omega⟩
  have hLeft : strandVertex B alpha current ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B alpha current (by simpa [current])
  have hRight : strandVertex B alpha next ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B alpha next (by simp [next])
  simp only [oneChip]
  rw [if_neg hRight, if_neg hLeft]
  norm_num

private theorem coordinateStep_leftEndpoint {g : ℕ} (B : Banana g)
    (alpha : Fin (g + 1)) :
    bananaCoordinateStep B alpha (leftEndpoint B) = -1 := by
  let one : B.PathPosition alpha :=
    ⟨1, by have := B.length_pos alpha; omega⟩
  have hOne : strandVertex B alpha one ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B alpha one (by simp [one])
  unfold bananaCoordinateStep
  change (if leftEndpoint B = strandVertex B alpha one then 1 else 0) -
      (if leftEndpoint B = leftEndpoint B then 1 else 0) = -1
  rw [if_neg hOne.symm, if_pos rfl]
  norm_num

private theorem coordinateStep_rightEndpoint {g : ℕ} (B : Banana g)
    (alpha : Fin (g + 1)) :
    bananaCoordinateStep B alpha (rightEndpoint B) =
      if B.length alpha = 1 then 1 else 0 := by
  let one : B.PathPosition alpha :=
    ⟨1, by have := B.length_pos alpha; omega⟩
  have hLR : rightEndpoint B ≠ leftEndpoint B :=
    (leftEndpoint_ne_rightEndpoint B).symm
  by_cases hLength : B.length alpha = 1
  · have hOnePosition : one =
        (⟨B.length alpha, by omega⟩ : B.PathPosition alpha) := by
      apply Fin.ext
      simp [one, hLength]
    have hOneVertex : strandVertex B alpha one = rightEndpoint B := by
      rw [hOnePosition, strandVertex_length]
    have hOneVertex' : strandVertex B alpha
        (⟨1, by have := B.length_pos alpha; omega⟩ : B.PathPosition alpha) =
          rightEndpoint B := by
      simpa [one] using hOneVertex
    rw [if_pos hLength]
    unfold bananaCoordinateStep
    simp only [Pi.sub_apply, oneChip]
    rw [if_pos hOneVertex'.symm, if_neg hLR]
    norm_num
  · have hLt : 1 < B.length alpha := by
      have := B.length_pos alpha
      omega
    have hOneVertex : strandVertex B alpha one ≠ rightEndpoint B :=
      strandVertex_ne_rightEndpoint B alpha one (by simpa [one])
    have hOneVertex' : strandVertex B alpha
        (⟨1, by have := B.length_pos alpha; omega⟩ : B.PathPosition alpha) ≠
          rightEndpoint B := by
      simpa [one] using hOneVertex
    rw [if_neg hLength]
    unfold bananaCoordinateStep
    simp only [Pi.sub_apply, oneChip]
    rw [if_neg hOneVertex'.symm, if_neg hLR]
    norm_num

private theorem leftChip_finalSlope {g : ℕ} (B : Banana g)
    (alpha : Fin (g + 1)) :
    bananaStepSlope B (oneChip (leftEndpoint B)) alpha
        (B.length alpha - 1) =
      if B.length alpha = 1 then -1 else 0 := by
  by_cases hLength : B.length alpha = 1
  · rw [if_pos hLength]
    simpa [hLength] using leftChip_initialSlope B alpha
  · rw [if_neg hLength]
    apply leftChip_slope_eq_zero_of_pos B alpha
    · have := B.length_pos alpha
      omega
    · have := B.length_pos alpha
      omega

private theorem coordinateStep_normalizedInterior {g : ℕ} (B : Banana g)
    (alpha beta : Fin (g + 1)) (p : B.PathPosition alpha)
    (hp : B.IsInteriorPosition alpha p) :
    bananaCoordinateStep B beta (strandVertex B alpha p) =
      if beta = alpha ∧ p.val = 1 then 1 else 0 := by
  let one : B.PathPosition beta :=
    ⟨1, by have := B.length_pos beta; omega⟩
  have hFirstEq :
      strandVertex B beta one = strandVertex B alpha p ↔
        beta = alpha ∧ p.val = 1 := by
    by_cases hLength : B.length beta = 1
    · have hOnePosition : one =
          (⟨B.length beta, by omega⟩ : B.PathPosition beta) := by
        apply Fin.ext
        simp [one, hLength]
      have hOneVertex : strandVertex B beta one = rightEndpoint B := by
        rw [hOnePosition, strandVertex_length]
      constructor
      · intro hEq
        have hTargetRight : strandVertex B alpha p ≠ rightEndpoint B :=
          strandVertex_ne_rightEndpoint B alpha p hp.2
        exact (hTargetRight (hEq.symm.trans hOneVertex)).elim
      · rintro ⟨hBetaAlpha, hpOne⟩
        subst beta
        change 0 < p.val ∧ p.val < B.length alpha at hp
        omega
    · have hOneInterior : B.IsInteriorPosition beta one := by
        change 0 < one.val ∧ one.val < B.length beta
        simp only [one]
        have := B.length_pos beta
        omega
      constructor
      · intro hEq
        have hBetaAlpha := strand_eq_of_interior_vertex_eq B beta alpha one p
          hOneInterior hp hEq
        subst beta
        have hPosition : one = p := strandVertex_injective B alpha hEq
        refine ⟨rfl, ?_⟩
        simpa [one] using congrArg Fin.val hPosition.symm
      · rintro ⟨hBetaAlpha, hpOne⟩
        subst beta
        apply congrArg (strandVertex B alpha)
        apply Fin.ext
        simpa [one] using hpOne.symm
  have hFirstEq' :
      strandVertex B alpha p = strandVertex B beta
          (⟨1, by have := B.length_pos beta; omega⟩ : B.PathPosition beta) ↔
        beta = alpha ∧ p.val = 1 := by
    rw [eq_comm]
    simpa [one] using hFirstEq
  have hTargetLeft : strandVertex B alpha p ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B alpha p hp.1
  unfold bananaCoordinateStep
  simp only [Pi.sub_apply, oneChip]
  simp only [hFirstEq', if_neg hTargetLeft, sub_zero]

private theorem prin_leftChip_normalizedInterior {g : ℕ} (B : Banana g)
    (alpha : Fin (g + 1)) (p : B.PathPosition alpha)
    (hp : B.IsInteriorPosition alpha p) :
    prin B.graph (oneChip (leftEndpoint B)) (strandVertex B alpha p) =
      if p.val = 1 then 1 else 0 := by
  let r : Fin (B.length alpha - 1) := ⟨p.val - 1, by
    change 0 < p.val ∧ p.val < B.length alpha at hp
    omega⟩
  have hrSucc : r.val + 1 = p.val := by
    simp only [r]
    change 0 < p.val ∧ p.val < B.length alpha at hp
    omega
  have hpEq :
      (⟨r.val + 1, by omega⟩ : B.PathPosition alpha) = p :=
    Fin.ext hrSucc
  have hPrin := prin_normalized_interior_general B
    (oneChip (leftEndpoint B)) alpha r
  rw [hpEq] at hPrin
  rw [hPrin]
  by_cases hpOne : p.val = 1
  · rw [if_pos hpOne]
    have hrZero : r.val = 0 := by omega
    have hNext : bananaStepSlope B (oneChip (leftEndpoint B)) alpha
        (r.val + 1) = 0 := by
      apply leftChip_slope_eq_zero_of_pos B alpha
      · omega
      · rw [hrSucc]
        exact hp.2
    have hInitial : bananaStepSlope B (oneChip (leftEndpoint B)) alpha
        r.val = -1 := by
      simpa [hrZero] using leftChip_initialSlope B alpha
    rw [hNext, hInitial]
    norm_num
  · rw [if_neg hpOne]
    have hrPos : 0 < r.val := by omega
    have hCurrent : bananaStepSlope B (oneChip (leftEndpoint B)) alpha
        r.val = 0 := by
      apply leftChip_slope_eq_zero_of_pos B alpha r.val hrPos
      omega
    have hNext : bananaStepSlope B (oneChip (leftEndpoint B)) alpha
        (r.val + 1) = 0 := by
      apply leftChip_slope_eq_zero_of_pos B alpha
      · omega
      · rw [hrSucc]
        exact hp.2
    rw [hCurrent, hNext]
    norm_num

/-- The diagonal coordinate vector maps to the principal divisor obtained by
firing the common left endpoint once. -/
theorem bananaDiagonalRelation_image_eq_prin_leftEndpoint {g : ℕ}
    (B : Banana g) :
    bananaCoordinateDivisorHom B (bananaDiagonalRelation (g := g)) =
      prin B.graph (oneChip (leftEndpoint B)) := by
  rw [bananaCoordinateDivisorHom_diagonalRelation]
  funext vertex
  rcases vertex with core | ⟨alpha, offset⟩
  · rcases fin_two_eq_zero_or_one core with hCore | hCore
    · subst core
      change (∑ alpha : Fin (g + 1), bananaCoordinateStep B alpha)
          (leftEndpoint B) =
        prin B.graph (oneChip (leftEndpoint B)) (leftEndpoint B)
      rw [prin_leftEndpoint_eq_sum_initialSlope]
      rw [Finset.sum_apply]
      simp_rw [coordinateStep_leftEndpoint, leftChip_initialSlope]
    · subst core
      change (∑ alpha : Fin (g + 1), bananaCoordinateStep B alpha)
          (rightEndpoint B) =
        prin B.graph (oneChip (leftEndpoint B)) (rightEndpoint B)
      rw [prin_rightEndpoint_eq_neg_sum_finalSlope]
      rw [Finset.sum_apply]
      simp_rw [coordinateStep_rightEndpoint, leftChip_finalSlope]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro beta _
      split <;> norm_num
  · change (∑ beta : Fin (g + 1), bananaCoordinateStep B beta)
        (B.interiorVertex alpha offset) =
      prin B.graph (oneChip (leftEndpoint B))
        (B.interiorVertex alpha offset)
    obtain ⟨p, hp, hpVertex⟩ :=
      exists_interior_strandVertex B alpha offset
    rw [← hpVertex, prin_leftChip_normalizedInterior B alpha p hp]
    rw [Finset.sum_apply]
    simp_rw [coordinateStep_normalizedInterior B alpha _ p hp]
    by_cases hpOne : p.val = 1
    · rw [if_pos hpOne]
      simp [hpOne]
    · rw [if_neg hpOne]
      simp [hpOne]

/-- Thus the diagonal relation maps to a principal divisor. -/
theorem bananaDiagonalRelation_image_principal {g : ℕ} (B : Banana g) :
    bananaCoordinateDivisorHom B (bananaDiagonalRelation (g := g)) ∈
      principalDivisors B.graph := by
  rw [bananaDiagonalRelation_image_eq_prin_leftEndpoint]
  exact (principal_iff_eq_prin B.graph _).2
    ⟨oneChip (leftEndpoint B), rfl⟩

/-- The diagonal generator belongs to the exact graph relation subgroup. -/
theorem bananaDiagonalRelation_mem_relations {g : ℕ} (B : Banana g) :
    bananaDiagonalRelation (g := g) ∈ bananaCoordinateRelations B := by
  rw [bananaCoordinateRelations, AddMonoidHom.mem_ker]
  apply (QuotientAddGroup.eq_zero_iff _).2
  exact bananaDiagonalRelation_image_principal B

end Bananas
