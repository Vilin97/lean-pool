/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition

/-! # Boundary Layer -/

@[expose] public section

namespace Homogenization

/-- The geometric boundary of a half-open cube, encoded as the difference between the half-open
realization and its open core. -/
def cubeBoundary {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  cubeSet Q \ openCubeSet Q

/-- The cube obtained by shrinking each face inward by the normalized amount `t`. For `t = 0` this
recovers the original half-open cube. -/
def cubeShrunkSet {d : ℕ} (Q : TriadicCube d) (t : ℝ) : Set (Vec d) :=
  { x | ∀ i,
      ((((Q.index i : ℝ) - (1 / 2 : ℝ)) + t) * cubeScaleFactor Q ≤ x i) ∧
      (x i < ((((Q.index i : ℝ) + (1 / 2 : ℝ)) - t) * cubeScaleFactor Q)) }

/-- The boundary layer of thickness `t`, defined as the part of the cube left after removing the
shrunk core. -/
def cubeBoundaryLayer {d : ℕ} (Q : TriadicCube d) (t : ℝ) : Set (Vec d) :=
  cubeSet Q \ cubeShrunkSet Q t

@[simp] theorem mem_cubeBoundary_iff {d : ℕ} {Q : TriadicCube d} {x : Vec d} :
    x ∈ cubeBoundary Q ↔ x ∈ cubeSet Q ∧ x ∉ openCubeSet Q := by
  rfl

@[simp] theorem mem_cubeShrunkSet_iff {d : ℕ} {Q : TriadicCube d} {t : ℝ} {x : Vec d} :
    x ∈ cubeShrunkSet Q t ↔
      ∀ i,
        ((((Q.index i : ℝ) - (1 / 2 : ℝ)) + t) * cubeScaleFactor Q ≤ x i) ∧
        (x i < ((((Q.index i : ℝ) + (1 / 2 : ℝ)) - t) * cubeScaleFactor Q)) := by
  rfl

@[simp] theorem mem_cubeBoundaryLayer_iff {d : ℕ} {Q : TriadicCube d} {t : ℝ} {x : Vec d} :
    x ∈ cubeBoundaryLayer Q t ↔ x ∈ cubeSet Q ∧ x ∉ cubeShrunkSet Q t := by
  rfl

@[simp] theorem cubeShrunkSet_zero {d : ℕ} (Q : TriadicCube d) :
    cubeShrunkSet Q 0 = cubeSet Q := by
  ext x
  simp [cubeShrunkSet, cubeSet]

@[simp] theorem cubeBoundaryLayer_zero {d : ℕ} (Q : TriadicCube d) :
    cubeBoundaryLayer Q 0 = ∅ := by
  ext x
  simp [cubeBoundaryLayer]

private theorem cubeScaleFactor_pos {d : ℕ} (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

theorem cubeBoundary_subset_cubeSet {d : ℕ} (Q : TriadicCube d) :
    cubeBoundary Q ⊆ cubeSet Q :=
  Set.sdiff_subset

theorem cubeBoundaryLayer_subset_cubeSet {d : ℕ} (Q : TriadicCube d) (t : ℝ) :
    cubeBoundaryLayer Q t ⊆ cubeSet Q :=
  Set.sdiff_subset

theorem cubeShrunkSet_anti {d : ℕ} (Q : TriadicCube d) :
    Antitone (cubeShrunkSet Q) := by
  intro s t hst x hx i
  rcases hx i with ⟨hlo, hhi⟩
  have hscale_nonneg : 0 ≤ cubeScaleFactor Q := le_of_lt (cubeScaleFactor_pos Q)
  have hlo_coeff :
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) + s) * cubeScaleFactor Q ≤
        ((((Q.index i : ℝ) - (1 / 2 : ℝ)) + t) * cubeScaleFactor Q) := by
    refine mul_le_mul_of_nonneg_right ?_ hscale_nonneg
    linarith
  have hhi_coeff :
      ((((Q.index i : ℝ) + (1 / 2 : ℝ)) - t) * cubeScaleFactor Q) ≤
        ((((Q.index i : ℝ) + (1 / 2 : ℝ)) - s) * cubeScaleFactor Q) := by
    refine mul_le_mul_of_nonneg_right ?_ hscale_nonneg
    linarith
  exact ⟨le_trans hlo_coeff hlo, lt_of_lt_of_le hhi hhi_coeff⟩

theorem cubeShrunkSet_subset_cubeSet {d : ℕ} (Q : TriadicCube d) {t : ℝ} (ht : 0 ≤ t) :
    cubeShrunkSet Q t ⊆ cubeSet Q := by
  simpa using cubeShrunkSet_anti Q ht

theorem cubeBoundaryLayer_mono {d : ℕ} (Q : TriadicCube d) :
    Monotone (cubeBoundaryLayer Q) := by
  intro s t hst x hx
  rcases hx with ⟨hxQ, hx_not_mem⟩
  refine ⟨hxQ, ?_⟩
  intro hxt
  exact hx_not_mem ((cubeShrunkSet_anti Q hst) hxt)

theorem openCubeSet_subset_cubeSet {d : ℕ} (Q : TriadicCube d) :
    openCubeSet Q ⊆ cubeSet Q := by
  intro x hx i
  rcases hx i with ⟨hlo, hhi⟩
  exact ⟨le_of_lt hlo, hhi⟩

theorem pairwiseDisjoint_openCubeSet_descendantsAtDepth {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    (descendantsAtDepth Q n : Set (TriadicCube d)).PairwiseDisjoint openCubeSet := by
  intro R hR S hS hneq
  exact (pairwiseDisjoint_descendantsAtDepth Q n hR hS hneq).mono
    (openCubeSet_subset_cubeSet R) (openCubeSet_subset_cubeSet S)

theorem openCubeSet_union_cubeBoundary_eq_cubeSet {d : ℕ} (Q : TriadicCube d) :
    openCubeSet Q ∪ cubeBoundary Q = cubeSet Q := by
  ext x
  constructor
  · rintro (hx | ⟨hx, _⟩)
    · exact openCubeSet_subset_cubeSet Q hx
    · exact hx
  · intro hx
    by_cases hopen : x ∈ openCubeSet Q
    · exact Or.inl hopen
    · exact Or.inr ⟨hx, hopen⟩

theorem cubeShrunkSet_eq_empty_of_half_le {d : ℕ} [NeZero d] (Q : TriadicCube d) {t : ℝ}
    (ht : (1 / 2 : ℝ) ≤ t) :
    cubeShrunkSet Q t = ∅ := by
  ext x
  constructor
  · intro hx
    have hx0 := hx 0
    exfalso
    have hscale_pos := cubeScaleFactor_pos Q
    nlinarith [hx0.1, hx0.2, hscale_pos, ht]
  · intro hx
    simp at hx

theorem cubeBoundaryLayer_eq_cubeSet_of_half_le {d : ℕ} [NeZero d] (Q : TriadicCube d) {t : ℝ}
    (ht : (1 / 2 : ℝ) ≤ t) :
    cubeBoundaryLayer Q t = cubeSet Q := by
  rw [cubeBoundaryLayer, cubeShrunkSet_eq_empty_of_half_le Q ht, Set.sdiff_empty]

theorem center_mem_cubeShrunkSet_of_lt_half {d : ℕ} (Q : TriadicCube d) {t : ℝ}
    (ht : t < (1 / 2 : ℝ)) :
    (fun i => (Q.index i : ℝ) * cubeScaleFactor Q) ∈ cubeShrunkSet Q t := by
  intro i
  have hscale_pos := cubeScaleFactor_pos Q
  constructor
  · nlinarith
  · nlinarith

theorem cubeShrunkSet_nonempty_of_lt_half {d : ℕ} (Q : TriadicCube d) {t : ℝ}
    (ht : t < (1 / 2 : ℝ)) :
    (cubeShrunkSet Q t).Nonempty := by
  refine ⟨fun i => (Q.index i : ℝ) * cubeScaleFactor Q, ?_⟩
  exact center_mem_cubeShrunkSet_of_lt_half Q ht

theorem cubeShrunkSet_nonempty_iff {d : ℕ} [NeZero d] {Q : TriadicCube d} {t : ℝ} :
    (cubeShrunkSet Q t).Nonempty ↔ t < (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨x, hx⟩
    by_contra ht
    have hempty : cubeShrunkSet Q t = ∅ :=
      cubeShrunkSet_eq_empty_of_half_le Q (le_of_not_gt ht)
    rw [hempty] at hx
    simp at hx
  · exact cubeShrunkSet_nonempty_of_lt_half Q

theorem cubeShrunkSet_eq_empty_iff {d : ℕ} [NeZero d] {Q : TriadicCube d} {t : ℝ} :
    cubeShrunkSet Q t = ∅ ↔ (1 / 2 : ℝ) ≤ t := by
  constructor
  · intro h
    by_contra ht
    rcases cubeShrunkSet_nonempty_of_lt_half Q (lt_of_not_ge ht) with ⟨x, hx⟩
    rw [h] at hx
    simp at hx
  · exact cubeShrunkSet_eq_empty_of_half_le Q

theorem cubeSet_middleChild_subset_cubeShrunkSet {d : ℕ} (Q : TriadicCube d) {t : ℝ}
    (ht : t ≤ (1 / 3 : ℝ)) :
    cubeSet
      ({ scale := Q.scale - 1
         index := fun i => 3 * Q.index i } : TriadicCube d) ⊆
      cubeShrunkSet Q t := by
  let middle : TriadicCube d :=
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i }
  intro x hx i
  have hx' := hx i
  have hscale_pos := cubeScaleFactor_pos Q
  have hchild_scale :
      cubeScaleFactor middle = cubeScaleFactor Q / 3 := by
    simpa [middle] using cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  rw [hchild_scale] at hx'
  have hindex_cast : ((3 * Q.index i : ℤ) : ℝ) = 3 * (Q.index i : ℝ) := by
    norm_num
  constructor
  · nlinarith [hx'.1, hindex_cast, hscale_pos, ht]
  · nlinarith [hx'.2, hindex_cast, hscale_pos, ht]

theorem cubeSet_childCube_subset_cubeShrunkSet_of_digits_eq_one {d : ℕ} (Q : TriadicCube d)
    (digits : Fin d → Fin 3) (hdigits : ∀ i, digits i = 1) {t : ℝ}
    (ht : t ≤ (1 / 3 : ℝ)) :
    cubeSet
      ({ scale := Q.scale - 1
         index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 } : TriadicCube d) ⊆
      cubeShrunkSet Q t := by
  simpa [hdigits] using cubeSet_middleChild_subset_cubeShrunkSet Q ht

@[simp] theorem descendantsAtScale_pred {d : ℕ} (Q : TriadicCube d) :
    descendantsAtScale Q (Q.scale - 1) = childCubes Q := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q (by omega)]
  simp

theorem middleChild_mem_childCubes {d : ℕ} (Q : TriadicCube d) :
    ({ scale := Q.scale - 1
       index := fun i => 3 * Q.index i } : TriadicCube d) ∈ childCubes Q := by
  refine Finset.mem_image.mpr ?_
  refine ⟨fun _ => (1 : Fin 3), Finset.mem_univ _, ?_⟩
  cases Q
  simp

theorem middleChild_mem_descendantsAtScale_pred {d : ℕ} (Q : TriadicCube d) :
    ({ scale := Q.scale - 1
       index := fun i => 3 * Q.index i } : TriadicCube d) ∈
      descendantsAtScale Q (Q.scale - 1) := by
  rw [descendantsAtScale_pred]
  exact middleChild_mem_childCubes Q

@[simp] theorem descendantsAtScale_pred_card {d : ℕ} (Q : TriadicCube d) :
    (descendantsAtScale Q (Q.scale - 1)).card = 3 ^ d := by
  rw [descendantsAtScale_pred]
  exact childCubes_card Q

theorem cubeBoundaryLayer_subset_iUnion_childCubes_except_middle {d : ℕ} (Q : TriadicCube d)
    {t : ℝ} (ht : t ≤ (1 / 3 : ℝ)) :
    cubeBoundaryLayer Q t ⊆
      ⋃ R ∈ ({S : TriadicCube d | S ∈ childCubes Q ∧
          S ≠ ({ scale := Q.scale - 1
                 index := fun i => 3 * Q.index i } : TriadicCube d)} : Set (TriadicCube d)),
        cubeSet R := by
  let middle : TriadicCube d :=
    { scale := Q.scale - 1
      index := fun i => 3 * Q.index i }
  intro x hx
  rcases hx with ⟨hxQ, hx_not_shrunk⟩
  rcases exists_mem_childCubes_of_mem_cubeSet hxQ with ⟨R, hR, hxR⟩
  have hmid : cubeSet middle ⊆ cubeShrunkSet Q t := cubeSet_middleChild_subset_cubeShrunkSet Q ht
  have hneq : R ≠ middle := by
    intro hEq
    apply hx_not_shrunk
    exact hmid (hEq ▸ hxR)
  exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨by simpa [middle] using And.intro hR hneq, hxR⟩⟩

end Homogenization
