/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.SiblingFailureTree

/-!
# Swapping the two blue children

The four-child minimax has two matching branches. Swapping only the blue children identifies the
anti-diagonal branch with the diagonal one and preserves admissibility and every packing score.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The index permutation that interchanges the two blue children. -/
def swapBlueIndexEquiv : SixPointIndex ≃ SixPointIndex where
  toFun
    | (.red, label) => (.red, label)
    | (.blue, label) => (.blue, swapChildLabel label)
  invFun
    | (.red, label) => (.red, label)
    | (.blue, label) => (.blue, swapChildLabel label)
  left_inv index := by
    rcases index with ⟨color, label⟩
    cases color <;> cases label <;> rfl
  right_inv index := by
    rcases index with ⟨color, label⟩
    cases color <;> cases label <;> rfl

@[simp] private theorem swapBlueIndexEquiv_color (index : SixPointIndex) :
    (swapBlueIndexEquiv index).1 = index.1 := by
  rcases index with ⟨color, label⟩
  cases color <;> rfl

@[simp] private theorem swapBlueIndexEquiv_involution (index : SixPointIndex) :
    swapBlueIndexEquiv (swapBlueIndexEquiv index) = index := by
  rcases index with ⟨color, label⟩
  cases color <;> cases label <;> rfl

/-- The configuration obtained by interchanging the two blue children. -/
def swapBlueChildren (configuration : SixPointConfiguration) : SixPointConfiguration
  | .red, label => configuration .red label
  | .blue, label => configuration .blue (swapChildLabel label)

private theorem swapBlueChildren_swapBlueIndex
    (configuration : SixPointConfiguration) (index : SixPointIndex) :
    swapBlueChildren configuration (swapBlueIndexEquiv index).1
        (swapBlueIndexEquiv index).2 = configuration index.1 index.2 := by
  rcases index with ⟨color, label⟩
  cases color <;> cases label <;> rfl

@[simp] private theorem swapBlueChildren_swappedLabel
    (configuration : SixPointConfiguration) (index : SixPointIndex) :
    swapBlueChildren configuration index.1 (swapBlueIndexEquiv index).2 =
      configuration index.1 index.2 := by
  rcases index with ⟨color, label⟩
  cases color <;> cases label <;> rfl

@[simp] private theorem swapBlueChildren_eq_swapBlueIndex
    (configuration : SixPointConfiguration) (index : SixPointIndex) :
    swapBlueChildren configuration index.1 index.2 =
      configuration (swapBlueIndexEquiv index).1 (swapBlueIndexEquiv index).2 := by
  rcases index with ⟨color, label⟩
  cases color <;> cases label <;> rfl

/-- Swapping the blue children preserves endpoint admissibility. -/
theorem IsAdmissibleAt.swapBlueChildren {configuration : SixPointConfiguration} {s : ℝ}
    (h : configuration.IsAdmissibleAt s) :
    (swapBlueChildren configuration).IsAdmissibleAt s where
  root_distance := h.root_distance
  child_distance color label hlabel := by
    cases color
    · exact h.child_distance .red label hlabel
    · cases label with
      | root => simp at hlabel
      | left => exact h.child_distance .blue .right (by simp)
      | right => exact h.child_distance .blue .left (by simp)
  sibling_distance color := by
    cases color
    · exact h.sibling_distance .red
    · change 2 * s ≤
        dist (configuration .blue .right) (configuration .blue .left)
      simpa only [dist_comm] using h.sibling_distance .blue

/-- After swapping the blue children, the selected diagonal is the original anti-diagonal. -/
theorem selectedDiagonalMatchingFails_swapBlueChildren
    (configuration : SixPointConfiguration) :
    SelectedDiagonalMatchingFails (swapBlueChildren configuration) ↔
      (2 * barC - 1) *
          (dist (configuration .red .left) (configuration .red .right) +
            dist (configuration .blue .left) (configuration .blue .right)) ≤
        dist (configuration .red .left) (configuration .blue .right) +
          dist (configuration .red .right) (configuration .blue .left) := by
  simp [SelectedDiagonalMatchingFails, incidenceCrossDistance, incidenceChild,
    swapBlueChildren, swapChildLabel, dist_comm, add_comm]

namespace SixPointPacking

/-- Membership in a swapped support pulls back along the involution. -/
theorem swapBlueIndex_mem_of_mem_map {support : Finset SixPointIndex}
    {index : SixPointIndex} (hindex : index ∈ support.map swapBlueIndexEquiv.toEmbedding) :
    swapBlueIndexEquiv index ∈ support := by
  rw [Finset.mem_map] at hindex
  obtain ⟨source, hsource, rfl⟩ := hindex
  simpa using hsource

/-- Relabel a packing after the two blue children have been swapped. -/
def unswapBlue {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) :
    SixPointPacking configuration where
  support := packing.support.map swapBlueIndexEquiv.toEmbedding
  meets_color color := by
    obtain ⟨label, hlabel⟩ := packing.meets_color color
    cases color with
    | red =>
        exact ⟨label, Finset.mem_map.2 ⟨(.red, label), hlabel, rfl⟩⟩
    | blue =>
        exact ⟨swapChildLabel label,
          Finset.mem_map.2 ⟨(.blue, label), hlabel, by cases label <;> rfl⟩⟩
  radius index := packing.radius ⟨swapBlueIndexEquiv index,
    swapBlueIndex_mem_of_mem_map index.2⟩
  same_color_disjoint i j hij hcolor := by
    let i' : packing.support := ⟨swapBlueIndexEquiv i,
      swapBlueIndex_mem_of_mem_map i.2⟩
    let j' : packing.support := ⟨swapBlueIndexEquiv j,
      swapBlueIndex_mem_of_mem_map j.2⟩
    have hij' : i' ≠ j' := by
      intro heq
      apply hij
      apply Subtype.ext
      exact swapBlueIndexEquiv.injective (congrArg Subtype.val heq)
    have hcolor' : i'.1.1 = j'.1.1 := by
      simpa [i', j'] using hcolor
    have hp := packing.same_color_disjoint i' j' hij' hcolor'
    simpa [i', j', swapBlueChildren_swappedLabel] using hp

private def unswapBlueSupportEquiv {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) :
    (packing.unswapBlue).support ≃ packing.support where
  toFun index := ⟨swapBlueIndexEquiv index, swapBlueIndex_mem_of_mem_map index.2⟩
  invFun index := ⟨swapBlueIndexEquiv index, Finset.mem_map.2 ⟨index, index.2, rfl⟩⟩
  left_inv index := by
    apply Subtype.ext
    exact swapBlueIndexEquiv_involution index
  right_inv index := by
    apply Subtype.ext
    exact swapBlueIndexEquiv_involution index

@[simp] private theorem unswapBlueSupportEquiv_apply_val
    {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration))
    (index : packing.unswapBlue.support) :
    ((unswapBlueSupportEquiv packing index : packing.support) : SixPointIndex) =
      swapBlueIndexEquiv index := rfl

@[simp] private theorem unswapBlueSupportEquiv_symm_apply_val
    {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration))
    (index : packing.support) :
    (((unswapBlueSupportEquiv packing).symm index : packing.unswapBlue.support) :
      SixPointIndex) = swapBlueIndexEquiv index := rfl

@[simp] private theorem unswapBlue_radius_eq
    {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration))
    (index : packing.unswapBlue.support) :
    (packing.unswapBlue.radius index : ℝ) =
      packing.radius (unswapBlueSupportEquiv packing index) := by
  congr 1

private theorem unswapBlue_radius_symm_eq
    {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration))
    (index : packing.support) :
    (packing.unswapBlue.radius ((unswapBlueSupportEquiv packing).symm index) : ℝ) =
      packing.radius index := by
  rw [unswapBlue_radius_eq]
  exact congrArg (fun supportIndex ↦ (packing.radius supportIndex : ℝ))
    ((unswapBlueSupportEquiv packing).apply_symm_apply index)

/-- Swapping child names leaves the packing's total radius unchanged. -/
theorem unswapBlue_totalRadius {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) :
    packing.unswapBlue.totalRadius = packing.totalRadius := by
  unfold totalRadius
  rw [← Finset.univ_eq_attach, ← Finset.univ_eq_attach]
  apply Fintype.sum_equiv (unswapBlueSupportEquiv packing)
  intro index
  congr 1

/-- Swapping child names leaves the packing's virtual diameter unchanged. -/
theorem unswapBlue_virtualDiameter {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) :
    packing.unswapBlue.virtualDiameter = packing.virtualDiameter := by
  apply le_antisymm
  · unfold virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    simpa only [unswapBlueSupportEquiv_apply_val, unswapBlue_radius_eq,
      swapBlueChildren_swapBlueIndex, virtualDiameter] using
      packing.pair_le_virtualDiameter (unswapBlueSupportEquiv packing i)
        (unswapBlueSupportEquiv packing j)
  · unfold virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    simpa only [unswapBlueSupportEquiv_symm_apply_val, unswapBlue_radius_symm_eq,
      swapBlueChildren_eq_swapBlueIndex, swapBlueIndexEquiv_involution, virtualDiameter] using
      packing.unswapBlue.pair_le_virtualDiameter
        ((unswapBlueSupportEquiv packing).symm i) ((unswapBlueSupportEquiv packing).symm j)

/-- Swapping child names leaves the packing score unchanged. -/
theorem unswapBlue_score {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) (s : ℝ) :
    packing.unswapBlue.score s = packing.score s := by
  simp only [score, packing.unswapBlue_totalRadius, packing.unswapBlue_virtualDiameter]

end SixPointPacking

end LeanPool.Besicovitch
