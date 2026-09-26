/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.PackingRelabel

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

/-- Child relabelling preserves the color of each index. -/
@[simp] theorem swapBlueIndexEquiv_color (index : SixPointIndex) :
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

/-- The permuted configuration agrees with the relabelled original centers. -/
@[simp] theorem swapBlueChildren_eq_swapBlueIndex
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

/-- Transport a packing through the child permutation. -/
def unswapBlue {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) :
    SixPointPacking configuration :=
  packing.relabel swapBlueIndexEquiv swapBlueIndexEquiv_color
    (swapBlueChildren_eq_swapBlueIndex configuration)

/-- Child relabelling preserves the total radius. -/
theorem unswapBlue_totalRadius {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) :
    packing.unswapBlue.totalRadius = packing.totalRadius := by
  exact packing.relabel_totalRadius swapBlueIndexEquiv swapBlueIndexEquiv_color
    (swapBlueChildren_eq_swapBlueIndex configuration)

/-- Child relabelling preserves the virtual diameter. -/
theorem unswapBlue_virtualDiameter {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) :
    packing.unswapBlue.virtualDiameter = packing.virtualDiameter := by
  exact packing.relabel_virtualDiameter swapBlueIndexEquiv swapBlueIndexEquiv_color
    (swapBlueChildren_eq_swapBlueIndex configuration)

/-- Child relabelling preserves the packing score. -/
theorem unswapBlue_score {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapBlueChildren configuration)) (s : ℝ) :
    packing.unswapBlue.score s = packing.score s := by
  exact packing.relabel_score swapBlueIndexEquiv swapBlueIndexEquiv_color
    (swapBlueChildren_eq_swapBlueIndex configuration) s

end SixPointPacking

end LeanPool.Besicovitch
