/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.PackingRelabel

public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger

/-!
# Relabelling a packing by the simultaneous child swap

The sibling failure tree can select either diagonal endpoint.  This file transports a packing
across the simultaneous swap of both colors, preserving its total radius, virtual diameter, and
score.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The involution on six-point indices that swaps both pairs of children. -/
def swapChildrenIndexEquiv : SixPointIndex ≃ SixPointIndex where
  toFun index := (index.1, swapChildLabel index.2)
  invFun index := (index.1, swapChildLabel index.2)
  left_inv index := by
    rcases index with ⟨color, label⟩
    cases label <;> rfl
  right_inv index := by
    rcases index with ⟨color, label⟩
    cases label <;> rfl

/-- Child relabelling preserves the color of each index. -/
@[simp] theorem swapChildrenIndexEquiv_color (index : SixPointIndex) :
    (swapChildrenIndexEquiv index).1 = index.1 := rfl

@[simp] private theorem swapChildrenIndexEquiv_involution (index : SixPointIndex) :
    swapChildrenIndexEquiv (swapChildrenIndexEquiv index) = index := by
  rcases index with ⟨color, label⟩
  cases label <;> rfl

/-- The permuted configuration agrees with the relabelled original centers. -/
@[simp] theorem swapConfigurationChildren_eq_swapIndex
    (configuration : SixPointConfiguration) (index : SixPointIndex) :
    swapConfigurationChildren configuration index.1 index.2 =
      configuration (swapChildrenIndexEquiv index).1 (swapChildrenIndexEquiv index).2 := by
  rcases index with ⟨color, label⟩
  cases label <;> rfl

namespace SixPointPacking

/-- Membership in a swapped support pulls back along the child-swap involution. -/
theorem swapChildrenIndex_mem_of_mem_map {support : Finset SixPointIndex}
    {index : SixPointIndex} (hindex : index ∈ support.map swapChildrenIndexEquiv.toEmbedding) :
    swapChildrenIndexEquiv index ∈ support := by
  rw [Finset.mem_map] at hindex
  obtain ⟨source, hsource, rfl⟩ := hindex
  simpa using hsource

/-- Transport a packing through the child permutation. -/
def unswapChildren {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) :
    SixPointPacking configuration :=
  packing.relabel swapChildrenIndexEquiv swapChildrenIndexEquiv_color
    (swapConfigurationChildren_eq_swapIndex configuration)

/-- Child relabelling preserves the total radius. -/
theorem unswapChildren_totalRadius {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) :
    packing.unswapChildren.totalRadius = packing.totalRadius := by
  exact packing.relabel_totalRadius swapChildrenIndexEquiv swapChildrenIndexEquiv_color
    (swapConfigurationChildren_eq_swapIndex configuration)

/-- Child relabelling preserves the virtual diameter. -/
theorem unswapChildren_virtualDiameter {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) :
    packing.unswapChildren.virtualDiameter = packing.virtualDiameter := by
  exact packing.relabel_virtualDiameter swapChildrenIndexEquiv swapChildrenIndexEquiv_color
    (swapConfigurationChildren_eq_swapIndex configuration)

/-- Child relabelling preserves the packing score. -/
theorem unswapChildren_score {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) (s : ℝ) :
    packing.unswapChildren.score s = packing.score s := by
  exact packing.relabel_score swapChildrenIndexEquiv swapChildrenIndexEquiv_color
    (swapConfigurationChildren_eq_swapIndex configuration) s

end SixPointPacking

end LeanPool.Besicovitch
