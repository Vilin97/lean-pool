/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

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

@[simp] private theorem swapChildrenIndexEquiv_color (index : SixPointIndex) :
    (swapChildrenIndexEquiv index).1 = index.1 := rfl

@[simp] private theorem swapChildrenIndexEquiv_involution (index : SixPointIndex) :
    swapChildrenIndexEquiv (swapChildrenIndexEquiv index) = index := by
  rcases index with ⟨color, label⟩
  cases label <;> rfl

private theorem swapConfigurationChildren_swapIndex
    (configuration : SixPointConfiguration) (index : SixPointIndex) :
    swapConfigurationChildren configuration (swapChildrenIndexEquiv index).1
        (swapChildrenIndexEquiv index).2 = configuration index.1 index.2 := by
  rcases index with ⟨color, label⟩
  cases label <;> rfl

@[simp] private theorem swapConfigurationChildren_swappedLabel
    (configuration : SixPointConfiguration) (index : SixPointIndex) :
    swapConfigurationChildren configuration index.1 (swapChildrenIndexEquiv index).2 =
      configuration index.1 index.2 := by
  rcases index with ⟨color, label⟩
  cases label <;> rfl

@[simp] private theorem swapConfigurationChildren_eq_swapIndex
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

/-- Relabel a packing after both pairs of children have been swapped. -/
def unswapChildren {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) :
    SixPointPacking configuration where
  support := packing.support.map swapChildrenIndexEquiv.toEmbedding
  meets_color color := by
    obtain ⟨label, hlabel⟩ := packing.meets_color color
    exact ⟨swapChildLabel label,
      Finset.mem_map.2 ⟨(color, label), hlabel, by cases label <;> rfl⟩⟩
  radius index := packing.radius ⟨swapChildrenIndexEquiv index,
    swapChildrenIndex_mem_of_mem_map index.2⟩
  same_color_disjoint i j hij hcolor := by
    let i' : packing.support := ⟨swapChildrenIndexEquiv i,
      swapChildrenIndex_mem_of_mem_map i.2⟩
    let j' : packing.support := ⟨swapChildrenIndexEquiv j,
      swapChildrenIndex_mem_of_mem_map j.2⟩
    have hij' : i' ≠ j' := by
      intro heq
      apply hij
      apply Subtype.ext
      exact swapChildrenIndexEquiv.injective (congrArg Subtype.val heq)
    have hcolor' : i'.1.1 = j'.1.1 := by
      simpa [i', j'] using hcolor
    have hp := packing.same_color_disjoint i' j' hij' hcolor'
    simpa [i', j', swapConfigurationChildren_swappedLabel] using hp

private def unswapChildrenSupportEquiv {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) :
    packing.unswapChildren.support ≃ packing.support where
  toFun index := ⟨swapChildrenIndexEquiv index, swapChildrenIndex_mem_of_mem_map index.2⟩
  invFun index := ⟨swapChildrenIndexEquiv index, Finset.mem_map.2 ⟨index, index.2, rfl⟩⟩
  left_inv index := by
    apply Subtype.ext
    exact swapChildrenIndexEquiv_involution index
  right_inv index := by
    apply Subtype.ext
    exact swapChildrenIndexEquiv_involution index

@[simp] private theorem unswapChildrenSupportEquiv_apply_val
    {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration))
    (index : packing.unswapChildren.support) :
    ((unswapChildrenSupportEquiv packing index : packing.support) : SixPointIndex) =
      swapChildrenIndexEquiv index := rfl

@[simp] private theorem unswapChildrenSupportEquiv_symm_apply_val
    {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration))
    (index : packing.support) :
    (((unswapChildrenSupportEquiv packing).symm index : packing.unswapChildren.support) :
      SixPointIndex) = swapChildrenIndexEquiv index := rfl

@[simp] private theorem unswapChildren_radius_eq
    {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration))
    (index : packing.unswapChildren.support) :
    (packing.unswapChildren.radius index : ℝ) =
      packing.radius (unswapChildrenSupportEquiv packing index) := by
  congr 1

private theorem unswapChildren_radius_symm_eq
    {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration))
    (index : packing.support) :
    (packing.unswapChildren.radius ((unswapChildrenSupportEquiv packing).symm index) : ℝ) =
      packing.radius index := by
  rw [unswapChildren_radius_eq]
  exact congrArg (fun supportIndex ↦ (packing.radius supportIndex : ℝ))
    ((unswapChildrenSupportEquiv packing).apply_symm_apply index)

/-- Simultaneously swapping child names leaves the total radius unchanged. -/
theorem unswapChildren_totalRadius {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) :
    packing.unswapChildren.totalRadius = packing.totalRadius := by
  unfold totalRadius
  rw [← Finset.univ_eq_attach, ← Finset.univ_eq_attach]
  apply Fintype.sum_equiv (unswapChildrenSupportEquiv packing)
  intro index
  congr 1

/-- Simultaneously swapping child names leaves the virtual diameter unchanged. -/
theorem unswapChildren_virtualDiameter {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) :
    packing.unswapChildren.virtualDiameter = packing.virtualDiameter := by
  apply le_antisymm
  · unfold virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    simpa only [unswapChildrenSupportEquiv_apply_val, unswapChildren_radius_eq,
      swapConfigurationChildren_swapIndex, virtualDiameter] using
      packing.pair_le_virtualDiameter (unswapChildrenSupportEquiv packing i)
        (unswapChildrenSupportEquiv packing j)
  · unfold virtualDiameter
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    simpa only [unswapChildrenSupportEquiv_symm_apply_val, unswapChildren_radius_symm_eq,
      swapConfigurationChildren_eq_swapIndex, swapChildrenIndexEquiv_involution,
      virtualDiameter] using
      packing.unswapChildren.pair_le_virtualDiameter
        ((unswapChildrenSupportEquiv packing).symm i)
        ((unswapChildrenSupportEquiv packing).symm j)

/-- Simultaneously swapping child names leaves the packing score unchanged. -/
theorem unswapChildren_score {configuration : SixPointConfiguration}
    (packing : SixPointPacking (swapConfigurationChildren configuration)) (s : ℝ) :
    packing.unswapChildren.score s = packing.score s := by
  simp only [score, packing.unswapChildren_totalRadius, packing.unswapChildren_virtualDiameter]

end SixPointPacking

end LeanPool.Besicovitch
