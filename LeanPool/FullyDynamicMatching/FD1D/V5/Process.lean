/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.SquaredCost
import LeanPool.FullyDynamicMatching.FD1D.UniformArrival
import LeanPool.FullyDynamicMatching.FD1D.Realization

/-! # Process -/

namespace FD1D

noncomputable section

open Set MeasureTheory

/-!
# One-step spatial dynamics

This module lifts one transition of the hierarchical count chain to the
actual labeled supply configuration. The selected label is retained, so
replacing its coordinate and dyadic leaf gives a pathwise update rather than
only a count-law coupling.
-/

namespace V5.Dynamics

variable {L m : ℕ}

/-- The v5 deletion-mass tree, re-exported at the spatial-dynamics boundary. -/
abbrev stateDyadicMass (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : DyadicMass L :=
  Transport.stateDyadicMass a x

theorem stateDyadicMass_isProbability
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    (stateDyadicMass a x).IsProbability :=
  Transport.stateDyadicMass_isProbability a ha hm x

theorem stateDyadicMass_leafMass_eq_deletionRule
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (stateDyadicMass a x).leafMass w =
      (deletionRule a ha hm).prob x w :=
  Transport.stateDyadicMass_leafMass_eq_deletionRule a ha hm x w

/-- The concrete supply label selected from the hierarchical dyadic mass. -/
def selectedSupplyLabel (a : ℝ) (C : SupplyConfiguration L m)
    (fallback : Fin m) (u : ℝ) : Fin m :=
  C.selectedSupplyIndex (stateDyadicMass a C.countState) fallback u

/-- The leaf actually deleted by the concrete label selection. -/
def selectedDeletedLeaf (a : ℝ) (C : SupplyConfiguration L m)
    (fallback : Fin m) (u : ℝ) : DyadicNode L :=
  C.leaf (selectedSupplyLabel a C fallback u)

/--
One actual hierarchical-policy step: match demand `u` to the selected supply
label and replace that same label by the replenishment coordinate `v`.
-/
def actualStep (a : ℝ) (C : SupplyConfiguration L m)
    (fallback : Fin m) (u v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    SupplyConfiguration L m where
  location := Function.update C.location
    (selectedSupplyLabel a C fallback u) v
  leaf := Function.update C.leaf
    (selectedSupplyLabel a C fallback u)
    (DyadicMass.uniformArrivalLeaf L v)
  location_mem_unit := by
    intro j
    by_cases hj : j = selectedSupplyLabel a C fallback u
    · subst j
      simpa using hv
    · simpa [Function.update_of_ne hj] using C.location_mem_unit j
  location_mem_cell := by
    intro j
    by_cases hj : j = selectedSupplyLabel a C fallback u
    · subst j
      simpa using DyadicMass.uniformArrival_mem_dyadicCell L hv
    · simpa [Function.update_of_ne hj] using C.location_mem_cell j

@[simp]
theorem actualStep_location_selected
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m)
    (u v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    (actualStep a C fallback u v hv).location
        (selectedSupplyLabel a C fallback u) = v := by
  simp [actualStep]

@[simp]
theorem actualStep_leaf_selected
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m)
    (u v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    (actualStep a C fallback u v hv).leaf
        (selectedSupplyLabel a C fallback u) =
      DyadicMass.uniformArrivalLeaf L v := by
  simp [actualStep]

theorem actualStep_location_of_ne
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m)
    (u v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) (j : Fin m)
    (hj : j ≠ selectedSupplyLabel a C fallback u) :
    (actualStep a C fallback u v hv).location j = C.location j := by
  simp [actualStep, Function.update_of_ne hj]

theorem actualStep_leaf_of_ne
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m)
    (u v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) (j : Fin m)
    (hj : j ≠ selectedSupplyLabel a C fallback u) :
    (actualStep a C fallback u v hv).leaf j = C.leaf j := by
  simp [actualStep, Function.update_of_ne hj]

/-- Replacing one labeled leaf changes every fiber count by the corresponding
delete/arrive indicators. -/
private theorem leafCount_update
    (C : SupplyConfiguration L m) (j : Fin m)
    (arrived i : DyadicNode L) :
    (Finset.univ.filter fun k : Fin m =>
        Function.update C.leaf j arrived k = i).card =
      C.leafCount i + (if i = arrived then 1 else 0) -
        (if i = C.leaf j then 1 else 0) := by
  classical
  let rest : Finset (Fin m) := Finset.univ.erase j
  let restCount : ℕ :=
    (rest.filter fun k : Fin m => C.leaf k = i).card
  have huniv : Finset.univ = insert j rest := by
    exact (Finset.insert_erase (Finset.mem_univ j)).symm
  have hjrest : j ∉ rest := by
    simp [rest]
  have hjfilter :
      j ∉ rest.filter fun k : Fin m => C.leaf k = i := by
    simp [hjrest]
  have hrest :
      (rest.filter fun k : Fin m =>
          Function.update C.leaf j arrived k = i) =
        rest.filter fun k : Fin m => C.leaf k = i := by
    apply Finset.filter_congr
    intro k hk
    have hkj : k ≠ j := by
      exact (Finset.mem_erase.mp hk).1
    rw [Function.update_of_ne hkj]
  have hnew :
      (Finset.univ.filter fun k : Fin m =>
          Function.update C.leaf j arrived k = i).card =
        restCount + (if arrived = i then 1 else 0) := by
    rw [huniv, Finset.filter_insert, hrest]
    by_cases harrived : arrived = i
    · simp [harrived, restCount, hjfilter]
    · simp [harrived, restCount]
  have hold :
      C.leafCount i =
        restCount + (if C.leaf j = i then 1 else 0) := by
    unfold SupplyConfiguration.leafCount
    rw [huniv, Finset.filter_insert]
    by_cases hold : C.leaf j = i
    · simp [hold, restCount, hjfilter]
    · simp [hold, restCount]
  rw [hnew, hold]
  by_cases harrived : arrived = i
  · have hiarrived : i = arrived := harrived.symm
    by_cases hold : C.leaf j = i
    · have hiold : i = C.leaf j := hold.symm
      rw [ite_eq_left harrived, ite_eq_left hiarrived, ite_eq_left hold, ite_eq_left hiold]
      omega
    · have hiold : i ≠ C.leaf j := fun h => hold h.symm
      rw [ite_eq_left harrived, ite_eq_left hiarrived, ite_eq_right hold, ite_eq_right hiold]
      omega
  · have hiarrived : i ≠ arrived := fun h => harrived h.symm
    by_cases hold : C.leaf j = i
    · have hiold : i = C.leaf j := hold.symm
      rw [ite_eq_right harrived, ite_eq_right hiarrived, ite_eq_left hold, ite_eq_left hiold]
      omega
    · have hiold : i ≠ C.leaf j := fun h => hold h.symm
      rw [ite_eq_right harrived, ite_eq_right hiarrived, ite_eq_right hold, ite_eq_right hiold]
      omega

/--
Replace the fixed representative of an occupied deletion leaf by an arbitrary
point certified to lie in the arrival leaf. On an empty deletion leaf this
is a no-op, matching `InventoryState.move`.
-/
def actualLeafStep (C : SupplyConfiguration L m) (fallback : Fin m)
    (deleted arrived : DyadicNode L) (v : ℝ)
    (hv : v ∈ dyadicCell arrived) : SupplyConfiguration L m :=
  if h : ∃ j, C.leaf j = deleted then
    { location := Function.update C.location
        (C.representative fallback deleted) v
      leaf := Function.update C.leaf
        (C.representative fallback deleted) arrived
      location_mem_unit := by
        intro j
        by_cases hj : j = C.representative fallback deleted
        · subst j
          simpa using dyadicCell_subset_unit arrived hv
        · simpa [Function.update_of_ne hj] using C.location_mem_unit j
      location_mem_cell := by
        intro j
        by_cases hj : j = C.representative fallback deleted
        · subst j
          simpa using hv
        · simpa [Function.update_of_ne hj] using C.location_mem_cell j }
  else C

theorem actualLeafStep_of_occupied
    (C : SupplyConfiguration L m) (fallback : Fin m)
    (deleted arrived : DyadicNode L) (v : ℝ)
    (hv : v ∈ dyadicCell arrived)
    (h : ∃ j, C.leaf j = deleted) :
    actualLeafStep C fallback deleted arrived v hv =
      { location := Function.update C.location
          (C.representative fallback deleted) v
        leaf := Function.update C.leaf
          (C.representative fallback deleted) arrived
        location_mem_unit := by
          intro j
          by_cases hj : j = C.representative fallback deleted
          · subst j
            simpa using dyadicCell_subset_unit arrived hv
          · simpa [Function.update_of_ne hj] using C.location_mem_unit j
        location_mem_cell := by
          intro j
          by_cases hj : j = C.representative fallback deleted
          · subst j
            simpa using hv
          · simpa [Function.update_of_ne hj] using C.location_mem_cell j } := by
  rw [actualLeafStep, dite_eq_left h]

/-- The leaf-conditioned spatial update projects exactly to the finite count
move, including the zero-probability empty-deletion case. -/
@[simp]
theorem actualLeafStep_countState
    (C : SupplyConfiguration L m) (fallback : Fin m)
    (deleted arrived : DyadicNode L) (v : ℝ)
    (hv : v ∈ dyadicCell arrived) :
    (actualLeafStep C fallback deleted arrived v hv).countState =
      InventoryState.move C.countState deleted arrived := by
  classical
  by_cases h : ∃ j, C.leaf j = deleted
  · rw [actualLeafStep, dite_eq_left h]
    have hleaf :
        C.leaf (C.representative fallback deleted) = deleted :=
      C.representative_leaf fallback deleted h
    have hpos : 0 < C.countState.1 deleted := by
      change 0 < (Finset.univ.filter fun j : Fin m =>
        C.leaf j = deleted).card
      obtain ⟨j, hj⟩ := h
      exact Finset.card_pos.mpr ⟨j, by simp [hj]⟩
    apply InventoryState.ext
    intro i
    rw [InventoryState.move_apply_of_pos C.countState hpos]
    change
      (Finset.univ.filter fun k : Fin m =>
        Function.update C.leaf (C.representative fallback deleted)
          arrived k = i).card =
        C.leafCount i + (if i = arrived then 1 else 0) -
          (if i = deleted then 1 else 0)
    simpa [hleaf] using
      (leafCount_update C (C.representative fallback deleted) arrived i)
  · rw [actualLeafStep, dite_eq_right h]
    have hempty : C.countState.1 deleted = 0 := by
      change (Finset.univ.filter fun j : Fin m =>
        C.leaf j = deleted).card = 0
      rw [Finset.card_eq_zero]
      simpa only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies,
        not_exists] using h
    exact (InventoryState.move_empty C.countState hempty).symm

/-- The selected concrete slot certifies that its old leaf is occupied. -/
theorem selectedDeletedLeaf_count_pos
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m) (u : ℝ) :
    0 < C.countState.1 (selectedDeletedLeaf a C fallback u) := by
  classical
  change 0 < (Finset.univ.filter fun j : Fin m =>
    C.leaf j = C.leaf (selectedSupplyLabel a C fallback u)).card
  exact Finset.card_pos.mpr
    ⟨selectedSupplyLabel a C fallback u, by simp⟩

/--
The spatial update projects exactly to deletion of the selected slot's old
leaf followed by insertion of the uniform-arrival leaf.
-/
@[simp]
theorem actualStep_countState
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m)
    (u v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    (actualStep a C fallback u v hv).countState =
      InventoryState.move C.countState
        (selectedDeletedLeaf a C fallback u)
        (DyadicMass.uniformArrivalLeaf L v) := by
  apply InventoryState.ext
  intro i
  rw [InventoryState.move_apply_of_pos C.countState
    (selectedDeletedLeaf_count_pos a C fallback u)]
  exact leafCount_update C (selectedSupplyLabel a C fallback u)
    (DyadicMass.uniformArrivalLeaf L v) i

/--
Away from the null boundary `u = 0`, the old leaf of the selected concrete
slot is exactly the leaf selected by the hierarchical mass tree.
-/
theorem selectedDeletedLeaf_eq_selectedIndex
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (C : SupplyConfiguration L m) (fallback : Fin m)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hu0 : u ≠ 0) :
    selectedDeletedLeaf a C fallback u =
      (stateDyadicMass a C.countState).selectedIndex u := by
  apply C.selectedSupplyIndex_leaf_of_ne_zero
    (stateDyadicMass a C.countState)
    (stateDyadicMass_isProbability a ha hm C.countState)
    (C.supports_of_deletionRule
      (stateDyadicMass a C.countState)
      (deletionRule a ha hm)
      (stateDyadicMass_leafMass_eq_deletionRule
        a ha hm C.countState))
    fallback hu hu0

/-- Off the null demand boundary, the continuous-coordinate update is exactly
the corresponding leaf-conditioned update. -/
theorem actualStep_eq_actualLeafStep
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (C : SupplyConfiguration L m) (fallback : Fin m)
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hu0 : u ≠ 0)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    actualStep a C fallback u v hv =
      actualLeafStep C fallback
        ((stateDyadicMass a C.countState).selectedIndex u)
        (DyadicMass.uniformArrivalLeaf L v) v
        (DyadicMass.uniformArrival_mem_dyadicCell L hv) := by
  have hselected :
      C.leaf
          (C.representative fallback
            ((stateDyadicMass a C.countState).selectedIndex u)) =
        (stateDyadicMass a C.countState).selectedIndex u := by
    simpa [selectedDeletedLeaf, selectedSupplyLabel,
      SupplyConfiguration.selectedSupplyIndex] using
      selectedDeletedLeaf_eq_selectedIndex
        a ha hm C fallback hu hu0
  have hoccupied :
      ∃ j, C.leaf j =
        (stateDyadicMass a C.countState).selectedIndex u :=
    ⟨C.representative fallback
      ((stateDyadicMass a C.countState).selectedIndex u), hselected⟩
  rw [actualLeafStep, dite_eq_left hoccupied]
  rfl

/-- Pathwise cost of the actual match made in one hierarchical step. -/
def actualStepCost (a : ℝ) (C : SupplyConfiguration L m)
    (fallback : Fin m) (u : ℝ) : ℝ :=
  |C.location (selectedSupplyLabel a C fallback u) - u|

theorem actualStepCost_eq_selectedSupplyPoint
    (a : ℝ) (C : SupplyConfiguration L m)
    (fallback : Fin m) (u : ℝ) :
    actualStepCost a C fallback u =
      |C.selectedSupplyPoint (stateDyadicMass a C.countState)
          fallback u - u| :=
  rfl

/-- Integrating the pathwise one-step cost is exactly the existing configured
matching-cost functional. -/
theorem integral_actualStepCost_eq_expectedActualDistance
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m) :
    ∫ u in Icc (0 : ℝ) 1, actualStepCost a C fallback u =
      C.expectedActualDistance (stateDyadicMass a C.countState) fallback := by
  rfl

/-- Squared pathwise cost of the actual v5 match. -/
def actualStepSquaredCost (a : ℝ) (C : SupplyConfiguration L m)
    (fallback : Fin m) (u : ℝ) : ℝ :=
  (C.location (selectedSupplyLabel a C fallback u) - u) ^ 2

theorem actualStepSquaredCost_eq_selectedSupplyPoint
    (a : ℝ) (C : SupplyConfiguration L m)
    (fallback : Fin m) (u : ℝ) :
    actualStepSquaredCost a C fallback u =
      (C.selectedSupplyPoint (stateDyadicMass a C.countState)
        fallback u - u) ^ 2 :=
  rfl

theorem integral_actualStepSquaredCost_eq_expected
    (a : ℝ) (C : SupplyConfiguration L m) (fallback : Fin m) :
    ∫ u in Icc (0 : ℝ) 1, actualStepSquaredCost a C fallback u =
      Transport.expectedActualSquaredDistance C
        (stateDyadicMass a C.countState) fallback := by
  rfl

/-- The actual one-period expected distance of a concrete configuration. -/
def actualConfigurationCost (a : ℝ) (hm : 0 < m)
    (C : SupplyConfiguration L m) : ℝ :=
  C.expectedActualDistance (stateDyadicMass a C.countState)
    (SupplyConfiguration.canonicalFallback hm)

/-- The actual one-period expected squared distance. -/
def actualConfigurationSquaredCost (a : ℝ) (hm : 0 < m)
    (C : SupplyConfiguration L m) : ℝ :=
  Transport.expectedActualSquaredDistance C
    (stateDyadicMass a C.countState)
    (SupplyConfiguration.canonicalFallback hm)

/--
Selecting a leaf by the demand coordinate and adding an independent uniform
arrival leaf produces exactly the v5 finite count transition.
-/
theorem configured_transition_eq_kernel
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (C : SupplyConfiguration L m)
    (y : InventoryState (DyadicNode L) m) :
    (∑ deleted, ∑ arrived,
      if InventoryState.move C.countState deleted arrived = y then
        ((stateDyadicMass a C.countState).selectedIndexLaw
          (stateDyadicMass_isProbability a ha hm C.countState)).mass deleted *
          (1 / Fintype.card (DyadicNode L) : ℝ)
      else 0) =
      kernel a ha hm C.countState y := by
  exact C.selectedIndex_transition_eq_kernel
    (stateDyadicMass a C.countState)
    (stateDyadicMass_isProbability a ha hm C.countState)
    (deletionRule a ha hm)
    (stateDyadicMass_leafMass_eq_deletionRule a ha hm C.countState)
    y

end V5.Dynamics

end

end FD1D
