/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Spatial

/-! # Realization -/

namespace FD1D

noncomputable section

open Set

/-!
# Realizing fixed-total count states by spatial configurations

Every unit of a count vector is represented by one slot in the sigma type
`Σ i, Fin (x i)`.  An equivalence with `Fin m` enumerates those slots, and
placing each enumerated point at its cell's left endpoint gives an exact
spatial realization.
-/

namespace SupplyConfiguration

variable {L m : ℕ}

/-- One distinguishable slot for every unit of inventory in every leaf. -/
private abbrev CountSlot (x : InventoryState (DyadicNode L) m) :=
  Σ i : DyadicNode L, Fin (x.1 i)

/-- Enumerate all count slots by the `m` supply labels. -/
private noncomputable def countSlotEquiv
    (x : InventoryState (DyadicNode L) m) :
    Fin m ≃ CountSlot x :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_sigma]
    simpa using x.2.symm)

/-- The leaf label obtained by forgetting which copy of a count slot was used. -/
private noncomputable def countAssignment
    (x : InventoryState (DyadicNode L) m) (j : Fin m) :
    DyadicNode L :=
  (countSlotEquiv x j).1

/-- A fiber of the slot projection consists of exactly the slots at that leaf. -/
private def countSlotFiberEquiv
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    {s : CountSlot x // s.1 = i} ≃ Fin (x.1 i) where
  toFun s :=
    Fin.cast
      (congrArg (fun k => x.1 k) s.2)
      s.1.2
  invFun k :=
    ⟨⟨i, k⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨k, slot⟩, hki⟩
    dsimp at hki
    subst k
    rfl
  right_inv _ := rfl

/-- The assignment fiber is the corresponding fiber of the slot projection. -/
private noncomputable def countAssignmentFiberSlotEquiv
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    ↥(Finset.univ.filter fun j : Fin m => countAssignment x j = i) ≃
      {s : CountSlot x // s.1 = i} where
  toFun j :=
    ⟨countSlotEquiv x j.1, by
      simpa [countAssignment] using (Finset.mem_filter.mp j.2).2⟩
  invFun s :=
    ⟨(countSlotEquiv x).symm s.1, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (countSlotEquiv x ((countSlotEquiv x).symm s.1)).1 = i
      rw [Equiv.apply_symm_apply]
      exact s.2⟩
  left_inv j := by
    apply Subtype.ext
    exact (countSlotEquiv x).symm_apply_apply j.1
  right_inv s := by
    apply Subtype.ext
    exact (countSlotEquiv x).apply_symm_apply s.1

/-- The labels assigned to one leaf are equivalent to that leaf's count slots. -/
private noncomputable def countAssignmentFiberEquiv
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    ↥(Finset.univ.filter fun j : Fin m => countAssignment x j = i) ≃
      Fin (x.1 i) :=
  (countAssignmentFiberSlotEquiv x i).trans (countSlotFiberEquiv x i)

/-- The slot enumeration has exactly the prescribed fiber cardinalities. -/
private theorem countAssignment_fiber_card
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    (Finset.univ.filter fun j : Fin m => countAssignment x j = i).card =
      x.1 i := by
  rw [← Fintype.card_coe
    (Finset.univ.filter fun j : Fin m => countAssignment x j = i)]
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (countAssignmentFiberEquiv x i)

/--
The canonical spatial realization of a fixed-total leaf count state.
Every point is placed at the left endpoint of its declared dyadic cell.
-/
noncomputable def ofCountState
    (x : InventoryState (DyadicNode L) m) :
    SupplyConfiguration L m where
  location j := dyadicCellLeft (countAssignment x j)
  leaf j := countAssignment x j
  location_mem_unit j :=
    dyadicCell_subset_unit (countAssignment x j) (by
      exact ⟨le_rfl, le_add_of_nonneg_right (dyadicCellWidth_pos L).le⟩)
  location_mem_cell j :=
    ⟨le_rfl, le_add_of_nonneg_right (dyadicCellWidth_pos L).le⟩

@[simp]
theorem ofCountState_location
    (x : InventoryState (DyadicNode L) m) (j : Fin m) :
    (ofCountState x).location j =
      dyadicCellLeft ((ofCountState x).leaf j) :=
  rfl

@[simp]
theorem ofCountState_leafCount
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    (ofCountState x).leafCount i = x.1 i := by
  change
    (Finset.univ.filter fun j : Fin m => countAssignment x j = i).card =
      x.1 i
  exact countAssignment_fiber_card x i

/-- The canonical spatial realization projects back to the original state. -/
@[simp]
theorem ofCountState_countState
    (x : InventoryState (DyadicNode L) m) :
    (ofCountState x).countState = x := by
  apply InventoryState.ext
  intro i
  exact ofCountState_leafCount x i

/-- Every fixed-total leaf count state has an exact spatial realization. -/
theorem exists_countState_eq
    (x : InventoryState (DyadicNode L) m) :
    ∃ C : SupplyConfiguration L m, C.countState = x :=
  ⟨ofCountState x, ofCountState_countState x⟩

/-- A canonical total representative fallback whenever the inventory is nonempty. -/
def canonicalFallback (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

@[simp]
theorem canonicalFallback_val (hm : 0 < m) :
    (canonicalFallback hm).val = 0 :=
  rfl

end SupplyConfiguration

end

end FD1D
