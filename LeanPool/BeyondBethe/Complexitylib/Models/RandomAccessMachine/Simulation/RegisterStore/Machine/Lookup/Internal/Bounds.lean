/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Defs

/-!
# Reusable sparse-register lookup -- reset bounds
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

theorem entryLookupEntryWidth_le_storeWidth_internal
    (store : Store) (address : ℕ) (entry : Entry) (hentry : entry ∈ store) :
    entryLookupEntryWidth entry address ≤
      entryLookupStoreWidth address store := by
  induction store with
  | nil => simp at hentry
  | cons current rest ih =>
      simp only [List.mem_cons] at hentry
      simp only [entryLookupStoreWidth]
      rcases hentry with rfl | hentry
      · exact le_max_left _ _
      · exact le_trans (ih hentry) (le_max_right _ _)

theorem entryLookupEntryWidth_le_resetWidth_internal
    (store : Store) (address : ℕ) (entry : Entry) (hentry : entry ∈ store) :
    entryLookupEntryWidth entry address ≤
      entryLookupResetWidth store address :=
  le_trans (entryLookupEntryWidth_le_storeWidth_internal store address entry hentry)
    (le_max_right _ _)

theorem entryLookupAddressWidth_le_resetWidth_internal
    (store : Store) (address : ℕ) :
    address.bits.length ≤ entryLookupResetWidth store address := by
  apply le_trans _ (le_max_right _ _)
  induction store with
  | nil => exact le_rfl
  | cons entry rest ih =>
      exact le_trans ih (le_max_right _ _)

theorem entryLookupRemainingWidth_le_resetWidth_internal
    (store : Store) (address remaining : ℕ) (hle : remaining ≤ store.length) :
    remaining.bits.length ≤ entryLookupResetWidth store address := by
  have hsize := Nat.size_le_size hle
  have hbits : remaining.bits.length ≤ store.length.bits.length := by
    simpa only [Nat.size_eq_bits_len] using hsize
  exact le_trans hbits (le_max_left _ _)

theorem entryLookupEntryAddressWidth_le_internal
    (entry : Entry) (address : ℕ) :
    entry.1.bits.length ≤ entryLookupEntryWidth entry address := by
  simp only [entryLookupEntryWidth]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem entryLookupEntryValueWidth_le_internal
    (entry : Entry) (address : ℕ) :
    entry.2.bits.length ≤ entryLookupEntryWidth entry address := by
  simp only [entryLookupEntryWidth]
  exact le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))

theorem entryLookupEntryAddressCounterWidth_le_internal
    (entry : Entry) (address : ℕ) :
    bitlen entry.1 ≤ entryLookupEntryWidth entry address := by
  simp only [entryLookupEntryWidth]
  exact le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem entryLookupEntryValueCounterWidth_le_internal
    (entry : Entry) (address : ℕ) :
    bitlen entry.2 ≤ entryLookupEntryWidth entry address := by
  simp only [entryLookupEntryWidth]
  exact le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))))

theorem entryLookupResultWidth_le_internal (entry : Entry) (address : ℕ) :
    1 ≤ entryLookupEntryWidth entry address := by
  simp only [entryLookupEntryWidth]
  exact le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))))

end Machine

end RegisterStore

end RAM

end Complexity
