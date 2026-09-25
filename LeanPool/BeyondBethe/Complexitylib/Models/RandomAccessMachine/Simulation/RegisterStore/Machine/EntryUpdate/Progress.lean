/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs

/-!
# Bounded encoded sparse-store update — progress invariant internals

This file isolates the pure list semantics of the entry-update loop. The
invariant relates the processed and remaining portions of the old store to the
entries already emitted by the machine, independently of the tape-level
simulation proof.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Pure semantic progress of a left-to-right sparse-store update.

The output equation is deliberately phrased as a completion equation. Before
the target address is found, completing the emitted prefix requires updating
the remaining suffix. Afterwards, the untouched remaining suffix is copied
verbatim. -/
structure EntryUpdateProgress
    (store : Store) (address newValue : ℕ)
    (processed remaining emitted : Store)
    (found : Bool) (resultCount : ℕ) : Prop where
  /-- The scan decomposition still covers the original store. -/
  store_eq : store = processed ++ remaining
  /-- The flag records exactly whether the processed prefix contains the
  requested address. -/
  found_iff : found = true ↔ address ∈ processed.map Prod.fst
  /-- Completing the emitted prefix produces the abstract sparse-store write. -/
  output_eq :
    emitted ++ (if found = true then remaining
      else RegisterStore.write remaining address newValue) =
      RegisterStore.write store address newValue
  /-- Until the optional final append, the runtime result count equals emitted
  entries plus old entries still remaining. -/
  resultCount_eq : resultCount = emitted.length + remaining.length

/-- Before scanning any entries, the empty emitted prefix satisfies the
progress invariant. -/
theorem entryUpdateProgress_initial_internal
    (store : Store) (address newValue : ℕ) :
    EntryUpdateProgress store address newValue [] store [] false store.length := by
  constructor <;> simp

/-- Copying a nonmatching entry advances all three list frontiers without
changing either the found flag or the result count. -/
theorem EntryUpdateProgress.miss_internal
    {store : Store} {address newValue : ℕ}
    {processed remaining emitted : Store} {entry : Entry}
    {found : Bool} {resultCount : ℕ}
    (h : EntryUpdateProgress store address newValue processed
      (entry :: remaining) emitted found resultCount)
    (hne : entry.1 ≠ address) :
    EntryUpdateProgress store address newValue (processed ++ [entry])
      remaining (emitted ++ [entry]) found resultCount := by
  constructor
  · simpa [List.append_assoc] using h.store_eq
  · simpa [List.map_append, hne, Ne.symm hne] using h.found_iff
  · by_cases hfound : found = true
    · simpa [hfound, List.append_assoc] using h.output_eq
    · simpa [hfound, RegisterStore.write, Ne.symm hne,
        List.append_assoc] using h.output_eq
  · have hcount := h.resultCount_eq
    simp only [List.length_cons] at hcount
    simp only [List.length_append, List.length_singleton]
    omega

/-- Replacing the first matching entry emits the new nonzero pair and records
that the target address has been found. -/
theorem EntryUpdateProgress.replace_internal
    {store : Store} {address newValue : ℕ}
    {processed remaining emitted : Store} {entry : Entry}
    {resultCount : ℕ}
    (h : EntryUpdateProgress store address newValue processed
      (entry :: remaining) emitted false resultCount)
    (haddress : address = entry.1) (hvalue : newValue ≠ 0) :
    EntryUpdateProgress store address newValue (processed ++ [entry])
      remaining (emitted ++ [(address, newValue)]) true resultCount := by
  constructor
  · simpa [List.append_assoc] using h.store_eq
  · simp [List.map_append, haddress]
  · simpa [RegisterStore.write, haddress, hvalue, List.append_assoc]
      using h.output_eq
  · have hcount := h.resultCount_eq
    simp only [List.length_cons] at hcount
    simp only [List.length_append, List.length_singleton]
    omega

/-- Deleting the first matching entry emits nothing for it, records the hit,
and decrements the result count. -/
theorem EntryUpdateProgress.delete_internal
    {store : Store} {address : ℕ}
    {processed remaining emitted : Store} {entry : Entry}
    {resultCount : ℕ}
    (h : EntryUpdateProgress store address 0 processed
      (entry :: remaining) emitted false resultCount)
    (haddress : address = entry.1) :
    EntryUpdateProgress store address 0 (processed ++ [entry]) remaining
      emitted true (resultCount - 1) := by
  constructor
  · simpa [List.append_assoc] using h.store_eq
  · simp [List.map_append, haddress]
  · simpa [RegisterStore.write, haddress] using h.output_eq
  · have hcount := h.resultCount_eq
    simp only [List.length_cons] at hcount
    omega

/-- Once the scan is exhausted after a hit, the emitted store and result count
are already the abstract write result. -/
theorem EntryUpdateProgress.terminal_found_internal
    {store : Store} {address newValue : ℕ}
    {processed emitted : Store} {resultCount : ℕ}
    (h : EntryUpdateProgress store address newValue processed [] emitted true
      resultCount) :
    emitted = RegisterStore.write store address newValue ∧
      resultCount = (RegisterStore.write store address newValue).length := by
  have houtput : emitted = RegisterStore.write store address newValue := by
    simpa using h.output_eq
  exact ⟨houtput, by simpa [houtput] using h.resultCount_eq⟩

/-- An absent address written with zero requires no append; exhaustion already
produces the abstract empty write contribution. -/
theorem EntryUpdateProgress.terminal_zero_internal
    {store : Store} {address : ℕ}
    {processed emitted : Store} {resultCount : ℕ}
    (h : EntryUpdateProgress store address 0 processed [] emitted false
      resultCount) :
    emitted = RegisterStore.write store address 0 ∧
      resultCount = (RegisterStore.write store address 0).length := by
  have houtput : emitted = RegisterStore.write store address 0 := by
    simpa [RegisterStore.write] using h.output_eq
  exact ⟨houtput, by simpa [houtput] using h.resultCount_eq⟩

/-- An absent address written with a nonzero value is completed by one final
append and one result-count increment. -/
theorem EntryUpdateProgress.terminal_append_internal
    {store : Store} {address newValue : ℕ}
    {processed emitted : Store} {resultCount : ℕ}
    (h : EntryUpdateProgress store address newValue processed [] emitted false
      resultCount)
    (hvalue : newValue ≠ 0) :
    emitted ++ [(address, newValue)] =
        RegisterStore.write store address newValue ∧
      resultCount + 1 =
        (RegisterStore.write store address newValue).length := by
  have houtput : emitted ++ [(address, newValue)] =
      RegisterStore.write store address newValue := by
    simpa [RegisterStore.write, hvalue] using h.output_eq
  constructor
  · exact houtput
  · rw [← houtput]
    have hcount := h.resultCount_eq
    simp only [List.length_nil, Nat.add_zero] at hcount
    simp only [List.length_append, List.length_singleton]
    omega

/-- In a store with unique addresses, finding the target in the processed
prefix excludes it from the unprocessed suffix. -/
theorem EntryUpdateProgress.not_mem_remaining_of_found_internal
    {store : Store} {address newValue : ℕ}
    {processed remaining emitted : Store} {found : Bool}
    {resultCount : ℕ}
    (h : EntryUpdateProgress store address newValue processed remaining
      emitted found resultCount)
    (hnodup : AddressesNodup store) (hfound : found = true) :
    address ∉ remaining.map Prod.fst := by
  rw [h.store_eq] at hnodup
  simp only [AddressesNodup, List.map_append] at hnodup
  exact fun hremaining =>
    (List.nodup_append.mp hnodup).2.2 address
      (h.found_iff.mp hfound) address hremaining rfl

end Machine

end RegisterStore

end RAM

end Complexity
