/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Bounds
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

/-!
# Reusable sparse-register lookup -- reset certificates
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem matched_mem_store
    (tapes : EntryScanTapes n) (store scanned : Store)
    (matched : Entry) (rest : Store) (queryBits : List Bool)
    (initialWork hitBase finalWork : Fin n → Tape)
    (hfound : EntryScanFound tapes store scanned matched rest queryBits
      initialWork hitBase finalWork) :
    matched ∈ store := by
  rw [hfound.store_eq]
  simp

private theorem found_reset_content
    (tapes : EntryLookupRestoreTapes n) (store scanned : Store)
    (matched : Entry) (rest : Store) (address : ℕ)
    (initialWork hitBase finalWork : Fin n → Tape)
    (hfound : EntryScanFound tapes.scan store scanned matched rest address.bits
      initialWork hitBase finalWork) :
    ∀ i, i ∈ entryLookupResetTargets tapes →
      (finalWork i).HasBinaryContent
        (entryLookupFoundBits tapes matched (rest.length + 1) address i) := by
  obtain ⟨iterationWork, hreadable⟩ := hfound.hit.readable
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · change (finalWork tapes.scan.entry.address).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.entry.address)
    simpa only [entryLookupFoundBits_zero] using hreadable.address
  · change (finalWork tapes.scan.entry.value).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.entry.value)
    simpa only [entryLookupFoundBits_one] using! hreadable.value.2
  · change (finalWork tapes.scan.entry.addressCounter).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.entry.addressCounter)
    simpa only [entryLookupFoundBits_two] using!
      hreadable.addressCounter.2
  · change (finalWork tapes.scan.entry.addressWidth).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.entry.addressWidth)
    simpa only [entryLookupFoundBits_three] using!
      hreadable.addressWidth.2.hasBinaryContent
  · change (finalWork tapes.scan.entry.valueCounter).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.entry.valueCounter)
    simpa only [entryLookupFoundBits_four] using!
      hreadable.valueCounter.2
  · change (finalWork tapes.scan.entry.valueWidth).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.entry.valueWidth)
    simpa only [entryLookupFoundBits_five] using!
      hreadable.valueWidth.2.hasBinaryContent
  · change (finalWork tapes.scan.entry.result).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.entry.result)
    simpa only [entryLookupFoundBits_six] using
      hreadable.result.hasBinaryContent
  · change (finalWork tapes.scan.entry.query).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.entry.query)
    simpa only [entryLookupFoundBits_seven] using hreadable.query
  · change (finalWork tapes.scan.count).HasBinaryContent
      (entryLookupFoundBits tapes matched (rest.length + 1) address
        tapes.scan.count)
    simpa only [EntryLookupRestoreTapes.scan_count,
      entryLookupFoundBits_eight] using
      hfound.count.2.hasBinaryContent

private theorem found_reset_start
    (tapes : EntryLookupRestoreTapes n) (store scanned : Store)
    (matched : Entry) (rest : Store) (address : ℕ)
    (initialWork hitBase finalWork : Fin n → Tape)
    (hfound : EntryScanFound tapes.scan store scanned matched rest address.bits
      initialWork hitBase finalWork) :
    ∀ i, i ∈ entryLookupResetTargets tapes →
      (finalWork i).cells 0 = Γ.start := by
  obtain ⟨iterationWork, hreadable⟩ := hfound.hit.readable
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · exact hreadable.addressStart
  · exact hreadable.valueStart
  · exact hreadable.addressCounterStart
  · exact hreadable.addressWidth.1
  · exact hreadable.valueCounterStart
  · exact hreadable.valueWidth.1
  · exact hreadable.resultStart
  · exact hreadable.queryStart
  · exact hfound.count.1

private theorem found_reset_width
    (tapes : EntryLookupRestoreTapes n) (store scanned : Store)
    (matched : Entry) (rest : Store) (address : ℕ)
    (initialWork hitBase finalWork : Fin n → Tape)
    (hfound : EntryScanFound tapes.scan store scanned matched rest address.bits
      initialWork hitBase finalWork) :
    ∀ i, i ∈ entryLookupResetTargets tapes →
      (entryLookupFoundBits tapes matched (rest.length + 1) address i).length ≤
        entryLookupResetWidth store address := by
  have hmem := matched_mem_store tapes.scan store scanned matched rest
    address.bits initialWork hitBase finalWork hfound
  have hentry := entryLookupEntryWidth_le_resetWidth_internal store address
    matched hmem
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.entry.address).length ≤ _
    rw [entryLookupFoundBits_zero]
    exact le_trans (entryLookupEntryAddressWidth_le_internal matched address)
      hentry
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.entry.value).length ≤ _
    rw [entryLookupFoundBits_one]
    exact le_trans (entryLookupEntryValueWidth_le_internal matched address)
      hentry
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.entry.addressCounter).length ≤ _
    rw [entryLookupFoundBits_two]
    simpa using le_trans
      (entryLookupEntryAddressCounterWidth_le_internal matched address) hentry
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.entry.addressWidth).length ≤ _
    rw [entryLookupFoundBits_three]
    simp
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.entry.valueCounter).length ≤ _
    rw [entryLookupFoundBits_four]
    simpa using le_trans
      (entryLookupEntryValueCounterWidth_le_internal matched address) hentry
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.entry.valueWidth).length ≤ _
    rw [entryLookupFoundBits_five]
    simp
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.entry.result).length ≤ _
    rw [entryLookupFoundBits_six]
    simpa using le_trans (entryLookupResultWidth_le_internal matched address)
      hentry
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.entry.query).length ≤ _
    rw [entryLookupFoundBits_seven]
    exact entryLookupAddressWidth_le_resetWidth_internal store address
  · change (entryLookupFoundBits tapes matched (rest.length + 1) address
      tapes.scan.count).length ≤ _
    simp only [EntryLookupRestoreTapes.scan_count,
      entryLookupFoundBits_eight]
    apply entryLookupRemainingWidth_le_resetWidth_internal
    rw [hfound.store_eq]
    simp

private theorem miss_reset_content
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork readyBase finalWork : Fin n → Tape)
    (hmiss : EntryScanMiss tapes.scan store address.bits initialWork readyBase
      finalWork) :
    ∀ i, i ∈ entryLookupResetTargets tapes →
      (finalWork i).HasBinaryContent (entryLookupMissBits tapes address i) := by
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · change (finalWork tapes.scan.entry.address).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.entry.address)
    rw [entryLookupMissBits_zero]
    exact hmiss.ready.address.2
  · change (finalWork tapes.scan.entry.value).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.entry.value)
    rw [entryLookupMissBits_one]
    exact hmiss.ready.value.2
  · change (finalWork tapes.scan.entry.addressCounter).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.entry.addressCounter)
    rw [entryLookupMissBits_two]
    exact hmiss.ready.addressCounter.2.hasBinaryContent
  · change (finalWork tapes.scan.entry.addressWidth).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.entry.addressWidth)
    rw [entryLookupMissBits_three]
    exact hmiss.ready.addressWidth.2.hasBinaryContent
  · change (finalWork tapes.scan.entry.valueCounter).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.entry.valueCounter)
    rw [entryLookupMissBits_four]
    exact hmiss.ready.valueCounter.2.hasBinaryContent
  · change (finalWork tapes.scan.entry.valueWidth).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.entry.valueWidth)
    rw [entryLookupMissBits_five]
    exact hmiss.ready.valueWidth.2.hasBinaryContent
  · change (finalWork tapes.scan.entry.result).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.entry.result)
    rw [entryLookupMissBits_six]
    exact hmiss.ready.result.2
  · change (finalWork tapes.scan.entry.query).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.entry.query)
    rw [entryLookupMissBits_seven]
    exact hmiss.ready.query.hasBinaryContent
  · change (finalWork tapes.scan.count).HasBinaryContent
      (entryLookupMissBits tapes address tapes.scan.count)
    simpa only [EntryLookupRestoreTapes.scan_count,
      entryLookupMissBits_eight] using! hmiss.count.2.hasBinaryContent

private theorem miss_reset_start
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork readyBase finalWork : Fin n → Tape)
    (hmiss : EntryScanMiss tapes.scan store address.bits initialWork readyBase
      finalWork) :
    ∀ i, i ∈ entryLookupResetTargets tapes →
      (finalWork i).cells 0 = Γ.start := by
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · exact hmiss.ready.addressStart
  · exact hmiss.ready.valueStart
  · exact hmiss.ready.addressCounter.1
  · exact hmiss.ready.addressWidth.1
  · exact hmiss.ready.valueCounter.1
  · exact hmiss.ready.valueWidth.1
  · exact hmiss.ready.resultStart
  · exact hmiss.ready.queryStart
  · exact hmiss.count.1

private theorem miss_reset_width
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ) :
    ∀ i, i ∈ entryLookupResetTargets tapes →
      (entryLookupMissBits tapes address i).length ≤
        entryLookupResetWidth store address := by
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · change (entryLookupMissBits tapes address
      tapes.scan.entry.address).length ≤ _
    rw [entryLookupMissBits_zero]
    simp
  · change (entryLookupMissBits tapes address
      tapes.scan.entry.value).length ≤ _
    rw [entryLookupMissBits_one]
    simp
  · change (entryLookupMissBits tapes address
      tapes.scan.entry.addressCounter).length ≤ _
    rw [entryLookupMissBits_two]
    simp
  · change (entryLookupMissBits tapes address
      tapes.scan.entry.addressWidth).length ≤ _
    rw [entryLookupMissBits_three]
    simp
  · change (entryLookupMissBits tapes address
      tapes.scan.entry.valueCounter).length ≤ _
    rw [entryLookupMissBits_four]
    simp
  · change (entryLookupMissBits tapes address
      tapes.scan.entry.valueWidth).length ≤ _
    rw [entryLookupMissBits_five]
    simp
  · change (entryLookupMissBits tapes address
      tapes.scan.entry.result).length ≤ _
    rw [entryLookupMissBits_six]
    simp
  · change (entryLookupMissBits tapes address
      tapes.scan.entry.query).length ≤ _
    rw [entryLookupMissBits_seven]
    exact entryLookupAddressWidth_le_resetWidth_internal store address
  · change (entryLookupMissBits tapes address tapes.scan.count).length ≤ _
    simp only [EntryLookupRestoreTapes.scan_count,
      entryLookupMissBits_eight]
    simp

/-- Every semantic scanner result determines exact bounded contents for all
nine reset targets. -/
theorem EntryLookupResult.resetReady_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hresult : EntryLookupResult tapes.scan store address initialWork
      finalWork) :
    EntryLookupResetReady tapes store address finalWork := by
  rcases hresult.outcome with hfound | hmiss
  · rcases hfound with ⟨scanned, matched, rest, hitBase, hfound⟩
    exact ⟨entryLookupFoundBits tapes matched (rest.length + 1) address,
      found_reset_content tapes store scanned matched rest address initialWork
        hitBase finalWork hfound,
      found_reset_start tapes store scanned matched rest address initialWork
        hitBase finalWork hfound,
      found_reset_width tapes store scanned matched rest address initialWork
        hitBase finalWork hfound,
      hresult.parked⟩
  · rcases hmiss with ⟨readyBase, hmiss⟩
    exact ⟨entryLookupMissBits tapes address,
      miss_reset_content tapes store address initialWork readyBase finalWork
        hmiss,
      miss_reset_start tapes store address initialWork readyBase finalWork
        hmiss,
      miss_reset_width tapes store address,
      hresult.parked⟩

end Machine

end RegisterStore

end RAM

end Complexity
