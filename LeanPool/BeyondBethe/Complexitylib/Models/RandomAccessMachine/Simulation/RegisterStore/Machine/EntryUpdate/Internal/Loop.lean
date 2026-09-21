/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Progress
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Inv

/-!
# Bounded encoded sparse-store update — loop invariant internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- Tape and list semantics carried between controller iterations. -/
structure EntryUpdateLoopInv (tapes : EntryUpdateTapes n)
    (store : Store) (address newValue : ℕ)
    (processed remaining emitted : Store) (found : Bool)
    (resultCount : ℕ) (initialWork work : Fin n → Tape) : Prop where
  progress : EntryUpdateProgress store address newValue processed remaining
    emitted found resultCount
  ready : EntryScanReady tapes.entry (remaining.flatMap Entry.encode)
    address.bits work work
  replacement : (work tapes.replacement).HasBinaryNat newValue
  replacement_eq : work tapes.replacement = initialWork tapes.replacement
  remainingCount : (work tapes.remaining).HasBinaryNat remaining.length
  foundCount : (work tapes.found).HasBinaryNat
    (if found = true then 1 else 0)
  resultCountTape : (work tapes.resultCount).HasBinaryNat resultCount
  resultCount_le : resultCount ≤ store.length
  frame : EntryUpdateFrame tapes initialWork work

/-- The controller frame is reflexive. -/
theorem entryUpdateFrame_refl_internal (tapes : EntryUpdateTapes n)
    (work : Fin n → Tape) : EntryUpdateFrame tapes work work := by
  intro _ _
  rfl

/-- Controller frames compose. -/
theorem EntryUpdateFrame.trans_internal
    {tapes : EntryUpdateTapes n} {work₀ work₁ work₂ : Fin n → Tape}
    (h₁ : EntryUpdateFrame tapes work₀ work₁)
    (h₂ : EntryUpdateFrame tapes work₁ work₂) :
    EntryUpdateFrame tapes work₀ work₂ := by
  intro i hi
  exact (h₂ i hi).trans (h₁ i hi)

/-- Changing the found flag preserves the frame outside all controller tapes. -/
theorem EntryUpdateFrame.markFound_internal
    {tapes : EntryUpdateTapes n} {initialWork work : Fin n → Tape}
    (h : EntryUpdateFrame tapes initialWork work) :
    EntryUpdateFrame tapes initialWork (entryUpdateMarkFoundWork tapes work) := by
  intro i hi
  have hfound : i ≠ tapes.found := by
    simpa [EntryUpdateTapes.found] using hi (11 : Fin 13)
  rw [entryUpdateMarkFoundWork_apply_ne_internal tapes work i hfound]
  exact h i hi

/-- An entry-machine frame extends an existing controller frame. -/
theorem EntryUpdateFrame.trans_ready_internal
    {tapes : EntryUpdateTapes n} {remaining queryBits : List Bool}
    {initialWork work finalWork : Fin n → Tape}
    (hframe : EntryUpdateFrame tapes initialWork work)
    (hready : EntryScanReady tapes.entry remaining queryBits work finalWork) :
    EntryUpdateFrame tapes initialWork finalWork := by
  intro i hi
  have hslot (slot : Fin 9) : i ≠ tapes.entry.idx slot := by
    simpa [EntryUpdateTapes.entry] using hi ⟨slot, by omega⟩
  exact (hready.frame i
    (by simpa [EntryMatchTapes.source] using hslot 0)
    (by simpa [EntryMatchTapes.address] using hslot 1)
    (by simpa [EntryMatchTapes.value] using hslot 2)
    (by simpa [EntryMatchTapes.addressCounter] using hslot 3)
    (by simpa [EntryMatchTapes.addressWidth] using hslot 4)
    (by simpa [EntryMatchTapes.valueCounter] using hslot 5)
    (by simpa [EntryMatchTapes.valueWidth] using hslot 6)
    (by simpa [EntryMatchTapes.query] using hslot 7)
    (by simpa [EntryMatchTapes.result] using hslot 8)).trans
      (hframe i hi)

/-- A one-tape arithmetic frame extends an existing controller frame. -/
theorem EntryUpdateFrame.trans_single_internal
    {tapes : EntryUpdateTapes n} {initialWork work finalWork : Fin n → Tape}
    (hframe : EntryUpdateFrame tapes initialWork work) (slot : Fin 13)
    (hother : ∀ i, i ≠ tapes.idx slot → finalWork i = work i) :
    EntryUpdateFrame tapes initialWork finalWork := by
  intro i hi
  exact (hother i (hi slot)).trans (hframe i hi)

/-- The public initial tape contract establishes the first loop invariant. -/
theorem entryUpdateLoopInv_initial_internal
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (work : Fin n → Tape)
    (hready : EntryScanReady tapes.entry (store.flatMap Entry.encode)
      address.bits work work)
    (hreplacement : (work tapes.replacement).HasBinaryNat newValue)
    (hremaining : (work tapes.remaining).HasBinaryNat store.length)
    (hfound : (work tapes.found).HasBinaryNat 0)
    (hresultCount : (work tapes.resultCount).HasBinaryNat store.length) :
    EntryUpdateLoopInv tapes store address newValue [] store [] false
      store.length work work := by
  exact ⟨entryUpdateProgress_initial_internal store address newValue,
    hready, hreplacement, rfl, hremaining, by simpa using hfound,
    hresultCount, le_rfl, entryUpdateFrame_refl_internal tapes work⟩

end Machine

end RegisterStore

end RAM

end Complexity
