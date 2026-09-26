/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode.Defs

/-!
# Sparse-entry replacement — definitions

The replacement branch emits the matched address paired with a distinct
canonical new-value tape, rewinds that external value source, and restores the
ordinary next-entry scan invariant.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Entry-match tapes plus a distinct source containing the replacement value. -/
structure EntryReplaceTapes (n : ℕ) where
  /-- The nine tapes used to decode and match the old entry. -/
  entry : EntryMatchTapes n
  /-- Canonical new-value source. -/
  replacement : Fin n
  /-- The replacement source is outside the complete entry-match assignment. -/
  replacement_ne : ∀ i, replacement ≠ entry.idx i

namespace EntryReplaceTapes

/-- Emit the matched decoded address paired with the replacement source. -/
def encodeTapes {n : ℕ} (tapes : EntryReplaceTapes n) : EntryEncodeTapes n where
  address := tapes.entry.address
  value := tapes.replacement
  ne := Ne.symm (tapes.replacement_ne 1)

@[simp] theorem encodeTapes_address {n : ℕ} (tapes : EntryReplaceTapes n) :
    tapes.encodeTapes.address = tapes.entry.address := rfl

@[simp] theorem encodeTapes_value {n : ℕ} (tapes : EntryReplaceTapes n) :
    tapes.encodeTapes.value = tapes.replacement := rfl

end EntryReplaceTapes

/-- Exact work family after replacement emission and restoration of the
external replacement cursor. Only the decoded address head remains changed. -/
def entryReplaceReadyWork {n : ℕ} (tapes : EntryReplaceTapes n)
    (entry : Entry) (work : Fin n → Tape) (i : Fin n) : Tape :=
  if i = tapes.entry.address then
    { head := entry.1.bits.length + 1, cells := (work i).cells }
  else work i

/-- Emit the replacement entry, restore the replacement cursor, and clear all
entry decoder/result scratch. -/
def entryReplaceCleanupTM {n : ℕ} (tapes : EntryReplaceTapes n) : TM n :=
  TM.seqTM (rewindEntryEncodeTM tapes.encodeTapes)
    (TM.seqTM (TM.rewindWorkTM tapes.replacement)
      (entryMissCleanupTM tapes.entry))

/-- Compositional runtime bound for replacement emission and cleanup. -/
def entryReplaceCleanupTime {n : ℕ} (tapes : EntryReplaceTapes n)
    (entry : Entry) (newValue : ℕ) (queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape) : ℕ :=
  rewindEntryEncodeTime (entry.1, newValue)
      (entryMissHeadBound entry queryBits initialWork tapes.entry.address) 1 +
    1 + (newValue.bits.length + 1 + 2 + 1 +
      entryMissCleanupTime tapes.entry entry queryBits
        (entryReplaceReadyWork tapes entry matchedWork))

end Machine

end RegisterStore

end RAM

end Complexity
