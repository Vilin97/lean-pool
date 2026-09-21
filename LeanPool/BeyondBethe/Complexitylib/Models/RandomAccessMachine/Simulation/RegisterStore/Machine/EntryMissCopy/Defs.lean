/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode.Defs

/-!
# Sparse-entry miss copy — definitions

An update scan must preserve every unmatched sparse entry. This module first
emits the decoded address/value pair to the output stream and then restores the
ordinary next-entry scan invariant.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

namespace EntryMatchTapes

/-- View the decoded address and value tapes as entry-emission sources. -/
def encodeTapes {n : ℕ} (tapes : EntryMatchTapes n) : EntryEncodeTapes n where
  address := tapes.address
  value := tapes.value
  ne := tapes.ne (by decide)

@[simp] theorem encodeTapes_address {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.encodeTapes.address = tapes.address := rfl

@[simp] theorem encodeTapes_value {n : ℕ} (tapes : EntryMatchTapes n) :
    tapes.encodeTapes.value = tapes.value := rfl

end EntryMatchTapes

/-- Exact work family after the decoded address and value have been emitted.
Only their heads change; their canonical contents and every other tape remain
literal copies of the readable-match endpoint. -/
def entryMissCopiedWork {n : ℕ} (tapes : EntryMatchTapes n)
    (entry : Entry) (work : Fin n → Tape) (i : Fin n) : Tape :=
  if i = tapes.address then
    { head := entry.1.bits.length + 1, cells := (work i).cells }
  else if i = tapes.value then
    { head := entry.2.bits.length + 1, cells := (work i).cells }
  else work i

/-- Emit the decoded unmatched entry and restore the next-iteration scratch
invariant. -/
def entryMissCopyTM {n : ℕ} (tapes : EntryMatchTapes n) : TM n :=
  TM.seqTM (rewindEntryEncodeTM tapes.encodeTapes)
    (entryMissCleanupTM tapes)

/-- Compositional runtime bound for copying and cleaning one unmatched entry. -/
def entryMissCopyTime {n : ℕ} (tapes : EntryMatchTapes n)
    (entry : Entry) (queryBits : List Bool)
    (initialWork matchedWork : Fin n → Tape) : ℕ :=
  rewindEntryEncodeTime entry
      (entryMissHeadBound entry queryBits initialWork tapes.address)
      (entryMissHeadBound entry queryBits initialWork tapes.value) +
    1 +
    entryMissCleanupTime tapes entry queryBits
      (entryMissCopiedWork tapes entry matchedWork)

end Machine

end RegisterStore

end RAM

end Complexity
