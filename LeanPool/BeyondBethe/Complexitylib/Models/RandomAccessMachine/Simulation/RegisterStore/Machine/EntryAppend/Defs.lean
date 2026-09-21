/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryReplace.Defs

/-!
# Sparse-entry final append — definitions

When an update exhausts the old store without a match, a nonzero new value is
appended using the preserved query and replacement tapes. Both sources are then
restored exactly so the caller retains its canonical work frame.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

namespace EntryReplaceTapes

/-- View the preserved query and replacement tapes as a fresh-entry encoder. -/
def appendEncodeTapes {n : ℕ}
    (tapes : EntryReplaceTapes n) : EntryEncodeTapes n where
  address := tapes.entry.query
  value := tapes.replacement
  ne := Ne.symm (tapes.replacement_ne 7)

@[simp] theorem appendEncodeTapes_address {n : ℕ}
    (tapes : EntryReplaceTapes n) :
    tapes.appendEncodeTapes.address = tapes.entry.query := rfl

@[simp] theorem appendEncodeTapes_value {n : ℕ}
    (tapes : EntryReplaceTapes n) :
    tapes.appendEncodeTapes.value = tapes.replacement := rfl

end EntryReplaceTapes

/-- Emit a fresh query/value entry and restore both canonical source cursors. -/
def entryAppendRestoreTM {n : ℕ} (tapes : EntryReplaceTapes n) : TM n :=
  TM.seqTM (rewindEntryEncodeTM tapes.appendEncodeTapes)
    (TM.seqTM (TM.rewindWorkTM tapes.entry.query)
      (TM.rewindWorkTM tapes.replacement))

/-- Exact compositional bound for final append and two-source restoration. -/
def entryAppendRestoreTime (address newValue : ℕ) : ℕ :=
  rewindEntryEncodeTime (address, newValue) 1 1 + 1 +
    (address.bits.length + 1 + 2 + 1 +
      (newValue.bits.length + 1 + 2))

end Machine

end RegisterStore

end RAM

end Complexity
