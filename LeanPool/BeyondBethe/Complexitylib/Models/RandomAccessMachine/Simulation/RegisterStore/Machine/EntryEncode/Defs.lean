/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordEncode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs

/-!
# Sparse entry emission — definitions
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Distinct decoded address and value tapes used to emit one sparse entry. -/
structure EntryEncodeTapes (n : ℕ) where
  /-- Decoded address source. -/
  address : Fin n
  /-- Decoded value source. -/
  value : Fin n
  /-- The address and value sources are distinct. -/
  ne : address ≠ value

/-- Emit one address/value entry as two consecutive self-delimiting words. -/
def entryEncodeTM {n : ℕ} (tapes : EntryEncodeTapes n) : TM n :=
  TM.seqTM (wordEncodeTM tapes.address) (wordEncodeTM tapes.value)

/-- Compositional time bound for one encoded entry. -/
def entryEncodeTime (entry : Entry) : ℕ :=
  wordEncodeTime entry.1 + 1 + wordEncodeTime entry.2

/-- Rewind arbitrary decoded address/value cursors and emit the entry. -/
def rewindEntryEncodeTM {n : ℕ} (tapes : EntryEncodeTapes n) : TM n :=
  TM.seqTM (rewindWordEncodeTM tapes.address)
    (rewindWordEncodeTM tapes.value)

/-- Composition bound for emitting an entry from arbitrary bounded cursors. -/
def rewindEntryEncodeTime (entry : Entry)
    (addressHeadBound valueHeadBound : ℕ) : ℕ :=
  rewindWordEncodeTime entry.1 addressHeadBound + 1 +
    rewindWordEncodeTime entry.2 valueHeadBound

/-- Emit an entry from canonical sources and restore both source heads to
cell one. -/
def rewindEntryEncodeRestoreTM {n : ℕ} (tapes : EntryEncodeTapes n) : TM n :=
  TM.seqTM (rewindEntryEncodeTM tapes)
    (TM.seqTM (TM.rewindWorkTM tapes.address)
      (TM.rewindWorkTM tapes.value))

/-- Compositional bound for entry emission followed by two-source restore. -/
def rewindEntryEncodeRestoreTime (entry : Entry) : ℕ :=
  rewindEntryEncodeTime entry 1 1 + 1 +
    (entry.1.bits.length + 3 + 1 + entry.2.bits.length + 3)

end Machine

end RegisterStore

end RAM

end Complexity
