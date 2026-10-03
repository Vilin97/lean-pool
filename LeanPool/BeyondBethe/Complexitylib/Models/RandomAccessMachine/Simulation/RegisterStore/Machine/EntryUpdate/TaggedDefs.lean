/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Defs

/-!
# Positive-tag sparse updates

Dense overlays encode an actual register value `v` by the positive sparse
value `v + 1`. This module packages successor followed by the existing sparse
update controller as one reusable write-side kernel.
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Convert an actual register value to its positive overlay tag, then update
the encoded sparse overlay. -/
def taggedEntryUpdateTM {n : ℕ} (tapes : EntryUpdateTapes n) : TM n :=
  TM.seqTM (TM.binarySuccTM tapes.replacement) (entryUpdateTM tapes)

/-- Exact compositional time budget for one positive-tag overlay write. -/
def taggedEntryUpdateTime {n : ℕ} (tapes : EntryUpdateTapes n)
    (overlay : Store) (address value : ℕ) : ℕ :=
  TM.binarySuccTime value + 1 +
    entryUpdateTime tapes overlay address (value + 1)

/-- Semantic boundary for successor tagging followed by sparse update. -/
def TaggedEntryUpdateResult {n : ℕ} (tapes : EntryUpdateTapes n)
    (overlay : Store) (address value : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop :=
  ∃ taggedWork : Fin n → Tape,
    (taggedWork tapes.replacement).HasBinaryNat (value + 1) ∧
    (∀ i, i ≠ tapes.replacement → taggedWork i = initialWork i) ∧
    EntryUpdateOutcome tapes overlay address (value + 1) taggedWork finalWork ∧
    (finalWork tapes.entry.source).cells =
      (initialWork tapes.entry.source).cells

end Machine
end RegisterStore
end RAM
end Complexity
