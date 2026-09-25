/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan.Defs

/-!
# Sparse register lookup — definitions

The bounded scanner is already the concrete lookup machine. This module names
its semantic endpoint in terms of the pure sparse-store `read` operation.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- A completed lookup leaves the pure sparse-store value on the decoded-value
tape and preserves the scanner's complete external frame. -/
structure EntryLookupResult {n : ℕ} (tapes : EntryScanTapes n)
    (store : Store) (address : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop where
  value : (finalWork tapes.entry.value).HasBinaryPrefix
    (RegisterStore.read store address).bits
  valueStart : (finalWork tapes.entry.value).cells 0 = Γ.start
  /-- The runtime counter records the unscanned suffix beginning at a hit, or
  zero after an unsuccessful scan. -/
  count : ∃ remaining, remaining ≤ store.length ∧
    (finalWork tapes.count).HasBinaryNat remaining
  parked : ∀ i, TM.Parked (finalWork i)
  frame : EntryScanFrame tapes initialWork finalWork
  /-- The complete scanner endpoint is retained so a caller can restore every
  owned cursor and scratch tape without re-proving the scan decomposition. -/
  outcome : EntryScanOutcome tapes store address.bits initialWork finalWork

/-- The concrete sparse lookup is the fixed runtime-count entry scanner. -/
abbrev entryLookupTM {n : ℕ} (tapes : EntryScanTapes n) : TM n :=
  entryScanTM tapes

/-- Lookup inherits the scanner's explicit runtime bound. -/
abbrev entryLookupTime {n : ℕ} (tapes : EntryScanTapes n)
    (address : ℕ) (store : Store) : ℕ :=
  entryScanTime tapes address.bits store

end Machine

end RegisterStore

end RAM

end Complexity
