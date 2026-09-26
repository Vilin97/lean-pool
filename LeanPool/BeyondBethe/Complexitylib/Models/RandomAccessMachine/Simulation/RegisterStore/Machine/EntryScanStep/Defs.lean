/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Defs

/-!
# One bounded sparse-entry scan iteration — definitions

One iteration decodes and compares the next entry, branches directly on the
readable equality flag, preserves the decoded value on a hit, and restores the
next-iteration scratch invariant on a miss.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Direct hit/miss branch selected by the readable equality-result tape. -/
def entryScanBranchTM {n : ℕ} (tapes : EntryMatchTapes n) : TM n :=
  TM.branchWorkSymbolTM tapes.result Γ.one TM.skipTM (entryMissCleanupTM tapes)

/-- Decode, compare, and dispatch one encoded sparse entry. -/
def entryScanStepTM {n : ℕ} (tapes : EntryMatchTapes n) : TM n :=
  TM.seqTM (entryMatchReadTM tapes) (entryScanBranchTM tapes)

/-- Coarse branch bound covering both the one-step hit and miss cleanup. -/
def entryScanBranchTime {n : ℕ} (tapes : EntryMatchTapes n)
    (entry : Entry) (queryBits : List Bool) (initialWork : Fin n → Tape) : ℕ :=
  TM.branchWorkSymbolTime 1
    (entryMissCleanupTime tapes entry queryBits initialWork)

/-- Compositional time bound for one complete scan iteration. -/
def entryScanStepTime {n : ℕ} (tapes : EntryMatchTapes n)
    (entry : Entry) (queryBits : List Bool) (initialWork : Fin n → Tape) : ℕ :=
  entryMatchReadTime entry queryBits + 1 +
    entryScanBranchTime tapes entry queryBits initialWork

/-- Successful scan endpoint exposing the decoded value and the global
external frame. -/
structure EntryScanHit {n : ℕ} (tapes : EntryMatchTapes n)
    (entry : Entry) (rest queryBits : List Bool)
    (initialWork finalWork : Fin n → Tape) : Prop where
  addressEq : entry.1.bits = queryBits
  source : (finalWork tapes.source).HasBinarySuffix rest
  value : (finalWork tapes.value).HasBinaryPrefix entry.2.bits
  valueStart : (finalWork tapes.value).cells 0 = Γ.start
  query : (finalWork tapes.query).HasBinaryContent queryBits
  queryStart : (finalWork tapes.query).cells 0 = Γ.start
  result : (finalWork tapes.result).HasBinaryString [true]
  resultStart : (finalWork tapes.result).cells 0 = Γ.start
  parked : ∀ i, TM.Parked (finalWork i)
  frame : ∀ i, i ≠ tapes.source → i ≠ tapes.address →
    i ≠ tapes.value → i ≠ tapes.addressCounter →
    i ≠ tapes.addressWidth → i ≠ tapes.valueCounter →
    i ≠ tapes.valueWidth → i ≠ tapes.query → i ≠ tapes.result →
    finalWork i = initialWork i
  /-- The complete readable-match endpoint is retained for downstream
  consumers that must reset every decoder scratch tape after a hit. -/
  readable : ∃ iterationWork,
    ReadableEntryMatch tapes entry rest queryBits iterationWork finalWork

end Machine

end RegisterStore

end RAM

end Complexity
