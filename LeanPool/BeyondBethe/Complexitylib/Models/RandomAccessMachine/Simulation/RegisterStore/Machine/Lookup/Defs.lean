/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Defs
public import Mathlib.Tactic.FinCases

public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.ResetLayout

/-!
# Reusable sparse-register operand lookup -- definitions

One RAM instruction may need several direct or indirect register reads. This
module gives lookup a reusable phase boundary: it loads a query from a
canonical source, scans the encoded store, copies out the decoded value, resets
all scanner scratch, rewinds the source, and restores the runtime entry count.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Uniform scanner-head bound from a canonical cell-one start. -/
def entryLookupRestoreHeadBound {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ) : ℕ :=
  1 + entryLookupTime tapes.scan address store

/-- Reset budget obtained from the nine fixed owned targets and the common
head/width envelopes. -/
def entryLookupResetTime {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (store : Store) (address : ℕ) : ℕ :=
  9 * (entryLookupRestoreHeadBound tapes store address +
    2 * entryLookupResetWidth store address + 9) + 1

/-- Restore scanner scratch, source cursor, and runtime count after a completed
lookup whose value has already been copied out. -/
def entryLookupRestoreTailTM {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) : TM n :=
  TM.seqTM (TM.resetBinaryWorkManyTM (entryLookupResetTargets tapes))
    (TM.seqTM (TM.rewindWorkTM tapes.scan.entry.source)
      (TM.binaryCopyIntoTM tapes.countSource tapes.scan.count
        tapes.copyScratch))

/-- Copy out a lookup result, then restore the complete reusable scanner ABI. -/
def entryLookupCopyRestoreTM {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) : TM n :=
  TM.seqTM (entryLookupTM tapes.scan)
    (TM.seqTM (TM.rewindWorkTM tapes.scan.entry.value)
      (TM.seqTM
        (TM.binaryCopyIntoTM tapes.scan.entry.value tapes.destination
          tapes.copyScratch)
        (entryLookupRestoreTailTM tapes)))

/-- Load the supplied query, perform one sparse lookup, copy out its value, and
return to the same reusable blank-query scanner boundary. -/
def entryLookupLoadedTM {n : ℕ} (tapes : EntryLookupRestoreTapes n) : TM n :=
  TM.seqTM
    (TM.binaryCopyIntoTM tapes.querySource tapes.scan.entry.query
      tapes.copyScratch)
    (entryLookupCopyRestoreTM tapes)

/-- Time bound for scanner reset, source rewind, and count restoration. -/
def entryLookupRestoreTailTime {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ) : ℕ :=
  entryLookupResetTime tapes store address + 1 +
    (entryLookupRestoreHeadBound tapes store address + 2 + 1 +
      TM.binaryCopyTime store.length 0)

/-- Time bound after the query has been prepared. -/
def entryLookupCopyRestoreTime {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ) : ℕ :=
  entryLookupTime tapes.scan address store + 1 +
    (entryLookupRestoreHeadBound tapes store address + 2 + 1 +
      (TM.binaryCopyTime (RegisterStore.read store address) 0 + 1 +
        entryLookupRestoreTailTime tapes store address))

/-- Complete reusable loaded-lookup time bound. -/
def entryLookupLoadedTime {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ) : ℕ :=
  TM.binaryCopyTime address 0 + 1 +
    entryLookupCopyRestoreTime tapes store address

/-- Read a positive-tag sparse overlay and either decode the tag or fall back
to the immutable public-input bank on a sparse miss. -/
def denseOverlayLookupTM {n : ℕ} (tapes : EntryLookupRestoreTapes n) : TM n :=
  TM.seqTM (entryLookupLoadedTM tapes)
    (TM.branchWorkBlankTM tapes.destination
      (denseInputLookupTM tapes.querySource tapes.scan.entry.address
        tapes.destination tapes.copyScratch)
      (TM.binaryPredTM tapes.destination))

/-- Complete reusable dense-overlay lookup budget. -/
def denseOverlayLookupTime {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (inputLength : ℕ) (overlay : Store) (address : ℕ) : ℕ :=
  entryLookupLoadedTime tapes overlay address + 1 +
    TM.branchWorkBlankTime (denseInputLookupTime inputLength address)
      (TM.binaryPredTime (RegisterStore.read overlay address - 1))

/-- Load one fixed address from canonical zero, read through the dense input
and sparse overlay, then clear the fixed-address source back to zero. -/
def denseOverlayLookupStaticTM {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) : TM n :=
  TM.seqTM (TM.binaryAddConstTM tapes.querySource address)
    (TM.seqTM (denseOverlayLookupTM tapes)
      (TM.resetBinaryWorkTM tapes.querySource))

/-- Complete fixed-address dense-overlay lookup budget. -/
def denseOverlayLookupStaticTime {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (inputLength : ℕ)
    (overlay : Store) (address : ℕ) : ℕ :=
  TM.binaryAddConstTime address 0 + 1 +
    (denseOverlayLookupTime tapes inputLength overlay address + 1 +
      TM.resetBinaryWorkTime 1 address.bits.length)

/-- Load one fixed address from canonical zero, run a reusable lookup, then
clear the fixed-address source back to zero. -/
def entryLookupStaticTM {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (address : ℕ) : TM n :=
  TM.seqTM (TM.binaryAddConstTM tapes.querySource address)
    (TM.seqTM (entryLookupLoadedTM tapes)
      (TM.resetBinaryWorkTM tapes.querySource))

/-- Complete fixed-address lookup budget. -/
def entryLookupStaticTime {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (store : Store) (address : ℕ) : ℕ :=
  TM.binaryAddConstTime address 0 + 1 +
    (entryLookupLoadedTime tapes store address + 1 +
      TM.resetBinaryWorkTime 1 address.bits.length)

/-- Canonical precondition for one reusable loaded lookup. -/
structure EntryLookupRestoreReady {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (work : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.scan.entry (store.flatMap Entry.encode) []
    work work
  sourceStart : (work tapes.scan.entry.source).cells 0 = Γ.start
  sourceHead : (work tapes.scan.entry.source).head = 1
  count : (work tapes.scan.count).HasBinaryNat store.length
  countSource : (work tapes.countSource).HasBinaryNat store.length
  querySource : (work tapes.querySource).HasBinaryNat address
  destination : (work tapes.destination).HasBinaryNat 0
  copyScratch : (work tapes.copyScratch).HasBinaryNat 0

/-- Canonical precondition for a fixed-address lookup whose query source starts
at zero and is restored to zero. -/
structure EntryLookupStaticReady {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store)
    (work : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.scan.entry (store.flatMap Entry.encode) []
    work work
  sourceStart : (work tapes.scan.entry.source).cells 0 = Γ.start
  sourceHead : (work tapes.scan.entry.source).head = 1
  count : (work tapes.scan.count).HasBinaryNat store.length
  countSource : (work tapes.countSource).HasBinaryNat store.length
  querySource : (work tapes.querySource).HasBinaryNat 0
  destination : (work tapes.destination).HasBinaryNat 0
  copyScratch : (work tapes.copyScratch).HasBinaryNat 0

/-- Boundary after the external query has been copied into scanner storage. -/
structure EntryLookupPrepared {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.scan.entry (store.flatMap Entry.encode)
    address.bits work work
  sourceStart : (work tapes.scan.entry.source).cells 0 = Γ.start
  sourceHead : (work tapes.scan.entry.source).head = 1
  count : (work tapes.scan.count).HasBinaryNat store.length
  countSource : work tapes.countSource = initialWork tapes.countSource
  countSourceNat : (work tapes.countSource).HasBinaryNat store.length
  querySource : work tapes.querySource = initialWork tapes.querySource
  querySourceNat : (work tapes.querySource).HasBinaryNat address
  destination : (work tapes.destination).HasBinaryNat 0
  copyScratch : (work tapes.copyScratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (work i)
  frame : ∀ i, i ≠ tapes.scan.entry.query → work i = initialWork i

/-- Uniform cleanup certificate extracted from either scanner outcome. -/
def EntryLookupResetReady {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (work : Fin n → Tape) : Prop :=
  ∃ bits : Fin n → List Bool,
    (∀ i, i ∈ entryLookupResetTargets tapes →
      (work i).HasBinaryContent (bits i)) ∧
    (∀ i, i ∈ entryLookupResetTargets tapes →
      (work i).cells 0 = Γ.start) ∧
    (∀ i, i ∈ entryLookupResetTargets tapes →
      (bits i).length ≤ entryLookupResetWidth store address) ∧
    ∀ i, TM.Parked (work i)

/-- Boundary after the bounded scanner has produced a semantic lookup result.
It retains the exact cleanup certificate, the read-only source image, a
uniform cursor bound, and the complete external frame needed by restoration. -/
structure EntryLookupScanned {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork preparedWork work : Fin n → Tape) : Prop where
  result : EntryLookupResult tapes.scan store address preparedWork work
  resetReady : EntryLookupResetReady tapes store address work
  sourceCells : (work tapes.scan.entry.source).cells =
    (initialWork tapes.scan.entry.source).cells
  sourceStart : (work tapes.scan.entry.source).cells 0 = Γ.start
  sourceHeadBound : (work tapes.scan.entry.source).head ≤
    entryLookupRestoreHeadBound tapes store address
  resetHeadBound : ∀ i, i ∈ entryLookupResetTargets tapes →
    (work i).head ≤ entryLookupRestoreHeadBound tapes store address
  countSource : work tapes.countSource = initialWork tapes.countSource
  querySource : work tapes.querySource = initialWork tapes.querySource
  destination : work tapes.destination = initialWork tapes.destination
  copyScratch : work tapes.copyScratch = initialWork tapes.copyScratch
  frame : ∀ i, (∀ slot, i ≠ tapes.idx slot) →
    work i = initialWork i

/-- Existentially packages the concrete prepared work family between query
copying and scanning, so subsequent phases can use a semantic Hoare boundary. -/
def EntryLookupScannedReady {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape) : Prop :=
  ∃ preparedWork,
    EntryLookupPrepared tapes store address initialWork preparedWork ∧
    EntryLookupScanned tapes store address initialWork preparedWork work

/-- Stable semantic state carried through value rewind, value copy, scratch
reset, source rewind, and count restoration. -/
structure EntryLookupRestoreInvariant {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape) : Prop where
  valueContent : (work tapes.scan.entry.value).HasBinaryContent
    (RegisterStore.read store address).bits
  valueStart : (work tapes.scan.entry.value).cells 0 = Γ.start
  resetReady : EntryLookupResetReady tapes store address work
  sourceCells : (work tapes.scan.entry.source).cells =
    (initialWork tapes.scan.entry.source).cells
  sourceStart : (work tapes.scan.entry.source).cells 0 = Γ.start
  sourceHeadBound : (work tapes.scan.entry.source).head ≤
    entryLookupRestoreHeadBound tapes store address
  resetHeadBound : ∀ i, i ∈ entryLookupResetTargets tapes →
    (work i).head ≤ entryLookupRestoreHeadBound tapes store address
  countSource : work tapes.countSource = initialWork tapes.countSource
  countSourceNat : (work tapes.countSource).HasBinaryNat store.length
  querySource : work tapes.querySource = initialWork tapes.querySource
  querySourceNat : (work tapes.querySource).HasBinaryNat address
  copyScratch : work tapes.copyScratch = initialWork tapes.copyScratch
  copyScratchNat : (work tapes.copyScratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (work i)
  frame : ∀ i, (∀ slot, i ≠ tapes.idx slot) →
    work i = initialWork i

/-- The decoded value has been rewound to the canonical read boundary. -/
structure EntryLookupValueReady {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape) : Prop where
  restore : EntryLookupRestoreInvariant tapes store address initialWork work
  value : (work tapes.scan.entry.value).HasBinaryNat
    (RegisterStore.read store address)
  destination : (work tapes.destination).HasBinaryNat 0

/-- The decoded value has been copied to the instruction operand tape while
all scanner restoration data remains available. -/
structure EntryLookupCopied {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape) : Prop where
  restore : EntryLookupRestoreInvariant tapes store address initialWork work
  value : (work tapes.scan.entry.value).HasBinaryNat
    (RegisterStore.read store address)
  destination : (work tapes.destination).HasBinaryNat
    (RegisterStore.read store address)

/-- Exact boundary after all nine scanner-owned binary tapes have been reset. -/
structure EntryLookupResetDone {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork copiedWork work : Fin n → Tape) : Prop where
  copied : EntryLookupCopied tapes store address initialWork copiedWork
  work_eq : work = TM.resetBinaryWorkManyResult copiedWork
    (entryLookupResetTargets tapes)

/-- Semantic form of the reset endpoint, stable while the encoded source is
rewound. -/
structure EntryLookupScratchReset {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape) : Prop where
  sourceCells : (work tapes.scan.entry.source).cells =
    (initialWork tapes.scan.entry.source).cells
  sourceStart : (work tapes.scan.entry.source).cells 0 = Γ.start
  sourceHeadBound : (work tapes.scan.entry.source).head ≤
    entryLookupRestoreHeadBound tapes store address
  targetsBlank : ∀ i, i ∈ entryLookupResetTargets tapes →
    work i = TM.resetBinaryBlank
  countSource : work tapes.countSource = initialWork tapes.countSource
  countSourceNat : (work tapes.countSource).HasBinaryNat store.length
  querySource : work tapes.querySource = initialWork tapes.querySource
  querySourceNat : (work tapes.querySource).HasBinaryNat address
  destination : (work tapes.destination).HasBinaryNat
    (RegisterStore.read store address)
  copyScratch : work tapes.copyScratch = initialWork tapes.copyScratch
  copyScratchNat : (work tapes.copyScratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (work i)
  frame : ∀ i, (∀ slot, i ≠ tapes.idx slot) →
    work i = initialWork i

/-- Boundary after scanner reset and encoded-source rewind, immediately before
the runtime entry count is copied back. -/
structure EntryLookupSourceReady {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.scan.entry (store.flatMap Entry.encode) []
    work work
  sourceCells : (work tapes.scan.entry.source).cells =
    (initialWork tapes.scan.entry.source).cells
  sourceStart : (work tapes.scan.entry.source).cells 0 = Γ.start
  sourceHead : (work tapes.scan.entry.source).head = 1
  countZero : (work tapes.scan.count).HasBinaryNat 0
  countSource : work tapes.countSource = initialWork tapes.countSource
  countSourceNat : (work tapes.countSource).HasBinaryNat store.length
  querySource : work tapes.querySource = initialWork tapes.querySource
  destination : (work tapes.destination).HasBinaryNat
    (RegisterStore.read store address)
  copyScratch : work tapes.copyScratch = initialWork tapes.copyScratch
  copyScratchNat : (work tapes.copyScratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (work i)
  frame : ∀ i, (∀ slot, i ≠ tapes.idx slot) →
    work i = initialWork i

/-- Reusable endpoint after one loaded sparse-register read. -/
structure EntryLookupRestoreResult {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.scan.entry (store.flatMap Entry.encode) []
    finalWork finalWork
  sourceCells : (finalWork tapes.scan.entry.source).cells =
    (initialWork tapes.scan.entry.source).cells
  sourceStart : (finalWork tapes.scan.entry.source).cells 0 = Γ.start
  sourceHead : (finalWork tapes.scan.entry.source).head = 1
  count : (finalWork tapes.scan.count).HasBinaryNat store.length
  countSource : finalWork tapes.countSource = initialWork tapes.countSource
  querySource : finalWork tapes.querySource = initialWork tapes.querySource
  value : (finalWork tapes.destination).HasBinaryNat
    (RegisterStore.read store address)
  copyScratch : (finalWork tapes.copyScratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (finalWork i)
  frame : ∀ i, (∀ slot, i ≠ tapes.idx slot) →
    finalWork i = initialWork i

/-- Reusable endpoint after reading through a tagged mutable overlay into the
immutable public-input bank. -/
structure DenseOverlayLookupResult {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.scan.entry (overlay.flatMap Entry.encode) []
    finalWork finalWork
  sourceCells : (finalWork tapes.scan.entry.source).cells =
    (initialWork tapes.scan.entry.source).cells
  sourceStart : (finalWork tapes.scan.entry.source).cells 0 = Γ.start
  sourceHead : (finalWork tapes.scan.entry.source).head = 1
  count : (finalWork tapes.scan.count).HasBinaryNat overlay.length
  countSource : finalWork tapes.countSource = initialWork tapes.countSource
  querySource : finalWork tapes.querySource = initialWork tapes.querySource
  value : (finalWork tapes.destination).HasBinaryNat
    (DenseOverlay.read input overlay address)
  copyScratch : (finalWork tapes.copyScratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (finalWork i)
  frame : ∀ i, (∀ slot, i ≠ tapes.idx slot) →
    finalWork i = initialWork i

/-- Reusable fixed-address dense-overlay endpoint. The destination contains
the decoded register value and the temporary query source is zero again. -/
structure DenseOverlayLookupStaticResult {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.scan.entry (overlay.flatMap Entry.encode) []
    finalWork finalWork
  sourceCells : (finalWork tapes.scan.entry.source).cells =
    (initialWork tapes.scan.entry.source).cells
  sourceStart : (finalWork tapes.scan.entry.source).cells 0 = Γ.start
  sourceHead : (finalWork tapes.scan.entry.source).head = 1
  count : (finalWork tapes.scan.count).HasBinaryNat overlay.length
  countSource : finalWork tapes.countSource = initialWork tapes.countSource
  querySource : (finalWork tapes.querySource).HasBinaryNat 0
  destination : (finalWork tapes.destination).HasBinaryNat
    (DenseOverlay.read input overlay address)
  copyScratch : (finalWork tapes.copyScratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (finalWork i)
  frame : ∀ i, (∀ slot, i ≠ tapes.idx slot) →
    finalWork i = initialWork i

/-- Reusable fixed-address endpoint. The destination holds the semantic read,
the scanner is restored, and the fixed query source is zero again. -/
structure EntryLookupStaticResult {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork finalWork : Fin n → Tape) : Prop where
  scanner : EntryScanReady tapes.scan.entry (store.flatMap Entry.encode) []
    finalWork finalWork
  sourceCells : (finalWork tapes.scan.entry.source).cells =
    (initialWork tapes.scan.entry.source).cells
  sourceStart : (finalWork tapes.scan.entry.source).cells 0 = Γ.start
  sourceHead : (finalWork tapes.scan.entry.source).head = 1
  count : (finalWork tapes.scan.count).HasBinaryNat store.length
  countSource : finalWork tapes.countSource = initialWork tapes.countSource
  querySource : (finalWork tapes.querySource).HasBinaryNat 0
  destination : (finalWork tapes.destination).HasBinaryNat
    (RegisterStore.read store address)
  copyScratch : (finalWork tapes.copyScratch).HasBinaryNat 0
  parked : ∀ i, TM.Parked (finalWork i)
  frame : ∀ i, (∀ slot, i ≠ tapes.idx slot) →
    finalWork i = initialWork i

end Machine

end RegisterStore

end RAM

end Complexity
