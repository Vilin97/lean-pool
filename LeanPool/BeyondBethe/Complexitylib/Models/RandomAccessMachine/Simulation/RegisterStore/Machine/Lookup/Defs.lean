/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookup.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst.Defs
public import Mathlib.Tactic.FinCases

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

/-- Fourteen pairwise-distinct tapes for a reusable sparse operand lookup.
Slots `0..9` are the bounded scanner; the final four slots preserve the entry
count, supply the query, receive the value, and provide zero copy scratch. -/
structure EntryLookupRestoreTapes (n : ℕ) where
  /-- Physical work tape assigned to each logical lookup role. -/
  idx : Fin 14 → Fin n
  /-- Distinct logical lookup roles occupy distinct physical tapes. -/
  injective : Function.Injective idx

namespace EntryLookupRestoreTapes

/-- Bounded scanner view of the reusable lookup assignment. -/
def scan {n : ℕ} (tapes : EntryLookupRestoreTapes n) : EntryScanTapes n where
  entry :=
    { idx := fun i => tapes.idx ⟨i, by omega⟩
      injective := by
        intro i j h
        apply Fin.ext
        simpa using congrArg Fin.val (tapes.injective h) }
  count := tapes.idx 9
  count_ne := by
    intro i h
    have h' : (9 : Fin 14) = ⟨i.val, by omega⟩ := tapes.injective h
    have hval := congrArg Fin.val h'
    change (9 : ℕ) = i.val at hval
    omega

@[simp] theorem scan_entry_idx {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (slot : Fin 9) :
    tapes.scan.entry.idx slot = tapes.idx ⟨slot.val, by omega⟩ := rfl

@[simp] theorem scan_count {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.scan.count = tapes.idx 9 := rfl

/-- Preserved canonical copy of the store cardinality. -/
def countSource {n : ℕ} (tapes : EntryLookupRestoreTapes n) : Fin n :=
  tapes.idx 10

/-- Canonical address supplied to this lookup. -/
def querySource {n : ℕ} (tapes : EntryLookupRestoreTapes n) : Fin n :=
  tapes.idx 11

/-- Canonical destination receiving the looked-up register value. -/
def destination {n : ℕ} (tapes : EntryLookupRestoreTapes n) : Fin n :=
  tapes.idx 12

/-- Preserved zero tape used by width-linear binary copying. -/
def copyScratch {n : ℕ} (tapes : EntryLookupRestoreTapes n) : Fin n :=
  tapes.idx 13

/-- Inequality of logical slots gives inequality of physical tapes. -/
theorem ne {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    {i j : Fin 14} (hne : i ≠ j) : tapes.idx i ≠ tapes.idx j :=
  fun heq => hne (tapes.injective heq)

/-- Every scanner tape is distinct from an external reusable-lookup role. -/
theorem scan_ne_external {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (slot : Fin 10) (external : Fin 4) :
    tapes.idx ⟨slot.val, by omega⟩ ≠
      tapes.idx ⟨external.val + 10, by omega⟩ := by
  apply tapes.ne
  intro h
  have hval := congrArg Fin.val h
  change slot.val = external.val + 10 at hval
  omega

theorem countSource_ne_querySource {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) :
    tapes.countSource ≠ tapes.querySource := tapes.ne (by decide)

theorem countSource_ne_destination {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) :
    tapes.countSource ≠ tapes.destination := tapes.ne (by decide)

theorem countSource_ne_copyScratch {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) :
    tapes.countSource ≠ tapes.copyScratch := tapes.ne (by decide)

theorem querySource_ne_destination {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) :
    tapes.querySource ≠ tapes.destination := tapes.ne (by decide)

theorem querySource_ne_copyScratch {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) :
    tapes.querySource ≠ tapes.copyScratch := tapes.ne (by decide)

theorem destination_ne_copyScratch {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) :
    tapes.destination ≠ tapes.copyScratch := tapes.ne (by decide)

/-- Logical parent slots reset after one lookup. -/
def resetSlot (slot : Fin 9) : Fin 14 :=
  match slot.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 8
  | 7 => 7
  | _ => 9

private theorem resetSlot_injective : Function.Injective resetSlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [resetSlot] at h ⊢

/-- Physical reset target selected by a finite logical slot. -/
def resetIdx {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (slot : Fin 9) : Fin n := tapes.idx (resetSlot slot)

theorem resetIdx_injective {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    Function.Injective tapes.resetIdx :=
  fun _ _ h => resetSlot_injective (tapes.injective h)

@[simp] theorem resetIdx_zero {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 0 = tapes.scan.entry.address := rfl

@[simp] theorem resetIdx_one {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 1 = tapes.scan.entry.value := rfl

@[simp] theorem resetIdx_two {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 2 = tapes.scan.entry.addressCounter := rfl

@[simp] theorem resetIdx_three {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 3 = tapes.scan.entry.addressWidth := rfl

@[simp] theorem resetIdx_four {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 4 = tapes.scan.entry.valueCounter := rfl

@[simp] theorem resetIdx_five {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 5 = tapes.scan.entry.valueWidth := rfl

@[simp] theorem resetIdx_six {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 6 = tapes.scan.entry.result := rfl

@[simp] theorem resetIdx_seven {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 7 = tapes.scan.entry.query := rfl

@[simp] theorem resetIdx_eight {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    tapes.resetIdx 8 = tapes.scan.count := rfl

end EntryLookupRestoreTapes

/-- Scanner-owned tapes reset after copying out a lookup result. The encoded
source is deliberately excluded because it is read-only and merely rewound. -/
def entryLookupResetTargets {n : ℕ} (tapes : EntryLookupRestoreTapes n) :
    List (Fin n) :=
  List.ofFn tapes.resetIdx

/-- Width envelope for every binary scratch value at a successful hit on one
entry. -/
def entryLookupEntryWidth (entry : Entry) (address : ℕ) : ℕ :=
  max address.bits.length
    (max entry.1.bits.length
      (max entry.2.bits.length
        (max (bitlen entry.1)
          (max (bitlen entry.2) 1))))

/-- Width envelope contributed by possible hit entries in a complete store. -/
def entryLookupStoreWidth (address : ℕ) : Store → ℕ
  | [] => address.bits.length
  | entry :: rest =>
      max (entryLookupEntryWidth entry address)
        (entryLookupStoreWidth address rest)

/-- Width envelope for every hit or miss reset target in a complete store. -/
def entryLookupResetWidth (store : Store) (address : ℕ) : ℕ :=
  max store.length.bits.length (entryLookupStoreWidth address store)

/-- Exact reset contents at a successful lookup endpoint. -/
def entryLookupFoundBits {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (entry : Entry) (remaining address : ℕ) (i : Fin n) : List Bool :=
  if i = tapes.scan.entry.query then address.bits
  else if i = tapes.scan.count then remaining.bits
  else entryMissBits tapes.scan.entry entry address.bits i

/-- Exact reset contents at an unsuccessful lookup endpoint. -/
def entryLookupMissBits {n : ℕ} (tapes : EntryLookupRestoreTapes n)
    (address : ℕ) (i : Fin n) : List Bool :=
  if i = tapes.scan.entry.query then address.bits else []

-- These repetitive projection simplifications intentionally share one stable
-- simp set; individual cases use different subsets of it.
@[simp] theorem entryLookupFoundBits_zero {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address
      tapes.scan.entry.address =
      entry.1.bits := by
  simp [entryLookupFoundBits, entryMissBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.address,
    EntryMatchTapes.value, EntryMatchTapes.addressCounter,
    EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
    EntryMatchTapes.valueWidth, EntryMatchTapes.query, EntryMatchTapes.result,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupFoundBits_one {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address tapes.scan.entry.value =
      entry.2.bits := by
  simp [entryLookupFoundBits, entryMissBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.address,
    EntryMatchTapes.value, EntryMatchTapes.addressCounter,
    EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
    EntryMatchTapes.valueWidth, EntryMatchTapes.query, EntryMatchTapes.result,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupFoundBits_two {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address
      tapes.scan.entry.addressCounter =
      List.replicate (bitlen entry.1) true := by
  simp [entryLookupFoundBits, entryMissBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.address,
    EntryMatchTapes.value, EntryMatchTapes.addressCounter,
    EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
    EntryMatchTapes.valueWidth, EntryMatchTapes.query, EntryMatchTapes.result,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupFoundBits_three {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address
      tapes.scan.entry.addressWidth =
      [] := by
  simp [entryLookupFoundBits, entryMissBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.address,
    EntryMatchTapes.value, EntryMatchTapes.addressCounter,
    EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
    EntryMatchTapes.valueWidth, EntryMatchTapes.query, EntryMatchTapes.result,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupFoundBits_four {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address
      tapes.scan.entry.valueCounter =
      List.replicate (bitlen entry.2) true := by
  simp [entryLookupFoundBits, entryMissBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.address,
    EntryMatchTapes.value, EntryMatchTapes.addressCounter,
    EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
    EntryMatchTapes.valueWidth, EntryMatchTapes.query, EntryMatchTapes.result,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupFoundBits_five {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address
      tapes.scan.entry.valueWidth =
      [] := by
  simp [entryLookupFoundBits, entryMissBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.address,
    EntryMatchTapes.value, EntryMatchTapes.addressCounter,
    EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
    EntryMatchTapes.valueWidth, EntryMatchTapes.query, EntryMatchTapes.result,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupFoundBits_six {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address tapes.scan.entry.result =
      [decide (entry.1.bits = address.bits)] := by
  simp [entryLookupFoundBits, entryMissBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.address,
    EntryMatchTapes.value, EntryMatchTapes.addressCounter,
    EntryMatchTapes.addressWidth, EntryMatchTapes.valueCounter,
    EntryMatchTapes.valueWidth, EntryMatchTapes.query, EntryMatchTapes.result,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupFoundBits_seven {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address tapes.scan.entry.query =
      address.bits := by
  simp [entryLookupFoundBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.query,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupFoundBits_eight {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (entry : Entry)
    (remaining address : ℕ) :
    entryLookupFoundBits tapes entry remaining address (tapes.idx 9) =
      remaining.bits := by
  simp [entryLookupFoundBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.query,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_seven {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address tapes.scan.entry.query = address.bits := by
  simp [entryLookupMissBits, EntryLookupRestoreTapes.resetIdx,
    EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.query,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_zero {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address tapes.scan.entry.address = [] := by
  simp [entryLookupMissBits, EntryMatchTapes.address, EntryMatchTapes.query,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_one {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address tapes.scan.entry.value = [] := by
  simp [entryLookupMissBits, EntryMatchTapes.value, EntryMatchTapes.query,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_two {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address tapes.scan.entry.addressCounter = [] := by
  simp [entryLookupMissBits, EntryMatchTapes.addressCounter,
    EntryMatchTapes.query, tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_three {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address tapes.scan.entry.addressWidth = [] := by
  simp [entryLookupMissBits, EntryMatchTapes.addressWidth,
    EntryMatchTapes.query, tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_four {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address tapes.scan.entry.valueCounter = [] := by
  simp [entryLookupMissBits, EntryMatchTapes.valueCounter,
    EntryMatchTapes.query, tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_five {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address tapes.scan.entry.valueWidth = [] := by
  simp [entryLookupMissBits, EntryMatchTapes.valueWidth,
    EntryMatchTapes.query, tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_six {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address tapes.scan.entry.result = [] := by
  simp [entryLookupMissBits, EntryMatchTapes.result, EntryMatchTapes.query,
    tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_eight {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) :
    entryLookupMissBits tapes address (tapes.idx 9) = [] := by
  simp [entryLookupMissBits, EntryMatchTapes.query, tapes.injective.eq_iff]

@[simp] theorem entryLookupMissBits_other {n : ℕ}
    (tapes : EntryLookupRestoreTapes n) (address : ℕ) (slot : Fin 9)
    (hslot : slot ≠ 7) :
    entryLookupMissBits tapes address (tapes.resetIdx slot) = [] := by
  fin_cases slot <;>
    simp_all [entryLookupMissBits, EntryLookupRestoreTapes.resetIdx,
      EntryLookupRestoreTapes.resetSlot, EntryMatchTapes.query,
      tapes.injective.eq_iff]
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
