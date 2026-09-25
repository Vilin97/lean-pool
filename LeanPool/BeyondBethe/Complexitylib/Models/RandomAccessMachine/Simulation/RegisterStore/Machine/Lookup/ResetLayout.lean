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
# Reusable lookup tape layout and scratch encodings

The fourteen-tape lookup assignment, fixed reset targets, width bounds, and
found/missing bit encodings used by the reusable lookup controller.
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

end Machine

end RegisterStore

end RAM

end Complexity
