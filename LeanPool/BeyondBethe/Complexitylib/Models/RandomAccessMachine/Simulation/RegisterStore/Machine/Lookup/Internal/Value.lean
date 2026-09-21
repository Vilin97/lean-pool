/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Reusable sparse-register lookup -- value rewind and copy
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem reset_value_mem (tapes : EntryLookupRestoreTapes n) :
    tapes.scan.entry.value ∈ entryLookupResetTargets tapes := by
  apply List.mem_ofFn.mpr
  exact ⟨1, EntryLookupRestoreTapes.resetIdx_one tapes⟩

private theorem scanned_restoreInvariant
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork preparedWork scannedWork : Fin n → Tape)
    (hprepared : EntryLookupPrepared tapes store address initialWork
      preparedWork)
    (hscanned : EntryLookupScanned tapes store address initialWork
      preparedWork scannedWork) :
    EntryLookupRestoreInvariant tapes store address initialWork scannedWork := by
  have hpreparedScratch : preparedWork tapes.copyScratch =
      initialWork tapes.copyScratch :=
    hprepared.frame _ (Ne.symm (tapes.scan_ne_external 7 3))
  refine
    { valueContent := hscanned.result.value.2
      valueStart := hscanned.result.valueStart
      resetReady := hscanned.resetReady
      sourceCells := hscanned.sourceCells
      sourceStart := hscanned.sourceStart
      sourceHeadBound := hscanned.sourceHeadBound
      resetHeadBound := hscanned.resetHeadBound
      countSource := hscanned.countSource
      countSourceNat := ?_
      querySource := hscanned.querySource
      querySourceNat := ?_
      copyScratch := hscanned.copyScratch
      copyScratchNat := ?_
      parked := hscanned.result.parked
      frame := hscanned.frame }
  · rw [hscanned.countSource, ← hprepared.countSource]
    exact hprepared.countSourceNat
  · rw [hscanned.querySource, ← hprepared.querySource]
    exact hprepared.querySourceNat
  · rw [hscanned.copyScratch, ← hpreparedScratch]
    exact hprepared.copyScratch

private theorem restoreInvariant_rewindValue
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work work' : Fin n → Tape)
    (hrestore : EntryLookupRestoreInvariant tapes store address initialWork
      work)
    (hcells : (work' tapes.scan.entry.value).cells =
      (work tapes.scan.entry.value).cells)
    (hhead : (work' tapes.scan.entry.value).head = 1)
    (hother : ∀ i, i ≠ tapes.scan.entry.value → work' i = work i) :
    EntryLookupRestoreInvariant tapes store address initialWork work' := by
  have hsourceValue :
      tapes.scan.entry.source ≠ tapes.scan.entry.value :=
    tapes.scan.entry.ne (by decide)
  have hcountSourceValue : tapes.countSource ≠
      tapes.scan.entry.value :=
    Ne.symm (tapes.scan_ne_external 2 0)
  have hquerySourceValue : tapes.querySource ≠
      tapes.scan.entry.value :=
    Ne.symm (tapes.scan_ne_external 2 1)
  have hcopyScratchValue : tapes.copyScratch ≠
      tapes.scan.entry.value :=
    Ne.symm (tapes.scan_ne_external 2 3)
  have hreset : EntryLookupResetReady tapes store address work' := by
    rcases hrestore.resetReady with
      ⟨bits, hcontent, hstart, hwidth, hparked⟩
    refine ⟨bits, ?_, ?_, hwidth, ?_⟩
    · intro i hi
      by_cases hivalue : i = tapes.scan.entry.value
      · subst i
        simpa only [Tape.HasBinaryContent, hcells] using hcontent _ hi
      · rw [hother i hivalue]
        exact hcontent i hi
    · intro i hi
      by_cases hivalue : i = tapes.scan.entry.value
      · subst i
        simpa only [hcells] using hstart _ hi
      · rw [hother i hivalue]
        exact hstart i hi
    · intro i
      by_cases hivalue : i = tapes.scan.entry.value
      · subst i
        exact ⟨by omega, by
          simpa only [hcells] using
            hrestore.valueContent.cells_ne_start⟩
      · rw [hother i hivalue]
        exact hparked i
  refine
    { valueContent := by
        simpa only [Tape.HasBinaryContent, hcells] using
          hrestore.valueContent
      valueStart := by simpa only [hcells] using hrestore.valueStart
      resetReady := hreset
      sourceCells := by
        rw [hother _ hsourceValue]
        exact hrestore.sourceCells
      sourceStart := by
        rw [hother _ hsourceValue]
        exact hrestore.sourceStart
      sourceHeadBound := by
        rw [hother _ hsourceValue]
        exact hrestore.sourceHeadBound
      resetHeadBound := ?_
      countSource := by
        rw [hother _ hcountSourceValue]
        exact hrestore.countSource
      countSourceNat := by
        rw [hother _ hcountSourceValue]
        exact hrestore.countSourceNat
      querySource := by
        rw [hother _ hquerySourceValue]
        exact hrestore.querySource
      querySourceNat := by
        rw [hother _ hquerySourceValue]
        exact hrestore.querySourceNat
      copyScratch := by
        rw [hother _ hcopyScratchValue]
        exact hrestore.copyScratch
      copyScratchNat := by
        rw [hother _ hcopyScratchValue]
        exact hrestore.copyScratchNat
      parked := hreset.choose_spec.2.2.2
      frame := ?_ }
  · intro i hi
    by_cases hivalue : i = tapes.scan.entry.value
    · subst i
      simp only [entryLookupRestoreHeadBound]
      omega
    · rw [hother i hivalue]
      exact hrestore.resetHeadBound i hi
  · intro i hall
    rw [hother i (hall 2)]
    exact hrestore.frame i hall

private theorem destination_zero_of_scanned
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork preparedWork scannedWork : Fin n → Tape)
    (hprepared : EntryLookupPrepared tapes store address initialWork
      preparedWork)
    (hscanned : EntryLookupScanned tapes store address initialWork
      preparedWork scannedWork) :
    (scannedWork tapes.destination).HasBinaryNat 0 := by
  have hpreparedDestination : preparedWork tapes.destination =
      initialWork tapes.destination :=
    hprepared.frame _ (Ne.symm (tapes.scan_ne_external 7 2))
  rw [hscanned.destination, ← hpreparedDestination]
  exact hprepared.destination

/-- Rewinding the decoded value converts its append-position prefix into a
canonical binary natural without losing any cleanup or frame information. -/
theorem entryLookupValueRewind_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork preparedWork scannedWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hprepared : EntryLookupPrepared tapes store address initialWork
      preparedWork)
    (hscanned : EntryLookupScanned tapes store address initialWork
      preparedWork scannedWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.rewindWorkTM tapes.scan.entry.value).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = scannedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupValueReady tapes store address initialWork work ∧
        out = out₀)
      (entryLookupRestoreHeadBound tapes store address + 2) := by
  let P : Tape → (Fin n → Tape) → Tape → Prop :=
    fun inp work out =>
      inp = inp₀ ∧
      EntryLookupRestoreInvariant tapes store address initialWork work ∧
      (work tapes.destination).HasBinaryNat 0 ∧
      out = out₀
  have hpreserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' tapes.scan.entry.value).cells =
        (work tapes.scan.entry.value).cells →
      (work' tapes.scan.entry.value).head = 1 →
      (∀ i, i ≠ tapes.scan.entry.value → work' i = work i) →
      inp' = inp → out'.cells = out.cells → out'.head = out.head →
      P inp' work' out' := by
    rintro inp work out inp' work' out'
      ⟨hinp, hrestore, hdestination, hout⟩ hcells hhead hother
      hinp' houtCells houtHead
    have hdestinationValue : tapes.destination ≠
        tapes.scan.entry.value :=
      Ne.symm (tapes.scan_ne_external 2 2)
    refine ⟨hinp'.trans hinp,
      restoreInvariant_rewindValue tapes store address initialWork work work'
        hrestore hcells hhead hother, ?_, ?_⟩
    · rw [hother _ hdestinationValue]
      exact hdestination
    · exact (Tape.ext houtHead houtCells).trans hout
  have hrewind := TM.rewindWorkTM_hoareTime_frame
    tapes.scan.entry.value
    (entryLookupRestoreHeadBound tapes store address) hpreserved
  exact hrewind.consequence
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      rw [hinp, hwork, hout]
      have hrestore := scanned_restoreInvariant tapes store address initialWork
        preparedWork scannedWork hprepared hscanned
      refine ⟨hrestore.valueStart,
        hrestore.valueContent.cells_ne_start,
        hrestore.resetHeadBound _ (reset_value_mem tapes),
        hinput.read_ne_start, houtput.read_ne_start, houtput.1, ?_, ?_⟩
      · intro i hi
        exact ⟨(hrestore.parked i).read_ne_start,
          (hrestore.parked i).1⟩
      · exact ⟨rfl, hrestore,
          destination_zero_of_scanned tapes store address initialWork
            preparedWork scannedWork hprepared hscanned,
          rfl⟩)
    (by
      rintro inp work out ⟨hvalueHead, hinp, hrestore, hdestination, hout⟩
      exact ⟨hinp, ⟨hrestore,
        ⟨hrestore.valueStart,
          hrestore.valueContent.hasBinaryString hvalueHead⟩,
        hdestination⟩, hout⟩)
    le_rfl

private theorem reset_destination_not_mem
    (tapes : EntryLookupRestoreTapes n) :
    tapes.destination ∉ entryLookupResetTargets tapes := by
  intro hi
  obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · change tapes.scan.entry.address = tapes.destination at hslot
    exact tapes.scan_ne_external 1 2 hslot
  · change tapes.scan.entry.value = tapes.destination at hslot
    exact tapes.scan_ne_external 2 2 hslot
  · change tapes.scan.entry.addressCounter = tapes.destination at hslot
    exact tapes.scan_ne_external 3 2 hslot
  · change tapes.scan.entry.addressWidth = tapes.destination at hslot
    exact tapes.scan_ne_external 4 2 hslot
  · change tapes.scan.entry.valueCounter = tapes.destination at hslot
    exact tapes.scan_ne_external 5 2 hslot
  · change tapes.scan.entry.valueWidth = tapes.destination at hslot
    exact tapes.scan_ne_external 6 2 hslot
  · change tapes.scan.entry.result = tapes.destination at hslot
    exact tapes.scan_ne_external 8 2 hslot
  · change tapes.scan.entry.query = tapes.destination at hslot
    exact tapes.scan_ne_external 7 2 hslot
  · change tapes.scan.count = tapes.destination at hslot
    exact tapes.scan_ne_external 9 2 hslot

private theorem restoreInvariant_update_destination
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape) (destinationTape : Tape)
    (hrestore : EntryLookupRestoreInvariant tapes store address initialWork
      work)
    (hdestinationParked : TM.Parked destinationTape) :
    EntryLookupRestoreInvariant tapes store address initialWork
      (Function.update work tapes.destination destinationTape) := by
  let work' := Function.update work tapes.destination destinationTape
  have hsourceDestination : tapes.scan.entry.source ≠ tapes.destination :=
    tapes.scan_ne_external 0 2
  have hvalueDestination : tapes.scan.entry.value ≠ tapes.destination :=
    tapes.scan_ne_external 2 2
  have hcountSourceDestination :
      tapes.countSource ≠ tapes.destination :=
    tapes.countSource_ne_destination
  have hquerySourceDestination :
      tapes.querySource ≠ tapes.destination :=
    tapes.querySource_ne_destination
  have hcopyScratchDestination :
      tapes.copyScratch ≠ tapes.destination :=
    Ne.symm tapes.destination_ne_copyScratch
  have hreset : EntryLookupResetReady tapes store address work' := by
    rcases hrestore.resetReady with
      ⟨bits, hcontent, hstart, hwidth, hparked⟩
    refine ⟨bits, ?_, ?_, hwidth, ?_⟩
    · intro i hi
      have hne : i ≠ tapes.destination := by
        intro heq
        exact reset_destination_not_mem tapes (heq ▸ hi)
      simp only [work', Function.update_of_ne hne]
      exact hcontent i hi
    · intro i hi
      have hne : i ≠ tapes.destination := by
        intro heq
        exact reset_destination_not_mem tapes (heq ▸ hi)
      simp only [work', Function.update_of_ne hne]
      exact hstart i hi
    · intro i
      by_cases hi : i = tapes.destination
      · subst i
        simpa only [work', Function.update_self] using hdestinationParked
      · simp only [work', Function.update_of_ne hi]
        exact hparked i
  refine
    { valueContent := by
        simpa only [work', Function.update_of_ne hvalueDestination] using
          hrestore.valueContent
      valueStart := by
        simpa only [work', Function.update_of_ne hvalueDestination] using
          hrestore.valueStart
      resetReady := hreset
      sourceCells := by
        simpa only [work', Function.update_of_ne hsourceDestination] using
          hrestore.sourceCells
      sourceStart := by
        simpa only [work', Function.update_of_ne hsourceDestination] using
          hrestore.sourceStart
      sourceHeadBound := by
        simpa only [work', Function.update_of_ne hsourceDestination] using
          hrestore.sourceHeadBound
      resetHeadBound := ?_
      countSource := by
        simpa only [work', Function.update_of_ne hcountSourceDestination] using
          hrestore.countSource
      countSourceNat := by
        simpa only [work', Function.update_of_ne hcountSourceDestination] using
          hrestore.countSourceNat
      querySource := by
        simpa only [work', Function.update_of_ne hquerySourceDestination] using
          hrestore.querySource
      querySourceNat := by
        simpa only [work', Function.update_of_ne hquerySourceDestination] using
          hrestore.querySourceNat
      copyScratch := by
        simpa only [work', Function.update_of_ne hcopyScratchDestination] using
          hrestore.copyScratch
      copyScratchNat := by
        simpa only [work', Function.update_of_ne hcopyScratchDestination] using
          hrestore.copyScratchNat
      parked := hreset.choose_spec.2.2.2
      frame := ?_ }
  · intro i hi
    have hne : i ≠ tapes.destination := by
      intro heq
      exact reset_destination_not_mem tapes (heq ▸ hi)
    simpa only [work', Function.update_of_ne hne] using
      hrestore.resetHeadBound i hi
  · intro i hall
    have hne : i ≠ tapes.destination := hall 12
    change Function.update work tapes.destination destinationTape i =
      initialWork i
    rw [Function.update_of_ne hne]
    exact hrestore.frame i hall

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

/-- Copy the rewound decoded value into the instruction operand tape. The
source value and zero scratch stay canonical, and all restoration data is
preserved. -/
theorem entryLookupValueCopy_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work₀ : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryLookupValueReady tapes store address initialWork work₀)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.binaryCopyIntoTM tapes.scan.entry.value tapes.destination
      tapes.copyScratch).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupCopied tapes store address initialWork work ∧
        out = out₀)
      (TM.binaryCopyTime (RegisterStore.read store address) 0) := by
  let value := RegisterStore.read store address
  have hcopy := TM.binaryCopyIntoTM_hoareTime_frame
    tapes.scan.entry.value tapes.destination tapes.copyScratch
    (tapes.scan_ne_external 2 2) (tapes.scan_ne_external 2 3)
    tapes.destination_ne_copyScratch value 0 inp₀ work₀ out₀
    hready.value hready.destination hready.restore.copyScratchNat hinput
    (fun i _ _ _ => hready.restore.parked i) houtput
  exact hcopy.strengthen_post (by
    rintro inp work out ⟨hinp, hwork, hout⟩
    let destinationTape :=
      (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right
    let copiedWork := Function.update work₀ tapes.destination destinationTape
    have hwork' : work = copiedWork := by
      simpa [copiedWork, destinationTape, value] using hwork
    clear hwork
    subst work
    have hdestinationNat :
        (copiedWork tapes.destination).HasBinaryNat value := by
      rw [show copiedWork tapes.destination = destinationTape by
        simp [copiedWork]]
      simpa [destinationTape] using
        Tape.init_move_right_hasBinaryNat value
    have hrestore : EntryLookupRestoreInvariant tapes store address
        initialWork copiedWork := by
      exact restoreInvariant_update_destination tapes store address initialWork
        work₀ destinationTape hready.restore
          (hasBinaryNat_parked (by
            simpa [destinationTape] using
              Tape.init_move_right_hasBinaryNat value))
    have hvalueNat :
        (copiedWork tapes.scan.entry.value).HasBinaryNat value := by
      have heq : copiedWork tapes.scan.entry.value =
          work₀ tapes.scan.entry.value := by
        have hne : tapes.scan.entry.value ≠ tapes.destination :=
          tapes.scan_ne_external 2 2
        change Function.update work₀ tapes.destination destinationTape
          tapes.scan.entry.value = work₀ tapes.scan.entry.value
        rw [Function.update_of_ne hne]
      rw [heq]
      simpa [value] using hready.value
    exact ⟨hinp, ⟨hrestore, by simpa [value] using hvalueNat,
      by simpa [value] using hdestinationNat⟩, hout⟩)

end Machine

end RegisterStore

end RAM

end Complexity
