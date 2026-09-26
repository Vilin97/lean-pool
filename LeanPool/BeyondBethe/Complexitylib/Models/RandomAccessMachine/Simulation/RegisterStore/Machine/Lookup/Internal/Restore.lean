/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

/-!
# Reusable sparse-register lookup -- scanner restoration
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- Reset all nine scanner-owned binary tapes under one uniform width and
cursor envelope. -/
theorem entryLookupReset_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork copiedWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hcopied : EntryLookupCopied tapes store address initialWork copiedWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.resetBinaryWorkManyTM (entryLookupResetTargets tapes)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupResetDone tapes store address initialWork copiedWork work ∧
        out = out₀)
      (entryLookupResetTime tapes store address) := by
  rcases hcopied.restore.resetReady with
    ⟨bits, hcontent, hstart, hwidth, hparked⟩
  let headBound : Fin n → ℕ :=
    fun _ => entryLookupRestoreHeadBound tapes store address
  have hreset := TM.resetBinaryWorkManyTM_hoareTime_frame
    (entryLookupResetTargets tapes) bits headBound inp₀ copiedWork out₀
    (List.nodup_ofFn_ofInjective tapes.resetIdx_injective)
    hcontent hstart
    (by
      intro i hi
      exact hcopied.restore.resetHeadBound i hi)
    hinput hparked houtput
  have htime : TM.resetBinaryWorkManyTime bits headBound
      (entryLookupResetTargets tapes) ≤
      entryLookupResetTime tapes store address := by
    have hcoarse := TM.resetBinaryWorkManyTime_le
      (entryLookupResetTargets tapes) bits headBound
      (entryLookupRestoreHeadBound tapes store address)
      (entryLookupResetWidth store address)
      (by intro i hi; exact le_rfl) hwidth
    simpa [entryLookupResetTime, entryLookupResetTargets] using hcoarse
  exact (hreset.mono_bound htime).strengthen_post (by
    rintro inp work out ⟨hinp, hwork, hout⟩
    exact ⟨hinp, ⟨hcopied, hwork⟩, hout⟩)

private theorem reset_source_not_mem
    (tapes : EntryLookupRestoreTapes n) :
    tapes.scan.entry.source ∉ entryLookupResetTargets tapes := by
  intro hi
  obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · change tapes.scan.entry.address = tapes.scan.entry.source at hslot
    exact tapes.scan.entry.ne (i := 1) (j := 0) (by decide) hslot
  · change tapes.scan.entry.value = tapes.scan.entry.source at hslot
    exact tapes.scan.entry.ne (i := 2) (j := 0) (by decide) hslot
  · change tapes.scan.entry.addressCounter =
      tapes.scan.entry.source at hslot
    exact tapes.scan.entry.ne (i := 3) (j := 0) (by decide) hslot
  · change tapes.scan.entry.addressWidth =
      tapes.scan.entry.source at hslot
    exact tapes.scan.entry.ne (i := 4) (j := 0) (by decide) hslot
  · change tapes.scan.entry.valueCounter =
      tapes.scan.entry.source at hslot
    exact tapes.scan.entry.ne (i := 5) (j := 0) (by decide) hslot
  · change tapes.scan.entry.valueWidth = tapes.scan.entry.source at hslot
    exact tapes.scan.entry.ne (i := 6) (j := 0) (by decide) hslot
  · change tapes.scan.entry.result = tapes.scan.entry.source at hslot
    exact tapes.scan.entry.ne (i := 8) (j := 0) (by decide) hslot
  · change tapes.scan.entry.query = tapes.scan.entry.source at hslot
    exact tapes.scan.entry.ne (i := 7) (j := 0) (by decide) hslot
  · change tapes.scan.count = tapes.scan.entry.source at hslot
    exact tapes.scan.count_ne_source hslot

private theorem reset_external_not_mem
    (tapes : EntryLookupRestoreTapes n) (external : Fin 4) :
    tapes.idx ⟨external.val + 10, by omega⟩ ∉
      entryLookupResetTargets tapes := by
  intro hi
  obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · change tapes.scan.entry.address =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 1 external hslot
  · change tapes.scan.entry.value =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 2 external hslot
  · change tapes.scan.entry.addressCounter =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 3 external hslot
  · change tapes.scan.entry.addressWidth =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 4 external hslot
  · change tapes.scan.entry.valueCounter =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 5 external hslot
  · change tapes.scan.entry.valueWidth =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 6 external hslot
  · change tapes.scan.entry.result =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 8 external hslot
  · change tapes.scan.entry.query =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 7 external hslot
  · change tapes.scan.count =
      tapes.idx ⟨external.val + 10, by omega⟩ at hslot
    exact tapes.scan_ne_external 9 external hslot

private theorem not_mem_resetTargets_of_outside
    (tapes : EntryLookupRestoreTapes n) (i : Fin n)
    (hall : ∀ slot, i ≠ tapes.idx slot) :
    i ∉ entryLookupResetTargets tapes := by
  intro hi
  obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hi
  exact hall (EntryLookupRestoreTapes.resetSlot slot) hslot.symm

private theorem resetDone_scratchReset
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork copiedWork resetWork : Fin n → Tape)
    (hdone : EntryLookupResetDone tapes store address initialWork copiedWork
      resetWork) :
    EntryLookupScratchReset tapes store address initialWork resetWork := by
  rw [hdone.work_eq]
  let targets := entryLookupResetTargets tapes
  let work := TM.resetBinaryWorkManyResult copiedWork targets
  have hsource : work tapes.scan.entry.source =
      copiedWork tapes.scan.entry.source := by
    exact TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork targets _
      (reset_source_not_mem tapes)
  have hcountSource : TM.resetBinaryWorkManyResult copiedWork
      (entryLookupResetTargets tapes) tapes.countSource =
      copiedWork tapes.countSource :=
    TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork targets _
      (reset_external_not_mem tapes 0)
  have hquerySource : TM.resetBinaryWorkManyResult copiedWork
      (entryLookupResetTargets tapes) tapes.querySource =
      copiedWork tapes.querySource :=
    TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork targets _
      (reset_external_not_mem tapes 1)
  have hdestination : TM.resetBinaryWorkManyResult copiedWork
      (entryLookupResetTargets tapes) tapes.destination =
      copiedWork tapes.destination :=
    TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork targets _
      (reset_external_not_mem tapes 2)
  have hcopyScratch : TM.resetBinaryWorkManyResult copiedWork
      (entryLookupResetTargets tapes) tapes.copyScratch =
      copiedWork tapes.copyScratch :=
    TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork targets _
      (reset_external_not_mem tapes 3)
  refine
    { sourceCells := by
        rw [TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork
          (entryLookupResetTargets tapes) _ (reset_source_not_mem tapes)]
        exact hdone.copied.restore.sourceCells
      sourceStart := by
        rw [TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork
          (entryLookupResetTargets tapes) _ (reset_source_not_mem tapes)]
        exact hdone.copied.restore.sourceStart
      sourceHeadBound := by
        rw [TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork
          (entryLookupResetTargets tapes) _ (reset_source_not_mem tapes)]
        exact hdone.copied.restore.sourceHeadBound
      targetsBlank := by
        intro i hi
        exact TM.resetBinaryWorkManyResult_eq_blank_of_mem copiedWork targets i hi
      countSource := hcountSource.trans hdone.copied.restore.countSource
      countSourceNat := by
        rw [hcountSource]
        exact hdone.copied.restore.countSourceNat
      querySource := hquerySource.trans hdone.copied.restore.querySource
      querySourceNat := by
        rw [hquerySource]
        exact hdone.copied.restore.querySourceNat
      destination := by
        rw [hdestination]
        exact hdone.copied.destination
      copyScratch := hcopyScratch.trans hdone.copied.restore.copyScratch
      copyScratchNat := by
        rw [hcopyScratch]
        exact hdone.copied.restore.copyScratchNat
      parked := TM.resetBinaryWorkManyResult_parked copiedWork targets
        hdone.copied.restore.parked
      frame := ?_ }
  intro i hall
  rw [TM.resetBinaryWorkManyResult_eq_of_not_mem copiedWork targets i
    (not_mem_resetTargets_of_outside tapes i hall)]
  exact hdone.copied.restore.frame i hall

private theorem scratchReset_rewindSource
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work work' : Fin n → Tape)
    (hreset : EntryLookupScratchReset tapes store address initialWork work)
    (hcells : (work' tapes.scan.entry.source).cells =
      (work tapes.scan.entry.source).cells)
    (hhead : (work' tapes.scan.entry.source).head = 1)
    (hother : ∀ i, i ≠ tapes.scan.entry.source → work' i = work i) :
    EntryLookupScratchReset tapes store address initialWork work' := by
  have hcountSource : tapes.countSource ≠ tapes.scan.entry.source :=
    Ne.symm (tapes.scan_ne_external 0 0)
  have hquerySource : tapes.querySource ≠ tapes.scan.entry.source :=
    Ne.symm (tapes.scan_ne_external 0 1)
  have hdestination : tapes.destination ≠ tapes.scan.entry.source :=
    Ne.symm (tapes.scan_ne_external 0 2)
  have hcopyScratch : tapes.copyScratch ≠ tapes.scan.entry.source :=
    Ne.symm (tapes.scan_ne_external 0 3)
  refine
    { sourceCells := by
        rw [hcells]
        exact hreset.sourceCells
      sourceStart := by
        rw [hcells]
        exact hreset.sourceStart
      sourceHeadBound := by
        simp only [entryLookupRestoreHeadBound]
        omega
      targetsBlank := ?_
      countSource := by
        rw [hother _ hcountSource]
        exact hreset.countSource
      countSourceNat := by
        rw [hother _ hcountSource]
        exact hreset.countSourceNat
      querySource := by
        rw [hother _ hquerySource]
        exact hreset.querySource
      querySourceNat := by
        rw [hother _ hquerySource]
        exact hreset.querySourceNat
      destination := by
        rw [hother _ hdestination]
        exact hreset.destination
      copyScratch := by
        rw [hother _ hcopyScratch]
        exact hreset.copyScratch
      copyScratchNat := by
        rw [hother _ hcopyScratch]
        exact hreset.copyScratchNat
      parked := ?_
      frame := ?_ }
  · intro i hi
    have hne : i ≠ tapes.scan.entry.source := by
      intro heq
      exact reset_source_not_mem tapes (heq ▸ hi)
    rw [hother i hne]
    exact hreset.targetsBlank i hi
  · intro i
    by_cases hi : i = tapes.scan.entry.source
    · subst i
      exact ⟨by omega, by simpa only [hcells] using (hreset.parked _).2⟩
    · rw [hother i hi]
      exact hreset.parked i
  · intro i hall
    rw [hother i (hall 0)]
    exact hreset.frame i hall

private theorem reset_target_mem
    (tapes : EntryLookupRestoreTapes n) (slot : Fin 9) :
    tapes.resetIdx slot ∈ entryLookupResetTargets tapes :=
  List.mem_ofFn.mpr ⟨slot, rfl⟩

private theorem blank_hasBinaryNat_zero :
    TM.resetBinaryBlank.HasBinaryNat 0 := by
  simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0

private theorem blank_hasBinaryPrefix_nil :
    TM.resetBinaryBlank.HasBinaryPrefix [] := by
  have hstring : TM.resetBinaryBlank.HasBinaryString [] := by
    simpa using blank_hasBinaryNat_zero.2
  exact ⟨by simpa using hstring.1, hstring.2⟩

private theorem blank_parked : TM.Parked TM.resetBinaryBlank :=
  ⟨by rw [blank_hasBinaryNat_zero.2.1],
    blank_hasBinaryNat_zero.2.hasBinaryContent.cells_ne_start⟩

private theorem scratchReset_sourceReady
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work : Fin n → Tape)
    (hinitial : EntryLookupRestoreReady tapes store address initialWork)
    (hreset : EntryLookupScratchReset tapes store address initialWork work)
    (hsourceHead : (work tapes.scan.entry.source).head = 1) :
    EntryLookupSourceReady tapes store address initialWork work := by
  have hsource : (work tapes.scan.entry.source).HasBinarySuffix
      (store.flatMap Entry.encode) := by
    rw [Tape.HasBinarySuffix, hreset.sourceCells, hsourceHead]
    have hinitialSource := hinitial.scanner.source
    rw [Tape.HasBinarySuffix, hinitial.sourceHead] at hinitialSource
    exact hinitialSource
  have hblank := hreset.targetsBlank
  have haddress : work tapes.scan.entry.address = TM.resetBinaryBlank := by
    change work (tapes.resetIdx 0) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 0)
  have hvalue : work tapes.scan.entry.value = TM.resetBinaryBlank := by
    change work (tapes.resetIdx 1) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 1)
  have haddressCounter : work tapes.scan.entry.addressCounter =
      TM.resetBinaryBlank := by
    change work (tapes.resetIdx 2) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 2)
  have haddressWidth : work tapes.scan.entry.addressWidth =
      TM.resetBinaryBlank := by
    change work (tapes.resetIdx 3) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 3)
  have hvalueCounter : work tapes.scan.entry.valueCounter =
      TM.resetBinaryBlank := by
    change work (tapes.resetIdx 4) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 4)
  have hvalueWidth : work tapes.scan.entry.valueWidth =
      TM.resetBinaryBlank := by
    change work (tapes.resetIdx 5) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 5)
  have hresult : work tapes.scan.entry.result = TM.resetBinaryBlank := by
    change work (tapes.resetIdx 6) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 6)
  have hquery : work tapes.scan.entry.query = TM.resetBinaryBlank := by
    change work (tapes.resetIdx 7) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 7)
  have hcount : work tapes.scan.count = TM.resetBinaryBlank := by
    change work (tapes.resetIdx 8) = TM.resetBinaryBlank
    exact hblank _ (reset_target_mem tapes 8)
  have hscanner : EntryScanReady tapes.scan.entry
      (store.flatMap Entry.encode) [] work work := by
    refine
      { source := hsource
        address := by rw [haddress]; exact blank_hasBinaryPrefix_nil
        addressStart := by rw [haddress]; exact blank_hasBinaryNat_zero.1
        value := by rw [hvalue]; exact blank_hasBinaryPrefix_nil
        valueStart := by rw [hvalue]; exact blank_hasBinaryNat_zero.1
        addressCounter := by rw [haddressCounter]; exact blank_hasBinaryNat_zero
        addressWidth := by rw [haddressWidth]; exact blank_hasBinaryNat_zero
        valueCounter := by rw [hvalueCounter]; exact blank_hasBinaryNat_zero
        valueWidth := by rw [hvalueWidth]; exact blank_hasBinaryNat_zero
        query := by
          rw [hquery]
          simpa using blank_hasBinaryNat_zero.2
        queryStart := by rw [hquery]; exact blank_hasBinaryNat_zero.1
        result := by rw [hresult]; exact blank_hasBinaryPrefix_nil
        resultStart := by rw [hresult]; exact blank_hasBinaryNat_zero.1
        parked := hreset.parked
        frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
  exact
    { scanner := hscanner
      sourceCells := hreset.sourceCells
      sourceStart := hreset.sourceStart
      sourceHead := hsourceHead
      countZero := by rw [hcount]; exact blank_hasBinaryNat_zero
      countSource := hreset.countSource
      countSourceNat := hreset.countSourceNat
      querySource := hreset.querySource
      destination := hreset.destination
      copyScratch := hreset.copyScratch
      copyScratchNat := hreset.copyScratchNat
      parked := hreset.parked
      frame := hreset.frame }

/-- Rewind the read-only encoded store after resetting scanner scratch. -/
theorem entryLookupSourceRewind_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork copiedWork resetWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hinitial : EntryLookupRestoreReady tapes store address initialWork)
    (hdone : EntryLookupResetDone tapes store address initialWork copiedWork
      resetWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.rewindWorkTM tapes.scan.entry.source).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = resetWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupSourceReady tapes store address initialWork work ∧
        out = out₀)
      (entryLookupRestoreHeadBound tapes store address + 2) := by
  let P : Tape → (Fin n → Tape) → Tape → Prop :=
    fun inp work out => inp = inp₀ ∧
      EntryLookupScratchReset tapes store address initialWork work ∧
      out = out₀
  have hpreserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' tapes.scan.entry.source).cells =
        (work tapes.scan.entry.source).cells →
      (work' tapes.scan.entry.source).head = 1 →
      (∀ i, i ≠ tapes.scan.entry.source → work' i = work i) →
      inp' = inp → out'.cells = out.cells → out'.head = out.head →
      P inp' work' out' := by
    rintro inp work out inp' work' out' ⟨hinp, hreset, hout⟩
      hcells hhead hother hinp' houtCells houtHead
    exact ⟨hinp'.trans hinp,
      scratchReset_rewindSource tapes store address initialWork work work'
        hreset hcells hhead hother,
      (Tape.ext houtHead houtCells).trans hout⟩
  have hrewind := TM.rewindWorkTM_hoareTime_frame
    tapes.scan.entry.source
    (entryLookupRestoreHeadBound tapes store address) hpreserved
  exact hrewind.consequence
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      rw [hinp, hwork, hout]
      have hreset := resetDone_scratchReset tapes store address initialWork
        copiedWork resetWork hdone
      refine ⟨hreset.sourceStart, (hreset.parked _).2,
        hreset.sourceHeadBound, hinput.read_ne_start,
        houtput.read_ne_start, houtput.1, ?_, ⟨rfl, hreset, rfl⟩⟩
      intro i hi
      exact ⟨(hreset.parked i).read_ne_start, (hreset.parked i).1⟩)
    (by
      rintro inp work out ⟨hsourceHead, hinp, hreset, hout⟩
      exact ⟨hinp,
        scratchReset_sourceReady tapes store address initialWork work hinitial
          hreset hsourceHead,
        hout⟩)
    le_rfl

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

/-- Restore the runtime entry count from its preserved canonical copy. This is
the final phase returning the scanner to its reusable blank-query boundary. -/
theorem entryLookupCountRestore_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork work₀ : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryLookupSourceReady tapes store address initialWork work₀)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.binaryCopyIntoTM tapes.countSource tapes.scan.count
      tapes.copyScratch).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupRestoreResult tapes store address initialWork work ∧
        out = out₀)
      (TM.binaryCopyTime store.length 0) := by
  have hcopy := TM.binaryCopyIntoTM_hoareTime_frame
    tapes.countSource tapes.scan.count tapes.copyScratch
    (Ne.symm (tapes.scan_ne_external 9 0))
    tapes.countSource_ne_copyScratch
    (tapes.scan_ne_external 9 3) store.length 0 inp₀ work₀ out₀
    hready.countSourceNat hready.countZero hready.copyScratchNat hinput
    (fun i _ _ _ => hready.parked i) houtput
  exact hcopy.strengthen_post (by
    rintro inp work out ⟨hinp, hwork, hout⟩
    let countTape :=
      (Tape.init (store.length.bits.map Γ.ofBool)).move Dir3.right
    let restoredWork := Function.update work₀ tapes.scan.count countTape
    have hwork' : work = restoredWork := by
      simpa [restoredWork, countTape] using hwork
    clear hwork
    subst work
    have hother : ∀ i, i ≠ tapes.scan.count →
        restoredWork i = work₀ i := by
      intro i hi
      have hi' : i ≠ tapes.scan.count := hi
      exact Function.update_of_ne hi' countTape work₀
    have hcount :
        (restoredWork tapes.scan.count).HasBinaryNat store.length := by
      rw [show restoredWork tapes.scan.count = countTape by
        simp [restoredWork]]
      simpa [countTape] using Tape.init_move_right_hasBinaryNat store.length
    have hscanner : EntryScanReady tapes.scan.entry
        (store.flatMap Entry.encode) [] restoredWork restoredWork := by
      have hcountNe : ∀ slot, tapes.scan.entry.idx slot ≠
          tapes.scan.count := by
        intro slot
        exact Ne.symm (tapes.scan.count_ne slot)
      have hentryOther : ∀ slot, restoredWork (tapes.scan.entry.idx slot) =
          work₀ (tapes.scan.entry.idx slot) := by
        intro slot
        exact hother _ (hcountNe slot)
      refine
        { source := by
            change (restoredWork (tapes.scan.entry.idx 0)).HasBinarySuffix _
            rw [hentryOther 0]
            exact hready.scanner.source
          address := by
            change (restoredWork (tapes.scan.entry.idx 1)).HasBinaryPrefix []
            rw [hentryOther 1]
            exact hready.scanner.address
          addressStart := by
            change (restoredWork (tapes.scan.entry.idx 1)).cells 0 = Γ.start
            rw [hentryOther 1]
            exact hready.scanner.addressStart
          value := by
            change (restoredWork (tapes.scan.entry.idx 2)).HasBinaryPrefix []
            rw [hentryOther 2]
            exact hready.scanner.value
          valueStart := by
            change (restoredWork (tapes.scan.entry.idx 2)).cells 0 = Γ.start
            rw [hentryOther 2]
            exact hready.scanner.valueStart
          addressCounter := by
            change (restoredWork (tapes.scan.entry.idx 3)).HasBinaryNat 0
            rw [hentryOther 3]
            exact hready.scanner.addressCounter
          addressWidth := by
            change (restoredWork (tapes.scan.entry.idx 4)).HasBinaryNat 0
            rw [hentryOther 4]
            exact hready.scanner.addressWidth
          valueCounter := by
            change (restoredWork (tapes.scan.entry.idx 5)).HasBinaryNat 0
            rw [hentryOther 5]
            exact hready.scanner.valueCounter
          valueWidth := by
            change (restoredWork (tapes.scan.entry.idx 6)).HasBinaryNat 0
            rw [hentryOther 6]
            exact hready.scanner.valueWidth
          query := by
            change (restoredWork (tapes.scan.entry.idx 7)).HasBinaryString []
            rw [hentryOther 7]
            exact hready.scanner.query
          queryStart := by
            change (restoredWork (tapes.scan.entry.idx 7)).cells 0 = Γ.start
            rw [hentryOther 7]
            exact hready.scanner.queryStart
          result := by
            change (restoredWork (tapes.scan.entry.idx 8)).HasBinaryPrefix []
            rw [hentryOther 8]
            exact hready.scanner.result
          resultStart := by
            change (restoredWork (tapes.scan.entry.idx 8)).cells 0 = Γ.start
            rw [hentryOther 8]
            exact hready.scanner.resultStart
          parked := by
            intro i
            by_cases hi : i = tapes.scan.count
            · subst i
              exact hasBinaryNat_parked hcount
            · rw [hother i hi]
              exact hready.parked i
          frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
    have hcountSource : restoredWork tapes.countSource =
        initialWork tapes.countSource := by
      have heq : restoredWork tapes.countSource = work₀ tapes.countSource :=
        hother _ (Ne.symm (tapes.scan_ne_external 9 0))
      exact heq.trans hready.countSource
    have hquerySource : restoredWork tapes.querySource =
        initialWork tapes.querySource := by
      have heq : restoredWork tapes.querySource = work₀ tapes.querySource :=
        hother _ (Ne.symm (tapes.scan_ne_external 9 1))
      exact heq.trans hready.querySource
    have hdestination :
        (restoredWork tapes.destination).HasBinaryNat
          (RegisterStore.read store address) := by
      have heq : restoredWork tapes.destination = work₀ tapes.destination :=
        hother _ (Ne.symm (tapes.scan_ne_external 9 2))
      rw [heq]
      exact hready.destination
    have hcopyScratch : restoredWork tapes.copyScratch =
        initialWork tapes.copyScratch := by
      have heq : restoredWork tapes.copyScratch = work₀ tapes.copyScratch :=
        hother _ (Ne.symm (tapes.scan_ne_external 9 3))
      exact heq.trans hready.copyScratch
    have hcopyScratchNat :
        (restoredWork tapes.copyScratch).HasBinaryNat 0 := by
      have heq : restoredWork tapes.copyScratch = work₀ tapes.copyScratch :=
        hother _ (Ne.symm (tapes.scan_ne_external 9 3))
      rw [heq]
      exact hready.copyScratchNat
    have hparked : ∀ i, TM.Parked (restoredWork i) := hscanner.parked
    have hsourceStart :
        (restoredWork tapes.scan.entry.source).cells 0 = Γ.start := by
      rw [hother _ (Ne.symm tapes.scan.count_ne_source)]
      exact hready.sourceStart
    have hsourceHead :
        (restoredWork tapes.scan.entry.source).head = 1 := by
      rw [hother _ (Ne.symm tapes.scan.count_ne_source)]
      exact hready.sourceHead
    refine ⟨hinp, ⟨hscanner, ?_, hsourceStart, hsourceHead, hcount,
      hcountSource, hquerySource,
      hdestination, hcopyScratchNat, hparked, ?_⟩, hout⟩
    · rw [hother _ (Ne.symm tapes.scan.count_ne_source)]
      exact hready.sourceCells
    intro i hall
    rw [hother i (hall 9)]
    exact hready.frame i hall)

/-- Semantic reset boundary used by sequential lookup composition. -/
theorem entryLookupReset_ready_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.resetBinaryWorkManyTM (entryLookupResetTargets tapes)).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupCopied tapes store address initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupScratchReset tapes store address initialWork work ∧
        out = out₀)
      (entryLookupResetTime tapes store address) := by
  intro inp work out ⟨hinp, hcopied, hout⟩
  have hrun := entryLookupReset_hoareTime_internal tapes store address
    initialWork work inp₀ out₀ hcopied hinput houtput
  obtain ⟨final, time, htime, hreach, hhalt, hfinalInput, hdone,
      hfinalOutput⟩ :=
    hrun inp work out ⟨hinp, rfl, hout⟩
  exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
    resetDone_scratchReset tapes store address initialWork work final.work
      hdone,
    hfinalOutput⟩

/-- Semantic encoded-source rewind boundary used by sequential composition. -/
theorem entryLookupSourceRewind_ready_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hinitial : EntryLookupRestoreReady tapes store address initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.rewindWorkTM tapes.scan.entry.source).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupScratchReset tapes store address initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupSourceReady tapes store address initialWork work ∧
        out = out₀)
      (entryLookupRestoreHeadBound tapes store address + 2) := by
  let P : Tape → (Fin n → Tape) → Tape → Prop :=
    fun inp work out => inp = inp₀ ∧
      EntryLookupScratchReset tapes store address initialWork work ∧
      out = out₀
  have hpreserved : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' tapes.scan.entry.source).cells =
        (work tapes.scan.entry.source).cells →
      (work' tapes.scan.entry.source).head = 1 →
      (∀ i, i ≠ tapes.scan.entry.source → work' i = work i) →
      inp' = inp → out'.cells = out.cells → out'.head = out.head →
      P inp' work' out' := by
    rintro inp work out inp' work' out' ⟨hinp, hreset, hout⟩
      hcells hhead hother hinp' houtCells houtHead
    exact ⟨hinp'.trans hinp,
      scratchReset_rewindSource tapes store address initialWork work work'
        hreset hcells hhead hother,
      (Tape.ext houtHead houtCells).trans hout⟩
  have hrewind := TM.rewindWorkTM_hoareTime_frame
    tapes.scan.entry.source
    (entryLookupRestoreHeadBound tapes store address) hpreserved
  exact hrewind.consequence
    (by
      rintro inp work out ⟨hinp, hreset, hout⟩
      refine ⟨hreset.sourceStart, (hreset.parked _).2,
        hreset.sourceHeadBound, ?_, ?_, ?_, ?_, ⟨hinp, hreset, hout⟩⟩
      · simpa [hinp] using hinput.read_ne_start
      · simpa [hout] using houtput.read_ne_start
      · simpa [hout] using houtput.1
      · intro i hi
        exact ⟨(hreset.parked i).read_ne_start, (hreset.parked i).1⟩)
    (by
      rintro inp work out ⟨hsourceHead, hinp, hreset, hout⟩
      exact ⟨hinp,
        scratchReset_sourceReady tapes store address initialWork work hinitial
          hreset hsourceHead,
        hout⟩)
    le_rfl

/-- Semantic count-copy boundary used by sequential composition. -/
theorem entryLookupCountRestore_ready_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.binaryCopyIntoTM tapes.countSource tapes.scan.count
      tapes.copyScratch).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupSourceReady tapes store address initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupRestoreResult tapes store address initialWork work ∧
        out = out₀)
      (TM.binaryCopyTime store.length 0) := by
  intro inp work out ⟨hinp, hready, hout⟩
  exact entryLookupCountRestore_hoareTime_internal tapes store address
    initialWork work inp₀ out₀ hready hinput houtput inp work out
      ⟨hinp, rfl, hout⟩

end Machine

end RegisterStore

end RAM

end Complexity
