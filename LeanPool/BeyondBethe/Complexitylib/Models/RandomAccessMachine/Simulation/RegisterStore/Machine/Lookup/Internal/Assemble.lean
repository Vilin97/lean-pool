/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Prepare
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Restore
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Scan
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Value

/-!
# Reusable sparse-register lookup -- phase assembly
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem entryLookupScan_ready_hoareTime
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupTM tapes.scan).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupPrepared tapes store address initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupScannedReady tapes store address initialWork work ∧
        out = out₀)
      (entryLookupTime tapes.scan address store) := by
  intro inp work out ⟨hinp, hprepared, hout⟩
  have hrun := entryLookupScan_hoareTime_internal tapes store address
    initialWork work inp₀ out₀ hprepared hinput houtput
  obtain ⟨final, time, htime, hreach, hhalt, hfinalInput, hscanned,
      hfinalOutput⟩ := hrun inp work out ⟨hinp, rfl, hout⟩
  exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
    ⟨work, hprepared, hscanned⟩, hfinalOutput⟩

private theorem entryLookupValueRewind_ready_hoareTime
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.rewindWorkTM tapes.scan.entry.value).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupScannedReady tapes store address initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupValueReady tapes store address initialWork work ∧
        out = out₀)
      (entryLookupRestoreHeadBound tapes store address + 2) := by
  intro inp work out ⟨hinp, hscanned, hout⟩
  rcases hscanned with ⟨preparedWork, hprepared, hscanned⟩
  exact entryLookupValueRewind_hoareTime_internal tapes store address
    initialWork preparedWork work inp₀ out₀ hprepared hscanned hinput
      houtput inp work out ⟨hinp, rfl, hout⟩

private theorem entryLookupValueCopy_ready_hoareTime
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.binaryCopyIntoTM tapes.scan.entry.value tapes.destination
      tapes.copyScratch).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupValueReady tapes store address initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupCopied tapes store address initialWork work ∧
        out = out₀)
      (TM.binaryCopyTime (RegisterStore.read store address) 0) := by
  intro inp work out ⟨hinp, hready, hout⟩
  exact entryLookupValueCopy_hoareTime_internal tapes store address
    initialWork work inp₀ out₀ hready hinput houtput inp work out
      ⟨hinp, rfl, hout⟩

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_eq_self_of_reads_ne_start hinput.read_ne_start
    (fun i => (hwork i).read_ne_start) houtput.read_ne_start

/-- Scanner reset, source rewind, and count restoration form one reusable tail
whose endpoint is the original blank-query scanner ABI. -/
theorem entryLookupRestoreTail_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hinitial : EntryLookupRestoreReady tapes store address initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupRestoreTailTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupCopied tapes store address initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupRestoreResult tapes store address initialWork work ∧
        out = out₀)
      (entryLookupRestoreTailTime tapes store address) := by
  have hreset := entryLookupReset_ready_hoareTime_internal tapes store address
    initialWork inp₀ out₀ hinput houtput
  have hsource := entryLookupSourceRewind_ready_hoareTime_internal tapes store
    address initialWork inp₀ out₀ hinitial hinput houtput
  have hcount := entryLookupCountRestore_ready_hoareTime_internal tapes store
    address initialWork inp₀ out₀ hinput houtput
  have hsourceCount := TM.seqTM_hoareTime
    (TM.rewindWorkTM tapes.scan.entry.source)
    (TM.binaryCopyIntoTM tapes.countSource tapes.scan.count
      tapes.copyScratch)
    hsource
    (by
      rintro inp work out ⟨hinp, hready, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hready.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hready, hout⟩)
    hcount
  have hall := TM.seqTM_hoareTime
    (TM.resetBinaryWorkManyTM (entryLookupResetTargets tapes))
    (TM.seqTM (TM.rewindWorkTM tapes.scan.entry.source)
      (TM.binaryCopyIntoTM tapes.countSource tapes.scan.count
        tapes.copyScratch))
    hreset
    (by
      rintro inp work out ⟨hinp, hready, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hready.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hready, hout⟩)
    hsourceCount
  simpa [entryLookupRestoreTailTM, entryLookupRestoreTailTime] using hall

/-- Once the external query has been prepared, scanning, value extraction,
and complete restoration form one reusable lookup. -/
theorem entryLookupCopyRestore_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hinitial : EntryLookupRestoreReady tapes store address initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupCopyRestoreTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupPrepared tapes store address initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupRestoreResult tapes store address initialWork work ∧
        out = out₀)
      (entryLookupCopyRestoreTime tapes store address) := by
  have hscan := entryLookupScan_ready_hoareTime tapes store address initialWork
    inp₀ out₀ hinput houtput
  have hrewind := entryLookupValueRewind_ready_hoareTime tapes store address
    initialWork inp₀ out₀ hinput houtput
  have hcopy := entryLookupValueCopy_ready_hoareTime tapes store address
    initialWork inp₀ out₀ hinput houtput
  have htail := entryLookupRestoreTail_hoareTime_internal tapes store address
    initialWork inp₀ out₀ hinitial hinput houtput
  have hcopyTail := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM tapes.scan.entry.value tapes.destination
      tapes.copyScratch)
    (entryLookupRestoreTailTM tapes) hcopy
    (by
      rintro inp work out ⟨hinp, hready, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hready.restore.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hready, hout⟩)
    htail
  have hrewindRest := TM.seqTM_hoareTime
    (TM.rewindWorkTM tapes.scan.entry.value)
    (TM.seqTM
      (TM.binaryCopyIntoTM tapes.scan.entry.value tapes.destination
        tapes.copyScratch)
      (entryLookupRestoreTailTM tapes))
    hrewind
    (by
      rintro inp work out ⟨hinp, hready, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hready.restore.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hready, hout⟩)
    hcopyTail
  have hall := TM.seqTM_hoareTime (entryLookupTM tapes.scan)
    (TM.seqTM (TM.rewindWorkTM tapes.scan.entry.value)
      (TM.seqTM
        (TM.binaryCopyIntoTM tapes.scan.entry.value tapes.destination
          tapes.copyScratch)
        (entryLookupRestoreTailTM tapes)))
    hscan
    (by
      rintro inp work out ⟨hinp, hready, hout⟩
      rcases hready with ⟨preparedWork, hprepared, hscanned⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hscanned.result.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨preparedWork, hprepared, hscanned⟩, hout⟩)
    hrewindRest
  simpa [entryLookupCopyRestoreTM, entryLookupCopyRestoreTime] using hall

/-- Complete semantic and time contract for one reusable loaded sparse-register
lookup. -/
theorem entryLookupLoaded_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryLookupRestoreReady tapes store address initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupLoadedTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupRestoreResult tapes store address initialWork work ∧
        out = out₀)
      (entryLookupLoadedTime tapes store address) := by
  have hprepare := entryLookupPrepare_hoareTime_internal tapes store address
    initialWork inp₀ out₀ hready hinput houtput
  have hrest := entryLookupCopyRestore_hoareTime_internal tapes store address
    initialWork inp₀ out₀ hready hinput houtput
  have hall := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM tapes.querySource tapes.scan.entry.query
      tapes.copyScratch)
    (entryLookupCopyRestoreTM tapes) hprepare
    (by
      rintro inp work out ⟨hinp, hprepared, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hprepared.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hprepared, hout⟩)
    hrest
  simpa [entryLookupLoadedTM, entryLookupLoadedTime] using hall

end Machine

end RegisterStore

end RAM

end Complexity
