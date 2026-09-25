/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookup
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Reset

/-!
# Reusable sparse-register lookup -- bounded scan phase
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem external_frame
    (tapes : EntryLookupRestoreTapes n) (external : Fin 4)
    (initialWork finalWork : Fin n → Tape)
    (hframe : EntryScanFrame tapes.scan initialWork finalWork) :
    finalWork (tapes.idx ⟨external.val + 10, by omega⟩) =
      initialWork (tapes.idx ⟨external.val + 10, by omega⟩) := by
  apply hframe
  · exact Ne.symm (tapes.scan_ne_external 9 external)
  · exact Ne.symm (tapes.scan_ne_external 0 external)
  · exact Ne.symm (tapes.scan_ne_external 1 external)
  · exact Ne.symm (tapes.scan_ne_external 2 external)
  · exact Ne.symm (tapes.scan_ne_external 3 external)
  · exact Ne.symm (tapes.scan_ne_external 4 external)
  · exact Ne.symm (tapes.scan_ne_external 5 external)
  · exact Ne.symm (tapes.scan_ne_external 6 external)
  · exact Ne.symm (tapes.scan_ne_external 7 external)
  · exact Ne.symm (tapes.scan_ne_external 8 external)

private theorem prepared_reset_head
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork preparedWork : Fin n → Tape)
    (hprepared : EntryLookupPrepared tapes store address initialWork
      preparedWork) :
    ∀ i, i ∈ entryLookupResetTargets tapes →
      (preparedWork i).head = 1 := by
  intro i hi
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
  fin_cases slot
  · simpa using hprepared.scanner.address.1
  · simpa using hprepared.scanner.value.1
  · exact hprepared.scanner.addressCounter.2.1
  · exact hprepared.scanner.addressWidth.2.1
  · exact hprepared.scanner.valueCounter.2.1
  · exact hprepared.scanner.valueWidth.2.1
  · simpa using hprepared.scanner.result.1
  · exact hprepared.scanner.query.1
  · exact hprepared.count.2.1

/-- The scanner phase preserves the reusable external ABI and packages every
fact needed to copy the value and restore the scanner-owned tapes. -/
theorem entryLookupScan_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork preparedWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hprepared : EntryLookupPrepared tapes store address initialWork
      preparedWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupTM tapes.scan).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = preparedWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupScanned tapes store address initialWork preparedWork work ∧
        out = out₀)
      (entryLookupTime tapes.scan address store) := by
  have hlookup := entryLookupTM_hoareTime_frame_source tapes.scan store address
    preparedWork inp₀ out₀ hprepared.scanner hprepared.count hinput houtput
  exact hlookup.strengthen_post (by
    rintro inp work out
      ⟨hinp, hresult, hsourceCells, hheads, hout⟩
    have hsourcePrepared :
        preparedWork tapes.scan.entry.source =
          initialWork tapes.scan.entry.source :=
      hprepared.frame _ (tapes.scan.entry.ne (by decide))
    have hsourceInitial : (work tapes.scan.entry.source).cells =
        (initialWork tapes.scan.entry.source).cells :=
      hsourceCells.trans
        (congrArg Tape.cells hsourcePrepared)
    have hsourceHead : (work tapes.scan.entry.source).head ≤
        entryLookupRestoreHeadBound tapes store address := by
      have hhead := hheads tapes.scan.entry.source
      simp only [entryLookupRestoreHeadBound]
      rw [hprepared.sourceHead] at hhead
      omega
    have hresetHead : ∀ i, i ∈ entryLookupResetTargets tapes →
        (work i).head ≤
          entryLookupRestoreHeadBound tapes store address := by
      intro i hi
      have hhead := hheads i
      rw [prepared_reset_head tapes store address initialWork preparedWork
        hprepared i hi] at hhead
      simpa only [entryLookupRestoreHeadBound] using hhead
    have hcountSource : work tapes.countSource =
        initialWork tapes.countSource :=
      (external_frame tapes 0 preparedWork work hresult.frame).trans
        hprepared.countSource
    have hquerySource : work tapes.querySource =
        initialWork tapes.querySource :=
      (external_frame tapes 1 preparedWork work hresult.frame).trans
        hprepared.querySource
    have hdestination : work tapes.destination =
        initialWork tapes.destination :=
      (external_frame tapes 2 preparedWork work hresult.frame).trans (by
        exact hprepared.frame _
          (Ne.symm (tapes.scan_ne_external 7 2)))
    have hcopyScratch : work tapes.copyScratch =
        initialWork tapes.copyScratch :=
      (external_frame tapes 3 preparedWork work hresult.frame).trans (by
        exact hprepared.frame _
          (Ne.symm (tapes.scan_ne_external 7 3)))
    refine ⟨hinp, ⟨hresult,
      hresult.resetReady_internal tapes store address preparedWork work,
      hsourceInitial, by
        rw [hsourceCells]
        exact hprepared.sourceStart,
      hsourceHead, hresetHead, hcountSource, hquerySource,
      hdestination, hcopyScratch, ?_⟩, hout⟩
    intro i hall
    calc
      work i = preparedWork i := hresult.frame i
        (hall 9) (hall 0) (hall 1) (hall 2) (hall 3) (hall 4)
        (hall 5) (hall 6) (hall 7) (hall 8)
      _ = initialWork i := hprepared.frame i (hall 7))

end Machine

end RegisterStore

end RAM

end Complexity
