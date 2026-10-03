/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy

/-!
# Reusable sparse-register lookup -- query preparation
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem query_ne_external (tapes : EntryLookupRestoreTapes n)
    (external : Fin 4) :
    tapes.scan.entry.query ≠ tapes.idx ⟨external.val + 10, by omega⟩ :=
  tapes.scan_ne_external 7 external

/-- Copying the external query source into the blank scanner query tape
establishes the exact lookup-ready boundary and changes no other tape. -/
theorem entryLookupPrepare_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (work₀ : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryLookupRestoreReady tapes store address work₀)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.binaryCopyIntoTM tapes.querySource tapes.scan.entry.query
      tapes.copyScratch).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupPrepared tapes store address work₀ work ∧
        out = out₀)
      (TM.binaryCopyTime address 0) := by
  have hcopy := TM.binaryCopyIntoTM_hoareTime_frame
    tapes.querySource tapes.scan.entry.query tapes.copyScratch
    (Ne.symm (query_ne_external tapes 1))
    tapes.querySource_ne_copyScratch
    (query_ne_external tapes 3) address 0 inp₀ work₀ out₀
    hready.querySource
    ⟨hready.scanner.queryStart, by simpa using hready.scanner.query⟩
    hready.copyScratch hinput
    (fun i _ _ _ => hready.scanner.parked i) houtput
  exact hcopy.strengthen_post (by
    rintro inp work out ⟨hinp, hwork, hout⟩
    let queryTape := (Tape.init (address.bits.map Γ.ofBool)).move Dir3.right
    let preparedWork := Function.update work₀ tapes.scan.entry.query queryTape
    have hwork' : work = preparedWork := by
      simpa [preparedWork, queryTape] using hwork
    clear hwork
    subst work
    have hquery :
        preparedWork tapes.scan.entry.query = queryTape := by
      simp [preparedWork]
    have hother : ∀ i, i ≠ tapes.scan.entry.query →
        preparedWork i = work₀ i := by
      intro i hi
      simp [preparedWork, Function.update_of_ne hi]
    have hsourceQuery :
        tapes.scan.entry.source ≠ tapes.scan.entry.query :=
      tapes.scan.entry.ne (by decide)
    have haddressQuery :
        tapes.scan.entry.address ≠ tapes.scan.entry.query :=
      tapes.scan.entry.ne (by decide)
    have hvalueQuery :
        tapes.scan.entry.value ≠ tapes.scan.entry.query :=
      tapes.scan.entry.ne (by decide)
    have haddressCounterQuery :
        tapes.scan.entry.addressCounter ≠ tapes.scan.entry.query :=
      tapes.scan.entry.ne (by decide)
    have haddressWidthQuery :
        tapes.scan.entry.addressWidth ≠ tapes.scan.entry.query :=
      tapes.scan.entry.ne (by decide)
    have hvalueCounterQuery :
        tapes.scan.entry.valueCounter ≠ tapes.scan.entry.query :=
      tapes.scan.entry.ne (by decide)
    have hvalueWidthQuery :
        tapes.scan.entry.valueWidth ≠ tapes.scan.entry.query :=
      tapes.scan.entry.ne (by decide)
    have hresultQuery :
        tapes.scan.entry.result ≠ tapes.scan.entry.query :=
      tapes.scan.entry.ne (by decide)
    have hdestinationQuery :
        tapes.destination ≠ tapes.scan.entry.query := by
      exact Ne.symm (query_ne_external tapes 2)
    have hcopyScratchQuery :
        tapes.copyScratch ≠ tapes.scan.entry.query := by
      exact Ne.symm (query_ne_external tapes 3)
    have hscanner : EntryScanReady tapes.scan.entry
        (store.flatMap Entry.encode) address.bits preparedWork
        preparedWork := by
      refine
        { source := ?_
          address := ?_
          addressStart := ?_
          value := ?_
          valueStart := ?_
          addressCounter := ?_
          addressWidth := ?_
          valueCounter := ?_
          valueWidth := ?_
          query := ?_
          queryStart := ?_
          result := ?_
          resultStart := ?_
          parked := ?_
          frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
      · rw [hother _ hsourceQuery]
        exact hready.scanner.source
      · rw [hother _ haddressQuery]
        exact hready.scanner.address
      · rw [hother _ haddressQuery]
        exact hready.scanner.addressStart
      · rw [hother _ hvalueQuery]
        exact hready.scanner.value
      · rw [hother _ hvalueQuery]
        exact hready.scanner.valueStart
      · rw [hother _ haddressCounterQuery]
        exact hready.scanner.addressCounter
      · rw [hother _ haddressWidthQuery]
        exact hready.scanner.addressWidth
      · rw [hother _ hvalueCounterQuery]
        exact hready.scanner.valueCounter
      · rw [hother _ hvalueWidthQuery]
        exact hready.scanner.valueWidth
      · rw [hquery]
        exact Tape.init_move_right_hasBinaryString address.bits
      · rw [hquery]
        simp [queryTape, Tape.init, Tape.move]
      · rw [hother _ hresultQuery]
        exact hready.scanner.result
      · rw [hother _ hresultQuery]
        exact hready.scanner.resultStart
      · intro i
        by_cases hi : i = tapes.scan.entry.query
        · subst i
          rw [hquery]
          exact hasBinaryNat_parked
            (Tape.init_move_right_hasBinaryNat address)
        · rw [hother i hi]
          exact hready.scanner.parked i
    refine ⟨hinp, ⟨hscanner, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hscanner.parked,
      hother⟩, hout⟩
    · rw [hother _ hsourceQuery]
      exact hready.sourceStart
    · rw [hother _ hsourceQuery]
      exact hready.sourceHead
    · rw [hother _ (tapes.scan.count_ne 7)]
      exact hready.count
    · exact hother _ (Ne.symm (query_ne_external tapes 0))
    · have heq : preparedWork tapes.countSource =
          work₀ tapes.countSource :=
        hother _ (Ne.symm (query_ne_external tapes 0))
      rw [heq]
      exact hready.countSource
    · exact hother _ (Ne.symm (query_ne_external tapes 1))
    · have heq : preparedWork tapes.querySource =
          work₀ tapes.querySource :=
        hother _ (Ne.symm (query_ne_external tapes 1))
      rw [heq]
      exact hready.querySource
    · rw [hother _ hdestinationQuery]
      exact hready.destination
    · rw [hother _ hcopyScratchQuery]
      exact hready.copyScratch)

end Machine

end RegisterStore

end RAM

end Complexity
