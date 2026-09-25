/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseDefs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Load
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Tagged
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.DenseInternal

/-!
# Dense-overlay indirect load
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

private theorem hasBinaryPrefix_parked {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t := by
  refine ⟨by rw [h.1]; omega, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hi : i < bits.length
  · rw [h.2.1 i hi]
    exact Γ.ofBool_ne_start _
  · rw [h.2.2 i (Nat.le_of_not_gt hi)]
    decide

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_eq_self_of_reads_ne_start hinput.read_ne_start
    (fun i => (hwork i).read_ne_start) houtput.read_ne_start

private theorem denseScanner_indirect_of_lhs
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (source : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hlookup : DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
      source initialWork finalWork) :
    EntryScanReady tapes.indirectLoadLookup.scan.entry
      (overlay.flatMap Entry.encode) [] finalWork finalWork :=
  { source := hlookup.scanner.source
    address := hlookup.scanner.address
    addressStart := hlookup.scanner.addressStart
    value := hlookup.scanner.value
    valueStart := hlookup.scanner.valueStart
    addressCounter := hlookup.scanner.addressCounter
    addressWidth := hlookup.scanner.addressWidth
    valueCounter := hlookup.scanner.valueCounter
    valueWidth := hlookup.scanner.valueWidth
    query := hlookup.scanner.query
    queryStart := hlookup.scanner.queryStart
    result := hlookup.scanner.result
    resultStart := hlookup.scanner.resultStart
    parked := hlookup.parked
    frame := by intro i _ _ _ _ _ _ _ _ _; rfl }

private theorem denseIndirectLoaded_ready
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (addressRegister : ℕ)
    (initialWork addressWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (haddress : DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
      addressRegister initialWork addressWork) :
    EntryLookupRestoreReady tapes.indirectLoadLookup overlay
      (DenseOverlay.read input overlay addressRegister) addressWork := by
  have hreplacementEq : addressWork tapes.update.replacement =
      initialWork tapes.update.replacement :=
    haddress.frame tapes.update.replacement
      (fun slot => (tapes.lhsLookup_ne_replacement slot).symm)
  have hcountSource :
      (addressWork tapes.update.resultCount).HasBinaryNat overlay.length := by
    rw [show addressWork tapes.update.resultCount =
        initialWork tapes.update.resultCount by simpa using! haddress.countSource]
    simpa using! hinitial.countSource
  refine
    { scanner := denseScanner_indirect_of_lhs tapes input overlay
        addressRegister initialWork addressWork haddress
      sourceStart := haddress.sourceStart
      sourceHead := haddress.sourceHead
      count := by simpa using! haddress.count
      countSource := by simpa using! hcountSource
      querySource := by simpa using! haddress.destination
      destination := ?_
      copyScratch := by simpa using! haddress.copyScratch }
  change (addressWork tapes.update.replacement).HasBinaryNat 0
  rw [hreplacementEq]
  exact hreplacement

/-- One static dense-overlay address read followed by a loaded dense-overlay
read leaves the indirect value in the update replacement tape. -/
private theorem denseIndirectReads_hoareTime
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (addressRegister : ℕ)
    (initialWork : Fin n → Tape) (out₀ : Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (houtput : TM.Parked out₀) :
    (TM.seqTM (denseOverlayLookupStaticTM tapes.lhsLookup addressRegister)
      (denseOverlayLookupTM tapes.indirectLoadLookup)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        (∃ addressWork,
          DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
            addressRegister initialWork addressWork ∧
          DenseOverlayLookupResult tapes.indirectLoadLookup input overlay
            (DenseOverlay.read input overlay addressRegister) addressWork work) ∧
        out = out₀)
      (denseOverlayLookupStaticTime tapes.lhsLookup input.length overlay
          addressRegister + 1 +
        denseOverlayLookupTime tapes.indirectLoadLookup input.length overlay
          (DenseOverlay.read input overlay addressRegister)) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have haddress := denseOverlayLookupStaticTM_hoareTime_internal
    tapes.lhsLookup input overlay addressRegister initialWork out₀ hvalid
    hinitial houtput
  have hloaded : (denseOverlayLookupTM tapes.indirectLoadLookup).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
          addressRegister initialWork work ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ addressWork,
          DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
            addressRegister initialWork addressWork ∧
          DenseOverlayLookupResult tapes.indirectLoadLookup input overlay
            (DenseOverlay.read input overlay addressRegister) addressWork work) ∧
        out = out₀)
      (denseOverlayLookupTime tapes.indirectLoadLookup input.length overlay
        (DenseOverlay.read input overlay addressRegister)) := by
    rintro inp work out ⟨hinp, haddressResult, hout⟩
    have hready := denseIndirectLoaded_ready tapes input overlay addressRegister
      initialWork work hinitial hreplacement haddressResult
    have hrun := denseOverlayLookupTM_hoareTime_internal
      tapes.indirectLoadLookup input overlay
      (DenseOverlay.read input overlay addressRegister) work out₀ hvalid hready
      houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hloadedResult, hfinalOutput⟩ :=
      hrun inp work out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, haddressResult, hloadedResult⟩, hfinalOutput⟩
  have hall := TM.seqTM_hoareTime
    (denseOverlayLookupStaticTM tapes.lhsLookup addressRegister)
    (denseOverlayLookupTM tapes.indirectLoadLookup) haddress
    (by
      rintro inp work out ⟨hinp, haddressResult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [inp₀, hinp] using! hinput) haddressResult.parked
        (by simpa [hout] using! houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, haddressResult, hout⟩)
    hloaded
  simpa only [inp₀] using! hall

/-- Exact semantic and time contract for one dense-overlay indirect load. -/
theorem denseIndirectLoadInstructionTM_hoareTime_frame
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (destination addressRegister : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape) (out₀ : Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (denseIndirectLoadInstructionTM tapes destination addressRegister).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseIndirectLoadInstructionResult tapes input overlay destination
          addressRegister initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay destination
              (DenseOverlay.read input overlay
                (DenseOverlay.read input overlay addressRegister))).flatMap
              Entry.encode))
      (denseIndirectLoadInstructionTime tapes input overlay destination
        addressRegister) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have houtputParked := hasBinaryPrefix_parked houtput
  have hreads := denseIndirectReads_hoareTime tapes input overlay
    addressRegister initialWork out₀ hvalid hinitial hreplacement houtputParked
  have hquery : (TM.binaryAddConstTM tapes.update.entry.query
      destination).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ addressWork,
          DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
            addressRegister initialWork addressWork ∧
          DenseOverlayLookupResult tapes.indirectLoadLookup input overlay
            (DenseOverlay.read input overlay addressRegister) addressWork work) ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ addressWork loadedWork,
          DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
            addressRegister initialWork addressWork ∧
          DenseOverlayLookupResult tapes.indirectLoadLookup input overlay
            (DenseOverlay.read input overlay addressRegister) addressWork
            loadedWork ∧
          work = Function.update loadedWork tapes.update.entry.query
            ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (TM.binaryAddConstTime destination 0) := by
    rintro inp work out ⟨hinp, ⟨addressWork, haddressResult,
      hloadedResult⟩, hout⟩
    have hqueryZero : (work tapes.update.entry.query).HasBinaryNat 0 :=
      ⟨hloadedResult.scanner.queryStart, by
        simpa using! hloadedResult.scanner.query⟩
    have hrun := TM.binaryAddConstTM_hoareTime_frame
      tapes.update.entry.query destination 0 inp work out hqueryZero
      (by simpa [hinp] using! hinput)
      (fun i _ => hloadedResult.parked i)
      (by simpa [hout] using! houtputParked)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      ⟨addressWork, work, haddressResult, hloadedResult,
        by simpa only [zero_add] using! hfinalWork⟩,
      hfinalOutput.trans hout⟩
  have hupdate : (taggedEntryUpdateTM tapes.update).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ addressWork loadedWork,
          DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
            addressRegister initialWork addressWork ∧
          DenseOverlayLookupResult tapes.indirectLoadLookup input overlay
            (DenseOverlay.read input overlay addressRegister) addressWork
            loadedWork ∧
          work = Function.update loadedWork tapes.update.entry.query
            ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseIndirectLoadInstructionResult tapes input overlay destination
          addressRegister initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay destination
              (DenseOverlay.read input overlay
                (DenseOverlay.read input overlay addressRegister))).flatMap
              Entry.encode))
      (taggedEntryUpdateTime tapes.update overlay destination
        (DenseOverlay.read input overlay
          (DenseOverlay.read input overlay addressRegister))) := by
    rintro inp work out ⟨hinp, ⟨addressWork, loadedWork, haddressResult,
      hloadedResult, hwork⟩, hout⟩
    subst work
    let updateWork := Function.update loadedWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)
    have hscanner := scanner_updateQuery_of_indirect_internal tapes overlay
      destination loadedWork hloadedResult.scanner
    have hreplacementNe :
        tapes.update.replacement ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hremainingNe : tapes.update.remaining ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hfoundNe : tapes.update.found ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hresultCountNe :
        tapes.update.resultCount ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hresultCount :
        (loadedWork tapes.update.resultCount).HasBinaryNat overlay.length := by
      rw [show loadedWork tapes.update.resultCount =
          addressWork tapes.update.resultCount by
        simpa using! hloadedResult.countSource]
      rw [show addressWork tapes.update.resultCount =
          initialWork tapes.update.resultCount by
        simpa using! haddressResult.countSource]
      simpa using! hinitial.countSource
    have hrun := taggedEntryUpdateTM_hoareTime_frame tapes.update overlay
      destination
      (DenseOverlay.read input overlay
        (DenseOverlay.read input overlay addressRegister))
      emittedBits updateWork inp₀ out₀ hvalid.1 hscanner
      (by simpa only [updateWork, Function.update_of_ne hreplacementNe] using!
        hloadedResult.value)
      (by simpa only [updateWork, Function.update_of_ne hremainingNe] using!
        hloadedResult.count)
      (by simpa only [updateWork, Function.update_of_ne hfoundNe] using!
        hloadedResult.copyScratch)
      (by simpa only [updateWork, Function.update_of_ne hresultCountNe] using!
        hresultCount)
      hinput houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hupdateResult, hfinalOutput⟩ :=
      hrun inp updateWork out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨addressWork, loadedWork, updateWork, haddressResult, hloadedResult,
        rfl, hupdateResult⟩, hfinalOutput⟩
  have hqueryUpdate := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.update.entry.query destination)
    (taggedEntryUpdateTM tapes.update) hquery
    (by
      rintro inp work out ⟨hinp, ⟨addressWork, loadedWork, haddressResult,
        hloadedResult, hwork⟩, hout⟩
      subst work
      have hparked := (scanner_updateQuery_of_indirect_internal tapes overlay
        destination loadedWork hloadedResult.scanner).parked
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp)
        (work := Function.update loadedWork tapes.update.entry.query
          ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right))
        (out := out) (by simpa [hinp] using! hinput) hparked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨addressWork, loadedWork, haddressResult,
        hloadedResult, rfl⟩, hout⟩)
    hupdate
  have hall := TM.seqTM_hoareTime
    (TM.seqTM (denseOverlayLookupStaticTM tapes.lhsLookup addressRegister)
      (denseOverlayLookupTM tapes.indirectLoadLookup))
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (taggedEntryUpdateTM tapes.update)) hreads
    (by
      rintro inp work out ⟨hinp, ⟨addressWork, haddressResult,
        hloadedResult⟩, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput) hloadedResult.parked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨addressWork, haddressResult, hloadedResult⟩, hout⟩)
    hqueryUpdate
  simpa [denseIndirectLoadInstructionTM, denseIndirectLoadInstructionTime,
    inp₀] using! hall

end Machine
end RegisterStore
end RAM
end Complexity
