/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Defs
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Static

/-!
# Indirect sparse-store load instructions -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem scanner_indirect_of_lhs
    (tapes : BinaryInstructionTapes n) (store : Store) (source : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hlookup : EntryLookupStaticResult tapes.lhsLookup store source
      initialWork finalWork) :
    EntryScanReady tapes.indirectLoadLookup.scan.entry
      (store.flatMap Entry.encode) [] finalWork finalWork := by
  refine
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

private theorem indirectLoaded_ready
    (tapes : BinaryInstructionTapes n) (store : Store)
    (addressRegister : ℕ) (initialWork addressWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (haddress : EntryLookupStaticResult tapes.lhsLookup store addressRegister
      initialWork addressWork) :
    EntryLookupRestoreReady tapes.indirectLoadLookup store
      (RegisterStore.read store addressRegister) addressWork := by
  have hreplacementEq : addressWork tapes.update.replacement =
      initialWork tapes.update.replacement :=
    haddress.frame tapes.update.replacement
      (fun slot => (tapes.lhsLookup_ne_replacement slot).symm)
  have hcountSource :
      (addressWork tapes.update.resultCount).HasBinaryNat store.length := by
    rw [show addressWork tapes.update.resultCount =
        initialWork tapes.update.resultCount by
      simpa using! haddress.countSource]
    simpa using! hinitial.countSource
  refine
    { scanner := scanner_indirect_of_lhs tapes store addressRegister
        initialWork addressWork haddress
      sourceStart := haddress.sourceStart
      sourceHead := haddress.sourceHead
      count := by simpa using! haddress.count
      countSource := by simpa using! hcountSource
      querySource := by simpa using! haddress.destination
      destination := by
        change (addressWork tapes.update.replacement).HasBinaryNat 0
        rw [hreplacementEq]
        exact hreplacement
      copyScratch := by simpa using! haddress.copyScratch }

theorem scanner_updateQuery_of_indirect_internal
    (tapes : BinaryInstructionTapes n) (store : Store) (destination : ℕ)
    (work : Fin n → Tape)
    (hscanner : EntryScanReady tapes.indirectLoadLookup.scan.entry
      (store.flatMap Entry.encode) [] work work) :
    EntryScanReady tapes.update.entry (store.flatMap Entry.encode)
      destination.bits
      (Function.update work tapes.update.entry.query
        ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right))
      (Function.update work tapes.update.entry.query
        ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)) := by
  let finalWork := Function.update work tapes.update.entry.query
    ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)
  have hsource : tapes.update.entry.source ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have haddress : tapes.update.entry.address ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hvalue : tapes.update.entry.value ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have haddressCounter :
      tapes.update.entry.addressCounter ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have haddressWidth :
      tapes.update.entry.addressWidth ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hvalueCounter :
      tapes.update.entry.valueCounter ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hvalueWidth :
      tapes.update.entry.valueWidth ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hresult : tapes.update.entry.result ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hnat := Tape.init_move_right_hasBinaryNat destination
  refine
    { source := by
        simpa only [finalWork, Function.update_of_ne hsource] using!
          hscanner.source
      address := by
        simpa only [finalWork, Function.update_of_ne haddress] using!
          hscanner.address
      addressStart := by
        simpa only [finalWork, Function.update_of_ne haddress] using!
          hscanner.addressStart
      value := by
        simpa only [finalWork, Function.update_of_ne hvalue] using!
          hscanner.value
      valueStart := by
        simpa only [finalWork, Function.update_of_ne hvalue] using!
          hscanner.valueStart
      addressCounter := by
        simpa only [finalWork, Function.update_of_ne haddressCounter] using!
          hscanner.addressCounter
      addressWidth := by
        simpa only [finalWork, Function.update_of_ne haddressWidth] using!
          hscanner.addressWidth
      valueCounter := by
        simpa only [finalWork, Function.update_of_ne hvalueCounter] using!
          hscanner.valueCounter
      valueWidth := by
        simpa only [finalWork, Function.update_of_ne hvalueWidth] using!
          hscanner.valueWidth
      query := by
        simpa only [finalWork, Function.update_self] using! hnat.2
      queryStart := by
        simpa only [finalWork, Function.update_self] using! hnat.1
      result := by
        simpa only [finalWork, Function.update_of_ne hresult] using!
          hscanner.result
      resultStart := by
        simpa only [finalWork, Function.update_of_ne hresult] using!
          hscanner.resultStart
      parked := ?_
      frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
  intro i
  by_cases hi : i = tapes.update.entry.query
  · subst i
    simpa only [finalWork, Function.update_self] using!
      (show TM.Parked
          ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right) from
        ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
  · simpa only [finalWork, Function.update_of_ne hi] using! hscanner.parked i

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

/-- Exact semantic and time contract for one indirect sparse-register load. -/
theorem indirectLoadInstructionTM_hoareTime_frame_internal
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination addressRegister : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (indirectLoadInstructionTM tapes destination addressRegister).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        IndirectLoadInstructionResult tapes store destination addressRegister
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination
              (RegisterStore.read store
                (RegisterStore.read store addressRegister))).flatMap
              Entry.encode))
      (indirectLoadInstructionTime tapes store destination addressRegister) := by
  have houtputParked := hasBinaryPrefix_parked houtput
  have haddress := entryLookupStatic_hoareTime_internal tapes.lhsLookup store
    addressRegister initialWork inp₀ out₀ hinitial hinput houtputParked
  have hloaded : (entryLookupLoadedTM tapes.indirectLoadLookup).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupStaticResult tapes.lhsLookup store addressRegister
          initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ addressWork,
          EntryLookupStaticResult tapes.lhsLookup store addressRegister
            initialWork addressWork ∧
          EntryLookupRestoreResult tapes.indirectLoadLookup store
            (RegisterStore.read store addressRegister) addressWork work) ∧
        out = out₀)
      (entryLookupLoadedTime tapes.indirectLoadLookup store
        (RegisterStore.read store addressRegister)) := by
    rintro inp work out ⟨hinp, haddressResult, hout⟩
    have hready := indirectLoaded_ready tapes store addressRegister initialWork
      work hinitial hreplacement haddressResult
    have hrun := entryLookupLoaded_hoareTime_internal
      tapes.indirectLoadLookup store (RegisterStore.read store addressRegister)
      work inp₀ out₀ hready hinput houtputParked
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hloadedResult, hfinalOutput⟩ :=
      hrun inp work out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, haddressResult, hloadedResult⟩, hfinalOutput⟩
  have hquery :
      (TM.binaryAddConstTM tapes.update.entry.query destination).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧
          (∃ addressWork,
            EntryLookupStaticResult tapes.lhsLookup store addressRegister
              initialWork addressWork ∧
            EntryLookupRestoreResult tapes.indirectLoadLookup store
              (RegisterStore.read store addressRegister) addressWork work) ∧
          out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          (∃ addressWork loadedWork,
            EntryLookupStaticResult tapes.lhsLookup store addressRegister
              initialWork addressWork ∧
            EntryLookupRestoreResult tapes.indirectLoadLookup store
              (RegisterStore.read store addressRegister) addressWork loadedWork ∧
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
        hfinalWork, hfinalOutput⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      ⟨addressWork, work, haddressResult, hloadedResult,
        by simpa only [zero_add] using! hfinalWork⟩,
      hfinalOutput.trans hout⟩
  have hupdate : (entryUpdateTM tapes.update).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ addressWork loadedWork,
          EntryLookupStaticResult tapes.lhsLookup store addressRegister
            initialWork addressWork ∧
          EntryLookupRestoreResult tapes.indirectLoadLookup store
            (RegisterStore.read store addressRegister) addressWork loadedWork ∧
          work = Function.update loadedWork tapes.update.entry.query
            ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        IndirectLoadInstructionResult tapes store destination addressRegister
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination
              (RegisterStore.read store
                (RegisterStore.read store addressRegister))).flatMap
              Entry.encode))
      (entryUpdateTime tapes.update store destination
        (RegisterStore.read store
          (RegisterStore.read store addressRegister))) := by
    rintro inp work out ⟨hinp, ⟨addressWork, loadedWork, haddressResult,
      hloadedResult, hwork⟩, hout⟩
    subst work
    let updateWork := Function.update loadedWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)
    have hscanner := scanner_updateQuery_of_indirect_internal tapes store destination
      loadedWork hloadedResult.scanner
    have hreplacementNe :
        tapes.update.replacement ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hremainingNe :
        tapes.update.remaining ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hfoundNe : tapes.update.found ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hresultCountNe :
        tapes.update.resultCount ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hresultCount :
        (loadedWork tapes.update.resultCount).HasBinaryNat store.length := by
      rw [show loadedWork tapes.update.resultCount =
          addressWork tapes.update.resultCount by
        simpa using! hloadedResult.countSource]
      rw [show addressWork tapes.update.resultCount =
          initialWork tapes.update.resultCount by
        simpa using! haddressResult.countSource]
      simpa using! hinitial.countSource
    have hrun := entryUpdateTM_hoareTime_frame tapes.update store destination
      (RegisterStore.read store (RegisterStore.read store addressRegister))
      emittedBits updateWork inp₀ out₀ hcanonical hscanner
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
        hupdateResult, hfinalOutput, hsourceCells⟩ :=
      hrun inp updateWork out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨addressWork, loadedWork, updateWork, haddressResult, hloadedResult,
        rfl, hupdateResult, by
          calc
            (final.work tapes.update.entry.source).cells =
                (updateWork tapes.update.entry.source).cells := hsourceCells
            _ = (loadedWork tapes.update.entry.source).cells := by
              rw [show updateWork tapes.update.entry.source =
                  loadedWork tapes.update.entry.source by
                exact Function.update_of_ne (tapes.update.ne (by decide)) _ _]
            _ = (addressWork tapes.update.entry.source).cells :=
              hloadedResult.sourceCells
            _ = (initialWork tapes.update.entry.source).cells :=
              haddressResult.sourceCells⟩,
      hfinalOutput⟩
  have hqueryUpdate := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.update.entry.query destination)
    (entryUpdateTM tapes.update) hquery
    (by
      rintro inp work out ⟨hinp, ⟨addressWork, loadedWork, haddressResult,
        hloadedResult, hwork⟩, hout⟩
      subst work
      have hparked := (scanner_updateQuery_of_indirect_internal tapes store destination
        loadedWork hloadedResult.scanner).parked
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := Function.update loadedWork
          tapes.update.entry.query
          ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right))
        (out := out) (by simpa [hinp] using! hinput) hparked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨addressWork, loadedWork, haddressResult,
        hloadedResult, rfl⟩, hout⟩)
    hupdate
  have hloadedRest := TM.seqTM_hoareTime
    (entryLookupLoadedTM tapes.indirectLoadLookup)
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (entryUpdateTM tapes.update)) hloaded
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
  have hall := TM.seqTM_hoareTime
    (entryLookupStaticTM tapes.lhsLookup addressRegister)
    (TM.seqTM (entryLookupLoadedTM tapes.indirectLoadLookup)
      (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
        (entryUpdateTM tapes.update))) haddress
    (by
      rintro inp work out ⟨hinp, haddressResult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput) haddressResult.parked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, haddressResult, hout⟩)
    hloadedRest
  simpa [indirectLoadInstructionTM, indirectLoadInstructionTime] using! hall

end Machine

end RegisterStore

end RAM

end Complexity
