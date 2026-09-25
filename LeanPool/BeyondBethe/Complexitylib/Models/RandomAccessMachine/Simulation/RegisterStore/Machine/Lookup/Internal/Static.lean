/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Assemble
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst

/-!
# Fixed-address sparse-register lookup -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_eq_self_of_reads_ne_start hinput.read_ne_start
    (fun i => (hwork i).read_ne_start) houtput.read_ne_start

private theorem staticAddress_parked (address : ℕ) :
    TM.Parked
      ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) := by
  have hnat := Tape.init_move_right_hasBinaryNat address
  exact ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩

private theorem staticBlank_hasBinaryNat :
    ((Tape.init []).move Dir3.right).HasBinaryNat 0 := by
  simpa using Tape.init_move_right_hasBinaryNat 0

theorem staticAdd_ready_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape)
    (hready : EntryLookupStaticReady tapes store initialWork) :
    EntryLookupRestoreReady tapes store address
      (Function.update initialWork tapes.querySource
        ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)) := by
  let work₁ := Function.update initialWork tapes.querySource
    ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)
  have hsource : tapes.scan.entry.source ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have haddress : tapes.scan.entry.address ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hvalue : tapes.scan.entry.value ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have haddressCounter :
      tapes.scan.entry.addressCounter ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have haddressWidth :
      tapes.scan.entry.addressWidth ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hvalueCounter :
      tapes.scan.entry.valueCounter ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hvalueWidth : tapes.scan.entry.valueWidth ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hquery : tapes.scan.entry.query ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hresult : tapes.scan.entry.result ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hcount : tapes.scan.count ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hcountSource : tapes.countSource ≠ tapes.querySource :=
    tapes.countSource_ne_querySource
  have hdestination : tapes.destination ≠ tapes.querySource :=
    tapes.querySource_ne_destination.symm
  have hcopyScratch : tapes.copyScratch ≠ tapes.querySource :=
    tapes.querySource_ne_copyScratch.symm
  have hscanner : EntryScanReady tapes.scan.entry
      (store.flatMap Entry.encode) [] work₁ work₁ := by
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
        frame := ?_ }
    · simpa only [work₁, Function.update_of_ne hsource] using
        hready.scanner.source
    · simpa only [work₁, Function.update_of_ne haddress] using
        hready.scanner.address
    · simpa only [work₁, Function.update_of_ne haddress] using
        hready.scanner.addressStart
    · simpa only [work₁, Function.update_of_ne hvalue] using
        hready.scanner.value
    · simpa only [work₁, Function.update_of_ne hvalue] using
        hready.scanner.valueStart
    · simpa only [work₁, Function.update_of_ne haddressCounter] using
        hready.scanner.addressCounter
    · simpa only [work₁, Function.update_of_ne haddressWidth] using
        hready.scanner.addressWidth
    · simpa only [work₁, Function.update_of_ne hvalueCounter] using
        hready.scanner.valueCounter
    · simpa only [work₁, Function.update_of_ne hvalueWidth] using
        hready.scanner.valueWidth
    · simpa only [work₁, Function.update_of_ne hquery] using
        hready.scanner.query
    · simpa only [work₁, Function.update_of_ne hquery] using
        hready.scanner.queryStart
    · simpa only [work₁, Function.update_of_ne hresult] using
        hready.scanner.result
    · simpa only [work₁, Function.update_of_ne hresult] using
        hready.scanner.resultStart
    · intro i
      by_cases hi : i = tapes.querySource
      · subst i
        simpa only [work₁, Function.update_self] using
          staticAddress_parked address
      · simpa only [work₁, Function.update_of_ne hi] using
          hready.scanner.parked i
    · intro i _ _ _ _ _ _ _ _ _
      rfl
  refine
    { scanner := hscanner
      sourceStart := ?_
      sourceHead := ?_
      count := ?_
      countSource := ?_
      querySource := ?_
      destination := ?_
      copyScratch := ?_ }
  · simpa only [work₁, Function.update_of_ne hsource] using
      hready.sourceStart
  · simpa only [work₁, Function.update_of_ne hsource] using
      hready.sourceHead
  · simpa only [work₁, Function.update_of_ne hcount] using hready.count
  · simpa only [work₁, Function.update_of_ne
      hcountSource] using hready.countSource
  · simpa only [work₁, Function.update_self] using
      Tape.init_move_right_hasBinaryNat address
  · simpa only [work₁, Function.update_of_ne hdestination] using
      hready.destination
  · simpa only [work₁, Function.update_of_ne hcopyScratch] using
      hready.copyScratch

private theorem staticReset_result
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork loadedWork : Fin n → Tape)
    (hloaded : EntryLookupRestoreResult tapes store address
      (Function.update initialWork tapes.querySource
        ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
      loadedWork) :
    EntryLookupStaticResult tapes store address initialWork
      (Function.update loadedWork tapes.querySource
        ((Tape.init []).move Dir3.right)) := by
  let finalWork := Function.update loadedWork tapes.querySource
    ((Tape.init []).move Dir3.right)
  have hsource : tapes.scan.entry.source ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have haddress : tapes.scan.entry.address ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hvalue : tapes.scan.entry.value ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have haddressCounter :
      tapes.scan.entry.addressCounter ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have haddressWidth :
      tapes.scan.entry.addressWidth ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hvalueCounter :
      tapes.scan.entry.valueCounter ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hvalueWidth : tapes.scan.entry.valueWidth ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hquery : tapes.scan.entry.query ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hresult : tapes.scan.entry.result ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hcount : tapes.scan.count ≠ tapes.querySource := by
    exact tapes.ne (by decide)
  have hcountSource : tapes.countSource ≠ tapes.querySource :=
    tapes.countSource_ne_querySource
  have hdestination : tapes.destination ≠ tapes.querySource :=
    tapes.querySource_ne_destination.symm
  have hcopyScratch : tapes.copyScratch ≠ tapes.querySource :=
    tapes.querySource_ne_copyScratch.symm
  have hscanner : EntryScanReady tapes.scan.entry
      (store.flatMap Entry.encode) [] finalWork finalWork := by
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
        frame := ?_ }
    · simpa only [finalWork, Function.update_of_ne hsource] using
        hloaded.scanner.source
    · simpa only [finalWork, Function.update_of_ne haddress] using
        hloaded.scanner.address
    · simpa only [finalWork, Function.update_of_ne haddress] using
        hloaded.scanner.addressStart
    · simpa only [finalWork, Function.update_of_ne hvalue] using
        hloaded.scanner.value
    · simpa only [finalWork, Function.update_of_ne hvalue] using
        hloaded.scanner.valueStart
    · simpa only [finalWork, Function.update_of_ne haddressCounter] using
        hloaded.scanner.addressCounter
    · simpa only [finalWork, Function.update_of_ne haddressWidth] using
        hloaded.scanner.addressWidth
    · simpa only [finalWork, Function.update_of_ne hvalueCounter] using
        hloaded.scanner.valueCounter
    · simpa only [finalWork, Function.update_of_ne hvalueWidth] using
        hloaded.scanner.valueWidth
    · simpa only [finalWork, Function.update_of_ne hquery] using
        hloaded.scanner.query
    · simpa only [finalWork, Function.update_of_ne hquery] using
        hloaded.scanner.queryStart
    · simpa only [finalWork, Function.update_of_ne hresult] using
        hloaded.scanner.result
    · simpa only [finalWork, Function.update_of_ne hresult] using
        hloaded.scanner.resultStart
    · intro i
      by_cases hi : i = tapes.querySource
      · subst i
        have hzero := staticBlank_hasBinaryNat
        simpa only [finalWork, Function.update_self] using
          (show TM.Parked ((Tape.init []).move Dir3.right) from
            ⟨by rw [hzero.2.1], hzero.2.hasBinaryContent.cells_ne_start⟩)
      · simpa only [finalWork, Function.update_of_ne hi] using hloaded.parked i
    · intro i _ _ _ _ _ _ _ _ _
      rfl
  refine
    { scanner := hscanner
      sourceCells := by
        simpa only [finalWork, Function.update_of_ne hsource] using
          hloaded.sourceCells
      sourceStart := ?_
      sourceHead := ?_
      count := ?_
      countSource := ?_
      querySource := ?_
      destination := ?_
      copyScratch := ?_
      parked := hscanner.parked
      frame := ?_ }
  · simpa only [finalWork, Function.update_of_ne hsource] using
      hloaded.sourceStart
  · simpa only [finalWork, Function.update_of_ne hsource] using
      hloaded.sourceHead
  · simpa only [finalWork, Function.update_of_ne hcount] using hloaded.count
  · simp only [hloaded.countSource, Function.update_of_ne hcountSource]
  · simpa only [finalWork, Function.update_self] using staticBlank_hasBinaryNat
  · simpa only [finalWork, Function.update_of_ne hdestination] using
      hloaded.value
  · simpa only [finalWork, Function.update_of_ne hcopyScratch] using
      hloaded.copyScratch
  · intro i hi
    have hquery : i ≠ tapes.querySource := hi 11
    rw [Function.update_of_ne hquery]
    have houtside : ∀ slot, i ≠ tapes.idx slot := by
      intro slot
      exact hi slot
    rw [hloaded.frame i houtside]
    exact Function.update_of_ne hquery _ initialWork

theorem entryLookupStatic_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (store : Store) (address : ℕ)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryLookupStaticReady tapes store initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryLookupStaticTM tapes address).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupStaticResult tapes store address initialWork work ∧
        out = out₀)
      (entryLookupStaticTime tapes store address) := by
  let loadedInitial := Function.update initialWork tapes.querySource
    ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)
  have hadd := TM.binaryAddConstTM_hoareTime_frame tapes.querySource address 0
    inp₀ initialWork out₀ hready.querySource hinput
      (fun i _ => hready.scanner.parked i) houtput
  have hadd' : (TM.binaryAddConstTM tapes.querySource address).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = loadedInitial ∧ out = out₀)
      (TM.binaryAddConstTime address 0) := by
    simpa only [loadedInitial, zero_add] using hadd
  have hloadedReady : EntryLookupRestoreReady tapes store address loadedInitial := by
    simpa only [loadedInitial, zero_add] using
      staticAdd_ready_internal tapes store address initialWork hready
  have hloaded := entryLookupLoaded_hoareTime_internal tapes store address
    loadedInitial inp₀ out₀ hloadedReady hinput houtput
  have hreset : (TM.resetBinaryWorkTM tapes.querySource).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupRestoreResult tapes store address loadedInitial work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupStaticResult tapes store address initialWork work ∧
        out = out₀)
      (TM.resetBinaryWorkTime 1 address.bits.length) := by
    rintro inp work out ⟨hinp, hlookup, hout⟩
    have hqueryNat : (work tapes.querySource).HasBinaryNat address := by
      rw [hlookup.querySource]
      simpa only [loadedInitial, Function.update_self] using
        Tape.init_move_right_hasBinaryNat address
    have hrun := TM.resetBinaryWorkTM_hoareTime_frame tapes.querySource
      address.bits 1 inp work out hqueryNat.2.hasBinaryContent hqueryNat.1
      ⟨by rw [hqueryNat.2.1], by rw [hqueryNat.2.1]⟩
      (by simpa [hinp] using hinput)
      (fun i _ => hlookup.parked i)
      (by simpa [hout] using houtput)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨final, time, htime, hreach, hhalt,
      hfinalInput.trans hinp,
      (by
        rw [hfinalWork]
        exact staticReset_result tapes store address initialWork work hlookup),
      hfinalOutput.trans hout⟩
  have hloadedReset := TM.seqTM_hoareTime
    (entryLookupLoadedTM tapes)
    (TM.resetBinaryWorkTM tapes.querySource) hloaded
    (by
      rintro inp work out ⟨hinp, hlookup, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hlookup.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hlookup, hout⟩)
    hreset
  have hall := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.querySource address)
    (TM.seqTM (entryLookupLoadedTM tapes)
      (TM.resetBinaryWorkTM tapes.querySource)) hadd'
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst work
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := loadedInitial) (out := out)
        (by simpa [hinp] using hinput) hloadedReady.scanner.parked
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, rfl, hout⟩)
    hloadedReset
  simpa [entryLookupStaticTM, entryLookupStaticTime, loadedInitial] using hall

end Machine

end RegisterStore

end RAM

end Complexity
