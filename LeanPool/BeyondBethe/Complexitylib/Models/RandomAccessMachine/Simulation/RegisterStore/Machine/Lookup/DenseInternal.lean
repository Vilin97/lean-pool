/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Static
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup.Internal

/-!
# Dense overlay lookup -- proof internals
-/


public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

private theorem denseOverlayResult_of_destination_update
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ)
    (initialWork loadedWork finalWork : Fin n → Tape)
    (hloaded : EntryLookupRestoreResult tapes overlay address initialWork
      loadedWork)
    (hvalue : (finalWork tapes.destination).HasBinaryNat
      (DenseOverlay.read input overlay address))
    (hother : ∀ i, i ≠ tapes.destination →
      finalWork i = loadedWork i)
    (hparked : ∀ i, TM.Parked (finalWork i)) :
    DenseOverlayLookupResult tapes input overlay address initialWork
      finalWork := by
  constructor
  · constructor
    · rw [hother tapes.scan.entry.source (tapes.scan_ne_external 0 2)]
      exact hloaded.scanner.source
    · rw [hother tapes.scan.entry.address (tapes.scan_ne_external 1 2)]
      exact hloaded.scanner.address
    · rw [hother tapes.scan.entry.address (tapes.scan_ne_external 1 2)]
      exact hloaded.scanner.addressStart
    · rw [hother tapes.scan.entry.value (tapes.scan_ne_external 2 2)]
      exact hloaded.scanner.value
    · rw [hother tapes.scan.entry.value (tapes.scan_ne_external 2 2)]
      exact hloaded.scanner.valueStart
    · rw [hother tapes.scan.entry.addressCounter
        (tapes.scan_ne_external 3 2)]
      exact hloaded.scanner.addressCounter
    · rw [hother tapes.scan.entry.addressWidth
        (tapes.scan_ne_external 4 2)]
      exact hloaded.scanner.addressWidth
    · rw [hother tapes.scan.entry.valueCounter
        (tapes.scan_ne_external 5 2)]
      exact hloaded.scanner.valueCounter
    · rw [hother tapes.scan.entry.valueWidth
        (tapes.scan_ne_external 6 2)]
      exact hloaded.scanner.valueWidth
    · rw [hother tapes.scan.entry.query (tapes.scan_ne_external 7 2)]
      exact hloaded.scanner.query
    · rw [hother tapes.scan.entry.query (tapes.scan_ne_external 7 2)]
      exact hloaded.scanner.queryStart
    · rw [hother tapes.scan.entry.result (tapes.scan_ne_external 8 2)]
      exact hloaded.scanner.result
    · rw [hother tapes.scan.entry.result (tapes.scan_ne_external 8 2)]
      exact hloaded.scanner.resultStart
    · exact hparked
    · intro i _ _ _ _ _ _ _ _ _
      rfl
  · rw [hother tapes.scan.entry.source (tapes.scan_ne_external 0 2)]
    exact hloaded.sourceCells
  · rw [hother tapes.scan.entry.source (tapes.scan_ne_external 0 2)]
    exact hloaded.sourceStart
  · rw [hother tapes.scan.entry.source (tapes.scan_ne_external 0 2)]
    exact hloaded.sourceHead
  · rw [hother tapes.scan.count (tapes.scan_ne_external 9 2)]
    exact hloaded.count
  · rw [hother tapes.countSource tapes.countSource_ne_destination]
    exact hloaded.countSource
  · rw [hother tapes.querySource tapes.querySource_ne_destination]
    exact hloaded.querySource
  · exact hvalue
  · rw [hother tapes.copyScratch tapes.destination_ne_copyScratch.symm]
    exact hloaded.copyScratch
  · exact hparked
  · intro i hi
    rw [hother i (hi 12)]
    exact hloaded.frame i hi

private theorem denseOverlayResult_of_fallback
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ)
    (initialWork loadedWork finalWork : Fin n → Tape)
    (hloaded : EntryLookupRestoreResult tapes overlay address initialWork
      loadedWork)
    (htagZero : RegisterStore.read overlay address = 0)
    (hfallback : DenseInputLookupResult tapes.querySource
      tapes.scan.entry.address tapes.destination tapes.copyScratch input address
      loadedWork finalWork) :
    DenseOverlayLookupResult tapes input overlay address initialWork
      finalWork := by
  have hscanFrame : ∀ slot : Fin 9, slot ≠ 1 →
      finalWork (tapes.scan.entry.idx slot) =
        loadedWork (tapes.scan.entry.idx slot) := by
    intro slot hslot
    exact hfallback.frame _
      (tapes.scan_ne_external ⟨slot.val, by omega⟩ 1)
      (tapes.scan.entry.ne hslot)
      (tapes.scan_ne_external ⟨slot.val, by omega⟩ 2)
      (tapes.scan_ne_external ⟨slot.val, by omega⟩ 3)
  have hcountFrame : finalWork tapes.scan.count =
      loadedWork tapes.scan.count := by
    exact hfallback.frame _ (tapes.scan_ne_external 9 1)
      (tapes.scan.count_ne 1) (tapes.scan_ne_external 9 2)
      (tapes.scan_ne_external 9 3)
  have hsourceFrame : finalWork tapes.scan.entry.source =
      loadedWork tapes.scan.entry.source := by
    exact hscanFrame 0 (by decide)
  have hvalueFrame : finalWork tapes.scan.entry.value =
      loadedWork tapes.scan.entry.value := by
    exact hscanFrame 2 (by decide)
  have haddressCounterFrame : finalWork tapes.scan.entry.addressCounter =
      loadedWork tapes.scan.entry.addressCounter := by
    exact hscanFrame 3 (by decide)
  have haddressWidthFrame : finalWork tapes.scan.entry.addressWidth =
      loadedWork tapes.scan.entry.addressWidth := by
    exact hscanFrame 4 (by decide)
  have hvalueCounterFrame : finalWork tapes.scan.entry.valueCounter =
      loadedWork tapes.scan.entry.valueCounter := by
    exact hscanFrame 5 (by decide)
  have hvalueWidthFrame : finalWork tapes.scan.entry.valueWidth =
      loadedWork tapes.scan.entry.valueWidth := by
    exact hscanFrame 6 (by decide)
  have hqueryFrame : finalWork tapes.scan.entry.query =
      loadedWork tapes.scan.entry.query := by
    exact hscanFrame 7 (by decide)
  have hresultFrame : finalWork tapes.scan.entry.result =
      loadedWork tapes.scan.entry.result := by
    exact hscanFrame 8 (by decide)
  constructor
  · constructor
    · rw [hsourceFrame]
      exact hloaded.scanner.source
    · exact hfallback.counter_zero.2
    · exact hfallback.counter_zero.1
    · rw [hvalueFrame]
      exact hloaded.scanner.value
    · rw [hvalueFrame]
      exact hloaded.scanner.valueStart
    · rw [haddressCounterFrame]
      exact hloaded.scanner.addressCounter
    · rw [haddressWidthFrame]
      exact hloaded.scanner.addressWidth
    · rw [hvalueCounterFrame]
      exact hloaded.scanner.valueCounter
    · rw [hvalueWidthFrame]
      exact hloaded.scanner.valueWidth
    · rw [hqueryFrame]
      exact hloaded.scanner.query
    · rw [hqueryFrame]
      exact hloaded.scanner.queryStart
    · rw [hresultFrame]
      exact hloaded.scanner.result
    · rw [hresultFrame]
      exact hloaded.scanner.resultStart
    · exact hfallback.parked
    · intro i _ _ _ _ _ _ _ _ _
      rfl
  · rw [hsourceFrame]
    exact hloaded.sourceCells
  · rw [hsourceFrame]
    exact hloaded.sourceStart
  · rw [hsourceFrame]
    exact hloaded.sourceHead
  · rw [hcountFrame]
    exact hloaded.count
  · rw [hfallback.frame tapes.countSource
      tapes.countSource_ne_querySource
      (tapes.scan_ne_external 1 0).symm
      tapes.countSource_ne_destination
      tapes.countSource_ne_copyScratch]
    exact hloaded.countSource
  · exact hfallback.query_eq.trans hloaded.querySource
  · simpa [DenseOverlay.read, htagZero] using hfallback.result_value
  · rw [hfallback.scratch_eq]
    exact hloaded.copyScratch
  · exact hfallback.parked
  · intro i hi
    rw [hfallback.frame i (hi 11) (hi 1) (hi 12) (hi 13)]
    exact hloaded.frame i hi

theorem denseOverlayLookupTM_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ) (initialWork : Fin n → Tape)
    (out₀ : Tape) (hvalid : DenseOverlay.Valid overlay)
    (hready : EntryLookupRestoreReady tapes overlay address initialWork)
    (houtput : TM.Parked out₀) :
    (denseOverlayLookupTM tapes).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseOverlayLookupResult tapes input overlay address initialWork work ∧
        out = out₀)
      (denseOverlayLookupTime tapes input.length overlay address) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let lookupPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
    EntryLookupRestoreResult tapes overlay address initialWork work ∧
    out = out₀
  let finalPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
    DenseOverlayLookupResult tapes input overlay address initialWork work ∧
    out = out₀
  let blankPre : TM.TapePred n := fun inp work out =>
    lookupPost inp work out ∧ (work tapes.destination).read = Γ.blank
  let nonblankPre : TM.TapePred n := fun inp work out =>
    lookupPost inp work out ∧ (work tapes.destination).read ≠ Γ.blank
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using Tape.init_ofBool_move_right_cells_ne_start input
  have hlookup := entryLookupLoaded_hoareTime_internal tapes overlay address
    initialWork inp₀ out₀ hready hinput houtput
  have hblank :
      (denseInputLookupTM tapes.querySource tapes.scan.entry.address
        tapes.destination tapes.copyScratch).HoareTime
        blankPre finalPost (denseInputLookupTime input.length address) := by
    intro inp work out ⟨⟨hinp, hloaded, hout⟩, hread⟩
    have htagZero : RegisterStore.read overlay address = 0 :=
      hloaded.value.read_eq_blank_iff.mp hread
    have haddress : address ≠ 0 := by
      intro hzero
      subst address
      exact hvalid.2 htagZero
    have hcounter :
        (work tapes.scan.entry.address).HasBinaryNat 0 := by
      refine ⟨hloaded.scanner.addressStart, ?_⟩
      simpa [Tape.HasBinaryString, Tape.HasBinaryPrefix] using
        hloaded.scanner.address
    have hdenseReady : DenseInputLookupReady tapes.querySource
        tapes.scan.entry.address tapes.destination tapes.copyScratch address
        work := by
      constructor
      · rw [hloaded.querySource]
        exact hready.querySource
      · exact hcounter
      · simpa [htagZero] using hloaded.value
      · exact hloaded.copyScratch
      · exact hloaded.parked
    have hdense := denseInputLookupTM_hoareTime_internal
      tapes.querySource tapes.scan.entry.address tapes.destination
      tapes.copyScratch (tapes.scan_ne_external 1 1).symm
      tapes.querySource_ne_destination tapes.querySource_ne_copyScratch
      (tapes.scan_ne_external 1 2) (tapes.scan_ne_external 1 3)
      tapes.destination_ne_copyScratch input address work out haddress
      hdenseReady (by simpa [hout] using houtput)
    obtain ⟨done, time, htime, hreach, hhalt, hdoneInput,
        hdenseResult, hdoneOutput⟩ :=
      hdense inp work out ⟨hinp, rfl, rfl⟩
    exact ⟨done, time, htime, hreach, hhalt, hdoneInput,
      denseOverlayResult_of_fallback tapes input overlay address initialWork
        work done.work hloaded htagZero hdenseResult,
      hdoneOutput.trans hout⟩
  have hnonblank : (TM.binaryPredTM tapes.destination).HoareTime
      nonblankPre finalPost
      (TM.binaryPredTime (RegisterStore.read overlay address - 1)) := by
    intro inp work out ⟨⟨hinp, hloaded, hout⟩, hread⟩
    have htagNonzero : RegisterStore.read overlay address ≠ 0 := by
      intro hzero
      have hblankRead := hloaded.value.read_eq_blank_iff.mpr hzero
      exact hread hblankRead
    have htagSucc : RegisterStore.read overlay address - 1 + 1 =
        RegisterStore.read overlay address := by omega
    have hpredValue : (work tapes.destination).HasBinaryNat
        (RegisterStore.read overlay address - 1 + 1) := by
      rw [htagSucc]
      exact hloaded.value
    have hpred := TM.binaryPredTM_hoareTime_frame tapes.destination
      (RegisterStore.read overlay address - 1) inp work out hpredValue
      (by simpa [hinp] using hinput.read_ne_start)
      (fun i _ => (hloaded.parked i).read_ne_start)
      (by simpa [hout] using houtput.read_ne_start)
    obtain ⟨done, time, htime, hreach, hhalt, hdoneInput,
        hdoneOther, hdoneValue, hdoneOutput⟩ :=
      hpred inp work out ⟨rfl, rfl, rfl⟩
    have hdenseValue : (done.work tapes.destination).HasBinaryNat
        (DenseOverlay.read input overlay address) := by
      simpa [DenseOverlay.read, htagNonzero] using hdoneValue
    have hdoneParked : ∀ i, TM.Parked (done.work i) := by
      intro i
      by_cases hi : i = tapes.destination
      · subst i
        exact ⟨by rw [hdoneValue.2.1],
          hdoneValue.2.hasBinaryContent.cells_ne_start⟩
      · rw [hdoneOther i hi]
        exact hloaded.parked i
    exact ⟨done, time, htime, hreach, hhalt,
      hdoneInput.trans hinp,
      denseOverlayResult_of_destination_update tapes input overlay address
        initialWork work done.work hloaded hdenseValue hdoneOther hdoneParked,
      hdoneOutput.trans hout⟩
  have hbranchRaw := TM.branchWorkBlankTM_hoareTime tapes.destination
    (denseInputLookupTM tapes.querySource tapes.scan.entry.address
      tapes.destination tapes.copyScratch)
    (TM.binaryPredTM tapes.destination)
    (pre := lookupPost) (blankPre := blankPre)
    (nonblankPre := nonblankPre)
    (blankPost := finalPost) (nonblankPost := finalPost)
    (by
      intro inp work out ⟨hinp, hloaded, hout⟩
      exact ⟨by simpa [hinp] using hinput.read_ne_start,
        fun i => (hloaded.parked i).read_ne_start,
        by simpa [hout] using houtput.read_ne_start⟩)
    (by
      intro inp work out hpost hread
      exact ⟨hpost, hread⟩)
    (by
      intro inp work out hpost hread
      exact ⟨hpost, hread⟩)
    hblank hnonblank
  have hbranch :
      (TM.branchWorkBlankTM tapes.destination
        (denseInputLookupTM tapes.querySource tapes.scan.entry.address
          tapes.destination tapes.copyScratch)
        (TM.binaryPredTM tapes.destination)).HoareTime
        lookupPost finalPost
        (TM.branchWorkBlankTime (denseInputLookupTime input.length address)
          (TM.binaryPredTime
            (RegisterStore.read overlay address - 1))) := by
    intro inp work out hpost
    obtain ⟨done, time, htime, hreach, hhalt, hfinal⟩ :=
      hbranchRaw inp work out hpost
    exact ⟨done, time, htime, hreach, hhalt, hfinal.elim id id⟩
  have htransition : ∀ inp work out, lookupPost inp work out →
      lookupPost (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out ⟨hinp, hloaded, hout⟩
    subst inp
    subst out
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinput.read_ne_start
      (fun i => (hloaded.parked i).read_ne_start)
      houtput.read_ne_start
    rw [hi, hw, ho]
    exact ⟨rfl, hloaded, rfl⟩
  have hall := TM.seqTM_hoareTime (entryLookupLoadedTM tapes)
    (TM.branchWorkBlankTM tapes.destination
      (denseInputLookupTM tapes.querySource tapes.scan.entry.address
        tapes.destination tapes.copyScratch)
      (TM.binaryPredTM tapes.destination))
    hlookup htransition hbranch
  simpa [denseOverlayLookupTM, denseOverlayLookupTime, inp₀, lookupPost,
    finalPost] using hall

private theorem denseStaticReset_result
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ)
    (initialWork loadedWork : Fin n → Tape)
    (hloaded : DenseOverlayLookupResult tapes input overlay address
      (Function.update initialWork tapes.querySource
        ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
      loadedWork) :
    DenseOverlayLookupStaticResult tapes input overlay address initialWork
      (Function.update loadedWork tapes.querySource
        ((Tape.init []).move Dir3.right)) := by
  let finalWork := Function.update loadedWork tapes.querySource
    ((Tape.init []).move Dir3.right)
  have hsource : tapes.scan.entry.source ≠ tapes.querySource :=
    tapes.ne (by decide)
  have haddress : tapes.scan.entry.address ≠ tapes.querySource :=
    tapes.ne (by decide)
  have hvalue : tapes.scan.entry.value ≠ tapes.querySource :=
    tapes.ne (by decide)
  have haddressCounter :
      tapes.scan.entry.addressCounter ≠ tapes.querySource :=
    tapes.ne (by decide)
  have haddressWidth : tapes.scan.entry.addressWidth ≠ tapes.querySource :=
    tapes.ne (by decide)
  have hvalueCounter : tapes.scan.entry.valueCounter ≠ tapes.querySource :=
    tapes.ne (by decide)
  have hvalueWidth : tapes.scan.entry.valueWidth ≠ tapes.querySource :=
    tapes.ne (by decide)
  have hquery : tapes.scan.entry.query ≠ tapes.querySource :=
    tapes.ne (by decide)
  have hresult : tapes.scan.entry.result ≠ tapes.querySource :=
    tapes.ne (by decide)
  have hcount : tapes.scan.count ≠ tapes.querySource :=
    tapes.ne (by decide)
  have hcountSource : tapes.countSource ≠ tapes.querySource :=
    tapes.countSource_ne_querySource
  have hdestination : tapes.destination ≠ tapes.querySource :=
    tapes.querySource_ne_destination.symm
  have hcopyScratch : tapes.copyScratch ≠ tapes.querySource :=
    tapes.querySource_ne_copyScratch.symm
  have hzero : ((Tape.init []).move Dir3.right).HasBinaryNat 0 := by
    simpa using Tape.init_move_right_hasBinaryNat 0
  have hscanner : EntryScanReady tapes.scan.entry
      (overlay.flatMap Entry.encode) [] finalWork finalWork := by
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
        exact ⟨by
            simpa only [finalWork, Function.update_self] using
              (show 1 ≤ ((Tape.init []).move Dir3.right).head by
                rw [hzero.2.1]),
          by simpa only [finalWork, Function.update_self] using
            hzero.2.hasBinaryContent.cells_ne_start⟩
      · simpa only [finalWork, Function.update_of_ne hi] using hloaded.parked i
  refine
    { scanner := hscanner
      sourceCells := ?_
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
      hloaded.sourceCells
  · simpa only [finalWork, Function.update_of_ne hsource] using
      hloaded.sourceStart
  · simpa only [finalWork, Function.update_of_ne hsource] using
      hloaded.sourceHead
  · simpa only [finalWork, Function.update_of_ne hcount] using hloaded.count
  · simp only [hloaded.countSource, Function.update_of_ne hcountSource]
  · simpa only [finalWork, Function.update_self] using hzero
  · simpa only [finalWork, Function.update_of_ne hdestination] using
      hloaded.value
  · simpa only [finalWork, Function.update_of_ne hcopyScratch] using
      hloaded.copyScratch
  · intro i hi
    have hquerySource : i ≠ tapes.querySource := hi 11
    rw [Function.update_of_ne hquerySource]
    rw [hloaded.frame i hi]
    exact Function.update_of_ne hquerySource _ initialWork

theorem denseOverlayLookupStaticTM_hoareTime_internal
    (tapes : EntryLookupRestoreTapes n) (input : List Bool)
    (overlay : Store) (address : ℕ) (initialWork : Fin n → Tape)
    (out₀ : Tape) (hvalid : DenseOverlay.Valid overlay)
    (hready : EntryLookupStaticReady tapes overlay initialWork)
    (houtput : TM.Parked out₀) :
    (denseOverlayLookupStaticTM tapes address).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseOverlayLookupStaticResult tapes input overlay address initialWork
          work ∧ out = out₀)
      (denseOverlayLookupStaticTime tapes input.length overlay address) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let loadedInitial := Function.update initialWork tapes.querySource
    ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using Tape.init_ofBool_move_right_cells_ne_start input
  have hadd := TM.binaryAddConstTM_hoareTime_frame tapes.querySource address 0
    inp₀ initialWork out₀ hready.querySource hinput
    (fun i _ => hready.scanner.parked i) houtput
  have hadd' : (TM.binaryAddConstTM tapes.querySource address).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = loadedInitial ∧ out = out₀)
      (TM.binaryAddConstTime address 0) := by
    simpa only [loadedInitial, zero_add] using hadd
  have hloadedReady :
      EntryLookupRestoreReady tapes overlay address loadedInitial := by
    simpa only [loadedInitial, zero_add] using
      staticAdd_ready_internal tapes overlay address initialWork hready
  have hloaded := denseOverlayLookupTM_hoareTime_internal tapes input overlay
    address loadedInitial out₀ hvalid hloadedReady houtput
  have hreset : (TM.resetBinaryWorkTM tapes.querySource).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        DenseOverlayLookupResult tapes input overlay address loadedInitial work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseOverlayLookupStaticResult tapes input overlay address initialWork
          work ∧ out = out₀)
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
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      (by
        rw [hfinalWork]
        exact denseStaticReset_result tapes input overlay address initialWork
          work hlookup),
      hfinalOutput.trans hout⟩
  have hloadedReset := TM.seqTM_hoareTime (denseOverlayLookupTM tapes)
    (TM.resetBinaryWorkTM tapes.querySource) hloaded
    (by
      rintro inp work out ⟨hinp, hlookup, hout⟩
      subst inp
      subst out
      obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
        hinput.read_ne_start (fun i => (hlookup.parked i).read_ne_start)
        houtput.read_ne_start
      rw [hi, hw, ho]
      exact ⟨rfl, hlookup, rfl⟩)
    hreset
  have hall := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.querySource address)
    (TM.seqTM (denseOverlayLookupTM tapes)
      (TM.resetBinaryWorkTM tapes.querySource)) hadd'
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst work
      obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
        (inp := inp) (work := loadedInitial) (out := out)
        (by simpa [hinp] using hinput.read_ne_start)
        (fun i => (hloadedReady.scanner.parked i).read_ne_start)
        (by simpa [hout] using houtput.read_ne_start)
      rw [hi, hw, ho]
      exact ⟨hinp, rfl, hout⟩)
    hloadedReset
  simpa [denseOverlayLookupStaticTM, denseOverlayLookupStaticTime, inp₀,
    loadedInitial] using hall

end Machine
end RegisterStore
end RAM
end Complexity
