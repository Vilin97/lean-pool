/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseDefs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Direct
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Tagged
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.DenseInternal

/-!
# Dense-overlay direct arithmetic instructions
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

private theorem hasBinaryPrefix_parked {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  TM.hasBinaryPrefix_parked h

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_of_parked hinput hwork houtput

private theorem denseScanner_rhs_of_lhs
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (source : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hlookup : DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
      source initialWork finalWork) :
    EntryScanReady tapes.rhsLookup.scan.entry (overlay.flatMap Entry.encode) []
      finalWork finalWork := by
  exact
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

private theorem denseRhsReady_of_lhs
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (source : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hrhs : (initialWork tapes.rhs).HasBinaryNat 0)
    (hlookup : DenseOverlayLookupStaticResult tapes.lhsLookup input overlay
      source initialWork finalWork) :
    EntryLookupStaticReady tapes.rhsLookup overlay finalWork := by
  have hrhsEq : finalWork tapes.rhs = initialWork tapes.rhs :=
    hlookup.frame tapes.rhs (fun slot => (tapes.lhsLookup_ne_rhs slot).symm)
  refine
    { scanner := denseScanner_rhs_of_lhs tapes input overlay source initialWork
        finalWork hlookup
      sourceStart := hlookup.sourceStart
      sourceHead := hlookup.sourceHead
      count := by simpa using! hlookup.count
      countSource := ?_
      querySource := by simpa using! hlookup.querySource
      destination := by
        change (finalWork tapes.rhs).HasBinaryNat 0
        rw [hrhsEq]
        exact hrhs
      copyScratch := by simpa using! hlookup.copyScratch }
  change (finalWork tapes.update.resultCount).HasBinaryNat overlay.length
  rw [show finalWork tapes.update.resultCount =
      initialWork tapes.update.resultCount by simpa using! hlookup.countSource]
  simpa using! hinitial.countSource

/-- Two fixed dense-overlay reads compose while retaining the shared scanner
ABI and the immutable input tape. -/
theorem denseDirectBinaryOperands_hoareTime
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (source₀ source₁ : ℕ)
    (initialWork : Fin n → Tape) (out₀ : Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hrhs₀ : (initialWork tapes.rhs).HasBinaryNat 0)
    (houtput : TM.Parked out₀) :
    (TM.seqTM (denseOverlayLookupStaticTM tapes.lhsLookup source₀)
      (denseOverlayLookupStaticTM tapes.rhsLookup source₁)).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseDirectBinaryOperandsResult tapes input overlay source₀ source₁
          initialWork work ∧ out = out₀)
      (denseOverlayLookupStaticTime tapes.lhsLookup input.length overlay
          source₀ + 1 +
        denseOverlayLookupStaticTime tapes.rhsLookup input.length overlay
          source₁) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have hlhs := denseOverlayLookupStaticTM_hoareTime_internal tapes.lhsLookup
    input overlay source₀ initialWork out₀ hvalid hinitial houtput
  have hrhs : (denseOverlayLookupStaticTM tapes.rhsLookup source₁).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        DenseOverlayLookupStaticResult tapes.lhsLookup input overlay source₀
          initialWork work ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseDirectBinaryOperandsResult tapes input overlay source₀ source₁
          initialWork work ∧ out = out₀)
      (denseOverlayLookupStaticTime tapes.rhsLookup input.length overlay
        source₁) := by
    rintro inp work out ⟨hinp, hlhsResult, hout⟩
    have hready := denseRhsReady_of_lhs tapes input overlay source₀ initialWork
      work hinitial hrhs₀ hlhsResult
    have hrun := denseOverlayLookupStaticTM_hoareTime_internal tapes.rhsLookup
      input overlay source₁ work out₀ hvalid hready houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hrhsResult, hfinalOutput⟩ :=
      hrun inp work out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, hlhsResult, hrhsResult⟩, hfinalOutput⟩
  have hall := TM.seqTM_hoareTime
    (denseOverlayLookupStaticTM tapes.lhsLookup source₀)
    (denseOverlayLookupStaticTM tapes.rhsLookup source₁) hlhs
    (by
      rintro inp work out ⟨hinp, hlhsResult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [inp₀, hinp] using! hinput) hlhsResult.parked
        (by simpa [hout] using! houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hlhsResult, hout⟩)
    hrhs
  simpa only [inp₀] using! hall

private theorem denseDirectAddress_ready
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (destination source₀ source₁ : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0)
    (haddress : DenseDirectBinaryAddressResult tapes input overlay destination
      source₀ source₁ initialWork finalWork) :
    EntryScanReady tapes.update.entry (overlay.flatMap Entry.encode)
        destination.bits finalWork finalWork ∧
      (finalWork tapes.lhs).HasBinaryNat
        (DenseOverlay.read input overlay source₀) ∧
      (finalWork tapes.rhs).HasBinaryNat
        (DenseOverlay.read input overlay source₁) ∧
      (finalWork tapes.update.replacement).HasBinaryNat 0 ∧
      (finalWork tapes.shift).HasBinaryNat 0 ∧
      (finalWork tapes.tmp).HasBinaryNat 0 ∧
      (finalWork tapes.dbl).HasBinaryNat 0 ∧
      (finalWork tapes.update.remaining).HasBinaryNat overlay.length ∧
      (finalWork tapes.update.found).HasBinaryNat 0 ∧
      (finalWork tapes.update.resultCount).HasBinaryNat overlay.length ∧
      ∀ i, TM.Parked (finalWork i) := by
  rcases haddress with ⟨operandsWork, ⟨lhsWork, hlhs, hrhs⟩, rfl⟩
  have hlhsEq : operandsWork tapes.lhs = lhsWork tapes.lhs :=
    hrhs.frame tapes.lhs (fun slot => (tapes.rhsLookup_ne_lhs slot).symm)
  have hreplacementEq : operandsWork tapes.update.replacement =
      initialWork tapes.update.replacement := by
    rw [hrhs.frame tapes.update.replacement
      (fun slot => (tapes.rhsLookup_ne_replacement slot).symm)]
    exact hlhs.frame tapes.update.replacement
      (fun slot => (tapes.lhsLookup_ne_replacement slot).symm)
  have htmpEq : operandsWork tapes.tmp = initialWork tapes.tmp := by
    rw [hrhs.frame tapes.tmp (fun slot => (tapes.rhsLookup_ne_tmp slot).symm)]
    exact hlhs.frame tapes.tmp (fun slot => (tapes.lhsLookup_ne_tmp slot).symm)
  have hdblEq : operandsWork tapes.dbl = initialWork tapes.dbl := by
    rw [hrhs.frame tapes.dbl (fun slot => (tapes.rhsLookup_ne_dbl slot).symm)]
    exact hlhs.frame tapes.dbl (fun slot => (tapes.lhsLookup_ne_dbl slot).symm)
  have hresultCount :
      (operandsWork tapes.update.resultCount).HasBinaryNat overlay.length := by
    rw [show operandsWork tapes.update.resultCount =
        lhsWork tapes.update.resultCount by simpa using! hrhs.countSource]
    rw [show lhsWork tapes.update.resultCount =
        initialWork tapes.update.resultCount by simpa using! hlhs.countSource]
    simpa using! hinitial.countSource
  have hqueryNe (i : Fin n) (h : i ≠ tapes.update.entry.query) :
      Function.update operandsWork tapes.update.entry.query
        ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right) i =
        operandsWork i := Function.update_of_ne h _ _
  have hscanner := scanner_updateQuery_internal tapes overlay destination
    operandsWork hrhs.scanner
  refine ⟨hscanner, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hscanner.parked⟩
  · rw [hqueryNe tapes.lhs (tapes.ne (by decide)), hlhsEq]
    exact hlhs.destination
  · rw [hqueryNe tapes.rhs (tapes.ne (by decide))]
    exact hrhs.destination
  · rw [hqueryNe tapes.update.replacement (tapes.update.ne (by decide)),
      hreplacementEq]
    exact hreplacement
  · rw [hqueryNe tapes.shift ((tapes.update_ne_shift 7).symm)]
    exact hrhs.querySource
  · rw [hqueryNe tapes.tmp ((tapes.update_ne_tmp 7).symm), htmpEq]
    exact htmp
  · rw [hqueryNe tapes.dbl ((tapes.update_ne_dbl 7).symm), hdblEq]
    exact hdbl
  · rw [hqueryNe tapes.update.remaining (tapes.update.ne (by decide))]
    exact hrhs.count
  · rw [hqueryNe tapes.update.found (tapes.update.ne (by decide))]
    exact hrhs.copyScratch
  · rw [hqueryNe tapes.update.resultCount (tapes.update.ne (by decide))]
    exact hresultCount

private theorem denseArithmetic_update_ready
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (overlay : Store) (address lhs rhs : ℕ)
    (initialWork work : Fin n → Tape)
    (hready : EntryScanReady tapes.update.entry
      (overlay.flatMap Entry.encode) address.bits initialWork initialWork)
    (hremaining :
      (initialWork tapes.update.remaining).HasBinaryNat overlay.length)
    (hfound : (initialWork tapes.update.found).HasBinaryNat 0)
    (hresultCount :
      (initialWork tapes.update.resultCount).HasBinaryNat overlay.length)
    (harith : BinaryInstructionArithmeticResult tapes op lhs rhs
      initialWork work) :
    EntryScanReady tapes.update.entry (overlay.flatMap Entry.encode)
        address.bits work work ∧
      (work tapes.update.remaining).HasBinaryNat overlay.length ∧
      (work tapes.update.found).HasBinaryNat 0 ∧
      (work tapes.update.resultCount).HasBinaryNat overlay.length := by
  have hslotEq (slot : Fin 13) (hne : slot ≠ 10) :
      work (tapes.update.idx slot) = initialWork (tapes.update.idx slot) :=
    harith.frame (tapes.update.idx slot)
      (tapes.update_ne_lhs slot) (tapes.update_ne_rhs slot)
      (tapes.update.ne hne) (tapes.update_ne_shift slot)
      (tapes.update_ne_tmp slot) (tapes.update_ne_dbl slot)
  have hready' : EntryScanReady tapes.update.entry
      (overlay.flatMap Entry.encode) address.bits work work := by
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
        parked := harith.parked
        frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
    · change (work (tapes.update.idx 0)).HasBinarySuffix _
      rw [hslotEq 0 (by decide)]
      exact hready.source
    · change (work (tapes.update.idx 1)).HasBinaryPrefix []
      rw [hslotEq 1 (by decide)]
      exact hready.address
    · change (work (tapes.update.idx 1)).cells 0 = Γ.start
      rw [hslotEq 1 (by decide)]
      exact hready.addressStart
    · change (work (tapes.update.idx 2)).HasBinaryPrefix []
      rw [hslotEq 2 (by decide)]
      exact hready.value
    · change (work (tapes.update.idx 2)).cells 0 = Γ.start
      rw [hslotEq 2 (by decide)]
      exact hready.valueStart
    · change (work (tapes.update.idx 3)).HasBinaryNat 0
      rw [hslotEq 3 (by decide)]
      exact hready.addressCounter
    · change (work (tapes.update.idx 4)).HasBinaryNat 0
      rw [hslotEq 4 (by decide)]
      exact hready.addressWidth
    · change (work (tapes.update.idx 5)).HasBinaryNat 0
      rw [hslotEq 5 (by decide)]
      exact hready.valueCounter
    · change (work (tapes.update.idx 6)).HasBinaryNat 0
      rw [hslotEq 6 (by decide)]
      exact hready.valueWidth
    · change (work (tapes.update.idx 7)).HasBinaryString address.bits
      rw [hslotEq 7 (by decide)]
      exact hready.query
    · change (work (tapes.update.idx 7)).cells 0 = Γ.start
      rw [hslotEq 7 (by decide)]
      exact hready.queryStart
    · change (work (tapes.update.idx 8)).HasBinaryPrefix []
      rw [hslotEq 8 (by decide)]
      exact hready.result
    · change (work (tapes.update.idx 8)).cells 0 = Γ.start
      rw [hslotEq 8 (by decide)]
      exact hready.resultStart
  refine ⟨hready', ?_, ?_, ?_⟩
  · change (work (tapes.update.idx 9)).HasBinaryNat _
    rw [hslotEq 9 (by decide)]
    exact hremaining
  · change (work (tapes.update.idx 11)).HasBinaryNat 0
    rw [hslotEq 11 (by decide)]
    exact hfound
  · change (work (tapes.update.idx 12)).HasBinaryNat _
    rw [hslotEq 12 (by decide)]
    exact hresultCount

/-- Arithmetic feeds its canonical result through successor tagging and into
the sparse overlay update controller. -/
theorem denseBinaryInstructionUpdateTM_hoareTime_frame
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (overlay : Store) (address lhs rhs : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape) (hcanonical : Canonical overlay)
    (hready : EntryScanReady tapes.update.entry
      (overlay.flatMap Entry.encode) address.bits initialWork initialWork)
    (hlhs : (initialWork tapes.lhs).HasBinaryNat lhs)
    (hrhs : (initialWork tapes.rhs).HasBinaryNat rhs)
    (hresult : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hshift : (initialWork tapes.shift).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0)
    (hremaining :
      (initialWork tapes.update.remaining).HasBinaryNat overlay.length)
    (hfound : (initialWork tapes.update.found).HasBinaryNat 0)
    (hresultCount :
      (initialWork tapes.update.resultCount).HasBinaryNat overlay.length)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (initialWork i))
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (denseBinaryInstructionUpdateTM tapes op).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseBinaryInstructionUpdateResult tapes op overlay address lhs rhs
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay address (op.eval lhs rhs)).flatMap
              Entry.encode))
      (denseBinaryInstructionUpdateTime tapes op overlay address lhs rhs) := by
  have harithmetic := binaryInstructionArithmeticTM_hoareTime_frame_internal
    tapes op lhs rhs inp₀ initialWork out₀ hlhs hrhs hresult hshift htmp hdbl
    hinput hwork (hasBinaryPrefix_parked houtput)
  have hupdate : (taggedEntryUpdateTM tapes.update).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        BinaryInstructionArithmeticResult tapes op lhs rhs initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseBinaryInstructionUpdateResult tapes op overlay address lhs rhs
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay address (op.eval lhs rhs)).flatMap
              Entry.encode))
      (taggedEntryUpdateTime tapes.update overlay address (op.eval lhs rhs)) := by
    rintro inp work out ⟨hinp, harith, hout⟩
    have hready' := denseArithmetic_update_ready tapes op overlay address lhs
      rhs initialWork work hready hremaining hfound hresultCount harith
    have hrun := taggedEntryUpdateTM_hoareTime_frame tapes.update overlay
      address (op.eval lhs rhs) emittedBits work inp₀ out₀ hcanonical
      hready'.1 harith.result hready'.2.1 hready'.2.2.1 hready'.2.2.2
      hinput houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        htagged, hfinalOutput⟩ :=
      hrun inp work out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, harith, htagged⟩, hfinalOutput⟩
  have hall := TM.seqTM_hoareTime (binaryInstructionArithmeticTM tapes op)
    (taggedEntryUpdateTM tapes.update) harithmetic
    (by
      rintro inp work out ⟨hinp, harith, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput) harith.parked
        (by simpa [hout] using! hasBinaryPrefix_parked houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, harith, hout⟩)
    hupdate
  simpa [denseBinaryInstructionUpdateTM,
    denseBinaryInstructionUpdateTime] using! hall

/-- Two dense reads, direct destination synthesis, arithmetic, successor
tagging, and sparse update implement one RAM arithmetic instruction. -/
theorem denseDirectBinaryInstructionTM_hoareTime_frame
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (input : List Bool) (overlay : Store)
    (destination source₀ source₁ : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (out₀ : Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hrhs₀ : (initialWork tapes.rhs).HasBinaryNat 0)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (denseDirectBinaryInstructionTM tapes op destination source₀ source₁).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseDirectBinaryInstructionResult tapes op input overlay destination
          source₀ source₁ initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay destination
              (op.eval (DenseOverlay.read input overlay source₀)
                (DenseOverlay.read input overlay source₁))).flatMap Entry.encode))
      (denseDirectBinaryInstructionTime tapes op input overlay destination
        source₀ source₁) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have houtputParked := hasBinaryPrefix_parked houtput
  have hoperands := denseDirectBinaryOperands_hoareTime tapes input overlay
    source₀ source₁ initialWork out₀ hvalid hinitial hrhs₀ houtputParked
  have haddress : (TM.binaryAddConstTM tapes.update.entry.query
      destination).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        DenseDirectBinaryOperandsResult tapes input overlay source₀ source₁
          initialWork work ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseDirectBinaryAddressResult tapes input overlay destination source₀
          source₁ initialWork work ∧ out = out₀)
      (TM.binaryAddConstTime destination 0) := by
    rintro inp work out ⟨hinp, operands, hout⟩
    rcases operands with ⟨lhsWork, hlhsResult, hrhsResult⟩
    have hquery : (work tapes.update.entry.query).HasBinaryNat 0 :=
      ⟨hrhsResult.scanner.queryStart, by simpa using! hrhsResult.scanner.query⟩
    have hrun := TM.binaryAddConstTM_hoareTime_frame
      tapes.update.entry.query destination 0 inp work out hquery
      (by simpa [hinp] using! hinput)
      (fun i _ => hrhsResult.parked i)
      (by simpa [hout] using! houtputParked)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      ⟨work, ⟨lhsWork, hlhsResult, hrhsResult⟩,
        by simpa only [zero_add] using! hfinalWork⟩,
      hfinalOutput.trans hout⟩
  have hupdate : (denseBinaryInstructionUpdateTM tapes op).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        DenseDirectBinaryAddressResult tapes input overlay destination source₀
          source₁ initialWork work ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseDirectBinaryInstructionResult tapes op input overlay destination
          source₀ source₁ initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay destination
              (op.eval (DenseOverlay.read input overlay source₀)
                (DenseOverlay.read input overlay source₁))).flatMap Entry.encode))
      (denseBinaryInstructionUpdateTime tapes op overlay destination
        (DenseOverlay.read input overlay source₀)
        (DenseOverlay.read input overlay source₁)) := by
    rintro inp work out ⟨hinp, haddressResult, hout⟩
    have hready := denseDirectAddress_ready tapes input overlay destination
      source₀ source₁ initialWork work hinitial hreplacement htmp hdbl
      haddressResult
    rcases hready with ⟨hscanner, hlhs, hrhs, hrepl, hshift, htmp', hdbl',
      hremaining, hfound, hresultCount, hparked⟩
    have hrun := denseBinaryInstructionUpdateTM_hoareTime_frame tapes op
      overlay destination (DenseOverlay.read input overlay source₀)
      (DenseOverlay.read input overlay source₁) emittedBits work inp₀ out₀
      hvalid.1 hscanner hlhs hrhs hrepl hshift htmp' hdbl' hremaining hfound
      hresultCount hinput hparked houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hupdateResult, hfinalOutput⟩ := hrun inp work out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, haddressResult, hupdateResult⟩, hfinalOutput⟩
  have haddressUpdate := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.update.entry.query destination)
    (denseBinaryInstructionUpdateTM tapes op) haddress
    (by
      rintro inp work out ⟨hinp, haddressResult, hout⟩
      have hready := denseDirectAddress_ready tapes input overlay destination
        source₀ source₁ initialWork work hinitial hreplacement htmp hdbl
        haddressResult
      rcases hready with ⟨_, _, _, _, _, _, _, _, _, _, hparked⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput)
        hparked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, haddressResult, hout⟩)
    hupdate
  have hall := TM.seqTM_hoareTime
    (TM.seqTM (denseOverlayLookupStaticTM tapes.lhsLookup source₀)
      (denseOverlayLookupStaticTM tapes.rhsLookup source₁))
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (denseBinaryInstructionUpdateTM tapes op)) hoperands
    (by
      rintro inp work out ⟨hinp, operands, hout⟩
      rcases operands with ⟨lhsWork, hlhsResult, hrhsResult⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput) hrhsResult.parked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨lhsWork, hlhsResult, hrhsResult⟩, hout⟩)
    haddressUpdate
  simpa [denseDirectBinaryInstructionTM, denseDirectBinaryInstructionTime,
    inp₀] using! hall

end Machine
end RegisterStore
end RAM
end Complexity
