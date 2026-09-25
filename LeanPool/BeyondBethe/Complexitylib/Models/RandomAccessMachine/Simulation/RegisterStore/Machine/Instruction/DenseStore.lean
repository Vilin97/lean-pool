/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseDirect

/-!
# Dense-overlay indirect store
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

variable {n : ℕ}

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

private theorem denseStoreOperands_values
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (addressRegister source : ℕ)
    (initialWork operandsWork : Fin n → Tape)
    (hoperands : DenseDirectBinaryOperandsResult tapes input overlay
      addressRegister source initialWork operandsWork) :
    (operandsWork tapes.lhs).HasBinaryNat
        (DenseOverlay.read input overlay addressRegister) ∧
      (operandsWork tapes.rhs).HasBinaryNat
        (DenseOverlay.read input overlay source) ∧
      (operandsWork tapes.update.found).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (operandsWork i) := by
  rcases hoperands with ⟨lhsWork, hlhs, hrhs⟩
  have hlhsEq : operandsWork tapes.lhs = lhsWork tapes.lhs :=
    hrhs.frame tapes.lhs (fun slot => (tapes.rhsLookup_ne_lhs slot).symm)
  refine ⟨?_, by simpa using! hrhs.destination,
    by simpa using! hrhs.copyScratch, hrhs.parked⟩
  rw [hlhsEq]
  exact hlhs.destination

private theorem scanner_after_replacement
    (tapes : BinaryInstructionTapes n) (overlay : Store) (address value : ℕ)
    (work : Fin n → Tape)
    (hscanner : EntryScanReady tapes.update.entry
      (overlay.flatMap Entry.encode) address.bits work work) :
    EntryScanReady tapes.update.entry (overlay.flatMap Entry.encode)
      address.bits
      (Function.update work tapes.update.replacement
        ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right))
      (Function.update work tapes.update.replacement
        ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)) := by
  let finalWork := Function.update work tapes.update.replacement
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)
  have hsource : tapes.update.entry.source ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have haddress : tapes.update.entry.address ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hvalue : tapes.update.entry.value ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have haddressCounter :
      tapes.update.entry.addressCounter ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have haddressWidth :
      tapes.update.entry.addressWidth ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hvalueCounter :
      tapes.update.entry.valueCounter ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hvalueWidth :
      tapes.update.entry.valueWidth ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hquery : tapes.update.entry.query ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hresult : tapes.update.entry.result ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hnat := Tape.init_move_right_hasBinaryNat value
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
        simpa only [finalWork, Function.update_of_ne hquery] using!
          hscanner.query
      queryStart := by
        simpa only [finalWork, Function.update_of_ne hquery] using!
          hscanner.queryStart
      result := by
        simpa only [finalWork, Function.update_of_ne hresult] using!
          hscanner.result
      resultStart := by
        simpa only [finalWork, Function.update_of_ne hresult] using!
          hscanner.resultStart
      parked := ?_
      frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
  intro i
  by_cases hi : i = tapes.update.replacement
  · subst i
    simpa only [finalWork, Function.update_self] using!
      (show TM.Parked
          ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right) from
        ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
  · simpa only [finalWork, Function.update_of_ne hi] using! hscanner.parked i

private theorem denseStoreUpdate_ready
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (addressRegister source : ℕ)
    (initialWork operandsWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hoperands : DenseDirectBinaryOperandsResult tapes input overlay
      addressRegister source initialWork operandsWork) :
    let address := DenseOverlay.read input overlay addressRegister
    let value := DenseOverlay.read input overlay source
    let queryWork := Function.update operandsWork tapes.update.entry.query
      ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)
    let updateWork := Function.update queryWork tapes.update.replacement
      ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)
    EntryScanReady tapes.update.entry (overlay.flatMap Entry.encode)
        address.bits updateWork updateWork ∧
      (updateWork tapes.update.replacement).HasBinaryNat value ∧
      (updateWork tapes.update.remaining).HasBinaryNat overlay.length ∧
      (updateWork tapes.update.found).HasBinaryNat 0 ∧
      (updateWork tapes.update.resultCount).HasBinaryNat overlay.length ∧
      ∀ i, TM.Parked (updateWork i) := by
  dsimp only
  rcases hoperands with ⟨lhsWork, hlhs, hrhs⟩
  let address := DenseOverlay.read input overlay addressRegister
  let value := DenseOverlay.read input overlay source
  let queryWork := Function.update operandsWork tapes.update.entry.query
    ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)
  let updateWork := Function.update queryWork tapes.update.replacement
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)
  have hqueryScanner := scanner_updateQuery_internal tapes overlay address
    operandsWork hrhs.scanner
  have hscanner : EntryScanReady tapes.update.entry
      (overlay.flatMap Entry.encode) address.bits updateWork updateWork := by
    simpa only [queryWork, updateWork] using!
      scanner_after_replacement tapes overlay address value queryWork
        hqueryScanner
  have hvalueNat := Tape.init_move_right_hasBinaryNat value
  have hresultCount :
      (operandsWork tapes.update.resultCount).HasBinaryNat overlay.length := by
    rw [show operandsWork tapes.update.resultCount =
        lhsWork tapes.update.resultCount by simpa using! hrhs.countSource]
    rw [show lhsWork tapes.update.resultCount =
        initialWork tapes.update.resultCount by simpa using! hlhs.countSource]
    simpa using! hinitial.countSource
  have hremainingReplacement :
      tapes.update.remaining ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hremainingQuery :
      tapes.update.remaining ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hfoundReplacement : tapes.update.found ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hfoundQuery : tapes.update.found ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hresultCountReplacement :
      tapes.update.resultCount ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hresultCountQuery :
      tapes.update.resultCount ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  refine ⟨hscanner, ?_, ?_, ?_, ?_, hscanner.parked⟩
  · simpa only [updateWork, Function.update_self] using! hvalueNat
  · simpa only [updateWork, Function.update_of_ne hremainingReplacement,
      queryWork, Function.update_of_ne hremainingQuery] using! hrhs.count
  · simpa only [updateWork, Function.update_of_ne hfoundReplacement,
      queryWork, Function.update_of_ne hfoundQuery] using! hrhs.copyScratch
  · simpa only [updateWork, Function.update_of_ne hresultCountReplacement,
      queryWork, Function.update_of_ne hresultCountQuery] using! hresultCount

/-- The dense-store update stage preserves its operand witnesses and exact encoded-write output. -/
private theorem denseStore_updateStage
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (addressRegister source : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (out₀ : Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hinput : TM.Parked ((Tape.init (input.map Γ.ofBool)).move Dir3.right))
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
    let address := DenseOverlay.read input overlay addressRegister
    let value := DenseOverlay.read input overlay source
    (taggedEntryUpdateTM tapes.update).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ operandsWork queryWork,
          DenseDirectBinaryOperandsResult tapes input overlay addressRegister
            source initialWork operandsWork ∧
          queryWork = Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) ∧
          work = Function.update queryWork tapes.update.replacement
            ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DenseIndirectStoreInstructionResult tapes input overlay addressRegister
          source initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay address value).flatMap Entry.encode))
      (taggedEntryUpdateTime tapes.update overlay address value) := by
  dsimp only
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let address := DenseOverlay.read input overlay addressRegister
  let value := DenseOverlay.read input overlay source
  rintro inp work out ⟨hinp, ⟨operandsWork, queryWork, hops,
    hqueryWork, hwork⟩, hout⟩
  subst queryWork
  subst work
  have hready := denseStoreUpdate_ready tapes input overlay addressRegister
    source initialWork operandsWork hinitial hops
  let updateWork := Function.update
    (Function.update operandsWork tapes.update.entry.query
      ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
    tapes.update.replacement
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)
  have hrun := taggedEntryUpdateTM_hoareTime_frame tapes.update overlay
    address value emittedBits updateWork inp₀ out₀ hvalid.1 hready.1
    hready.2.1 hready.2.2.1 hready.2.2.2.1 hready.2.2.2.2.1 hinput
    houtput
  obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
      houtcome, hfinalOutput⟩ :=
    hrun inp updateWork out ⟨hinp, rfl, hout⟩
  exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
    ⟨operandsWork,
      Function.update operandsWork tapes.update.entry.query
        ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right),
      updateWork, hops, rfl, rfl, by simpa [address, value] using! houtcome⟩,
    by simpa [address, value] using! hfinalOutput⟩

/-- Exact semantic and time contract for one dense-overlay indirect store. -/
theorem denseIndirectStoreInstructionTM_hoareTime_frame
    (tapes : BinaryInstructionTapes n) (input : List Bool)
    (overlay : Store) (addressRegister source : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape) (out₀ : Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup overlay initialWork)
    (hrhs₀ : (initialWork tapes.rhs).HasBinaryNat 0)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (denseIndirectStoreInstructionTM tapes addressRegister source).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseIndirectStoreInstructionResult tapes input overlay addressRegister
          source initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (DenseOverlay.write overlay
              (DenseOverlay.read input overlay addressRegister)
              (DenseOverlay.read input overlay source)).flatMap Entry.encode))
      (denseIndirectStoreInstructionTime tapes input overlay addressRegister
        source) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let address := DenseOverlay.read input overlay addressRegister
  let value := DenseOverlay.read input overlay source
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using! Tape.init_ofBool_move_right_cells_ne_start input
  have houtputParked := hasBinaryPrefix_parked houtput
  have hoperands := denseDirectBinaryOperands_hoareTime tapes input overlay
    addressRegister source initialWork out₀ hvalid hinitial hrhs₀ houtputParked
  have hquery :
      (TM.binaryCopyIntoTM tapes.lhs tapes.update.entry.query
        tapes.update.found).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        DenseDirectBinaryOperandsResult tapes input overlay addressRegister
          source initialWork work ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ operandsWork,
          DenseDirectBinaryOperandsResult tapes input overlay addressRegister
            source initialWork operandsWork ∧
          work = Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (TM.binaryCopyTime address 0) := by
    rintro inp work out ⟨hinp, hops, hout⟩
    have hvalues := denseStoreOperands_values tapes input overlay
      addressRegister source initialWork work hops
    have hrun := TM.binaryCopyIntoTM_hoareTime_frame tapes.lhs
      tapes.update.entry.query tapes.update.found (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.update.ne (by decide)) address 0 inp work
      out (by simpa [address] using! hvalues.1)
      ⟨(by rcases hops with ⟨_, _, hrhs⟩; exact hrhs.scanner.queryStart),
        (by rcases hops with ⟨_, _, hrhs⟩;
            simpa using! hrhs.scanner.query)⟩
      hvalues.2.2.1 (by simpa [hinp] using! hinput)
      (fun i _ _ _ => hvalues.2.2.2 i)
      (by simpa [hout] using! houtputParked)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ := hrun inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      ⟨work, hops, by simpa [address] using! hfinalWork⟩,
      hfinalOutput.trans hout⟩
  have hvalue :
      (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement
        tapes.update.found).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ operandsWork,
          DenseDirectBinaryOperandsResult tapes input overlay addressRegister
            source initialWork operandsWork ∧
          work = Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ operandsWork queryWork,
          DenseDirectBinaryOperandsResult tapes input overlay addressRegister
            source initialWork operandsWork ∧
          queryWork = Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) ∧
          work = Function.update queryWork tapes.update.replacement
            ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (TM.binaryCopyTime value 0) := by
    rintro inp work out ⟨hinp, ⟨operandsWork, hops, hwork⟩, hout⟩
    subst work
    have hvalues := denseStoreOperands_values tapes input overlay
      addressRegister source initialWork operandsWork hops
    let queryWork := Function.update operandsWork tapes.update.entry.query
      ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)
    have hrhsQuery : tapes.rhs ≠ tapes.update.entry.query :=
      tapes.ne (by decide)
    have hreplacementQuery :
        tapes.update.replacement ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hfoundQuery : tapes.update.found ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hrun := TM.binaryCopyIntoTM_hoareTime_frame tapes.rhs
      tapes.update.replacement tapes.update.found (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.update.ne (by decide)) value 0 inp
      queryWork out
      (by simpa only [queryWork, Function.update_of_ne hrhsQuery, value] using!
        hvalues.2.1)
      (by
        have hreplEq : operandsWork tapes.update.replacement =
            initialWork tapes.update.replacement := by
          rcases hops with ⟨lhsWork, hlhs, hrhs⟩
          rw [hrhs.frame tapes.update.replacement
            (fun slot => (tapes.rhsLookup_ne_replacement slot).symm)]
          exact hlhs.frame tapes.update.replacement
            (fun slot => (tapes.lhsLookup_ne_replacement slot).symm)
        simpa only [queryWork, Function.update_of_ne hreplacementQuery,
          hreplEq] using! hreplacement)
      (by simpa only [queryWork, Function.update_of_ne hfoundQuery] using!
        hvalues.2.2.1)
      (by simpa [hinp] using! hinput)
      (fun i _ _ _ => by
        by_cases hi : i = tapes.update.entry.query
        · subst i
          have hnat := Tape.init_move_right_hasBinaryNat address
          simpa only [queryWork, Function.update_self] using!
            (show TM.Parked
                ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) from
              ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
        · simpa only [queryWork, Function.update_of_ne hi] using!
            hvalues.2.2.2 i)
      (by simpa [hout] using! houtputParked)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ :=
      hrun inp queryWork out ⟨rfl, rfl, rfl⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      ⟨operandsWork, queryWork, hops, rfl,
        by simpa [value] using! hfinalWork⟩,
      hfinalOutput.trans hout⟩
  have hupdate := denseStore_updateStage tapes input overlay addressRegister source emittedBits
    initialWork out₀ hvalid hinitial hinput houtput
  have hvalueUpdate := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement tapes.update.found)
    (taggedEntryUpdateTM tapes.update) hvalue
    (by
      rintro inp work out ⟨hinp, ⟨operandsWork, queryWork, hops,
        hqueryWork, hwork⟩, hout⟩
      subst queryWork
      subst work
      have hready := denseStoreUpdate_ready tapes input overlay addressRegister
        source initialWork operandsWork hinitial hops
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp)
        (work := Function.update
          (Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
          tapes.update.replacement
          ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right))
        (out := out) (by simpa [hinp] using! hinput) hready.2.2.2.2.2
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨operandsWork, _, hops, rfl, rfl⟩, hout⟩)
    hupdate
  have hqueryRest := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM tapes.lhs tapes.update.entry.query tapes.update.found)
    (TM.seqTM
      (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement tapes.update.found)
      (taggedEntryUpdateTM tapes.update)) hquery
    (by
      rintro inp work out ⟨hinp, ⟨operandsWork, hops, hwork⟩, hout⟩
      subst work
      have hvalues := denseStoreOperands_values tapes input overlay
        addressRegister source initialWork operandsWork hops
      have hparked : ∀ i, TM.Parked
          (Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) i) := by
        intro i
        by_cases hi : i = tapes.update.entry.query
        · subst i
          have hnat := Tape.init_move_right_hasBinaryNat address
          simpa only [Function.update_self] using!
            (show TM.Parked
                ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) from
              ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
        · simpa only [Function.update_of_ne hi] using! hvalues.2.2.2 i
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp)
        (work := Function.update operandsWork tapes.update.entry.query
          ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
        (out := out) (by simpa [hinp] using! hinput) hparked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨operandsWork, hops, rfl⟩, hout⟩)
    hvalueUpdate
  have hall := TM.seqTM_hoareTime
    (TM.seqTM (denseOverlayLookupStaticTM tapes.lhsLookup addressRegister)
      (denseOverlayLookupStaticTM tapes.rhsLookup source))
    (TM.seqTM
      (TM.binaryCopyIntoTM tapes.lhs tapes.update.entry.query tapes.update.found)
      (TM.seqTM
        (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement
          tapes.update.found)
        (taggedEntryUpdateTM tapes.update))) hoperands
    (by
      rintro inp work out ⟨hinp, hops, hout⟩
      have hvalues := denseStoreOperands_values tapes input overlay
        addressRegister source initialWork work hops
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput) hvalues.2.2.2
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, hops, hout⟩)
    hqueryRest
  simpa [denseIndirectStoreInstructionTM, denseIndirectStoreInstructionTime,
    inp₀, address, value] using! hall

end Machine
end RegisterStore
end RAM
end Complexity
