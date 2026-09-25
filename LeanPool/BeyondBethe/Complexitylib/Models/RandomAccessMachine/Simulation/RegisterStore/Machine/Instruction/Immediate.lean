/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Defs

/-!
# Immediate sparse-store instructions -- proof internals
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

theorem immediateUpdate_ready_internal
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination value : ℕ) (initialWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork) :
    let valueWork := Function.update initialWork tapes.update.replacement
      ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)
    let updateWork := Function.update valueWork tapes.update.entry.query
      ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)
    EntryScanReady tapes.update.entry (store.flatMap Entry.encode)
        destination.bits updateWork updateWork ∧
      (updateWork tapes.update.replacement).HasBinaryNat value ∧
      (updateWork tapes.update.remaining).HasBinaryNat store.length ∧
      (updateWork tapes.update.found).HasBinaryNat 0 ∧
      (updateWork tapes.update.resultCount).HasBinaryNat store.length ∧
      ∀ i, TM.Parked (updateWork i) := by
  dsimp only
  let valueTape :=
    (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right
  let queryTape :=
    (Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right
  let valueWork := Function.update initialWork tapes.update.replacement valueTape
  let updateWork := Function.update valueWork tapes.update.entry.query queryTape
  have hsourceReplacement :
      tapes.update.entry.source ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hsourceQuery :
      tapes.update.entry.source ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have haddressReplacement :
      tapes.update.entry.address ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have haddressQuery :
      tapes.update.entry.address ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hvalueReplacement :
      tapes.update.entry.value ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hvalueQuery :
      tapes.update.entry.value ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have haddressCounterReplacement :
      tapes.update.entry.addressCounter ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have haddressCounterQuery :
      tapes.update.entry.addressCounter ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have haddressWidthReplacement :
      tapes.update.entry.addressWidth ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have haddressWidthQuery :
      tapes.update.entry.addressWidth ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hvalueCounterReplacement :
      tapes.update.entry.valueCounter ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hvalueCounterQuery :
      tapes.update.entry.valueCounter ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hvalueWidthReplacement :
      tapes.update.entry.valueWidth ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hvalueWidthQuery :
      tapes.update.entry.valueWidth ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hqueryReplacement :
      tapes.update.entry.query ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hresultReplacement :
      tapes.update.entry.result ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hresultQuery :
      tapes.update.entry.result ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hreplacementQuery :
      tapes.update.replacement ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hremainingReplacement :
      tapes.update.remaining ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hremainingQuery :
      tapes.update.remaining ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hfoundReplacement :
      tapes.update.found ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hfoundQuery : tapes.update.found ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hresultCountReplacement :
      tapes.update.resultCount ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hresultCountQuery :
      tapes.update.resultCount ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hvalueNat := Tape.init_move_right_hasBinaryNat value
  have hqueryNat := Tape.init_move_right_hasBinaryNat destination
  have hscanner : EntryScanReady tapes.update.entry
      (store.flatMap Entry.encode) destination.bits updateWork updateWork := by
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
    · simpa only [updateWork, valueWork, Function.update_of_ne hsourceQuery,
        Function.update_of_ne hsourceReplacement] using! hinitial.scanner.source
    · simpa only [updateWork, valueWork, Function.update_of_ne haddressQuery,
        Function.update_of_ne haddressReplacement] using! hinitial.scanner.address
    · simpa only [updateWork, valueWork, Function.update_of_ne haddressQuery,
        Function.update_of_ne haddressReplacement] using!
        hinitial.scanner.addressStart
    · simpa only [updateWork, valueWork, Function.update_of_ne hvalueQuery,
        Function.update_of_ne hvalueReplacement] using! hinitial.scanner.value
    · simpa only [updateWork, valueWork, Function.update_of_ne hvalueQuery,
        Function.update_of_ne hvalueReplacement] using!
        hinitial.scanner.valueStart
    · simpa only [updateWork, valueWork,
        Function.update_of_ne haddressCounterQuery,
        Function.update_of_ne haddressCounterReplacement] using!
        hinitial.scanner.addressCounter
    · simpa only [updateWork, valueWork,
        Function.update_of_ne haddressWidthQuery,
        Function.update_of_ne haddressWidthReplacement] using!
        hinitial.scanner.addressWidth
    · simpa only [updateWork, valueWork,
        Function.update_of_ne hvalueCounterQuery,
        Function.update_of_ne hvalueCounterReplacement] using!
        hinitial.scanner.valueCounter
    · simpa only [updateWork, valueWork,
        Function.update_of_ne hvalueWidthQuery,
        Function.update_of_ne hvalueWidthReplacement] using!
        hinitial.scanner.valueWidth
    · simpa only [updateWork, Function.update_self, queryTape] using!
        hqueryNat.2
    · simpa only [updateWork, Function.update_self, queryTape] using!
        hqueryNat.1
    · simpa only [updateWork, valueWork, Function.update_of_ne hresultQuery,
        Function.update_of_ne hresultReplacement] using! hinitial.scanner.result
    · simpa only [updateWork, valueWork, Function.update_of_ne hresultQuery,
        Function.update_of_ne hresultReplacement] using!
        hinitial.scanner.resultStart
    · intro i
      by_cases hiQuery : i = tapes.update.entry.query
      · subst i
        simpa only [updateWork, Function.update_self, queryTape] using!
          (show TM.Parked queryTape from
            ⟨by rw [hqueryNat.2.1],
              hqueryNat.2.hasBinaryContent.cells_ne_start⟩)
      · have hiEq : updateWork i = valueWork i :=
          Function.update_of_ne hiQuery _ valueWork
        rw [hiEq]
        by_cases hiReplacement : i = tapes.update.replacement
        · subst i
          simpa only [valueWork, Function.update_self, valueTape] using!
            (show TM.Parked valueTape from
              ⟨by rw [hvalueNat.2.1],
                hvalueNat.2.hasBinaryContent.cells_ne_start⟩)
        · simpa only [valueWork, Function.update_of_ne hiReplacement] using!
            hinitial.scanner.parked i
  refine ⟨hscanner, ?_, ?_, ?_, ?_, hscanner.parked⟩
  · simpa only [updateWork, Function.update_of_ne hreplacementQuery,
      valueWork, Function.update_self, valueTape] using! hvalueNat
  · simpa only [updateWork, Function.update_of_ne hremainingQuery,
      valueWork, Function.update_of_ne hremainingReplacement] using!
      hinitial.count
  · simpa only [updateWork, Function.update_of_ne hfoundQuery, valueWork,
      Function.update_of_ne hfoundReplacement] using! hinitial.copyScratch
  · simpa only [updateWork, Function.update_of_ne hresultCountQuery,
      valueWork, Function.update_of_ne hresultCountReplacement] using!
      hinitial.countSource

/-- Exact semantic and time contract for one immediate sparse assignment. -/
theorem immediateInstructionTM_hoareTime_frame_internal
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination value : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (immediateInstructionTM tapes destination value).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ImmediateInstructionResult tapes store destination value initialWork
          work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination value).flatMap Entry.encode))
      (immediateInstructionTime tapes store destination value) := by
  let valueWork := Function.update initialWork tapes.update.replacement
    ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)
  let updateWork := Function.update valueWork tapes.update.entry.query
    ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right)
  have houtputParked := hasBinaryPrefix_parked houtput
  have hvalue := TM.binaryAddConstTM_hoareTime_frame
    tapes.update.replacement value 0 inp₀ initialWork out₀ hreplacement
    hinput (fun i _ => hinitial.scanner.parked i) houtputParked
  have hvalue' : (TM.binaryAddConstTM tapes.update.replacement value).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = valueWork ∧ out = out₀)
      (TM.binaryAddConstTime value 0) := by
    simpa only [valueWork, zero_add] using! hvalue
  have hquery : (TM.binaryAddConstTM tapes.update.entry.query
      destination).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = valueWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = updateWork ∧ out = out₀)
      (TM.binaryAddConstTime destination 0) := by
    have hqueryZero : (valueWork tapes.update.entry.query).HasBinaryNat 0 := by
      have hqueryReplacement :
          tapes.update.entry.query ≠ tapes.update.replacement :=
        tapes.update.ne (by decide)
      have heq : valueWork tapes.update.entry.query =
          initialWork tapes.update.entry.query :=
        Function.update_of_ne hqueryReplacement _ initialWork
      rw [heq]
      exact ⟨hinitial.scanner.queryStart, by simpa using! hinitial.scanner.query⟩
    have hrun := TM.binaryAddConstTM_hoareTime_frame
      tapes.update.entry.query destination 0 inp₀ valueWork out₀ hqueryZero
      hinput
      (fun i _ => by
        by_cases hi : i = tapes.update.replacement
        · subst i
          exact ⟨by simp [valueWork, Tape.init, Tape.move], by
            simpa [valueWork] using!
              (Tape.init_move_right_hasBinaryNat value).2.hasBinaryContent.cells_ne_start⟩
        · simpa only [valueWork, Function.update_of_ne hi] using!
            hinitial.scanner.parked i)
      houtputParked
    simpa only [updateWork, zero_add] using! hrun
  have hready := immediateUpdate_ready_internal tapes store destination value initialWork
    hinitial
  have hupdate := entryUpdateTM_hoareTime_frame tapes.update store destination
    value emittedBits updateWork inp₀ out₀ hcanonical hready.1 hready.2.1
    hready.2.2.1 hready.2.2.2.1 hready.2.2.2.2.1 hinput houtput
  have hupdate' : (entryUpdateTM tapes.update).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = updateWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ImmediateInstructionResult tapes store destination value initialWork
          work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination value).flatMap Entry.encode))
      (entryUpdateTime tapes.update store destination value) :=
    hupdate.strengthen_post (by
      rintro inp work out ⟨hinp, houtcome, hout, hsourceCells⟩
      refine ⟨hinp, ⟨valueWork, updateWork, rfl, rfl, houtcome, ?_⟩, hout⟩
      calc
        (work tapes.update.entry.source).cells =
            (updateWork tapes.update.entry.source).cells := hsourceCells
        _ = (valueWork tapes.update.entry.source).cells := by
          rw [show updateWork tapes.update.entry.source =
              valueWork tapes.update.entry.source by
            exact Function.update_of_ne (tapes.update.ne (by decide)) _ _]
        _ = (initialWork tapes.update.entry.source).cells := by
          rw [show valueWork tapes.update.entry.source =
              initialWork tapes.update.entry.source by
            exact Function.update_of_ne (tapes.update.ne (by decide)) _ _])
  have hqueryUpdate := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.update.entry.query destination)
    (entryUpdateTM tapes.update) hquery
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst work
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := updateWork) (out := out)
        (by simpa [hinp] using! hinput) hready.2.2.2.2.2
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, rfl, hout⟩)
    hupdate'
  have hall := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.update.replacement value)
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (entryUpdateTM tapes.update)) hvalue'
    (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst work
      have hparked : ∀ i, TM.Parked (valueWork i) := by
        intro i
        by_cases hi : i = tapes.update.replacement
        · subst i
          have hnat := Tape.init_move_right_hasBinaryNat value
          simpa only [valueWork, Function.update_self] using!
            (show TM.Parked
                ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right) from
              ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
        · simpa only [valueWork, Function.update_of_ne hi] using!
            hinitial.scanner.parked i
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := valueWork) (out := out)
        (by simpa [hinp] using! hinput) hparked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, rfl, hout⟩)
    hqueryUpdate
  simpa [immediateInstructionTM, immediateInstructionTime] using! hall

end Machine

end RegisterStore

end RAM

end Complexity
