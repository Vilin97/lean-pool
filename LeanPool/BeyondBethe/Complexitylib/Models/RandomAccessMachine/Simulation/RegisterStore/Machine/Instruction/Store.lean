/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Direct

/-!
# Indirect sparse-store instructions -- proof internals
-/


public section

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

private theorem storeOperands_values
    (tapes : BinaryInstructionTapes n) (store : Store)
    (addressRegister source : ℕ) (initialWork operandsWork : Fin n → Tape)
    (hoperands : DirectBinaryOperandsResult tapes store addressRegister source
      initialWork operandsWork) :
    (operandsWork tapes.lhs).HasBinaryNat
        (RegisterStore.read store addressRegister) ∧
      (operandsWork tapes.rhs).HasBinaryNat (RegisterStore.read store source) ∧
      (operandsWork tapes.update.found).HasBinaryNat 0 ∧
      ∀ i, TM.Parked (operandsWork i) := by
  rcases hoperands with ⟨lhsWork, hlhs, hrhs⟩
  have hlhsEq : operandsWork tapes.lhs = lhsWork tapes.lhs :=
    hrhs.frame tapes.lhs
      (fun slot => (tapes.rhsLookup_ne_lhs slot).symm)
  refine ⟨?_, by simpa using hrhs.destination, by simpa using hrhs.copyScratch,
    hrhs.parked⟩
  rw [hlhsEq]
  simpa using hlhs.destination

private theorem storeUpdate_ready
    (tapes : BinaryInstructionTapes n) (store : Store)
    (addressRegister source : ℕ) (initialWork operandsWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hoperands : DirectBinaryOperandsResult tapes store addressRegister source
      initialWork operandsWork) :
    let queryWork := Function.update operandsWork tapes.update.entry.query
      ((Tape.init ((RegisterStore.read store addressRegister).bits.map
        Γ.ofBool)).move Dir3.right)
    let updateWork := Function.update queryWork tapes.update.replacement
      ((Tape.init ((RegisterStore.read store source).bits.map Γ.ofBool)).move
        Dir3.right)
    EntryScanReady tapes.update.entry (store.flatMap Entry.encode)
        (RegisterStore.read store addressRegister).bits updateWork updateWork ∧
      (updateWork tapes.update.replacement).HasBinaryNat
        (RegisterStore.read store source) ∧
      (updateWork tapes.update.remaining).HasBinaryNat store.length ∧
      (updateWork tapes.update.found).HasBinaryNat 0 ∧
      (updateWork tapes.update.resultCount).HasBinaryNat store.length ∧
      ∀ i, TM.Parked (updateWork i) := by
  dsimp only
  rcases hoperands with ⟨lhsWork, hlhs, hrhs⟩
  let queryTape :=
    (Tape.init ((RegisterStore.read store addressRegister).bits.map Γ.ofBool)).move
      Dir3.right
  let valueTape :=
    (Tape.init ((RegisterStore.read store source).bits.map Γ.ofBool)).move
      Dir3.right
  let queryWork := Function.update operandsWork tapes.update.entry.query queryTape
  let updateWork := Function.update queryWork tapes.update.replacement valueTape
  have hqueryNat := Tape.init_move_right_hasBinaryNat
    (RegisterStore.read store addressRegister)
  have hvalueNat := Tape.init_move_right_hasBinaryNat
    (RegisterStore.read store source)
  have hqueryReplacement :
      tapes.update.entry.query ≠ tapes.update.replacement :=
    tapes.update.ne (by decide)
  have hscanner : EntryScanReady tapes.update.entry
      (store.flatMap Entry.encode)
      (RegisterStore.read store addressRegister).bits updateWork updateWork := by
    have hsourceQuery :
        tapes.update.entry.source ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hsourceReplacement :
        tapes.update.entry.source ≠ tapes.update.replacement :=
      tapes.update.ne (by decide)
    have haddressQuery :
        tapes.update.entry.address ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have haddressReplacement :
        tapes.update.entry.address ≠ tapes.update.replacement :=
      tapes.update.ne (by decide)
    have hvalueQuery : tapes.update.entry.value ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hvalueReplacement :
        tapes.update.entry.value ≠ tapes.update.replacement :=
      tapes.update.ne (by decide)
    have haddressCounterQuery :
        tapes.update.entry.addressCounter ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have haddressCounterReplacement :
        tapes.update.entry.addressCounter ≠ tapes.update.replacement :=
      tapes.update.ne (by decide)
    have haddressWidthQuery :
        tapes.update.entry.addressWidth ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have haddressWidthReplacement :
        tapes.update.entry.addressWidth ≠ tapes.update.replacement :=
      tapes.update.ne (by decide)
    have hvalueCounterQuery :
        tapes.update.entry.valueCounter ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hvalueCounterReplacement :
        tapes.update.entry.valueCounter ≠ tapes.update.replacement :=
      tapes.update.ne (by decide)
    have hvalueWidthQuery :
        tapes.update.entry.valueWidth ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hvalueWidthReplacement :
        tapes.update.entry.valueWidth ≠ tapes.update.replacement :=
      tapes.update.ne (by decide)
    have hresultQuery :
        tapes.update.entry.result ≠ tapes.update.entry.query :=
      tapes.update.ne (by decide)
    have hresultReplacement :
        tapes.update.entry.result ≠ tapes.update.replacement :=
      tapes.update.ne (by decide)
    refine
      { source := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne hsourceReplacement,
            Function.update_of_ne hsourceQuery] using hrhs.scanner.source
        address := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne haddressReplacement,
            Function.update_of_ne haddressQuery] using hrhs.scanner.address
        addressStart := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne haddressReplacement,
            Function.update_of_ne haddressQuery] using
            hrhs.scanner.addressStart
        value := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne hvalueReplacement,
            Function.update_of_ne hvalueQuery] using hrhs.scanner.value
        valueStart := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne hvalueReplacement,
            Function.update_of_ne hvalueQuery] using hrhs.scanner.valueStart
        addressCounter := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne haddressCounterReplacement,
            Function.update_of_ne haddressCounterQuery] using
            hrhs.scanner.addressCounter
        addressWidth := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne haddressWidthReplacement,
            Function.update_of_ne haddressWidthQuery] using
            hrhs.scanner.addressWidth
        valueCounter := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne hvalueCounterReplacement,
            Function.update_of_ne hvalueCounterQuery] using
            hrhs.scanner.valueCounter
        valueWidth := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne hvalueWidthReplacement,
            Function.update_of_ne hvalueWidthQuery] using
            hrhs.scanner.valueWidth
        query := by
          simpa only [updateWork,
            Function.update_of_ne hqueryReplacement, queryWork,
            Function.update_self, queryTape] using hqueryNat.2
        queryStart := by
          simpa only [updateWork,
            Function.update_of_ne hqueryReplacement, queryWork,
            Function.update_self, queryTape] using hqueryNat.1
        result := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne hresultReplacement,
            Function.update_of_ne hresultQuery] using hrhs.scanner.result
        resultStart := by
          simpa only [updateWork, queryWork,
            Function.update_of_ne hresultReplacement,
            Function.update_of_ne hresultQuery] using
            hrhs.scanner.resultStart
        parked := ?_
        frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
    intro i
    by_cases hiReplacement : i = tapes.update.replacement
    · subst i
      simpa only [updateWork, Function.update_self, valueTape] using
        (show TM.Parked valueTape from
          ⟨by rw [hvalueNat.2.1],
            hvalueNat.2.hasBinaryContent.cells_ne_start⟩)
    · have hiUpdate : updateWork i = queryWork i :=
        Function.update_of_ne hiReplacement _ queryWork
      rw [hiUpdate]
      by_cases hiQuery : i = tapes.update.entry.query
      · subst i
        simpa only [queryWork, Function.update_self, queryTape] using
          (show TM.Parked queryTape from
            ⟨by rw [hqueryNat.2.1],
              hqueryNat.2.hasBinaryContent.cells_ne_start⟩)
      · simpa only [queryWork, Function.update_of_ne hiQuery] using
          hrhs.parked i
  have hresultCount :
      (operandsWork tapes.update.resultCount).HasBinaryNat store.length := by
    rw [show operandsWork tapes.update.resultCount =
        lhsWork tapes.update.resultCount by simpa using hrhs.countSource]
    rw [show lhsWork tapes.update.resultCount =
        initialWork tapes.update.resultCount by simpa using hlhs.countSource]
    simpa using hinitial.countSource
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
  refine ⟨hscanner, ?_, ?_, ?_, ?_, hscanner.parked⟩
  · simpa only [updateWork, Function.update_self, valueTape] using hvalueNat
  · simpa only [updateWork,
      Function.update_of_ne hremainingReplacement, queryWork,
      Function.update_of_ne hremainingQuery] using hrhs.count
  · simpa only [updateWork,
      Function.update_of_ne hfoundReplacement, queryWork,
      Function.update_of_ne hfoundQuery] using
      hrhs.copyScratch
  · simpa only [updateWork,
      Function.update_of_ne hresultCountReplacement, queryWork,
      Function.update_of_ne hresultCountQuery] using hresultCount

/-- Exact semantic and time contract for one indirect sparse store. -/
theorem indirectStoreInstructionTM_hoareTime_frame_internal
    (tapes : BinaryInstructionTapes n) (store : Store)
    (addressRegister source : ℕ) (emittedBits : List Bool)
    (initialWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hrhs₀ : (initialWork tapes.rhs).HasBinaryNat 0)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (indirectStoreInstructionTM tapes addressRegister source).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        IndirectStoreInstructionResult tapes store addressRegister source
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store
              (RegisterStore.read store addressRegister)
              (RegisterStore.read store source)).flatMap Entry.encode))
      (indirectStoreInstructionTime tapes store addressRegister source) := by
  let address := RegisterStore.read store addressRegister
  let value := RegisterStore.read store source
  have houtputParked := hasBinaryPrefix_parked houtput
  have hoperands := directBinaryOperands_hoareTime_internal tapes store
    addressRegister source initialWork inp₀ out₀ hinitial hrhs₀ hinput
    houtputParked
  have hquery :
      (TM.binaryCopyIntoTM tapes.lhs tapes.update.entry.query
        tapes.update.found).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        DirectBinaryOperandsResult tapes store addressRegister source
          initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ operandsWork,
          DirectBinaryOperandsResult tapes store addressRegister source
            initialWork operandsWork ∧
          work = Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (TM.binaryCopyTime address 0) := by
    rintro inp work out ⟨hinp, hops, hout⟩
    have hvalues := storeOperands_values tapes store addressRegister source
      initialWork work hops
    have hrun := TM.binaryCopyIntoTM_hoareTime_frame tapes.lhs
      tapes.update.entry.query tapes.update.found (tapes.ne (by decide))
      (tapes.ne (by decide)) (tapes.update.ne (by decide)) address 0 inp work
      out (by simpa [address] using hvalues.1)
      ⟨(by rcases hops with ⟨_, _, hrhs⟩; exact hrhs.scanner.queryStart),
        (by rcases hops with ⟨_, _, hrhs⟩;
            simpa using hrhs.scanner.query)⟩
      hvalues.2.2.1 (by simpa [hinp] using hinput)
      (fun i _ _ _ => hvalues.2.2.2 i)
      (by simpa [hout] using houtputParked)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      ⟨work, hops, by simpa [address] using hfinalWork⟩,
      hfinalOutput.trans hout⟩
  have hvalue :
      (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement
        tapes.update.found).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ operandsWork,
          DirectBinaryOperandsResult tapes store addressRegister source
            initialWork operandsWork ∧
          work = Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ operandsWork queryWork,
          DirectBinaryOperandsResult tapes store addressRegister source
            initialWork operandsWork ∧
          queryWork = Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) ∧
          work = Function.update queryWork tapes.update.replacement
            ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (TM.binaryCopyTime value 0) := by
    rintro inp work out ⟨hinp, ⟨operandsWork, hops, hwork⟩, hout⟩
    subst work
    have hvalues := storeOperands_values tapes store addressRegister source
      initialWork operandsWork hops
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
      (by simpa only [queryWork,
          Function.update_of_ne hrhsQuery, value] using hvalues.2.1)
      (by
        have hreplEq : operandsWork tapes.update.replacement =
            initialWork tapes.update.replacement := by
          rcases hops with ⟨lhsWork, hlhs, hrhs⟩
          rw [hrhs.frame tapes.update.replacement
            (fun slot => (tapes.rhsLookup_ne_replacement slot).symm)]
          exact hlhs.frame tapes.update.replacement
            (fun slot => (tapes.lhsLookup_ne_replacement slot).symm)
        simpa only [queryWork,
          Function.update_of_ne hreplacementQuery, hreplEq] using
          hreplacement)
      (by simpa only [queryWork,
          Function.update_of_ne hfoundQuery] using hvalues.2.2.1)
      (by simpa [hinp] using hinput)
      (fun i _ _ _ => by
        by_cases hi : i = tapes.update.entry.query
        · subst i
          have hnat := Tape.init_move_right_hasBinaryNat address
          simpa only [queryWork, Function.update_self] using
            (show TM.Parked
                ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) from
              ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
        · simpa only [queryWork, Function.update_of_ne hi] using
            hvalues.2.2.2 i)
      (by simpa [hout] using houtputParked)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ :=
      hrun inp queryWork out ⟨rfl, rfl, rfl⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput.trans hinp,
      ⟨operandsWork, queryWork, hops, rfl,
        by simpa [value] using hfinalWork⟩,
      hfinalOutput.trans hout⟩
  have hupdate : (entryUpdateTM tapes.update).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        (∃ operandsWork queryWork,
          DirectBinaryOperandsResult tapes store addressRegister source
            initialWork operandsWork ∧
          queryWork = Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) ∧
          work = Function.update queryWork tapes.update.replacement
            ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)) ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        IndirectStoreInstructionResult tapes store addressRegister source
          initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store address value).flatMap Entry.encode))
      (entryUpdateTime tapes.update store address value) := by
    rintro inp work out ⟨hinp, ⟨operandsWork, queryWork, hops,
      hqueryWork, hwork⟩, hout⟩
    subst queryWork
    subst work
    have hready := storeUpdate_ready tapes store addressRegister source
      initialWork operandsWork hinitial hops
    let updateWork := Function.update
      (Function.update operandsWork tapes.update.entry.query
        ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
      tapes.update.replacement
      ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)
    have hrun := entryUpdateTM_hoareTime_frame tapes.update store address value
      emittedBits updateWork inp₀ out₀ hcanonical hready.1 hready.2.1
      hready.2.2.1 hready.2.2.2.1 hready.2.2.2.2.1 hinput houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        houtcome, hfinalOutput, hsourceCells⟩ :=
      hrun inp updateWork out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨operandsWork,
        Function.update operandsWork tapes.update.entry.query
          ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right),
        updateWork, hops, rfl, rfl, by simpa [address, value] using houtcome,
        by
          rcases hops with ⟨lhsWork, hlhs, hrhs⟩
          calc
            (final.work tapes.update.entry.source).cells =
                (updateWork tapes.update.entry.source).cells := hsourceCells
            _ = (operandsWork tapes.update.entry.source).cells := by
              rw [show updateWork tapes.update.entry.source =
                  (Function.update operandsWork tapes.update.entry.query
                    ((Tape.init (address.bits.map Γ.ofBool)).move
                      Dir3.right)) tapes.update.entry.source by
                exact Function.update_of_ne (tapes.update.ne (by decide)) _ _]
              rw [show (Function.update operandsWork
                    tapes.update.entry.query
                    ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
                    tapes.update.entry.source =
                  operandsWork tapes.update.entry.source by
                exact Function.update_of_ne (tapes.update.ne (by decide)) _ _]
            _ = (lhsWork tapes.update.entry.source).cells := hrhs.sourceCells
            _ = (initialWork tapes.update.entry.source).cells :=
              hlhs.sourceCells⟩,
      by simpa [address, value] using hfinalOutput⟩
  have hvalueUpdate := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement tapes.update.found)
    (entryUpdateTM tapes.update) hvalue
    (by
      rintro inp work out ⟨hinp, ⟨operandsWork, queryWork, hops,
        hqueryWork, hwork⟩, hout⟩
      subst queryWork
      subst work
      have hready := storeUpdate_ready tapes store addressRegister source
        initialWork operandsWork hinitial hops
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp)
        (work := Function.update
          (Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
          tapes.update.replacement
          ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right))
        (out := out) (by simpa [hinp] using hinput) hready.2.2.2.2.2
        (by simpa [hout] using houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨operandsWork, _, hops, rfl, rfl⟩, hout⟩)
    hupdate
  have hqueryRest := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM tapes.lhs tapes.update.entry.query tapes.update.found)
    (TM.seqTM
      (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement tapes.update.found)
      (entryUpdateTM tapes.update)) hquery
    (by
      rintro inp work out ⟨hinp, ⟨operandsWork, hops, hwork⟩, hout⟩
      subst work
      have hvalues := storeOperands_values tapes store addressRegister source
        initialWork operandsWork hops
      have hparked : ∀ i, TM.Parked
          (Function.update operandsWork tapes.update.entry.query
            ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) i) := by
        intro i
        by_cases hi : i = tapes.update.entry.query
        · subst i
          have hnat := Tape.init_move_right_hasBinaryNat address
          simpa only [Function.update_self] using
            (show TM.Parked
                ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right) from
              ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
        · simpa only [Function.update_of_ne hi] using hvalues.2.2.2 i
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp)
        (work := Function.update operandsWork tapes.update.entry.query
          ((Tape.init (address.bits.map Γ.ofBool)).move Dir3.right))
        (out := out) (by simpa [hinp] using hinput) hparked
        (by simpa [hout] using houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, ⟨operandsWork, hops, rfl⟩, hout⟩)
    hvalueUpdate
  have hall := TM.seqTM_hoareTime
    (TM.seqTM (entryLookupStaticTM tapes.lhsLookup addressRegister)
      (entryLookupStaticTM tapes.rhsLookup source))
    (TM.seqTM
      (TM.binaryCopyIntoTM tapes.lhs tapes.update.entry.query tapes.update.found)
      (TM.seqTM
        (TM.binaryCopyIntoTM tapes.rhs tapes.update.replacement tapes.update.found)
        (entryUpdateTM tapes.update))) hoperands
    (by
      rintro inp work out ⟨hinp, hops, hout⟩
      have hvalues := storeOperands_values tapes store addressRegister source
        initialWork work hops
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput) hvalues.2.2.2
        (by simpa [hout] using houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, hops, hout⟩)
    hqueryRest
  simpa [indirectStoreInstructionTM, indirectStoreInstructionTime, address,
    value] using hall

end Machine

end RegisterStore

end RAM

end Complexity
