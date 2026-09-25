/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Internal
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Lookup.Internal.Static

/-!
# Direct sparse-store arithmetic instructions -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

theorem scanner_rhs_of_lhs_internal
    (tapes : BinaryInstructionTapes n) (store : Store) (source : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hlookup : EntryLookupStaticResult tapes.lhsLookup store source
      initialWork finalWork) :
    EntryScanReady tapes.rhsLookup.scan.entry (store.flatMap Entry.encode) []
      finalWork finalWork := by
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
      parked := hlookup.parked
      frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
  · exact hlookup.scanner.source
  · exact hlookup.scanner.address
  · exact hlookup.scanner.addressStart
  · exact hlookup.scanner.value
  · exact hlookup.scanner.valueStart
  · exact hlookup.scanner.addressCounter
  · exact hlookup.scanner.addressWidth
  · exact hlookup.scanner.valueCounter
  · exact hlookup.scanner.valueWidth
  · exact hlookup.scanner.query
  · exact hlookup.scanner.queryStart
  · exact hlookup.scanner.result
  · exact hlookup.scanner.resultStart

theorem rhsReady_of_lhs_internal
    (tapes : BinaryInstructionTapes n) (store : Store) (source : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hrhs : (initialWork tapes.rhs).HasBinaryNat 0)
    (hlookup : EntryLookupStaticResult tapes.lhsLookup store source
      initialWork finalWork) :
    EntryLookupStaticReady tapes.rhsLookup store finalWork := by
  have hrhsEq : finalWork tapes.rhs = initialWork tapes.rhs :=
    hlookup.frame tapes.rhs
      (fun slot => (tapes.lhsLookup_ne_rhs slot).symm)
  refine
    { scanner := scanner_rhs_of_lhs_internal tapes store source initialWork finalWork
        hlookup
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
  change (finalWork tapes.update.resultCount).HasBinaryNat store.length
  have hcountSource : finalWork tapes.update.resultCount =
      initialWork tapes.update.resultCount := by
    simpa using! hlookup.countSource
  rw [hcountSource]
  simpa using! hinitial.countSource

theorem scanner_updateQuery_internal
    (tapes : BinaryInstructionTapes n) (store : Store) (destination : ℕ)
    (work : Fin n → Tape)
    (hscanner : EntryScanReady tapes.rhsLookup.scan.entry
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
  · simpa only [finalWork, Function.update_of_ne hsource] using! hscanner.source
  · simpa only [finalWork, Function.update_of_ne haddress] using! hscanner.address
  · simpa only [finalWork, Function.update_of_ne haddress] using!
      hscanner.addressStart
  · simpa only [finalWork, Function.update_of_ne hvalue] using! hscanner.value
  · simpa only [finalWork, Function.update_of_ne hvalue] using!
      hscanner.valueStart
  · simpa only [finalWork, Function.update_of_ne haddressCounter] using!
      hscanner.addressCounter
  · simpa only [finalWork, Function.update_of_ne haddressWidth] using!
      hscanner.addressWidth
  · simpa only [finalWork, Function.update_of_ne hvalueCounter] using!
      hscanner.valueCounter
  · simpa only [finalWork, Function.update_of_ne hvalueWidth] using!
      hscanner.valueWidth
  · simpa only [finalWork, Function.update_self] using! hnat.2
  · simpa only [finalWork, Function.update_self] using! hnat.1
  · simpa only [finalWork, Function.update_of_ne hresult] using! hscanner.result
  · simpa only [finalWork, Function.update_of_ne hresult] using!
      hscanner.resultStart
  · intro i
    by_cases hi : i = tapes.update.entry.query
    · subst i
      simpa only [finalWork, Function.update_self] using!
        (show TM.Parked
            ((Tape.init (destination.bits.map Γ.ofBool)).move Dir3.right) from
          ⟨by rw [hnat.2.1], hnat.2.hasBinaryContent.cells_ne_start⟩)
    · simpa only [finalWork, Function.update_of_ne hi] using! hscanner.parked i

private theorem directAddress_ready
    (tapes : BinaryInstructionTapes n) (store : Store)
    (destination source₀ source₁ : ℕ)
    (initialWork finalWork : Fin n → Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0)
    (haddress : DirectBinaryAddressResult tapes store destination source₀
      source₁ initialWork finalWork) :
    DirectBinaryUpdateReady tapes store destination source₀ source₁
      finalWork := by
  rcases haddress with ⟨operandsWork, ⟨lhsWork, hlhs, hrhs⟩, rfl⟩
  have hlhsEq : operandsWork tapes.lhs = lhsWork tapes.lhs :=
    hrhs.frame tapes.lhs
      (fun slot => (tapes.rhsLookup_ne_lhs slot).symm)
  have hlhsValue :
      (operandsWork tapes.lhs).HasBinaryNat
        (RegisterStore.read store source₀) := by
    rw [hlhsEq]
    simpa using! hlhs.destination
  have hreplacementEq :
      operandsWork tapes.update.replacement =
        initialWork tapes.update.replacement := by
    rw [hrhs.frame tapes.update.replacement
      (fun slot => (tapes.rhsLookup_ne_replacement slot).symm)]
    exact hlhs.frame tapes.update.replacement
      (fun slot => (tapes.lhsLookup_ne_replacement slot).symm)
  have htmpEq : operandsWork tapes.tmp = initialWork tapes.tmp := by
    rw [hrhs.frame tapes.tmp
      (fun slot => (tapes.rhsLookup_ne_tmp slot).symm)]
    exact hlhs.frame tapes.tmp
      (fun slot => (tapes.lhsLookup_ne_tmp slot).symm)
  have hdblEq : operandsWork tapes.dbl = initialWork tapes.dbl := by
    rw [hrhs.frame tapes.dbl
      (fun slot => (tapes.rhsLookup_ne_dbl slot).symm)]
    exact hlhs.frame tapes.dbl
      (fun slot => (tapes.lhsLookup_ne_dbl slot).symm)
  have hresultCount :
      (operandsWork tapes.update.resultCount).HasBinaryNat store.length := by
    rw [show operandsWork tapes.update.resultCount =
        lhsWork tapes.update.resultCount by simpa using! hrhs.countSource]
    rw [show lhsWork tapes.update.resultCount =
        initialWork tapes.update.resultCount by simpa using! hlhs.countSource]
    simpa using! hinitial.countSource
  have hqueryNeLhs : tapes.lhs ≠ tapes.update.entry.query :=
    tapes.ne (by decide)
  have hqueryNeRhs : tapes.rhs ≠ tapes.update.entry.query :=
    tapes.ne (by decide)
  have hqueryNeReplacement :
      tapes.update.replacement ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hqueryNeShift : tapes.shift ≠ tapes.update.entry.query :=
    (tapes.update_ne_shift 7).symm
  have hqueryNeTmp : tapes.tmp ≠ tapes.update.entry.query :=
    (tapes.update_ne_tmp 7).symm
  have hqueryNeDbl : tapes.dbl ≠ tapes.update.entry.query :=
    (tapes.update_ne_dbl 7).symm
  have hqueryNeRemaining :
      tapes.update.remaining ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hqueryNeFound : tapes.update.found ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  have hqueryNeResultCount :
      tapes.update.resultCount ≠ tapes.update.entry.query :=
    tapes.update.ne (by decide)
  refine
    { scanner := scanner_updateQuery_internal tapes store destination operandsWork
        hrhs.scanner
      lhs := ?_
      rhs := ?_
      replacement := ?_
      shift := ?_
      tmp := ?_
      dbl := ?_
      remaining := ?_
      found := ?_
      resultCount := ?_
      parked := ?_ }
  · simpa only [Function.update_of_ne hqueryNeLhs] using! hlhsValue
  · simpa only [Function.update_of_ne hqueryNeRhs] using! hrhs.destination
  · simpa only [Function.update_of_ne hqueryNeReplacement, hreplacementEq]
      using! hreplacement
  · simpa only [Function.update_of_ne hqueryNeShift] using! hrhs.querySource
  · simpa only [Function.update_of_ne hqueryNeTmp, htmpEq] using! htmp
  · simpa only [Function.update_of_ne hqueryNeDbl, hdblEq] using! hdbl
  · simpa only [Function.update_of_ne hqueryNeRemaining] using! hrhs.count
  · simpa only [Function.update_of_ne hqueryNeFound] using! hrhs.copyScratch
  · simpa only [Function.update_of_ne hqueryNeResultCount] using! hresultCount
  · exact (scanner_updateQuery_internal tapes store destination operandsWork
      hrhs.scanner).parked

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

/-- The shared two-direct-operand prefix used by arithmetic and indirect
store instructions. -/
theorem directBinaryOperands_hoareTime_internal
    (tapes : BinaryInstructionTapes n) (store : Store)
    (source₀ source₁ : ℕ) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hrhs₀ : (initialWork tapes.rhs).HasBinaryNat 0)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (TM.seqTM (entryLookupStaticTM tapes.lhsLookup source₀)
      (entryLookupStaticTM tapes.rhsLookup source₁)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DirectBinaryOperandsResult tapes store source₀ source₁
          initialWork work ∧
        out = out₀)
      (entryLookupStaticTime tapes.lhsLookup store source₀ + 1 +
        entryLookupStaticTime tapes.rhsLookup store source₁) := by
  have hlhs := entryLookupStatic_hoareTime_internal tapes.lhsLookup store
    source₀ initialWork inp₀ out₀ hinitial hinput houtput
  have hrhs : (entryLookupStaticTM tapes.rhsLookup source₁).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupStaticResult tapes.lhsLookup store source₀
          initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DirectBinaryOperandsResult tapes store source₀ source₁
          initialWork work ∧
        out = out₀)
      (entryLookupStaticTime tapes.rhsLookup store source₁) := by
    rintro inp work out ⟨hinp, hlhsResult, hout⟩
    have hready := rhsReady_of_lhs_internal tapes store source₀ initialWork
      work hinitial hrhs₀ hlhsResult
    have hrun := entryLookupStatic_hoareTime_internal tapes.rhsLookup store
      source₁ work inp₀ out₀ hready hinput houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hrhsResult, hfinalOutput⟩ :=
      hrun inp work out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, hlhsResult, hrhsResult⟩, hfinalOutput⟩
  exact TM.seqTM_hoareTime
    (entryLookupStaticTM tapes.lhsLookup source₀)
    (entryLookupStaticTM tapes.rhsLookup source₁) hlhs
    (by
      rintro inp work out ⟨hinp, hlhsResult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput) hlhsResult.parked
        (by simpa [hout] using! houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hlhsResult, hout⟩)
    hrhs

/-- Two fixed sparse reads, direct destination synthesis, width-efficient
arithmetic, and sparse update compose to the pure direct RAM operation. -/
theorem directBinaryInstructionTM_hoareTime_frame_internal
    (tapes : BinaryInstructionTapes n) (op : BinaryInstrOp)
    (store : Store) (destination source₀ source₁ : ℕ)
    (emittedBits : List Bool) (initialWork : Fin n → Tape)
    (inp₀ out₀ : Tape)
    (hcanonical : Canonical store)
    (hinitial : EntryLookupStaticReady tapes.lhsLookup store initialWork)
    (hrhs₀ : (initialWork tapes.rhs).HasBinaryNat 0)
    (hreplacement : (initialWork tapes.update.replacement).HasBinaryNat 0)
    (htmp : (initialWork tapes.tmp).HasBinaryNat 0)
    (hdbl : (initialWork tapes.dbl).HasBinaryNat 0)
    (hinput : TM.Parked inp₀)
    (houtput : out₀.HasBinaryPrefix emittedBits) :
    (directBinaryInstructionTM tapes op destination source₀ source₁).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DirectBinaryInstructionResult tapes op store destination source₀
          source₁ initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination
              (op.eval (RegisterStore.read store source₀)
                (RegisterStore.read store source₁))).flatMap Entry.encode))
      (directBinaryInstructionTime tapes op store destination source₀
        source₁) := by
  have houtputParked := hasBinaryPrefix_parked houtput
  have hlhs := entryLookupStatic_hoareTime_internal tapes.lhsLookup store
    source₀ initialWork inp₀ out₀ hinitial hinput houtputParked
  have hrhs : (entryLookupStaticTM tapes.rhsLookup source₁).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        EntryLookupStaticResult tapes.lhsLookup store source₀
          initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DirectBinaryOperandsResult tapes store source₀ source₁
          initialWork work ∧
        out = out₀)
      (entryLookupStaticTime tapes.rhsLookup store source₁) := by
    rintro inp work out ⟨hinp, hlhsResult, hout⟩
    have hready := rhsReady_of_lhs_internal tapes store source₀ initialWork work
      hinitial hrhs₀ hlhsResult
    have hrun := entryLookupStatic_hoareTime_internal tapes.rhsLookup store
      source₁ work inp₀ out₀ hready hinput houtputParked
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hrhsResult, hfinalOutput⟩ :=
      hrun inp work out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, hlhsResult, hrhsResult⟩, hfinalOutput⟩
  have haddress :
      (TM.binaryAddConstTM tapes.update.entry.query destination).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧
          DirectBinaryOperandsResult tapes store source₀ source₁
            initialWork work ∧
          out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          DirectBinaryAddressResult tapes store destination source₀ source₁
            initialWork work ∧
          out = out₀)
        (TM.binaryAddConstTime destination 0) := by
    rintro inp work out ⟨hinp, operands, hout⟩
    rcases operands with ⟨lhsWork, hlhsResult, hrhsResult⟩
    have hquery : (work tapes.update.entry.query).HasBinaryNat 0 := by
      refine ⟨?_, ?_⟩
      · exact hrhsResult.scanner.queryStart
      · simpa using! hrhsResult.scanner.query
    have hrun := TM.binaryAddConstTM_hoareTime_frame
      tapes.update.entry.query destination 0 inp work out hquery
      (by simpa [hinp] using! hinput)
      (fun i _ => hrhsResult.parked i)
      (by simpa [hout] using! houtputParked)
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hfinalWork, hfinalOutput⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨final, time, htime, hreach, hhalt,
      hfinalInput.trans hinp, ?_, hfinalOutput.trans hout⟩
    exact ⟨work, ⟨lhsWork, hlhsResult, hrhsResult⟩,
      by simpa only [zero_add] using! hfinalWork⟩
  have hupdate : (binaryInstructionUpdateTM tapes op).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧
        DirectBinaryAddressResult tapes store destination source₀ source₁
          initialWork work ∧
        out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        DirectBinaryInstructionResult tapes op store destination source₀
          source₁ initialWork work ∧
        out.HasBinaryPrefix
          (emittedBits ++
            (RegisterStore.write store destination
              (op.eval (RegisterStore.read store source₀)
                (RegisterStore.read store source₁))).flatMap Entry.encode))
      (binaryInstructionUpdateTime tapes op store destination
        (RegisterStore.read store source₀)
        (RegisterStore.read store source₁)) := by
    rintro inp work out ⟨hinp, haddressResult, hout⟩
    have hready := directAddress_ready tapes store destination source₀
      source₁ initialWork work hinitial hreplacement htmp hdbl haddressResult
    have hrun := binaryInstructionUpdateTM_hoareTime_frame_internal tapes op
      store destination (RegisterStore.read store source₀)
      (RegisterStore.read store source₁) emittedBits work inp₀ out₀
      hcanonical hready.scanner hready.lhs hready.rhs hready.replacement
      hready.shift hready.tmp hready.dbl hready.remaining hready.found
      hready.resultCount hinput hready.parked houtput
    obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
        hupdateResult, hfinalOutput⟩ :=
      hrun inp work out ⟨hinp, rfl, hout⟩
    exact ⟨final, time, htime, hreach, hhalt, hfinalInput,
      ⟨work, haddressResult, hupdateResult⟩, hfinalOutput⟩
  have haddressUpdate := TM.seqTM_hoareTime
    (TM.binaryAddConstTM tapes.update.entry.query destination)
    (binaryInstructionUpdateTM tapes op) haddress
    (by
      rintro inp work out ⟨hinp, haddressResult, hout⟩
      have hready := directAddress_ready tapes store destination source₀
        source₁ initialWork work hinitial hreplacement htmp hdbl
        haddressResult
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput) hready.parked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, haddressResult, hout⟩)
    hupdate
  have hrhsRest := TM.seqTM_hoareTime
    (entryLookupStaticTM tapes.rhsLookup source₁)
    (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
      (binaryInstructionUpdateTM tapes op)) hrhs
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
  have hall := TM.seqTM_hoareTime
    (entryLookupStaticTM tapes.lhsLookup source₀)
    (TM.seqTM (entryLookupStaticTM tapes.rhsLookup source₁)
      (TM.seqTM (TM.binaryAddConstTM tapes.update.entry.query destination)
        (binaryInstructionUpdateTM tapes op))) hlhs
    (by
      rintro inp work out ⟨hinp, hlhsResult, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using! hinput) hlhsResult.parked
        (by simpa [hout] using! houtputParked)
      rw [hi, hw, ho]
      exact ⟨hinp, hlhsResult, hout⟩)
    hrhsRest
  simpa [directBinaryInstructionTM, directBinaryInstructionTime] using! hall

end Machine

end RegisterStore

end RAM

end Complexity
