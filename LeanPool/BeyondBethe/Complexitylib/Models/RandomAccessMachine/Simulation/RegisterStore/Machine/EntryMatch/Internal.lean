/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.AddressEq
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch.Defs

/-!
# RAM sparse-entry matching — proof internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

private theorem parked_of_hasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  ⟨by rw [h.1]; omega,
    Tape.HasBinaryContent.cells_ne_start
      (show t.HasBinaryContent bits from h.2)⟩

private theorem parked_of_hasBinarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasBinarySuffix bits) : TM.Parked t :=
  ⟨h.1, h.2.2.2⟩

private theorem parked_of_hasBinaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

theorem entryMatchTM_reachesIn_frame_internal {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ tapes.source).HasBinarySuffix (Entry.encode entry ++ rest))
    (haddress : (work₀ tapes.address).HasBinaryPrefix [])
    (hvalue : (work₀ tapes.value).HasBinaryPrefix [])
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (haddressCounter : (work₀ tapes.addressCounter).HasBinaryNat 0)
    (haddressWidth : (work₀ tapes.addressWidth).HasBinaryNat 0)
    (hvalueCounter : (work₀ tapes.valueCounter).HasBinaryNat 0)
    (hvalueWidth : (work₀ tapes.valueWidth).HasBinaryNat 0)
    (hquery : (work₀ tapes.query).HasBinaryString queryBits)
    (hqueryStart : (work₀ tapes.query).cells 0 = Γ.start)
    (hresult : (work₀ tapes.result).HasBinaryPrefix [])
    (hresultStart : (work₀ tapes.result).cells 0 = Γ.start)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    ∃ c' t,
      t ≤ entryMatchTime entry queryBits ∧
      (entryMatchTM tapes).reachesIn t
        { state := (entryMatchTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryMatchTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work tapes.source).HasBinarySuffix rest ∧
      (c'.work tapes.address).HasBinaryContent entry.1.bits ∧
      1 ≤ (c'.work tapes.address).head ∧
      (c'.work tapes.address).cells 0 = Γ.start ∧
      (c'.work tapes.value).HasBinaryPrefix entry.2.bits ∧
      (c'.work tapes.value).cells 0 = Γ.start ∧
      (c'.work tapes.addressCounter).HasBinaryPrefix
        (List.replicate (bitlen entry.1) true) ∧
      (c'.work tapes.addressCounter).cells 0 = Γ.start ∧
      (c'.work tapes.addressWidth).HasBinaryNat 0 ∧
      (c'.work tapes.valueCounter).HasBinaryPrefix
        (List.replicate (bitlen entry.2) true) ∧
      (c'.work tapes.valueCounter).cells 0 = Γ.start ∧
      (c'.work tapes.valueWidth).HasBinaryNat 0 ∧
      (c'.work tapes.query).HasBinaryContent queryBits ∧
      1 ≤ (c'.work tapes.query).head ∧
      (c'.work tapes.query).cells 0 = Γ.start ∧
      (c'.work tapes.result).HasBinaryPrefix
        [decide (entry.1.bits = queryBits)] ∧
      (c'.work tapes.result).cells 0 = Γ.start ∧
      (∀ i, TM.Parked (c'.work i)) ∧
      (∀ i, i ≠ tapes.source → i ≠ tapes.address → i ≠ tapes.value →
        i ≠ tapes.addressCounter → i ≠ tapes.addressWidth →
        i ≠ tapes.valueCounter → i ≠ tapes.valueWidth →
        i ≠ tapes.query → i ≠ tapes.result → c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let decodeTM := entryDecodeLinearTM tapes.decode
  let compareTM := decodedAddressEqTM tapes.address tapes.query tapes.result
  obtain ⟨decodeDone, hdecodeReach, hdecodeHalt, hdecodeInput,
      hdecodeSource, hdecodeAddress, hdecodeAddressStart, hdecodeValue,
      hdecodeValueStart, hdecodeAddressCounter, hdecodeValueCounter,
      hdecodeFrame, hdecodeOutput⟩ :=
    entryDecodeLinearTM_reachesIn_frame tapes.decode entry rest inp₀ work₀ out₀
      (by simpa using hsource) (by simpa using haddress)
      (by simpa using hvalue) (by simpa using haddressStart)
      (by simpa using hvalueStart)
      (by
        simpa [Tape.HasBinaryPrefix, Tape.HasBinaryString] using
          haddressCounter.2)
      haddressCounter.1
      (by
        simpa [Tape.HasBinaryPrefix, Tape.HasBinaryString] using
          hvalueCounter.2)
      hvalueCounter.1 hinput.read_ne_start
      (fun i => (hwork i).read_ne_start) houtput.read_ne_start
  have hdecodeAddressWidth :
      (decodeDone.work tapes.addressWidth).HasBinaryNat 0 := by
    rw [hdecodeFrame tapes.addressWidth
      (by simpa using tapes.ne (show (4 : Fin 9) ≠ 0 by decide))
      (by simpa using tapes.ne (show (4 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (4 : Fin 9) ≠ 2 by decide))
      (by simpa using tapes.ne (show (4 : Fin 9) ≠ 3 by decide))
      (by simpa using tapes.ne (show (4 : Fin 9) ≠ 5 by decide))]
    exact haddressWidth
  have hdecodeValueWidth :
      (decodeDone.work tapes.valueWidth).HasBinaryNat 0 := by
    rw [hdecodeFrame tapes.valueWidth
      (by simpa using tapes.ne (show (6 : Fin 9) ≠ 0 by decide))
      (by simpa using tapes.ne (show (6 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (6 : Fin 9) ≠ 2 by decide))
      (by simpa using tapes.ne (show (6 : Fin 9) ≠ 3 by decide))
      (by simpa using tapes.ne (show (6 : Fin 9) ≠ 5 by decide))]
    exact hvalueWidth
  have hdecodeQuery :
      (decodeDone.work tapes.query).HasBinaryString queryBits := by
    rw [hdecodeFrame tapes.query
      (by simpa using tapes.ne (show (7 : Fin 9) ≠ 0 by decide))
      (by simpa using tapes.ne (show (7 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (7 : Fin 9) ≠ 2 by decide))
      (by simpa using tapes.ne (show (7 : Fin 9) ≠ 3 by decide))
      (by simpa using tapes.ne (show (7 : Fin 9) ≠ 5 by decide))]
    exact hquery
  have hdecodeResult :
      (decodeDone.work tapes.result).HasBinaryPrefix [] := by
    rw [hdecodeFrame tapes.result
      (by simpa using tapes.ne (show (8 : Fin 9) ≠ 0 by decide))
      (by simpa using tapes.ne (show (8 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (8 : Fin 9) ≠ 2 by decide))
      (by simpa using tapes.ne (show (8 : Fin 9) ≠ 3 by decide))
      (by simpa using tapes.ne (show (8 : Fin 9) ≠ 5 by decide))]
    exact hresult
  have hdecodeParked : ∀ i, TM.Parked (decodeDone.work i) := by
    intro i
    by_cases his : i = tapes.source
    · subst i
      exact parked_of_hasBinarySuffix (by simpa using hdecodeSource)
    · by_cases hia : i = tapes.address
      · subst i
        exact parked_of_hasBinaryPrefix (by simpa using hdecodeAddress)
      · by_cases hiv : i = tapes.value
        · subst i
          exact parked_of_hasBinaryPrefix (by simpa using hdecodeValue)
        · by_cases hiac : i = tapes.addressCounter
          · subst i
            exact parked_of_hasBinaryPrefix
              (by simpa using hdecodeAddressCounter)
          · by_cases hiaw : i = tapes.addressWidth
            · subst i
              exact parked_of_hasBinaryNat
                (by simpa using hdecodeAddressWidth)
            · by_cases hivc : i = tapes.valueCounter
              · subst i
                exact parked_of_hasBinaryPrefix
                  (by simpa using hdecodeValueCounter)
              · by_cases hivw : i = tapes.valueWidth
                · subst i
                  exact parked_of_hasBinaryNat
                    (by simpa using hdecodeValueWidth)
                · by_cases hiq : i = tapes.query
                  · subst i
                    exact ⟨by rw [hdecodeQuery.1],
                      hdecodeQuery.hasBinaryContent.cells_ne_start⟩
                  · by_cases hir : i = tapes.result
                    · subst i
                      exact parked_of_hasBinaryPrefix hdecodeResult
                    · rw [hdecodeFrame i (by simpa using his)
                        (by simpa using hia) (by simpa using hiv)
                        (by simpa using hiac) (by simpa using hivc)]
                      exact hwork i
  have hdecodeQueryStart :
      (decodeDone.work tapes.query).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn tapes.query hdecodeReach
      hqueryStart
  obtain ⟨compareDone, compareTime, hcompareTime, hcompareReach,
      hcompareHalt, hcompareInput, hcompareResult, hcompareAddress,
      hcompareAddressHead, hcompareAddressStart, hcompareQuery,
      hcompareQueryHead, hcompareQueryStart, hcompareFrame, hcompareOutput⟩ :=
    decodedAddressEqTM_reachesIn_frame tapes.address tapes.query tapes.result
      tapes.binaryEqDistinct entry.1.bits queryBits decodeDone.input
      decodeDone.work decodeDone.output (by simpa using hdecodeAddress)
      (by simpa using hdecodeAddressStart) hdecodeQuery hdecodeQueryStart
      hdecodeResult (by rw [hdecodeInput]; exact hinput.read_ne_start)
      (fun i _ _ _ => ⟨(hdecodeParked i).read_ne_start,
        (hdecodeParked i).1⟩)
      (by rw [hdecodeOutput]; exact houtput.read_ne_start)
      (by rw [hdecodeOutput]; exact houtput.1)
  have htransitionInput : TM.transitionInput decodeDone.input =
      decodeDone.input :=
    TM.transitionInput_eq_self (by rw [hdecodeInput]; exact hinput.read_ne_start)
  have htransitionWork :
      (fun i => TM.transitionTape (decodeDone.work i)) = decodeDone.work := by
    funext i
    exact TM.transitionTape_eq_self (hdecodeParked i).read_ne_start
  have htransitionOutput : TM.transitionTape decodeDone.output =
      decodeDone.output :=
    TM.transitionTape_eq_self
      (by rw [hdecodeOutput]; exact houtput.read_ne_start)
  have hcompareReach' : compareTM.reachesIn compareTime
      { state := compareTM.qstart
        input := TM.transitionInput decodeDone.input
        work := fun i => TM.transitionTape (decodeDone.work i)
        output := TM.transitionTape decodeDone.output } compareDone := by
    rw [htransitionInput, htransitionWork, htransitionOutput]
    simpa [compareTM] using hcompareReach
  have hfullReach := TM.seqTM_reachesIn_of_reachesIn decodeTM compareTM
    (by simpa [decodeTM] using hdecodeReach) hdecodeHalt hcompareReach'
  let finalCfg := TM.phase2Wrap decodeTM compareTM compareDone
  have hresultStartFinal : (finalCfg.work tapes.result).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn
      (tm := TM.seqTM decodeTM compareTM) tapes.result hfullReach hresultStart
  have haddressCounterStartFinal :
      (finalCfg.work tapes.addressCounter).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn
      (tm := TM.seqTM decodeTM compareTM) tapes.addressCounter hfullReach
        haddressCounter.1
  have hvalueCounterStartFinal :
      (finalCfg.work tapes.valueCounter).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn
      (tm := TM.seqTM decodeTM compareTM) tapes.valueCounter hfullReach
        hvalueCounter.1
  have hfinalParked : ∀ i, TM.Parked (finalCfg.work i) := by
    intro i
    change TM.Parked (compareDone.work i)
    by_cases his : i = tapes.source
    · subst i
      apply parked_of_hasBinarySuffix
      rw [hcompareFrame tapes.source
        (by simpa using tapes.ne (show (0 : Fin 9) ≠ 1 by decide))
        (by simpa using tapes.ne (show (0 : Fin 9) ≠ 7 by decide))
        (by simpa using tapes.ne (show (0 : Fin 9) ≠ 8 by decide))]
      simpa using hdecodeSource
    · by_cases hia : i = tapes.address
      · subst i
        exact ⟨hcompareAddressHead,
          hcompareAddress.cells_ne_start⟩
      · by_cases hiv : i = tapes.value
        · subst i
          apply parked_of_hasBinaryPrefix
          rw [hcompareFrame tapes.value
            (by simpa using tapes.ne (show (2 : Fin 9) ≠ 1 by decide))
            (by simpa using tapes.ne (show (2 : Fin 9) ≠ 7 by decide))
            (by simpa using tapes.ne (show (2 : Fin 9) ≠ 8 by decide))]
          simpa using hdecodeValue
        · by_cases hiac : i = tapes.addressCounter
          · subst i
            apply parked_of_hasBinaryPrefix
            rw [hcompareFrame tapes.addressCounter
              (by simpa using tapes.ne (show (3 : Fin 9) ≠ 1 by decide))
              (by simpa using tapes.ne (show (3 : Fin 9) ≠ 7 by decide))
              (by simpa using tapes.ne (show (3 : Fin 9) ≠ 8 by decide))]
            simpa using hdecodeAddressCounter
          · by_cases hiaw : i = tapes.addressWidth
            · subst i
              apply parked_of_hasBinaryNat
              rw [hcompareFrame tapes.addressWidth
                (by simpa using tapes.ne (show (4 : Fin 9) ≠ 1 by decide))
                (by simpa using tapes.ne (show (4 : Fin 9) ≠ 7 by decide))
                (by simpa using tapes.ne (show (4 : Fin 9) ≠ 8 by decide))]
              simpa using hdecodeAddressWidth
            · by_cases hivc : i = tapes.valueCounter
              · subst i
                apply parked_of_hasBinaryPrefix
                rw [hcompareFrame tapes.valueCounter
                  (by simpa using tapes.ne (show (5 : Fin 9) ≠ 1 by decide))
                  (by simpa using tapes.ne (show (5 : Fin 9) ≠ 7 by decide))
                  (by simpa using tapes.ne (show (5 : Fin 9) ≠ 8 by decide))]
                simpa using hdecodeValueCounter
              · by_cases hivw : i = tapes.valueWidth
                · subst i
                  apply parked_of_hasBinaryNat
                  rw [hcompareFrame tapes.valueWidth
                    (by simpa using tapes.ne (show (6 : Fin 9) ≠ 1 by decide))
                    (by simpa using tapes.ne (show (6 : Fin 9) ≠ 7 by decide))
                    (by simpa using tapes.ne (show (6 : Fin 9) ≠ 8 by decide))]
                  simpa using hdecodeValueWidth
                · by_cases hiq : i = tapes.query
                  · subst i
                    exact ⟨hcompareQueryHead,
                      hcompareQuery.cells_ne_start⟩
                  · by_cases hir : i = tapes.result
                    · subst i
                      exact parked_of_hasBinaryPrefix hcompareResult
                    · rw [hcompareFrame i hia hiq hir,
                        hdecodeFrame i (by simpa using his)
                          (by simpa using hia) (by simpa using hiv)
                          (by simpa using hiac) (by simpa using hivc)]
                      exact hwork i
  refine ⟨finalCfg, entryDecodeLinearTime entry.1 entry.2 + 1 + compareTime,
    ?_, ?_, ?_, hcompareInput.trans hdecodeInput, ?_, hcompareAddress,
    hcompareAddressHead, hcompareAddressStart, ?_, ?_, ?_,
    haddressCounterStartFinal, ?_, ?_, hvalueCounterStartFinal, ?_,
    hcompareQuery, hcompareQueryHead, hcompareQueryStart, hcompareResult,
    hresultStartFinal, hfinalParked, ?_,
    hcompareOutput.trans hdecodeOutput⟩
  · simp only [entryMatchTime]
    omega
  · simpa [entryMatchTM, decodeTM, compareTM, finalCfg] using hfullReach
  · exact (TM.phase2Wrap_halted_iff decodeTM compareTM compareDone).2
      hcompareHalt
  · change (compareDone.work tapes.source).HasBinarySuffix rest
    rw [hcompareFrame tapes.source
      (by simpa using tapes.ne (show (0 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (0 : Fin 9) ≠ 7 by decide))
      (by simpa using tapes.ne (show (0 : Fin 9) ≠ 8 by decide))]
    simpa using hdecodeSource
  · change (compareDone.work tapes.value).HasBinaryPrefix entry.2.bits
    rw [hcompareFrame tapes.value
      (by simpa using tapes.ne (show (2 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (2 : Fin 9) ≠ 7 by decide))
      (by simpa using tapes.ne (show (2 : Fin 9) ≠ 8 by decide))]
    simpa using hdecodeValue
  · change (compareDone.work tapes.value).cells 0 = Γ.start
    rw [hcompareFrame tapes.value
      (by simpa using tapes.ne (show (2 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (2 : Fin 9) ≠ 7 by decide))
      (by simpa using tapes.ne (show (2 : Fin 9) ≠ 8 by decide))]
    simpa using hdecodeValueStart
  · change (compareDone.work tapes.addressCounter).HasBinaryPrefix
      (List.replicate (bitlen entry.1) true)
    rw [hcompareFrame tapes.addressCounter
      (by simpa using tapes.ne (show (3 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (3 : Fin 9) ≠ 7 by decide))
      (by simpa using tapes.ne (show (3 : Fin 9) ≠ 8 by decide))]
    simpa using hdecodeAddressCounter
  · change (compareDone.work tapes.addressWidth).HasBinaryNat 0
    rw [hcompareFrame tapes.addressWidth
      (by simpa using tapes.ne (show (4 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (4 : Fin 9) ≠ 7 by decide))
      (by simpa using tapes.ne (show (4 : Fin 9) ≠ 8 by decide))]
    simpa using hdecodeAddressWidth
  · change (compareDone.work tapes.valueCounter).HasBinaryPrefix
      (List.replicate (bitlen entry.2) true)
    rw [hcompareFrame tapes.valueCounter
      (by simpa using tapes.ne (show (5 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (5 : Fin 9) ≠ 7 by decide))
      (by simpa using tapes.ne (show (5 : Fin 9) ≠ 8 by decide))]
    simpa using hdecodeValueCounter
  · change (compareDone.work tapes.valueWidth).HasBinaryNat 0
    rw [hcompareFrame tapes.valueWidth
      (by simpa using tapes.ne (show (6 : Fin 9) ≠ 1 by decide))
      (by simpa using tapes.ne (show (6 : Fin 9) ≠ 7 by decide))
      (by simpa using tapes.ne (show (6 : Fin 9) ≠ 8 by decide))]
    simpa using hdecodeValueWidth
  · intro i his hia hiv hiac hiaw hivc hivw hiq hir
    change compareDone.work i = work₀ i
    rw [hcompareFrame i hia hiq hir,
      hdecodeFrame i (by simpa using his) (by simpa using hia)
        (by simpa using hiv) (by simpa using hiac) (by simpa using hivc)]

theorem entryMatchReadTM_reachesIn_frame_internal {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ tapes.source).HasBinarySuffix (Entry.encode entry ++ rest))
    (haddress : (work₀ tapes.address).HasBinaryPrefix [])
    (hvalue : (work₀ tapes.value).HasBinaryPrefix [])
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (haddressCounter : (work₀ tapes.addressCounter).HasBinaryNat 0)
    (haddressWidth : (work₀ tapes.addressWidth).HasBinaryNat 0)
    (hvalueCounter : (work₀ tapes.valueCounter).HasBinaryNat 0)
    (hvalueWidth : (work₀ tapes.valueWidth).HasBinaryNat 0)
    (hquery : (work₀ tapes.query).HasBinaryString queryBits)
    (hqueryStart : (work₀ tapes.query).cells 0 = Γ.start)
    (hresult : (work₀ tapes.result).HasBinaryPrefix [])
    (hresultStart : (work₀ tapes.result).cells 0 = Γ.start)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    ∃ c' t,
      t ≤ entryMatchReadTime entry queryBits ∧
      (entryMatchReadTM tapes).reachesIn t
        { state := (entryMatchReadTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryMatchReadTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      ReadableEntryMatch tapes entry rest queryBits work₀ c'.work ∧
      c'.output = out₀ := by
  let matchTM := entryMatchTM tapes
  let rewindTM := TM.rewindWorkTM tapes.result
  obtain ⟨matchDone, matchTime, hmatchTime, hmatchReach, hmatchHalt,
      hmatchInput, hmatchSource, hmatchAddress, hmatchAddressHead,
      hmatchAddressStart, hmatchValue, hmatchValueStart, hmatchAddressCounter,
      hmatchAddressCounterStart, hmatchAddressWidth, hmatchValueCounter,
      hmatchValueCounterStart, hmatchValueWidth, hmatchQuery, hmatchQueryHead,
      hmatchQueryStart, hmatchResult, hmatchResultStart, hmatchParked,
      hmatchFrame, hmatchOutput⟩ :=
    entryMatchTM_reachesIn_frame_internal tapes entry rest queryBits inp₀
      work₀ out₀ hsource haddress hvalue haddressStart hvalueStart
      haddressCounter haddressWidth hvalueCounter hvalueWidth hquery
      hqueryStart hresult hresultStart hinput hwork houtput
  let resultBits : List Bool := [decide (entry.1.bits = queryBits)]
  obtain ⟨rewindDone, rewindTime, hrewindTime, hrewindReach, hrewindHalt,
      hrewindInput, hrewindResult, hrewindFrame, hrewindOutput⟩ :=
    wordTargetRewind_reachesIn_frame tapes.result resultBits matchDone.input
      matchDone.work matchDone.output (by simpa [resultBits] using hmatchResult)
      hmatchResultStart
      (by rw [hmatchInput]; exact hinput.read_ne_start)
      (fun i _ => ⟨(hmatchParked i).read_ne_start, (hmatchParked i).1⟩)
      (by rw [hmatchOutput]; exact houtput.read_ne_start)
      (by rw [hmatchOutput]; exact houtput.1)
  have htransitionInput : TM.transitionInput matchDone.input =
      matchDone.input :=
    TM.transitionInput_eq_self
      (by rw [hmatchInput]; exact hinput.read_ne_start)
  have htransitionWork :
      (fun i => TM.transitionTape (matchDone.work i)) = matchDone.work := by
    funext i
    exact TM.transitionTape_eq_self (hmatchParked i).read_ne_start
  have htransitionOutput : TM.transitionTape matchDone.output =
      matchDone.output :=
    TM.transitionTape_eq_self
      (by rw [hmatchOutput]; exact houtput.read_ne_start)
  have hrewindReach' : rewindTM.reachesIn rewindTime
      { state := rewindTM.qstart
        input := TM.transitionInput matchDone.input
        work := fun i => TM.transitionTape (matchDone.work i)
        output := TM.transitionTape matchDone.output } rewindDone := by
    rw [htransitionInput, htransitionWork, htransitionOutput]
    simpa [rewindTM] using hrewindReach
  have hfullReach := TM.seqTM_reachesIn_of_reachesIn matchTM rewindTM
    (by simpa [matchTM] using hmatchReach) hmatchHalt hrewindReach'
  let finalCfg := TM.phase2Wrap matchTM rewindTM rewindDone
  have hresultStartFinal : (finalCfg.work tapes.result).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn
      (tm := TM.seqTM matchTM rewindTM) tapes.result hfullReach hresultStart
  have hfinalParked : ∀ i, TM.Parked (finalCfg.work i) := by
    intro i
    change TM.Parked (rewindDone.work i)
    by_cases hir : i = tapes.result
    · subst i
      exact ⟨by rw [hrewindResult.1],
        hrewindResult.hasBinaryContent.cells_ne_start⟩
    · rw [hrewindFrame i hir]
      exact hmatchParked i
  have hrewindTimeFour : rewindTime ≤ 4 := by
    simpa [resultBits] using hrewindTime
  have hfullTime : matchTime + 1 + rewindTime ≤
      entryMatchReadTime entry queryBits := by
    simp only [entryMatchReadTime]
    omega
  have hpreserve (i : Fin n) (hir : i ≠ tapes.result) :
      finalCfg.work i = matchDone.work i := by
    change rewindDone.work i = matchDone.work i
    exact hrewindFrame i hir
  have hreadable :
      ReadableEntryMatch tapes entry rest queryBits work₀ finalCfg.work := by
    constructor
    · rw [hpreserve tapes.source
        (by simpa using tapes.ne (show (0 : Fin 9) ≠ 8 by decide))]
      exact hmatchSource
    · rw [hpreserve tapes.address
        (by simpa using tapes.ne (show (1 : Fin 9) ≠ 8 by decide))]
      exact hmatchAddress
    · rw [hpreserve tapes.address
        (by simpa using tapes.ne (show (1 : Fin 9) ≠ 8 by decide))]
      exact hmatchAddressStart
    · rw [hpreserve tapes.value
        (by simpa using tapes.ne (show (2 : Fin 9) ≠ 8 by decide))]
      exact hmatchValue
    · rw [hpreserve tapes.value
        (by simpa using tapes.ne (show (2 : Fin 9) ≠ 8 by decide))]
      exact hmatchValueStart
    · rw [hpreserve tapes.addressCounter
        (by simpa using tapes.ne (show (3 : Fin 9) ≠ 8 by decide))]
      exact hmatchAddressCounter
    · rw [hpreserve tapes.addressCounter
        (by simpa using tapes.ne (show (3 : Fin 9) ≠ 8 by decide))]
      exact hmatchAddressCounterStart
    · rw [hpreserve tapes.addressWidth
        (by simpa using tapes.ne (show (4 : Fin 9) ≠ 8 by decide))]
      exact hmatchAddressWidth
    · rw [hpreserve tapes.valueCounter
        (by simpa using tapes.ne (show (5 : Fin 9) ≠ 8 by decide))]
      exact hmatchValueCounter
    · rw [hpreserve tapes.valueCounter
        (by simpa using tapes.ne (show (5 : Fin 9) ≠ 8 by decide))]
      exact hmatchValueCounterStart
    · rw [hpreserve tapes.valueWidth
        (by simpa using tapes.ne (show (6 : Fin 9) ≠ 8 by decide))]
      exact hmatchValueWidth
    · rw [hpreserve tapes.query
        (by simpa using tapes.ne (show (7 : Fin 9) ≠ 8 by decide))]
      exact hmatchQuery
    · rw [hpreserve tapes.query
        (by simpa using tapes.ne (show (7 : Fin 9) ≠ 8 by decide))]
      exact hmatchQueryStart
    · simpa [resultBits] using hrewindResult
    · exact hresultStartFinal
    · exact hfinalParked
    · intro i
      have hhead := (TM.seqTM matchTM rewindTM).work_head_reachesIn_bound
        hfullReach i
      have hhead' := le_trans hhead
        (Nat.add_le_add_left hfullTime (work₀ i).head)
      simpa [finalCfg] using hhead'
    · intro i his hia hiv hiac hiaw hivc hivw hiq hir
      rw [hpreserve i hir]
      exact hmatchFrame i his hia hiv hiac hiaw hivc hivw hiq hir
  refine ⟨finalCfg, matchTime + 1 + rewindTime, ?_, ?_, ?_,
    hrewindInput.trans hmatchInput, hreadable,
    hrewindOutput.trans hmatchOutput⟩
  · exact hfullTime
  · simpa [entryMatchReadTM, matchTM, rewindTM, finalCfg] using hfullReach
  · exact (TM.phase2Wrap_halted_iff matchTM rewindTM rewindDone).2
      hrewindHalt

/-- Closed form for the optimized unary-marker decode-and-match runtime. -/
theorem entryMatchReadTime_eq_internal (entry : Entry)
    (queryBits : List Bool) :
    entryMatchReadTime entry queryBits =
      4 * entry.1.bits.length + 3 * entry.2.bits.length +
        max entry.1.bits.length queryBits.length + 18 := by
  unfold entryMatchReadTime entryMatchTime entryDecodeLinearTime
    wordDecodeLinearTime decodedAddressEqTime TM.binaryEqTime
  simp only [bitlen, Nat.size_eq_bits_len]
  omega

/-- One optimized readable match is linear in the two encoded word widths and
the preserved query width. -/
theorem entryMatchReadTime_le_linear_internal (entry : Entry)
    (queryBits : List Bool) :
    entryMatchReadTime entry queryBits ≤
      5 * entry.1.bits.length + 3 * entry.2.bits.length +
        queryBits.length + 18 := by
  rw [entryMatchReadTime_eq_internal]
  have hmax : max entry.1.bits.length queryBits.length ≤
      entry.1.bits.length + queryBits.length :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  omega

end Machine

end RegisterStore

end RAM

end Complexity
