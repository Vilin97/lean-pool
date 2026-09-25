/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.AddressEq.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryEq

/-!
# Decoded sparse-address equality — proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

theorem decodedAddressEqTM_reachesIn_frame_internal {n : ℕ}
    (addressIdx queryIdx resultIdx : Fin n)
    (hdistinct : TM.BinaryEqDistinct addressIdx queryIdx resultIdx)
    (addressBits queryBits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (haddress : (work₀ addressIdx).HasBinaryPrefix addressBits)
    (haddressStart : (work₀ addressIdx).cells 0 = Γ.start)
    (hquery : (work₀ queryIdx).HasBinaryString queryBits)
    (hqueryStart : (work₀ queryIdx).cells 0 = Γ.start)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ addressIdx → i ≠ queryIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start ∧ 1 ≤ (work₀ i).head)
    (houtput : out₀.read ≠ Γ.start) (houtputHead : 1 ≤ out₀.head) :
    ∃ c' t,
      t ≤ decodedAddressEqTime addressBits queryBits ∧
      (decodedAddressEqTM addressIdx queryIdx resultIdx).reachesIn t
        { state := (decodedAddressEqTM addressIdx queryIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (decodedAddressEqTM addressIdx queryIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix
        [decide (addressBits = queryBits)] ∧
      (c'.work addressIdx).HasBinaryContent addressBits ∧
      1 ≤ (c'.work addressIdx).head ∧
      (c'.work addressIdx).cells 0 = Γ.start ∧
      (c'.work queryIdx).HasBinaryContent queryBits ∧
      1 ≤ (c'.work queryIdx).head ∧
      (c'.work queryIdx).cells 0 = Γ.start ∧
      (∀ i, i ≠ addressIdx → i ≠ queryIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let rewindTM := TM.rewindWorkTM addressIdx
  let compareTM := TM.binaryEqTM addressIdx queryIdx resultIdx
  have hrewindOther : ∀ i, i ≠ addressIdx →
      (work₀ i).read ≠ Γ.start ∧ 1 ≤ (work₀ i).head := by
    intro i hia
    by_cases hiq : i = queryIdx
    · subst i
      exact ⟨hquery.hasBinarySuffix.read_ne_start, by rw [hquery.1]⟩
    · by_cases hir : i = resultIdx
      · subst i
        exact ⟨by rw [hresult.read_blank]; decide, by rw [hresult.1]; simp⟩
      · exact hother i hia hiq hir
  obtain ⟨rewindDone, rewindTime, hrewindTime, hrewindReach, hrewindHalt,
      hrewindInput, hrewindAddress, hrewindFrame, hrewindOutput⟩ :=
    wordTargetRewind_reachesIn_frame addressIdx addressBits inp₀ work₀ out₀
      haddress haddressStart hinput hrewindOther houtput houtputHead
  have hrewindQuery : (rewindDone.work queryIdx).HasBinaryString queryBits := by
    rw [hrewindFrame queryIdx (Ne.symm hdistinct.lhs_rhs)]
    exact hquery
  have hrewindResult : (rewindDone.work resultIdx).HasBinaryPrefix [] := by
    rw [hrewindFrame resultIdx (Ne.symm hdistinct.lhs_result)]
    exact hresult
  have hrewindReads : ∀ i, (rewindDone.work i).read ≠ Γ.start := by
    intro i
    by_cases hia : i = addressIdx
    · subst i
      exact hrewindAddress.hasBinarySuffix.read_ne_start
    · rw [hrewindFrame i hia]
      exact (hrewindOther i hia).1
  obtain ⟨compareDone, compareTime, hcompareTime, hcompareReach,
      hcompareHalt, hcompareInput, hcompareResult, hcompareAddress,
      hcompareAddressHead, hcompareQuery, hcompareQueryHead, hcompareFrame,
      hcompareOutput⟩ :=
    TM.binaryEqTM_reachesIn_frame addressIdx queryIdx resultIdx hdistinct
      addressBits queryBits rewindDone.input rewindDone.work rewindDone.output
      hrewindAddress hrewindQuery hrewindResult
      (by rw [hrewindInput]; exact hinput)
      (fun i _ _ _ => hrewindReads i)
      (by rw [hrewindOutput]; exact houtput)
  have htransitionInput : TM.transitionInput rewindDone.input =
      rewindDone.input :=
    TM.transitionInput_eq_self (by rw [hrewindInput]; exact hinput)
  have htransitionWork :
      (fun i => TM.transitionTape (rewindDone.work i)) = rewindDone.work := by
    funext i
    exact TM.transitionTape_eq_self (hrewindReads i)
  have htransitionOutput : TM.transitionTape rewindDone.output =
      rewindDone.output :=
    TM.transitionTape_eq_self (by rw [hrewindOutput]; exact houtput)
  have hcompareReach' : compareTM.reachesIn compareTime
      { state := compareTM.qstart
        input := TM.transitionInput rewindDone.input
        work := fun i => TM.transitionTape (rewindDone.work i)
        output := TM.transitionTape rewindDone.output } compareDone := by
    rw [htransitionInput, htransitionWork, htransitionOutput]
    simpa [compareTM] using hcompareReach
  have hfullReach := TM.seqTM_reachesIn_of_reachesIn rewindTM compareTM
    (by simpa [rewindTM] using hrewindReach) hrewindHalt hcompareReach'
  let finalCfg := TM.phase2Wrap rewindTM compareTM compareDone
  have hfullReach' :
      (decodedAddressEqTM addressIdx queryIdx resultIdx).reachesIn
        (rewindTime + 1 + compareTime)
        { state := (decodedAddressEqTM addressIdx queryIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } finalCfg := by
    simpa [decodedAddressEqTM, rewindTM, compareTM, finalCfg] using! hfullReach
  have haddressStartFinal : (finalCfg.work addressIdx).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn
      (tm := decodedAddressEqTM addressIdx queryIdx resultIdx) addressIdx
      hfullReach' haddressStart
  have hqueryStartFinal : (finalCfg.work queryIdx).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn
      (tm := decodedAddressEqTM addressIdx queryIdx resultIdx) queryIdx
      hfullReach' hqueryStart
  refine ⟨finalCfg, rewindTime + 1 + compareTime, ?_, hfullReach', ?_,
    hcompareInput.trans hrewindInput, hcompareResult, hcompareAddress,
    hcompareAddressHead, haddressStartFinal, hcompareQuery,
    hcompareQueryHead, hqueryStartFinal, ?_,
    hcompareOutput.trans hrewindOutput⟩
  · simp only [decodedAddressEqTime]
    omega
  · exact (TM.phase2Wrap_halted_iff rewindTM compareTM compareDone).2
      hcompareHalt
  · intro i hia hiq hir
    change compareDone.work i = work₀ i
    rw [hcompareFrame i hia hiq hir, hrewindFrame i hia]

end Machine

end RegisterStore

end RAM

end Complexity
