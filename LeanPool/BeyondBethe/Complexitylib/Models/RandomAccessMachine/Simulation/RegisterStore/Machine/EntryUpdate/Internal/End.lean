/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Loop
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Out
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate.Internal.Time
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch

/-!
# Bounded encoded sparse-store update -- terminal loop case

This file closes the update loop once the old-entry counter is exhausted.  A
previous hit and an absent zero write halt immediately; an absent nonzero write
runs the checked append and result-count successor subroutines.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- Once no old entries remain, the controller realizes the pure sparse-store
write and establishes the complete final tape contract. -/
theorem entryUpdateTerminal_internal
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (processed emitted : Store) (found : Bool) (resultCount : ℕ)
    (initialWork work : Fin n → Tape) (outPrefix : List Bool)
    (inp out : Tape)
    (hinv : EntryUpdateLoopInv tapes store address newValue processed []
      emitted found resultCount initialWork work)
    (hinput : TM.Parked inp)
    (houtput : out.HasBinaryPrefix
      (outPrefix ++ emitted.flatMap Entry.encode)) :
    ∃ final time,
      time ≤ entryUpdateLoopTime tapes address newValue store.length [] ∧
      (entryUpdateTM tapes).reachesIn time
        (entryUpdateTestCfg tapes inp work out) final ∧
      (entryUpdateTM tapes).halted final ∧
      final.input = inp ∧
      EntryUpdateOutcome tapes store address newValue initialWork final.work ∧
      final.output.HasBinaryPrefix
        (outPrefix ++ (RegisterStore.write store address newValue).flatMap
          Entry.encode) := by
  have hremainingRead : (work tapes.remaining).read = Γ.blank :=
    hinv.remainingCount.read_eq_blank_iff.mpr rfl
  have houtputParked : TM.Parked out :=
    parked_of_binaryPrefix_internal houtput
  cases found with
  | false =>
      have hfoundZero : (work tapes.found).HasBinaryNat 0 := by
        simpa using! hinv.foundCount
      have hfoundRead : (work tapes.found).read ≠ Γ.one := by
        rw [hfoundZero.read_eq_blank_iff.mpr rfl]
        decide
      have hnotmemProcessed : address ∉ processed.map Prod.fst := by
        intro hmem
        exact Bool.false_ne_true (hinv.progress.found_iff.mpr hmem)
      have hnotmemStore : address ∉ store.map Prod.fst := by
        rw [hinv.progress.store_eq]
        simpa using! hnotmemProcessed
      by_cases hvalue : newValue = 0
      · subst newValue
        have hreplacementRead : (work tapes.replacement).read = Γ.blank :=
          hinv.replacement.read_eq_blank_iff.mpr rfl
        have hstep := entryUpdateTM_step_test_zero_internal tapes inp work out
          hremainingRead hfoundRead hreplacementRead hinput hinv.ready.parked
          houtputParked
        obtain ⟨houtputEq, hcountEq⟩ :=
          hinv.progress.terminal_zero_internal
        refine ⟨entryUpdateDoneCfg tapes inp work out, 1, ?_,
          .step hstep .zero, rfl, rfl, ?_, ?_⟩
        · simp [entryUpdateLoopTime]
        · exact
            { ready := hinv.ready
              replacement := hinv.replacement_eq
              remaining := hinv.remainingCount
              found := by simpa [hnotmemStore] using! hfoundZero
              resultCount := by
                simpa [hcountEq] using! hinv.resultCountTape
              frame := hinv.frame }
        · simpa [houtputEq] using! houtput
      · have hreplacementRead :
            (work tapes.replacement).read ≠ Γ.blank := by
          intro hblank
          exact hvalue (hinv.replacement.read_eq_blank_iff.mp hblank)
        have htest := entryUpdateTM_step_test_append_internal tapes inp work out
          hremainingRead hfoundRead hreplacementRead hinput hinv.ready.parked
          houtputParked
        have happendContract := entryAppendRestoreTM_hoareTime_frame
          tapes.replace address newValue
          (outPrefix ++ emitted.flatMap Entry.encode) work work inp out
          hinv.ready hinv.replacement hinput houtput
        obtain ⟨appendDone, appendTime, happendTime, happendReach,
            happendHalt, happendInput, happendWork, happendOutput⟩ :=
          happendContract inp work out ⟨rfl, rfl, rfl⟩
        have happendReach' :=
          entryUpdateTM_append_reachesIn_internal tapes happendReach
        have happendInputParked : TM.Parked appendDone.input := by
          rw [happendInput]
          exact hinput
        have happendWorkParked : ∀ i, TM.Parked (appendDone.work i) := by
          intro i
          rw [happendWork]
          exact hinv.ready.parked i
        have happendOutputParked : TM.Parked appendDone.output :=
          parked_of_binaryPrefix_internal happendOutput
        have happendSeam := entryUpdateTM_step_append_halt_internal tapes
          appendDone happendHalt happendInputParked happendWorkParked
          happendOutputParked
        have hresultCount :
            (appendDone.work tapes.resultCount).HasBinaryNat resultCount := by
          rw [happendWork]
          exact hinv.resultCountTape
        obtain ⟨succDone, hsuccReach, hsuccHalt, hsuccInput, hsuccOther,
            hsuccCount, hsuccOutput⟩ :=
          TM.binarySuccTM_reachesIn_frame tapes.resultCount resultCount
            appendDone.input appendDone.work appendDone.output hresultCount
            happendInputParked.read_ne_start
            (fun i _ => (happendWorkParked i).read_ne_start)
            happendOutputParked.read_ne_start
        have hsuccReach' :=
          entryUpdateTM_appendCount_reachesIn_internal tapes hsuccReach
        have hsuccInputParked : TM.Parked succDone.input := by
          rw [hsuccInput]
          exact happendInputParked
        have hsuccWorkParked : ∀ i, TM.Parked (succDone.work i) := by
          intro i
          by_cases hi : i = tapes.resultCount
          · subst i
            exact entryUpdateParked_of_hasBinaryNat_internal hsuccCount
          · rw [hsuccOther i hi]
            exact happendWorkParked i
        have hsuccOutputParked : TM.Parked succDone.output := by
          rw [hsuccOutput]
          exact happendOutputParked
        have hfinish := entryUpdateTM_step_appendCount_halt_internal tapes
          succDone hsuccHalt hsuccInputParked hsuccWorkParked
          hsuccOutputParked
        have hprefixReach : (entryUpdateTM tapes).reachesIn
            (appendTime + 1) (entryUpdateTestCfg tapes inp work out)
            (entryUpdateAppendWrap tapes appendDone) :=
          .step htest happendReach'
        have hsuccPrefix : (entryUpdateTM tapes).reachesIn
            (TM.binarySuccTime resultCount + 1)
            (entryUpdateAppendWrap tapes appendDone)
            (entryUpdateAppendCountWrap tapes succDone) :=
          .step happendSeam hsuccReach'
        have htotalReach : (entryUpdateTM tapes).reachesIn
            ((appendTime + 1) + (TM.binarySuccTime resultCount + 1) + 1)
            (entryUpdateTestCfg tapes inp work out)
            (entryUpdateDoneCfg tapes succDone.input succDone.work
              succDone.output) :=
          TM.reachesIn_trans _
            (TM.reachesIn_trans _ hprefixReach hsuccPrefix)
            (.step hfinish .zero)
        have hotherWork : ∀ i, i ≠ tapes.resultCount →
            succDone.work i = work i := by
          intro i hi
          exact (hsuccOther i hi).trans (congrFun happendWork i)
        have hreadyFinal := hinv.ready.change_resultCount_internal
          hotherWork hsuccCount
        obtain ⟨houtputEq, hcountEq⟩ :=
          hinv.progress.terminal_append_internal hvalue
        have hfinalOutput : succDone.output.HasBinaryPrefix
            (outPrefix ++ (RegisterStore.write store address newValue).flatMap
              Entry.encode) := by
          rw [hsuccOutput]
          rw [← houtputEq]
          simpa [List.flatMap_append, List.append_assoc] using!
            happendOutput
        have hfinalFrame : EntryUpdateFrame tapes initialWork succDone.work :=
          EntryUpdateFrame.trans_single_internal hinv.frame (12 : Fin 13)
            (by
              intro i hi
              exact hotherWork i (by
                simpa [EntryUpdateTapes.resultCount] using! hi))
        have hsuccTimeBound :=
          binarySuccTime_le_entryUpdateCountTime_internal hinv.resultCount_le
        refine ⟨entryUpdateDoneCfg tapes succDone.input succDone.work
            succDone.output,
          (appendTime + 1) + (TM.binarySuccTime resultCount + 1) + 1,
          ?_, htotalReach, rfl, ?_, ?_, ?_⟩
        · simp only [entryUpdateLoopTime]
          omega
        · simpa [entryUpdateDoneCfg] using! hsuccInput.trans happendInput
        · exact
            { ready := hreadyFinal
              replacement := by
                exact (hotherWork tapes.replacement
                  tapes.replacement_ne_resultCount).trans
                    hinv.replacement_eq
              remaining := by
                change (succDone.work tapes.remaining).HasBinaryNat 0
                rw [hotherWork tapes.remaining
                  tapes.remaining_ne_resultCount]
                exact hinv.remainingCount
              found := by
                change (succDone.work tapes.found).HasBinaryNat
                  (if address ∈ store.map Prod.fst then 1 else 0)
                rw [hotherWork tapes.found tapes.found_ne_resultCount]
                simpa [hnotmemStore] using! hfoundZero
              resultCount := by simpa [hcountEq] using! hsuccCount
              frame := hfinalFrame }
        · simpa [entryUpdateDoneCfg] using! hfinalOutput
  | true =>
      have hfoundOne : (work tapes.found).HasBinaryNat 1 := by
        simpa using! hinv.foundCount
      have hfoundRead : (work tapes.found).read = Γ.one := by
        simpa [Nat.bits, Γ.ofBool] using!
          hfoundOne.2.hasBinarySuffix.read_cons
      have hmemProcessed : address ∈ processed.map Prod.fst :=
        hinv.progress.found_iff.mp rfl
      have hmemStore : address ∈ store.map Prod.fst := by
        rw [hinv.progress.store_eq]
        simpa using! hmemProcessed
      have hstep := entryUpdateTM_step_test_found_internal tapes inp work out
        hremainingRead hfoundRead hinput hinv.ready.parked houtputParked
      obtain ⟨houtputEq, hcountEq⟩ :=
        hinv.progress.terminal_found_internal
      refine ⟨entryUpdateDoneCfg tapes inp work out, 1, ?_,
        .step hstep .zero, rfl, rfl, ?_, ?_⟩
      · simp [entryUpdateLoopTime]
      · exact
          { ready := hinv.ready
            replacement := hinv.replacement_eq
            remaining := hinv.remainingCount
            found := by simpa [hmemStore] using! hfoundOne
            resultCount := by simpa [hcountEq] using! hinv.resultCountTape
            frame := hinv.frame }
      · simpa [houtputEq] using! houtput

end Machine

end RegisterStore

end RAM

end Complexity
