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
# Bounded encoded sparse-store update -- matching iterations

This file composes the checked match, deletion or replacement, and counter
subroutines for the two branches in which the current old entry has the
requested address.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

/-- Deletion and both counter decrements restore the complete next-iteration invariant. -/
private theorem entryUpdateDelete_finalInvariant
    (tapes : EntryUpdateTapes n) (store : Store) (address : ℕ)
    (processed emitted : Store) (entry : Entry) (rest : Store) (resultCount : ℕ)
    (initialWork work deleteWork countWork remainingWork : Fin n → Tape)
    (hinv : EntryUpdateLoopInv tapes store address 0 processed
      (entry :: rest) emitted false resultCount initialWork work)
    (haddress : address = entry.1)
    (hfoundZero : (work tapes.found).HasBinaryNat 0)
    (hdeleteReady : EntryScanReady tapes.entry (rest.flatMap Entry.encode) address.bits
      (entryUpdateMarkFoundWork tapes work) deleteWork)
    (hcountOther : ∀ i, i ≠ tapes.resultCount → countWork i = deleteWork i)
    (hcountValue : (countWork tapes.resultCount).HasBinaryNat (resultCount - 1))
    (hremainingOther : ∀ i, i ≠ tapes.remaining → remainingWork i = countWork i)
    (hremainingValue : (remainingWork tapes.remaining).HasBinaryNat rest.length) :
    EntryUpdateLoopInv tapes store address 0 (processed ++ [entry]) rest
      emitted true (resultCount - 1) initialWork remainingWork := by
  have hreadyCount := hdeleteReady.change_resultCount_internal hcountOther hcountValue
  have hreadyFinal := hreadyCount.change_remaining_internal hremainingOther hremainingValue
  have hreplacementEq :
      remainingWork tapes.replacement =
        initialWork tapes.replacement := by
    rw [hremainingOther tapes.replacement
      (Ne.symm tapes.remaining_ne_replacement)]
    rw [hcountOther tapes.replacement tapes.replacement_ne_resultCount]
    rw [hdeleteReady.frame_outside_entry_internal tapes.replacement
      tapes.replacement_ne_entry]
    rw [entryUpdateMarkFoundWork_apply_ne_internal tapes work
      tapes.replacement tapes.replacement_ne_found]
    exact hinv.replacement_eq
  have hreplacementFinal :
      (remainingWork tapes.replacement).HasBinaryNat 0 := by
    rw [hreplacementEq]
    rw [← hinv.replacement_eq]
    exact hinv.replacement
  have hfoundFinal :
      (remainingWork tapes.found).HasBinaryNat 1 := by
    rw [hremainingOther tapes.found
      (Ne.symm tapes.remaining_ne_found)]
    rw [hcountOther tapes.found tapes.found_ne_resultCount]
    rw [hdeleteReady.frame_outside_entry_internal tapes.found
      tapes.found_ne_entry]
    exact entryUpdateMarkFoundWork_found_one_internal tapes work hfoundZero
  have hresultFinal :
      (remainingWork tapes.resultCount).HasBinaryNat
        (resultCount - 1) := by
    rw [hremainingOther tapes.resultCount
      (Ne.symm tapes.remaining_ne_resultCount)]
    exact hcountValue
  have hframeMarked := hinv.frame.markFound_internal
  have hframeDelete :=
    EntryUpdateFrame.trans_ready_internal hframeMarked hdeleteReady
  have hframeCount := EntryUpdateFrame.trans_single_internal hframeDelete
    (12 : Fin 13) (by
      intro i hi
      exact hcountOther i (by
        simpa [EntryUpdateTapes.resultCount] using hi))
  have hframeFinal := EntryUpdateFrame.trans_single_internal hframeCount
    (9 : Fin 13) (by
      intro i hi
      exact hremainingOther i (by
        simpa [EntryUpdateTapes.remaining] using hi))
  have hprogress := hinv.progress.delete_internal haddress
  have hinvFinal : EntryUpdateLoopInv tapes store address 0
      (processed ++ [entry]) rest emitted true (resultCount - 1)
      initialWork remainingWork :=
    { progress := hprogress
      ready := hreadyFinal
      replacement := hreplacementFinal
      replacement_eq := hreplacementEq
      remainingCount := hremainingValue
      foundCount := by simpa using hfoundFinal
      resultCountTape := hresultFinal
      resultCount_le := (Nat.sub_le resultCount 1).trans hinv.resultCount_le
      frame := hframeFinal }
  exact hinvFinal

/-- A bounded positive result counter and ready cleanup fit the controller's deletion budget. -/
private theorem entryUpdateDelete_branchBudget
    (tapes : EntryUpdateTapes n) (entry : Entry) (rest : Store)
    (address resultCount total deleteTime : ℕ) (readyWork : Fin n → Tape)
    (hreadyMarked : EntryScanReady tapes.entry
      (Entry.encode entry ++ rest.flatMap Entry.encode) address.bits readyWork readyWork)
    (hdeleteTime : deleteTime ≤ entryMissCleanupTime tapes.entry entry address.bits readyWork)
    (hresultPositive : 0 < resultCount) (hresultCountLe : resultCount ≤ total) :
    deleteTime + 1 + TM.binaryPredTime (resultCount - 1) + 1 ≤
      entryUpdateBranchTime tapes entry address 0 total := by
  have hcleanupBound : deleteTime ≤
      entryUpdateReadyCleanupTime tapes entry address := by
    rw [← entryMissCleanupTime_eq_entryUpdateReadyCleanupTime_internal
      tapes entry address hreadyMarked]
    exact hdeleteTime
  have hcountBound : TM.binaryPredTime (resultCount - 1) ≤
      entryUpdateCountTime total := by
    apply binaryPredTime_le_entryUpdateCountTime_internal
    calc
      resultCount - 1 + 1 = resultCount := by omega
      _ ≤ total := hresultCountLe
  have hdeleteBranchBound :
      deleteTime + 1 + TM.binaryPredTime (resultCount - 1) + 1 ≤
        entryUpdateBranchTime tapes entry address 0 total := by
    have hthird : entryUpdateReadyCleanupTime tapes entry address + 1 +
        entryUpdateCountTime total + 1 ≤
        entryUpdateBranchTime tapes entry address 0 total := by
      unfold entryUpdateBranchTime
      exact (le_max_right _ _).trans (le_max_right _ _)
    omega
  exact hdeleteBranchBound

/-- A matching zero write deletes the current entry, decrements both runtime
counters, and returns to the loop test with no output contribution. -/
theorem entryUpdateDeleteIteration_internal
    (tapes : EntryUpdateTapes n) (store : Store) (address : ℕ)
    (processed emitted : Store) (entry : Entry) (rest : Store)
    (resultCount : ℕ) (initialWork work : Fin n → Tape)
    (outPrefix : List Bool) (inp out : Tape)
    (hinv : EntryUpdateLoopInv tapes store address 0 processed
      (entry :: rest) emitted false resultCount initialWork work)
    (haddress : address = entry.1)
    (hinput : TM.Parked inp)
    (houtput : out.HasBinaryPrefix
      (outPrefix ++ emitted.flatMap Entry.encode)) :
    ∃ nextWork nextOut time,
      time ≤ entryUpdateIterationTime tapes entry rest address 0
        store.length ∧
      (entryUpdateTM tapes).reachesIn time
        (entryUpdateTestCfg tapes inp work out)
        (entryUpdateTestCfg tapes inp nextWork nextOut) ∧
      EntryUpdateLoopInv tapes store address 0 (processed ++ [entry]) rest
        emitted true (resultCount - 1) initialWork nextWork ∧
      nextOut.HasBinaryPrefix
        (outPrefix ++ emitted.flatMap Entry.encode) := by
  have hready : EntryScanReady tapes.entry
      (Entry.encode entry ++ rest.flatMap Entry.encode) address.bits work work := by
    simpa using hinv.ready
  have hremainingPositive :
      (work tapes.remaining).HasBinaryNat (rest.length + 1) := by
    simpa using hinv.remainingCount
  have hremainingRead : (work tapes.remaining).read ≠ Γ.blank := by
    intro hblank
    have hzero := hremainingPositive.read_eq_blank_iff.mp hblank
    omega
  have houtputParked : TM.Parked out :=
    parked_of_binaryPrefix_internal houtput
  have htest := entryUpdateTM_step_test_continue_internal tapes inp work out
    hremainingRead hinput hready.parked houtputParked
  have hmatchContract := entryMatchReadTM_reachesIn_frame tapes.entry entry
    (rest.flatMap Entry.encode) address.bits inp work out hready.source
    hready.address hready.value hready.addressStart hready.valueStart
    hready.addressCounter hready.addressWidth hready.valueCounter
    hready.valueWidth hready.query hready.queryStart hready.result
    hready.resultStart hinput hready.parked houtputParked
  obtain ⟨matchDone, matchTime, hmatchTime, hmatchReach, hmatchHalt,
      hmatchInput, hmatchInv, hmatchOutput⟩ := hmatchContract
  have hmatchReach' :=
    entryUpdateTM_match_reachesIn_internal tapes hmatchReach
  have hmatchInputParked : TM.Parked matchDone.input := by
    rw [hmatchInput]
    exact hinput
  have hmatchOutputParked : TM.Parked matchDone.output := by
    rw [hmatchOutput]
    exact houtputParked
  have hmatchFound : matchDone.work tapes.found = work tapes.found :=
    hmatchInv.frame_outside_entry_internal tapes.found
      tapes.found_ne_entry
  have hfoundZero : (work tapes.found).HasBinaryNat 0 := by
    simpa using hinv.foundCount
  have hmatchFoundZero :
      (matchDone.work tapes.found).HasBinaryNat 0 := by
    rw [hmatchFound]
    exact hfoundZero
  have hresultOne : (matchDone.work tapes.entry.result).read = Γ.one :=
    hmatchInv.result_read_eq_one_iff.mpr (congrArg Nat.bits haddress.symm)
  have hmatchReplacement :
      matchDone.work tapes.replacement = work tapes.replacement :=
    hmatchInv.frame_outside_entry_internal tapes.replacement
      tapes.replacement_ne_entry
  have hreplacementBlank :
      (matchDone.work tapes.replacement).read = Γ.blank := by
    rw [hmatchReplacement]
    exact hinv.replacement.read_eq_blank_iff.mpr rfl
  have hdispatch := entryUpdateTM_step_match_delete_internal tapes matchDone
    hmatchHalt hresultOne hreplacementBlank hmatchInputParked hmatchInv.parked
    hmatchOutputParked
  have hmatchMarked := hmatchInv.markFound_internal hmatchFoundZero
  have hreadyMarked := hready.markFound_internal hfoundZero
  have hcleanupContract := entryMissCleanupTM_hoareTime_frame tapes.entry entry
    (rest.flatMap Entry.encode) address.bits
    (entryUpdateMarkFoundWork tapes work)
    (entryUpdateMarkFoundWork tapes matchDone.work)
    matchDone.input matchDone.output hmatchMarked hmatchInputParked
    hmatchOutputParked
  obtain ⟨deleteDone, deleteTime, hdeleteTime, hdeleteReach, hdeleteHalt,
      hdeleteInput, hdeleteReady, hdeleteOutput⟩ :=
    hcleanupContract matchDone.input
      (entryUpdateMarkFoundWork tapes matchDone.work) matchDone.output
      ⟨rfl, rfl, rfl⟩
  have hdeleteReach' :=
    entryUpdateTM_delete_reachesIn_internal tapes hdeleteReach
  have hdeleteInputParked : TM.Parked deleteDone.input := by
    rw [hdeleteInput]
    exact hmatchInputParked
  have hdeleteOutputParked : TM.Parked deleteDone.output := by
    rw [hdeleteOutput]
    exact hmatchOutputParked
  have hdeleteSeam := entryUpdateTM_step_delete_halt_internal tapes
    deleteDone hdeleteHalt hdeleteInputParked hdeleteReady.parked
    hdeleteOutputParked
  have hdeleteResultCount :
      (deleteDone.work tapes.resultCount).HasBinaryNat resultCount := by
    rw [hdeleteReady.frame_outside_entry_internal tapes.resultCount
      tapes.resultCount_ne_entry]
    rw [entryUpdateMarkFoundWork_apply_ne_internal tapes work
      tapes.resultCount (Ne.symm tapes.found_ne_resultCount)]
    exact hinv.resultCountTape
  have hresultPositive : 0 < resultCount := by
    rw [hinv.progress.resultCount_eq]
    simp
  have hdeleteResultCountPositive :
      (deleteDone.work tapes.resultCount).HasBinaryNat
        ((resultCount - 1) + 1) := by
    convert hdeleteResultCount using 1
    omega
  obtain ⟨countDone, hcountReach, hcountHalt, hcountInput,
      hcountOther, hcountValue, hcountOutput⟩ :=
    TM.binaryPredTM_reachesIn_frame tapes.resultCount (resultCount - 1)
      deleteDone.input deleteDone.work deleteDone.output
      hdeleteResultCountPositive hdeleteInputParked.read_ne_start
      (fun i _ => (hdeleteReady.parked i).read_ne_start)
      hdeleteOutputParked.read_ne_start
  have hcountReach' :=
    entryUpdateTM_deleteCount_reachesIn_internal tapes hcountReach
  have hcountInputParked : TM.Parked countDone.input := by
    rw [hcountInput]
    exact hdeleteInputParked
  have hcountWorkParked : ∀ i, TM.Parked (countDone.work i) := by
    intro i
    by_cases hi : i = tapes.resultCount
    · subst i
      exact entryUpdateParked_of_hasBinaryNat_internal hcountValue
    · rw [hcountOther i hi]
      exact hdeleteReady.parked i
  have hcountOutputParked : TM.Parked countDone.output := by
    rw [hcountOutput]
    exact hdeleteOutputParked
  have hcountSeam := entryUpdateTM_step_deleteCount_halt_internal tapes
    countDone hcountHalt hcountInputParked hcountWorkParked
    hcountOutputParked
  have hcountRemaining :
      (countDone.work tapes.remaining).HasBinaryNat (rest.length + 1) := by
    rw [hcountOther tapes.remaining tapes.remaining_ne_resultCount]
    rw [hdeleteReady.frame_outside_entry_internal tapes.remaining
      tapes.remaining_ne_entry]
    rw [entryUpdateMarkFoundWork_apply_ne_internal tapes work
      tapes.remaining tapes.remaining_ne_found]
    exact hremainingPositive
  obtain ⟨remainingDone, hremainingReach, hremainingHalt,
      hremainingInput, hremainingOther, hremainingValue,
      hremainingOutput⟩ :=
    TM.binaryPredTM_reachesIn_frame tapes.remaining rest.length
      countDone.input countDone.work countDone.output hcountRemaining
      hcountInputParked.read_ne_start
      (fun i _ => (hcountWorkParked i).read_ne_start)
      hcountOutputParked.read_ne_start
  have hremainingReach' :=
    entryUpdateTM_remaining_reachesIn_internal tapes hremainingReach
  have hremainingInputParked : TM.Parked remainingDone.input := by
    rw [hremainingInput]
    exact hcountInputParked
  have hremainingWorkParked : ∀ i, TM.Parked (remainingDone.work i) := by
    intro i
    by_cases hi : i = tapes.remaining
    · subst i
      exact entryUpdateParked_of_hasBinaryNat_internal hremainingValue
    · rw [hremainingOther i hi]
      exact hcountWorkParked i
  have hremainingOutputParked : TM.Parked remainingDone.output := by
    rw [hremainingOutput]
    exact hcountOutputParked
  have hloop := entryUpdateTM_step_remaining_halt_internal tapes
    remainingDone hremainingHalt hremainingInputParked hremainingWorkParked
    hremainingOutputParked
  have hprefix : (entryUpdateTM tapes).reachesIn (matchTime + 1)
      (entryUpdateTestCfg tapes inp work out)
      (entryUpdateMatchWrap tapes matchDone) :=
    .step htest hmatchReach'
  have htoDelete : (entryUpdateTM tapes).reachesIn
      (matchTime + 1 + 1)
      (entryUpdateTestCfg tapes inp work out)
      (entryUpdateDeleteWrap tapes
        { state := (entryMissCleanupTM tapes.entry).qstart
          input := matchDone.input
          work := entryUpdateMarkFoundWork tapes matchDone.work
          output := matchDone.output }) :=
    TM.reachesIn_trans _ hprefix (.step hdispatch .zero)
  have hthroughDelete := TM.reachesIn_trans (entryUpdateTM tapes)
    htoDelete hdeleteReach'
  have htoCount := TM.reachesIn_trans (entryUpdateTM tapes)
    hthroughDelete (.step hdeleteSeam .zero)
  have hthroughCount := TM.reachesIn_trans (entryUpdateTM tapes)
    htoCount hcountReach'
  have htoRemaining := TM.reachesIn_trans (entryUpdateTM tapes)
    hthroughCount (.step hcountSeam .zero)
  have hthroughRemaining := TM.reachesIn_trans (entryUpdateTM tapes)
    htoRemaining hremainingReach'
  have htotalReach := TM.reachesIn_trans (entryUpdateTM tapes)
    hthroughRemaining (.step hloop .zero)
  have hinputEq : remainingDone.input = inp :=
    hremainingInput.trans (hcountInput.trans
      (hdeleteInput.trans hmatchInput))
  have houtputEq : remainingDone.output = out :=
    hremainingOutput.trans (hcountOutput.trans
      (hdeleteOutput.trans hmatchOutput))
  have hinvFinal := entryUpdateDelete_finalInvariant tapes store address processed emitted
    entry rest resultCount initialWork work deleteDone.work countDone.work remainingDone.work
    hinv haddress hfoundZero hdeleteReady hcountOther hcountValue
    hremainingOther hremainingValue
  have hdeleteBranchBound := entryUpdateDelete_branchBudget tapes entry rest address
    resultCount store.length deleteTime (entryUpdateMarkFoundWork tapes work)
    hreadyMarked hdeleteTime hresultPositive hinv.resultCount_le
  refine ⟨remainingDone.work, remainingDone.output,
    matchTime + 1 + 1 + deleteTime + 1 +
      TM.binaryPredTime (resultCount - 1) + 1 +
      TM.binaryPredTime rest.length + 1,
    ?_, ?_, hinvFinal, ?_⟩
  · unfold entryUpdateIterationTime entryUpdateBranchTime
    omega
  · simpa [hinputEq, Nat.add_assoc] using htotalReach
  · rw [houtputEq]
    exact houtput

/-- Replacement and the remaining-count decrement restore the next-iteration invariant. -/
private theorem entryUpdateReplace_finalInvariant
    (tapes : EntryUpdateTapes n) (store : Store) (address newValue : ℕ)
    (processed emitted : Store) (entry : Entry) (rest : Store) (resultCount : ℕ)
    (initialWork work matchedWork replaceWork remainingWork : Fin n → Tape)
    (hinv : EntryUpdateLoopInv tapes store address newValue processed
      (entry :: rest) emitted false resultCount initialWork work)
    (haddress : address = entry.1) (hvalue : newValue ≠ 0)
    (hfoundZero : (work tapes.found).HasBinaryNat 0)
    (hmatchReplacement : matchedWork tapes.replacement = work tapes.replacement)
    (hreplaceReady : EntryScanReady tapes.entry (rest.flatMap Entry.encode) address.bits
      (entryUpdateMarkFoundWork tapes work) replaceWork)
    (hreplaceReplacement : replaceWork tapes.replace.replacement =
      entryUpdateMarkFoundWork tapes matchedWork tapes.replace.replacement)
    (hremainingOther : ∀ i, i ≠ tapes.remaining → remainingWork i = replaceWork i)
    (hremainingValue : (remainingWork tapes.remaining).HasBinaryNat rest.length) :
    EntryUpdateLoopInv tapes store address newValue (processed ++ [entry]) rest
      (emitted ++ [(address, newValue)]) true resultCount initialWork remainingWork := by
  have hreadyFinal := hreplaceReady.change_remaining_internal hremainingOther hremainingValue
  have hreplacementWorkEq :
      remainingWork tapes.replacement = work tapes.replacement := by
    rw [hremainingOther tapes.replacement
      (Ne.symm tapes.remaining_ne_replacement)]
    have hreplaceReplacement' :
        replaceWork tapes.replacement =
          entryUpdateMarkFoundWork tapes matchedWork
            tapes.replacement := by
      simpa only [EntryUpdateTapes.replace_replacement] using
        hreplaceReplacement
    rw [hreplaceReplacement']
    rw [entryUpdateMarkFoundWork_apply_ne_internal tapes matchedWork
      tapes.replacement tapes.replacement_ne_found]
    exact hmatchReplacement
  have hreplacementEq :
      remainingWork tapes.replacement =
        initialWork tapes.replacement :=
    hreplacementWorkEq.trans hinv.replacement_eq
  have hreplacementFinal :
      (remainingWork tapes.replacement).HasBinaryNat newValue := by
    rw [hreplacementWorkEq]
    exact hinv.replacement
  have hfoundFinal :
      (remainingWork tapes.found).HasBinaryNat 1 := by
    rw [hremainingOther tapes.found
      (Ne.symm tapes.remaining_ne_found)]
    rw [hreplaceReady.frame_outside_entry_internal tapes.found
      tapes.found_ne_entry]
    exact entryUpdateMarkFoundWork_found_one_internal tapes work hfoundZero
  have hresultFinal :
      (remainingWork tapes.resultCount).HasBinaryNat resultCount := by
    rw [hremainingOther tapes.resultCount
      (Ne.symm tapes.remaining_ne_resultCount)]
    rw [hreplaceReady.frame_outside_entry_internal tapes.resultCount
      tapes.resultCount_ne_entry]
    rw [entryUpdateMarkFoundWork_apply_ne_internal tapes work
      tapes.resultCount (Ne.symm tapes.found_ne_resultCount)]
    exact hinv.resultCountTape
  have hframeMarked := hinv.frame.markFound_internal
  have hframeReplace :=
    EntryUpdateFrame.trans_ready_internal hframeMarked hreplaceReady
  have hframeFinal := EntryUpdateFrame.trans_single_internal hframeReplace
    (9 : Fin 13) (by
      intro i hi
      exact hremainingOther i (by
        simpa [EntryUpdateTapes.remaining] using hi))
  have hprogress := hinv.progress.replace_internal haddress hvalue
  have hinvFinal : EntryUpdateLoopInv tapes store address newValue
      (processed ++ [entry]) rest (emitted ++ [(address, newValue)]) true
      resultCount initialWork remainingWork :=
    { progress := hprogress
      ready := hreadyFinal
      replacement := hreplacementFinal
      replacement_eq := hreplacementEq
      remainingCount := hremainingValue
      foundCount := by simpa using hfoundFinal
      resultCountTape := hresultFinal
      resultCount_le := hinv.resultCount_le
      frame := hframeFinal }
  exact hinvFinal

/-- A matching nonzero write emits the replacement entry, records the hit,
decrements the remaining-entry counter, and returns to the loop test. -/
theorem entryUpdateReplaceIteration_internal
    (tapes : EntryUpdateTapes n) (store : Store)
    (address newValue : ℕ) (processed emitted : Store)
    (entry : Entry) (rest : Store) (resultCount : ℕ)
    (initialWork work : Fin n → Tape) (outPrefix : List Bool)
    (inp out : Tape)
    (hinv : EntryUpdateLoopInv tapes store address newValue processed
      (entry :: rest) emitted false resultCount initialWork work)
    (haddress : address = entry.1) (hvalue : newValue ≠ 0)
    (hinput : TM.Parked inp)
    (houtput : out.HasBinaryPrefix
      (outPrefix ++ emitted.flatMap Entry.encode)) :
    ∃ nextWork nextOut time,
      time ≤ entryUpdateIterationTime tapes entry rest address newValue
        store.length ∧
      (entryUpdateTM tapes).reachesIn time
        (entryUpdateTestCfg tapes inp work out)
        (entryUpdateTestCfg tapes inp nextWork nextOut) ∧
      EntryUpdateLoopInv tapes store address newValue
        (processed ++ [entry]) rest (emitted ++ [(address, newValue)]) true
        resultCount initialWork nextWork ∧
      nextOut.HasBinaryPrefix
        (outPrefix ++ (emitted ++ [(address, newValue)]).flatMap
          Entry.encode) := by
  have hready : EntryScanReady tapes.entry
      (Entry.encode entry ++ rest.flatMap Entry.encode) address.bits work work := by
    simpa using hinv.ready
  have hremainingPositive :
      (work tapes.remaining).HasBinaryNat (rest.length + 1) := by
    simpa using hinv.remainingCount
  have hremainingRead : (work tapes.remaining).read ≠ Γ.blank := by
    intro hblank
    have hzero := hremainingPositive.read_eq_blank_iff.mp hblank
    omega
  have houtputParked : TM.Parked out :=
    parked_of_binaryPrefix_internal houtput
  have htest := entryUpdateTM_step_test_continue_internal tapes inp work out
    hremainingRead hinput hready.parked houtputParked
  have hmatchContract := entryMatchReadTM_reachesIn_frame tapes.entry entry
    (rest.flatMap Entry.encode) address.bits inp work out hready.source
    hready.address hready.value hready.addressStart hready.valueStart
    hready.addressCounter hready.addressWidth hready.valueCounter
    hready.valueWidth hready.query hready.queryStart hready.result
    hready.resultStart hinput hready.parked houtputParked
  obtain ⟨matchDone, matchTime, hmatchTime, hmatchReach, hmatchHalt,
      hmatchInput, hmatchInv, hmatchOutput⟩ := hmatchContract
  have hmatchReach' :=
    entryUpdateTM_match_reachesIn_internal tapes hmatchReach
  have hmatchInputParked : TM.Parked matchDone.input := by
    rw [hmatchInput]
    exact hinput
  have hmatchOutputParked : TM.Parked matchDone.output := by
    rw [hmatchOutput]
    exact houtputParked
  have hmatchFound : matchDone.work tapes.found = work tapes.found :=
    hmatchInv.frame_outside_entry_internal tapes.found
      tapes.found_ne_entry
  have hfoundZero : (work tapes.found).HasBinaryNat 0 := by
    simpa using hinv.foundCount
  have hmatchFoundZero :
      (matchDone.work tapes.found).HasBinaryNat 0 := by
    rw [hmatchFound]
    exact hfoundZero
  have hresultOne : (matchDone.work tapes.entry.result).read = Γ.one :=
    hmatchInv.result_read_eq_one_iff.mpr (congrArg Nat.bits haddress.symm)
  have hmatchReplacement :
      matchDone.work tapes.replacement = work tapes.replacement :=
    hmatchInv.frame_outside_entry_internal tapes.replacement
      tapes.replacement_ne_entry
  have hmatchReplacementValue :
      (matchDone.work tapes.replacement).HasBinaryNat newValue := by
    rw [hmatchReplacement]
    exact hinv.replacement
  have hreplacementNonblank :
      (matchDone.work tapes.replacement).read ≠ Γ.blank := by
    intro hblank
    exact hvalue (hmatchReplacementValue.read_eq_blank_iff.mp hblank)
  have hdispatch := entryUpdateTM_step_match_replace_internal tapes matchDone
    hmatchHalt hresultOne hreplacementNonblank hmatchInputParked
    hmatchInv.parked hmatchOutputParked
  have hmatchMarked := hmatchInv.markFound_internal hmatchFoundZero
  have hreadyMarked := hready.markFound_internal hfoundZero
  have hmarkedReplacement :
      (entryUpdateMarkFoundWork tapes matchDone.work
        tapes.replacement).HasBinaryNat newValue := by
    rw [entryUpdateMarkFoundWork_apply_ne_internal tapes matchDone.work
      tapes.replacement tapes.replacement_ne_found]
    exact hmatchReplacementValue
  have hmatchOutputPrefix : matchDone.output.HasBinaryPrefix
      (outPrefix ++ emitted.flatMap Entry.encode) := by
    rw [hmatchOutput]
    exact houtput
  have hreplaceContract := entryReplaceCleanupTM_hoareTime_frame
    tapes.replace entry newValue (rest.flatMap Entry.encode) address.bits
    (outPrefix ++ emitted.flatMap Entry.encode)
    (entryUpdateMarkFoundWork tapes work)
    (entryUpdateMarkFoundWork tapes matchDone.work)
    matchDone.input matchDone.output hmatchMarked hmarkedReplacement
    hmatchInputParked hmatchOutputPrefix
  obtain ⟨replaceDone, replaceTime, hreplaceTime, hreplaceReach,
      hreplaceHalt, hreplaceInput, hreplaceReady, hreplaceReplacement,
      hreplaceOutput⟩ :=
    hreplaceContract matchDone.input
      (entryUpdateMarkFoundWork tapes matchDone.work) matchDone.output
      ⟨rfl, rfl, rfl⟩
  have hreplaceReach' :=
    entryUpdateTM_replace_reachesIn_internal tapes hreplaceReach
  have hreplaceInputParked : TM.Parked replaceDone.input := by
    rw [hreplaceInput]
    exact hmatchInputParked
  have hreplaceOutputParked : TM.Parked replaceDone.output :=
    parked_of_binaryPrefix_internal hreplaceOutput
  have hreplaceSeam := entryUpdateTM_step_replace_halt_internal tapes
    replaceDone hreplaceHalt hreplaceInputParked hreplaceReady.parked
    hreplaceOutputParked
  have hreplaceRemaining :
      (replaceDone.work tapes.remaining).HasBinaryNat (rest.length + 1) := by
    rw [hreplaceReady.frame_outside_entry_internal tapes.remaining
      tapes.remaining_ne_entry]
    rw [entryUpdateMarkFoundWork_apply_ne_internal tapes work
      tapes.remaining tapes.remaining_ne_found]
    exact hremainingPositive
  obtain ⟨remainingDone, hremainingReach, hremainingHalt,
      hremainingInput, hremainingOther, hremainingValue,
      hremainingOutput⟩ :=
    TM.binaryPredTM_reachesIn_frame tapes.remaining rest.length
      replaceDone.input replaceDone.work replaceDone.output hreplaceRemaining
      hreplaceInputParked.read_ne_start
      (fun i _ => (hreplaceReady.parked i).read_ne_start)
      hreplaceOutputParked.read_ne_start
  have hremainingReach' :=
    entryUpdateTM_remaining_reachesIn_internal tapes hremainingReach
  have hremainingInputParked : TM.Parked remainingDone.input := by
    rw [hremainingInput]
    exact hreplaceInputParked
  have hremainingWorkParked : ∀ i, TM.Parked (remainingDone.work i) := by
    intro i
    by_cases hi : i = tapes.remaining
    · subst i
      exact entryUpdateParked_of_hasBinaryNat_internal hremainingValue
    · rw [hremainingOther i hi]
      exact hreplaceReady.parked i
  have hremainingOutputParked : TM.Parked remainingDone.output := by
    rw [hremainingOutput]
    exact hreplaceOutputParked
  have hloop := entryUpdateTM_step_remaining_halt_internal tapes
    remainingDone hremainingHalt hremainingInputParked hremainingWorkParked
    hremainingOutputParked
  have hprefix : (entryUpdateTM tapes).reachesIn (matchTime + 1)
      (entryUpdateTestCfg tapes inp work out)
      (entryUpdateMatchWrap tapes matchDone) :=
    .step htest hmatchReach'
  have htoReplace : (entryUpdateTM tapes).reachesIn
      (matchTime + 1 + 1)
      (entryUpdateTestCfg tapes inp work out)
      (entryUpdateReplaceWrap tapes
        { state := (entryReplaceCleanupTM tapes.replace).qstart
          input := matchDone.input
          work := entryUpdateMarkFoundWork tapes matchDone.work
          output := matchDone.output }) :=
    TM.reachesIn_trans _ hprefix (.step hdispatch .zero)
  have hthroughReplace := TM.reachesIn_trans (entryUpdateTM tapes)
    htoReplace hreplaceReach'
  have htoRemaining := TM.reachesIn_trans (entryUpdateTM tapes)
    hthroughReplace (.step hreplaceSeam .zero)
  have hthroughRemaining := TM.reachesIn_trans (entryUpdateTM tapes)
    htoRemaining hremainingReach'
  have htotalReach := TM.reachesIn_trans (entryUpdateTM tapes)
    hthroughRemaining (.step hloop .zero)
  have hinputEq : remainingDone.input = inp :=
    hremainingInput.trans (hreplaceInput.trans hmatchInput)
  have hinvFinal := entryUpdateReplace_finalInvariant tapes store address newValue
    processed emitted entry rest resultCount initialWork work matchDone.work replaceDone.work
    remainingDone.work hinv haddress hvalue hfoundZero hmatchReplacement
    hreplaceReady hreplaceReplacement hremainingOther hremainingValue
  have hreplaceBound : replaceTime ≤
      entryUpdateReplaceTime tapes entry address newValue := by
    exact hreplaceTime.trans
      (entryReplaceCleanupTime_le_entryUpdateReplaceTime_internal tapes entry
        address newValue (rest.flatMap Entry.encode)
        (entryUpdateMarkFoundWork tapes work)
        (entryUpdateMarkFoundWork tapes work)
        (entryUpdateMarkFoundWork tapes matchDone.work)
        hreadyMarked hmatchMarked)
  have hreplaceBranchBound : replaceTime + 1 ≤
      entryUpdateBranchTime tapes entry address newValue store.length := by
    have hfixed : entryUpdateReplaceTime tapes entry address newValue + 1 ≤
        entryUpdateBranchTime tapes entry address newValue store.length := by
      unfold entryUpdateBranchTime
      exact (le_max_left _ _).trans (le_max_right _ _)
    omega
  refine ⟨remainingDone.work, remainingDone.output,
    matchTime + 1 + 1 + replaceTime + 1 +
      TM.binaryPredTime rest.length + 1,
    ?_, ?_, hinvFinal, ?_⟩
  · unfold entryUpdateIterationTime entryUpdateBranchTime
    omega
  · simpa [hinputEq, Nat.add_assoc] using htotalReach
  · simpa [List.flatMap_append, haddress, List.append_assoc,
      hremainingOutput] using hreplaceOutput

end Machine

end RegisterStore

end RAM

end Complexity
